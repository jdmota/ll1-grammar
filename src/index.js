// @flow
/* eslint no-console: 0 */

const EMPTY = "EMPTY";

class Rule {

  +name: string;
  +rightside: string[];
  +grammar: Grammar;
  _canBeEmpty: ?boolean;

  constructor( name: string, rightside: string, grammar: Grammar ) {
    this.name = name;
    this.rightside = rightside.trim().split( /\s+/ ).filter( e => e !== EMPTY );
    this.grammar = grammar;
    this._canBeEmpty = undefined;
  }

  canBeEmpty( stack: Set<string> = new Set() ): boolean {
    if ( this._canBeEmpty != null ) {
      return this._canBeEmpty;
    }
    return ( this._canBeEmpty = this.grammar.canBeEmpty( this.rightside, stack ) );
  }

  toString() {
    return `${this.name} = ${this.rightside.join( " " )}`;
  }

}

const emptySet = new Set();

class Grammar {

  +initial: string;
  +rules: Rule[];
  +rulesByName: Map<string, Rule[]>;
  +firstCache: Map<string, Set<string>>;
  +whereItShowsCache: Map<string, [Rule, string[]][]>;
  +followCache: Map<string, Set<string>>;
  +lookaheadCache: Map<Rule, Set<string>>;
  +canBeEmptyCache: Map<string, boolean>;
  +terminals: Set<string>;
  +table: Map<string, Map<string, Rule>>;

  constructor( grammarText ) {
    this.rules = [];
    this.rulesByName = new Map();
    this.firstCache = new Map();
    this.whereItShowsCache = new Map();
    this.followCache = new Map();
    this.lookaheadCache = new Map();
    this.canBeEmptyCache = new Map();
    this.terminals = new Set();

    grammarText.split( /\r?\n/ ).map( x => x.trim() ).filter( Boolean ).forEach( text => {

      const i = text.indexOf( "=" );
      const name = text.slice( 0, i ).trim();
      const rightside = text.slice( i + 1 ).trim();

      if ( name && rightside ) {
        this.addRule( name, new Rule( name, rightside, this ) );
      }

    } );

    if ( this.rules.length === 0 ) {
      throw new Error( "No rules found in this grammar" );
    }

    this.initial = this.rules[ 0 ].name;

    // Extract terminals
    this.rulesByName.forEach( rules => {
      for ( const rule of rules ) {
        for ( const v of rule.rightside ) {
          if ( !this.rulesByName.has( v ) ) {
            this.terminals.add( v );
          }
        }
      }
    } );

    // Create table
    this.table = this.parserTable();

  }

  isTerminal( v ) {
    return this.terminals.has( v );
  }

  addRule( variable: string, rule: Rule ) {

    let options = this.rulesByName.get( variable );

    if ( !options ) {
      options = [];
      this.rulesByName.set( variable, options );
    }

    options.push( rule );
    this.rules.push( rule );
  }

  getRules( variable: string ) {
    const arr = this.rulesByName.get( variable );
    if ( !arr ) {
      throw new Error( `Variable ${variable} not found` );
    }
    return arr;
  }

  canBeEmpty( variable: string[] | string, stack: Set<string> = new Set() ): boolean {

    if ( Array.isArray( variable ) ) {
      for ( const v of variable ) {
        if ( !this.canBeEmpty( v, stack ) ) {
          return false;
        }
      }
      return true;
    }

    if ( this.isTerminal( variable ) ) {
      return false;
    }

    if ( stack.has( variable ) ) {
      return false;
    }

    // Cache
    const cache = this.canBeEmptyCache.get( variable );
    if ( cache !== undefined ) return cache;

    let result = false;

    // Compute

    stack.add( variable );

    const rules = this.getRules( variable );

    for ( const rule of rules ) {
      if ( rule.canBeEmpty( stack ) ) {
        result = true;
        break;
      }
    }

    stack.delete( variable );

    this.canBeEmptyCache.set( variable, result );
    return result;
  }

  first( variables: string[], stack: Set<string> = new Set() ): Set<string> {

    if ( variables.length === 0 ) {
      return emptySet;
    }

    const variable = variables[ 0 ];

    if ( this.isTerminal( variable ) ) {
      return new Set( [ variable ] );
    }

    if ( stack.has( variable ) ) {
      throw new Error( `Variable ${variable} is left recursive` );
    }

    // Cache
    const cache = this.firstCache.get( variable );
    if ( cache ) return cache;

    const result = new Set();
    this.firstCache.set( variable, result );

    // Compute

    stack.add( variable );

    this.getRules( variable ).forEach( rule => {
      this.first( rule.rightside, stack ).forEach( t => result.add( t ) );
    } );

    if ( variables.length > 1 && this.canBeEmpty( variable ) ) {
      this.first( variables.slice( 1 ), stack ).forEach( t => result.add( t ) );
    }

    stack.delete( variable );

    return result;
  }

  whereItShows( variable: string ): [Rule, string[]][] {

    // Cache
    const cache = this.whereItShowsCache.get( variable );
    if ( cache ) return cache;

    // Compute

    const wheres = [];
    this.whereItShowsCache.set( variable, wheres );

    for ( const rule of this.rules ) {
      const idx = rule.rightside.indexOf( variable );
      if ( idx > -1 ) {
        wheres.push( [ rule, rule.rightside.slice( idx + 1 ) ] );
      }
    }
    return wheres;
  }

  follow( variable: string, stack: Set<string> = new Set() ): Set<string> {

    if ( stack.has( variable ) ) {
      return emptySet;
    }

    // Cache
    const cache = this.followCache.get( variable );
    if ( cache ) return cache;

    const result = new Set();
    this.followCache.set( variable, result );

    // Compute

    const wheres = this.whereItShows( variable );

    if ( wheres.length === 0 ) {
      return result;
    }

    stack.add( variable );

    for ( const [ rule, next ] of wheres ) {
      this.first( next ).forEach( t => result.add( t ) );
      if ( this.canBeEmpty( next ) ) {
        this.follow( rule.name, stack ).forEach( t => result.add( t ) );
      }
    }

    stack.delete( variable );

    return result;
  }

  lookahead( rule: Rule ): Set<string> {

    // Cache
    const cache = this.lookaheadCache.get( rule );
    if ( cache ) return cache;

    const result = new Set();
    this.lookaheadCache.set( rule, result );

    // Compute

    this.first( rule.rightside ).forEach( t => result.add( t ) );

    if ( rule.canBeEmpty() ) {
      this.follow( rule.name ).forEach( t => result.add( t ) );
    }

    return result;
  }

  checkDeterminism() {

    for ( const [ name, rules ] of this.rulesByName ) {
      const looks = new Set();

      for ( const rule of rules ) {

        for ( const look of this.lookahead( rule ) ) {
          if ( looks.has( look ) ) {
            throw new Error( `There is a collision on variable ${name}` );
          }
          looks.add( look );
        }
      }
    }

  }

  parserTable() {

    const table = new Map();

    for ( const [ name, rules ] of this.rulesByName ) {

      const line = new Map();
      table.set( name, line );

      for ( const rule of rules ) {

        for ( const look of this.lookahead( rule ) ) {
          line.set( look, rule );
        }

        if ( rule.canBeEmpty() ) {
          line.set( EMPTY, rule );
        }
      }

    }

    return table;
  }

  parse( text ) {

    const tokens = text.trim().split( /\r?\n|\s/ ).map( x => x.trim() ).filter( Boolean );
    const entry = tokens.reverse();
    const stack = [ this.initial ];

    while ( stack.length ) {

      const firstVar = stack[ stack.length - 1 ];
      const firstSym = entry[ entry.length - 1 ];

      if ( firstVar === firstSym ) {
        entry.pop();
        stack.pop();
      } else if ( this.isTerminal( firstVar ) ) {
        break;
      } else {

        const line = this.table.get( firstVar );
        const rule = line && line.get( firstSym || EMPTY );

        if ( rule ) {

          stack.pop();

          const rightside = rule.rightside;
          let i = rightside.length;
          while ( i-- ) {
            stack.push( rightside[ i ] );
          }

        } else {
          break;
        }

      }

    }

    return stack.length === 0 && entry.length === 0;
  }

}

const path = require( "path" );
const fs = require( "fs" );

const grammarText = fs.readFileSync( path.resolve( __dirname, "grammar" ), "utf8" );
const exampleText = fs.readFileSync( path.resolve( __dirname, "example" ), "utf8" );

const grammar = new Grammar( grammarText );

try {

  grammar.checkDeterminism();

  console.log( "Grammar is deterministic" );

  const ok = grammar.parse( exampleText );

  console.log( ok ? "Success" : "Didn't parse" );

} catch ( e ) {

  if ( /There is a collision/.test( e.message ) ) {
    console.error( e.message, ", so this grammar is not deterministic" );
  } else {
    console.error( e.stack );
  }

}
