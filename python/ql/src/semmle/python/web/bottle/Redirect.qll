/** Provides class representing the `bottle.redirect` function.
 * This module is intended to be imported into a taint-tracking query
 * to extend `TaintSink`.
 */
import python

import semmle.python.security.TaintTracking
import semmle.python.security.strings.Basic
import semmle.python.web.bottle.General

FunctionObject bottle_redirect() {
    result = theBottleModule().attr("redirect")
}

/**
 * Represents an argument to the `bottle.redirect` function.
 */
class BottleRedirect extends TaintSink {

    override string toString() {
        result = "bottle.redirect"
    }

    BottleRedirect() {
        exists(CallNode call |
            bottle_redirect().getACall() = call and
            this = call.getAnArg()
        )
    }

    override predicate sinks(TaintKind kind) {
        kind instanceof StringKind
    }

}
