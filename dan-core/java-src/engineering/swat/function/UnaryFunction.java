package engineering.swat.function;

import java.util.Optional;

import io.parsingdata.metal.data.ParseState;
import io.parsingdata.metal.encoding.Encoding;
import io.parsingdata.metal.expression.value.UnaryValueExpression;
import io.parsingdata.metal.expression.value.Value;
import io.parsingdata.metal.expression.value.ValueExpression;

public abstract class UnaryFunction {

	public abstract Optional<Value> internalApply(Value v, Encoding encoding);
	
	public ValueExpression apply(final ValueExpression target) {
        return new UnaryValueExpression(target) {
            @Override
            public Optional<Value> eval(final Value value, final ParseState parseState, final Encoding encoding) {
                return internalApply(value, encoding);
            }
        };
    }

}
