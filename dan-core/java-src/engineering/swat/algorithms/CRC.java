package engineering.swat.algorithms;

import static io.parsingdata.metal.data.Slice.createFromBytes;

import java.util.Optional;
import java.util.zip.CRC32;

import engineering.swat.function.UnaryFunction;
import io.parsingdata.metal.encoding.Encoding;
import io.parsingdata.metal.expression.value.Value;

public class CRC extends UnaryFunction{

	@Override
	public Optional<Value> internalApply(Value value, Encoding encoding) {
		final CRC32 crc = new CRC32();
        crc.update(value.getValue());
        final long crcValue = crc.getValue();
        return Optional.of(new Value(createFromBytes(encoding.byteOrder.apply(new byte[] {
            (byte)((crcValue & 0xff000000) >> 24),
            (byte)((crcValue & 0xff0000) >> 16),
            (byte)((crcValue & 0xff00) >> 8),
            (byte) (crcValue & 0xff) })), encoding));
	}
	
	
}
