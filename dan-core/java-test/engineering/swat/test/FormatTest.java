package engineering.swat.test;

import static io.parsingdata.metal.util.EncodingFactory.enc;
import static io.parsingdata.metal.util.ParseStateFactory.stream;

import java.io.IOException;
import java.net.URISyntaxException;
import java.util.Arrays;
import java.util.Collection;

import org.junit.runners.Parameterized;

import engineering.swat.formats.SimpleJPEG;
import engineering.swat.formats.SimplePNG;
import io.parsingdata.metal.data.ParseState;
import io.parsingdata.metal.util.ParameterizedParse;

public class FormatTest extends ParameterizedParse {

    @Parameterized.Parameters(name="{0} ({4})")
    public static Collection<Object[]> data() throws URISyntaxException, IOException {
        return Arrays.asList(new Object[][] {
            { "PNG", SimplePNG.PNG, parseState("/test.png"), enc(), true },
            { "JPEG", SimpleJPEG.Format, parseState("/test.jpg"), enc(), true }
        });
    }

    private static ParseState parseState(final String path) throws URISyntaxException, IOException {
        return stream(FormatTest.class.getResource(path).toURI());
    }

}
