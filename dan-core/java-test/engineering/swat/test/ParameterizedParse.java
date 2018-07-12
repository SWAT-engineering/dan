package engineering.swat.test;

import static io.parsingdata.metal.util.EnvironmentFactory.env;
import static org.junit.Assert.assertEquals;

import java.io.IOException;
import java.util.Optional;

import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;

import io.parsingdata.metal.data.ParseState;
import io.parsingdata.metal.encoding.Encoding;
import io.parsingdata.metal.token.Token;

@Ignore
@RunWith(Parameterized.class)
public class ParameterizedParse {

    @Parameter public String description;
    @Parameter(1) public Token token;
    @Parameter(2) public ParseState parseState;
    @Parameter(3) public Encoding encoding;
    @Parameter(4) public boolean result;
    @Parameter(5) public String format;
    @Parameter(6) public String fileName;
    @Parameter(7) public long fileSize;

    @Test
    public void test() throws IOException {
    	Optional<ParseState> graph = token.parse(env(parseState, encoding));
        System.out.println("Result of parsing "+ fileName+ " with "+ format+ " specification:");
        System.out.println();
        System.out.println(graph.toString());
        System.out.println("====================================================================================================");
        System.out.println();
    	assertEquals(result, graph.isPresent());
    	if (graph.isPresent())
    		assertEquals(fileSize, graph.get().offset.longValue());
    }

}
