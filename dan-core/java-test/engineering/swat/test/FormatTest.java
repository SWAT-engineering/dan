package engineering.swat.test;

import static io.parsingdata.metal.util.EncodingFactory.enc;
import static io.parsingdata.metal.util.ParseStateFactory.stream;

import java.io.IOException;
import java.lang.reflect.Field;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.json.JSONException;
import org.json.JSONObject;
import org.json.JSONTokener;
import org.junit.runners.Parameterized;

import io.parsingdata.metal.data.ParseState;
import io.parsingdata.metal.token.Token;

public class FormatTest extends ParameterizedParse {
	
	public static final String CONFIG_FILE_PATH = "/test-properties.json";

    @Parameterized.Parameters(name="{0} ({5})")
    public static Collection<Object[]> data() throws URISyntaxException, IOException {
    	return json2list(parseProperties(CONFIG_FILE_PATH));
    }
    
    private static JSONObject parseProperties(final String path) throws MalformedURLException, IOException, URISyntaxException {
    	JSONTokener tokener = new JSONTokener(FormatTest.class.getResource(path).toURI().toURL().openStream());
    	return new JSONObject(tokener);
    }
    
    private static Collection<Object[]> json2list(JSONObject json) throws URISyntaxException, IOException{
    	List<Object[]> list = new ArrayList<>();
    	for (String format: json.keySet()) {
    		for (int i = 0; i < json.getJSONArray(format).length(); i++) {
    			String[] formatAndTokenStart = format.split("\\.");
    			try {
					Class clz = Class.forName("engineering.swat.formats." + formatAndTokenStart[0]);
					Field f = clz.getField(formatAndTokenStart[1]);
					String fileName = json.getJSONArray(format).getString(i);
					list.add(new Object[]{ format + Integer.toString(i), (Token) f.get(null), parseState(formatAndTokenStart[0], "/" + fileName), enc(), true,  formatAndTokenStart[0], fileName});
				} catch (ClassNotFoundException | SecurityException  | NoSuchFieldException | IllegalArgumentException | IllegalAccessException | JSONException e) {
					e.printStackTrace();
				} 
    		}
    	}
    	return list;
    }

    private static ParseState parseState(final String format, final String path) throws URISyntaxException, IOException {
        return stream(FormatTest.class.getResource(path).toURI());
    }

}
