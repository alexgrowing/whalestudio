package demo;

import java.io.FileReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

/**
 * @author conner
 * @version 5.1.2
 * Created by conner on 2019/12/30
 */
public class Main {
    public static void main(String[] args) throws Exception {
        List<String> data = new ArrayList<>();
        Scanner sc = new Scanner(new FileReader("/Users/sean/MiniZone/code/go_workspace/src/SuRF/random.txt"));
        String line = null;
        while ((sc.hasNextLine() && (line = sc.nextLine()) != null)) {
            data.add(line);
        }
        sc.close();
        int lineSize = data.size();

        long start = System.currentTimeMillis();
        String[] toFindArray = data.toArray(new String[0]);
        Map<String, Integer> map = new HashMap<>();
        for (String s : data.toArray(new String[0])) {
            map.put(s, 1);
        }
        System.out.println("build map " + lineSize + " times:" + (System.currentTimeMillis() - start) + "ms");

        for (int j = 0; j < 5; j++) {
            start = System.currentTimeMillis();
            for (int i = 0; i < lineSize; i++) {
                read(map.get(toFindArray[i]));
            }
            System.out.println("get operation " + lineSize + " times:" + (System.currentTimeMillis() - start) + "ms");
        }

    }

    public static void read(Integer i) {

    }
}
