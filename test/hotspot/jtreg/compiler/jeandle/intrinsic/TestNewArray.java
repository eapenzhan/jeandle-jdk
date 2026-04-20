/*
 * Copyright (c) 2026, the Jeandle-JDK Authors. All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * @test
 * @summary Test _newArray intrinsic (Array.newInstance) via Jeandle compiler
 * @library /test/lib
 * @run main/othervm -XX:+UseJeandleCompiler -XX:-TieredCompilation -Xcomp
 *      -XX:CompileCommand=compileonly,TestNewArray::*
 *      TestNewArray
 */

import java.lang.reflect.Array;

public class TestNewArray {

    static Object createIntArray(int len) {
        return Array.newInstance(int.class, len);
    }

    static Object createObjectArray(int len) {
        return Array.newInstance(Object.class, len);
    }

    static Object createStringArray(int len) {
        return Array.newInstance(String.class, len);
    }

    public static void main(String[] args) throws Exception {
        // Warm up to trigger Jeandle compilation
        for (int i = 0; i < 3; i++) {
            Object ia = createIntArray(10);
            if (!(ia instanceof int[])) throw new RuntimeException("Expected int[], got: " + ia.getClass());
            if (((int[]) ia).length != 10) throw new RuntimeException("Wrong length: " + ((int[]) ia).length);

            Object oa = createObjectArray(5);
            if (!(oa instanceof Object[])) throw new RuntimeException("Expected Object[], got: " + oa.getClass());
            if (((Object[]) oa).length != 5) throw new RuntimeException("Wrong length: " + ((Object[]) oa).length);

            Object sa = createStringArray(3);
            if (!(sa instanceof String[])) throw new RuntimeException("Expected String[], got: " + sa.getClass());
            if (((String[]) sa).length != 3) throw new RuntimeException("Wrong length: " + ((String[]) sa).length);
        }

        // Zero-length array
        Object zero = createIntArray(0);
        if (((int[]) zero).length != 0) throw new RuntimeException("Zero-length failed");

        // NegativeArraySizeException
        try {
            createIntArray(-1);
            throw new RuntimeException("Expected NegativeArraySizeException");
        } catch (NegativeArraySizeException e) {
            // expected
        }

        // NullPointerException via null component type (only via reflection path)
        try {
            Array.newInstance(null, 5);
            throw new RuntimeException("Expected NullPointerException");
        } catch (NullPointerException e) {
            // expected
        }

        System.out.println("TestNewArray PASSED");
    }
}
