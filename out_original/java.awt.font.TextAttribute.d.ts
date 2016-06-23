/// <reference path="./_helpers.d.ts" />
/// <reference path="./java.lang.Boolean.d.ts" />
/// <reference path="./java.lang.Float.d.ts" />
/// <reference path="./java.lang.Integer.d.ts" />
/// <reference path="./java.lang.String.d.ts" />

declare module java {
	export module awt {
		export module font {
			export class TextAttribute {
				public constructor();
				public constructor(param0: string);
				public static BACKGROUND: java.awt.font.TextAttribute;
				public static BIDI_EMBEDDING: java.awt.font.TextAttribute;
				public static CHAR_REPLACEMENT: java.awt.font.TextAttribute;
				public static FAMILY: java.awt.font.TextAttribute;
				public static FONT: java.awt.font.TextAttribute;
				public static FOREGROUND: java.awt.font.TextAttribute;
				public static INPUT_METHOD_HIGHLIGHT: java.awt.font.TextAttribute;
				public static INPUT_METHOD_UNDERLINE: java.awt.font.TextAttribute;
				public static JUSTIFICATION: java.awt.font.TextAttribute;
				public static JUSTIFICATION_FULL: java.lang.Float;
				public static JUSTIFICATION_NONE: java.lang.Float;
				public static KERNING: java.awt.font.TextAttribute;
				public static KERNING_ON: java.lang.Integer;
				public static LIGATURES: java.awt.font.TextAttribute;
				public static LIGATURES_ON: java.lang.Integer;
				public static NUMERIC_SHAPING: java.awt.font.TextAttribute;
				public static POSTURE: java.awt.font.TextAttribute;
				public static POSTURE_OBLIQUE: java.lang.Float;
				public static POSTURE_REGULAR: java.lang.Float;
				public static RUN_DIRECTION: java.awt.font.TextAttribute;
				public static RUN_DIRECTION_LTR: java.lang.Boolean;
				public static RUN_DIRECTION_RTL: java.lang.Boolean;
				public static SIZE: java.awt.font.TextAttribute;
				public static STRIKETHROUGH: java.awt.font.TextAttribute;
				public static STRIKETHROUGH_ON: java.lang.Boolean;
				public static SUPERSCRIPT: java.awt.font.TextAttribute;
				public static SUPERSCRIPT_SUB: java.lang.Integer;
				public static SUPERSCRIPT_SUPER: java.lang.Integer;
				public static SWAP_COLORS: java.awt.font.TextAttribute;
				public static SWAP_COLORS_ON: java.lang.Boolean;
				public static TRACKING: java.awt.font.TextAttribute;
				public static TRACKING_LOOSE: java.lang.Float;
				public static TRACKING_TIGHT: java.lang.Float;
				public static TRANSFORM: java.awt.font.TextAttribute;
				public static UNDERLINE: java.awt.font.TextAttribute;
				public static UNDERLINE_LOW_DASHED: java.lang.Integer;
				public static UNDERLINE_LOW_DOTTED: java.lang.Integer;
				public static UNDERLINE_LOW_GRAY: java.lang.Integer;
				public static UNDERLINE_LOW_ONE_PIXEL: java.lang.Integer;
				public static UNDERLINE_LOW_TWO_PIXEL: java.lang.Integer;
				public static UNDERLINE_ON: java.lang.Integer;
				public static WEIGHT: java.awt.font.TextAttribute;
				public static WEIGHT_BOLD: java.lang.Float;
				public static WEIGHT_DEMIBOLD: java.lang.Float;
				public static WEIGHT_DEMILIGHT: java.lang.Float;
				public static WEIGHT_EXTRABOLD: java.lang.Float;
				public static WEIGHT_EXTRA_LIGHT: java.lang.Float;
				public static WEIGHT_HEAVY: java.lang.Float;
				public static WEIGHT_LIGHT: java.lang.Float;
				public static WEIGHT_MEDIUM: java.lang.Float;
				public static WEIGHT_REGULAR: java.lang.Float;
				public static WEIGHT_SEMIBOLD: java.lang.Float;
				public static WEIGHT_ULTRABOLD: java.lang.Float;
				public static WIDTH: java.awt.font.TextAttribute;
				public static WIDTH_CONDENSED: java.lang.Float;
				public static WIDTH_EXTENDED: java.lang.Float;
				public static WIDTH_REGULAR: java.lang.Float;
				public static WIDTH_SEMI_CONDENSED: java.lang.Float;
				public static WIDTH_SEMI_EXTENDED: java.lang.Float;
			}
		}
	}
}