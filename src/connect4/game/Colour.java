package connect4.game;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public enum Colour {
	//All colours from wikipedia with duplicate names removed.
	VOID(null),
	ABSOLUTE_ZERO("#0048BA"),
	ACID_GREEN("#B0BF1A"),
	AERO("#7CB9E8"),
	AERO_BLUE("#C9FFE5"),
	AFRICAN_VIOLET("#B284BE"),
	AIR_FORCE_BLUE("#5D8AA8"),
	AIR_SUPERIORITY_BLUE("#72A0C1"),
	ALABAMA_CRIMSON("#AF002A"),
	ALABASTER("#F2F0E6"),
	ALICE_BLUE("#F0F8FF"),
	ALIEN_ARMPIT("#84DE02"),
	ALIZARIN_CRIMSON("#E32636"),
	ALLOY_ORANGE("#C46210"),
	ALMOND("#EFDECD"),
	AMARANTH("#E52B50"),
	AMARANTH_DEEP_PURPLE("#9F2B68"),
	AMARANTH_PINK("#F19CBB"),
	AMARANTH_PURPLE("#AB274F"),
	AMARANTH_RED("#D3212D"),
	AMAZON("#3B7A57"),
	AMAZONITE("#00C4B0"),
	AMBER("#FFBF00"),
	AMERICAN_ROSE("#FF033E"),
	AMETHYST("#9966CC"),
	ANDROID_GREEN("#A4C639"),
	ANTI_FLASH_WHITE("#F2F3F4"),
	ANTIQUE_BRASS("#CD9575"),
	ANTIQUE_BRONZE("#665D1E"),
	ANTIQUE_FUCHSIA("#915C83"),
	ANTIQUE_RUBY("#841B2D"),
	ANTIQUE_WHITE("#FAEBD7"),
	AO("#008000"),
	APPLE_GREEN("#8DB600"),
	APRICOT("#FBCEB1"),
	AQUA("#00FFFF"),
	AQUAMARINE("#7FFFD4"),
	ARCTIC_LIME("#D0FF14"),
	ARMY_GREEN("#4B5320"),
	ARSENIC("#3B444B"),
	ARTICHOKE("#8F9779"),
	ARYLIDE_YELLOW("#E9D66B"),
	ASH_GREY("#B2BEB5"),
	ASPARAGUS("#87A96B"),
	ATOMIC_TANGERINE("#FF9966"),
	AUBURN("#A52A2A"),
	AUREOLIN("#FDEE00"),
	AUROMETALSAURUS("#6E7F80"),
	AVOCADO("#568203"),
	AWESOME("#FF2052"),
	AZTEC_GOLD("#C39953"),
	AZURE("#007FFF"),
	AZURE_MIST("#F0FFFF"),
	AZUREISH_WHITE("#DBE9F4"),
	BABY_BLUE("#89CFF0"),
	BABY_BLUE_EYES("#A1CAF1"),
	BABY_PINK("#F4C2C2"),
	BABY_POWDER("#FEFEFA"),
	BAKER_MILLER_PINK("#FF91AF"),
	BALL_BLUE("#21ABCD"),
	BANANA_MANIA("#FAE7B5"),
	BANANA_YELLOW("#FFE135"),
	BANGLADESH_GREEN("#006A4E"),
	BARBIE_PINK("#E0218A"),
	BARN_RED("#7C0A02"),
	BATTERY_CHARGED_BLUE("#1DACD6"),
	BATTLESHIP_GREY("#848482"),
	BAZAAR("#98777B"),
	BEAU_BLUE("#BCD4E6"),
	BEAVER("#9F8170"),
	BEGONIA("#FA6E79"),
	BEIGE("#F5F5DC"),
	B_DAZZLED_BLUE("#2E5894"),
	BIG_DIP_O_RUBY("#9C2542"),
	BIG_FOOT_FEET("#E88E5A"),
	BISQUE("#FFE4C4"),
	BISTRE("#3D2B1F"),
	BISTRE_BROWN("#967117"),
	BITTER_LEMON("#CAE00D"),
	BITTER_LIME("#BFFF00"),
	BITTERSWEET("#FE6F5E"),
	BITTERSWEET_SHIMMER("#BF4F51"),
	BLACK("#000000"),
	BLACK_BEAN("#3D0C02"),
	BLACK_CORAL("#54626F"),
	BLACK_LEATHER_JACKET("#253529"),
	BLACK_OLIVE("#3B3C36"),
	BLACK_SHADOWS("#BFAFB2"),
	BLANCHED_ALMOND("#FFEBCD"),
	BLAST_OFF_BRONZE("#A57164"),
	BLEU_DE_FRANCE("#318CE7"),
	BLIZZARD_BLUE("#ACE5EE"),
	BLOND("#FAF0BE"),
	BLUE("#0000FF"),
	BLUE_BELL("#A2A2D0"),
	BLUE_BOLT("#00B9FB"),
	BLUE_GRAY("#6699CC"),
	BLUE_GREEN("#0D98BA"),
	BLUE_JEANS("#5DADEC"),
	BLUE_LAGOON("#ACE5EE"),
	BLUE_MAGENTA_VIOLET("#553592"),
	BLUE_SAPPHIRE("#126180"),
	BLUE_VIOLET("#8A2BE2"),
	BLUE_YONDER("#5072A7"),
	BLUEBERRY("#4F86F7"),
	BLUEBONNET("#1C1CF0"),
	BLUSH("#DE5D83"),
	BOLE("#79443B"),
	BONDI_BLUE("#0095B6"),
	BONE("#E3DAC9"),
	BOOGER_BUSTER("#DDE26A"),
	BOSTON_UNIVERSITY_RED("#CC0000"),
	BOTTLE_GREEN("#006A4E"),
	BOYSENBERRY("#873260"),
	BRANDEIS_BLUE("#0070FF"),
	BRASS("#B5A642"),
	BRICK_RED("#CB4154"),
	BRIGHT_CERULEAN("#1DACD6"),
	BRIGHT_GREEN("#66FF00"),
	BRIGHT_LAVENDER("#BF94E4"),
	BRIGHT_LILAC("#D891EF"),
	BRIGHT_MAROON("#C32148"),
	BRIGHT_NAVY_BLUE("#1974D2"),
	BRIGHT_PINK("#FF007F"),
	BRIGHT_TURQUOISE("#08E8DE"),
	BRIGHT_UBE("#D19FE8"),
	BRIGHT_YELLOW("#FFAA1D"),
	BRILLIANT_AZURE("#3399FF"),
	BRILLIANT_LAVENDER("#F4BBFF"),
	BRILLIANT_ROSE("#FF55A3"),
	BRINK_PINK("#FB607F"),
	BRITISH_RACING_GREEN("#004225"),
	BRONZE("#CD7F32"),
	BRONZE_YELLOW("#737000"),
	BROWN("#964B00"),
	BROWN_NOSE("#6B4423"),
	BROWN_SUGAR("#AF6E4D"),
	BROWN_YELLOW("#cc9966"),
	BRUNSWICK_GREEN("#1B4D3E"),
	BUBBLE_GUM("#FFC1CC"),
	BUBBLES("#E7FEFF"),
	BUD_GREEN("#7BB661"),
	BUFF("#F0DC82"),
	BULGARIAN_ROSE("#480607"),
	BURGUNDY("#800020"),
	BURLYWOOD("#DEB887"),
	BURNISHED_BROWN("#A17A74"),
	BURNT_ORANGE("#CC5500"),
	BURNT_SIENNA("#E97451"),
	BURNT_UMBER("#8A3324"),
	BUTTON_BLUE("#24A0ED"),
	BYZANTINE("#BD33A4"),
	BYZANTIUM("#702963"),
	CADET("#536872"),
	CADET_BLUE("#5F9EA0"),
	CADET_GREY("#91A3B0"),
	CADMIUM_GREEN("#006B3C"),
	CADMIUM_ORANGE("#ED872D"),
	CADMIUM_RED("#E30022"),
	CADMIUM_YELLOW("#FFF600"),
	CAL_POLY_POMONA_GREEN("#1E4D2B"),
	CAMBRIDGE_BLUE("#A3C1AD"),
	CAMEL("#C19A6B"),
	CAMEO_PINK("#EFBBCC"),
	CAMOUFLAGE_GREEN("#78866B"),
	CANARY("#FFFF99"),
	CANARY_YELLOW("#FFEF00"),
	CANDY_APPLE_RED("#FF0800"),
	CANDY_PINK("#E4717A"),
	CAPRI("#00BFFF"),
	CAPUT_MORTUUM("#592720"),
	CARDINAL("#C41E3A"),
	CARIBBEAN_GREEN("#00CC99"),
	CARMINE("#960018"),
	CARMINE_PINK("#EB4C42"),
	CARMINE_RED("#FF0038"),
	CARNATION_PINK("#FFA6C9"),
	CARNELIAN("#B31B1B"),
	CAROLINA_BLUE("#56A0D3"),
	CARROT_ORANGE("#ED9121"),
	CASTLETON_GREEN("#00563F"),
	CATALINA_BLUE("#062A78"),
	CATAWBA("#703642"),
	CEDAR_CHEST("#C95A49"),
	CEIL("#92A1CF"),
	CELADON("#ACE1AF"),
	CELADON_BLUE("#007BA7"),
	CELADON_GREEN("#2F847C"),
	CELESTE("#B2FFFF"),
	CELESTIAL_BLUE("#4997D0"),
	CERISE("#DE3163"),
	CERISE_PINK("#EC3B83"),
	CERULEAN("#007BA7"),
	CERULEAN_BLUE("#2A52BE"),
	CERULEAN_FROST("#6D9BC3"),
	CG_BLUE("#007AA5"),
	CG_RED("#E03C31"),
	CHAMOISEE("#A0785A"),
	CHAMPAGNE("#F7E7CE"),
	CHAMPAGNE_PINK("#F1DDCF"),
	CHARCOAL("#36454F"),
	CHARLESTON_GREEN("#232B2B"),
	CHARM_PINK("#E68FAC"),
	CHARTREUSE("#DFFF00"),
	CHERRY("#DE3163"),
	CHERRY_BLOSSOM_PINK("#FFB7C5"),
	CHESTNUT("#954535"),
	CHINA_PINK("#DE6FA1"),
	CHINA_ROSE("#A8516E"),
	CHINESE_RED("#AA381E"),
	CHINESE_VIOLET("#856088"),
	CHLOROPHYLL_GREEN("#4AFF00"),
	CHOCOLATE("#7B3F00"),
	CHROME_YELLOW("#FFA700"),
	CINEREOUS("#98817B"),
	CINNABAR("#E34234"),
	CINNAMON("#D2691E"),
	CINNAMON_SATIN("#CD607E"),
	CITRINE("#E4D00A"),
	CITRON("#9FA91F"),
	CLARET("#7F1734"),
	CLASSIC_ROSE("#FBCCE7"),
	COBALT_BLUE("#0047AB"),
	COCOA_BROWN("#D2691E"),
	COCONUT("#965A3E"),
	COFFEE("#6F4E37"),
	COLUMBIA_BLUE("#C4D8E2"),
	CONGO_PINK("#F88379"),
	COOL_BLACK("#002E63"),
	COOL_GREY("#8C92AC"),
	COPPER("#B87333"),
	COPPER_PENNY("#AD6F69"),
	COPPER_RED("#CB6D51"),
	COPPER_ROSE("#996666"),
	COQUELICOT("#FF3800"),
	CORAL("#FF7F50"),
	CORAL_PINK("#F88379"),
	CORAL_RED("#FF4040"),
	CORAL_REEF("#FD7C6E"),
	CORDOVAN("#893F45"),
	CORN("#FBEC5D"),
	CORNELL_RED("#B31B1B"),
	CORNFLOWER_BLUE("#6495ED"),
	CORNSILK("#FFF8DC"),
	COSMIC_COBALT("#2E2D88"),
	COSMIC_LATTE("#FFF8E7"),
	COYOTE_BROWN("#81613C"),
	COTTON_CANDY("#FFBCD9"),
	CREAM("#FFFDD0"),
	CRIMSON("#DC143C"),
	CRIMSON_GLORY("#BE0032"),
	CRIMSON_RED("#990000"),
	CULTURED("#F5F5F5"),
	CYAN("#00FFFF"),
	CYAN_AZURE("#4E82B4"),
	CYAN_BLUE_AZURE("#4682BF"),
	CYAN_COBALT_BLUE("#28589C"),
	CYAN_CORNFLOWER_BLUE("#188BC2"),
	CYBER_GRAPE("#58427C"),
	CYBER_YELLOW("#FFD300"),
	CYCLAMEN("#F56FA1"),
	DAFFODIL("#FFFF31"),
	DANDELION("#F0E130"),
	DARK_BLUE("#00008B"),
	DARK_BLUE_GRAY("#666699"),
	DARK_BROWN("#654321"),
	DARK_BROWN_TANGELO("#88654E"),
	DARK_BYZANTIUM("#5D3954"),
	DARK_CANDY_APPLE_RED("#A40000"),
	DARK_CERULEAN("#08457E"),
	DARK_CHESTNUT("#986960"),
	DARK_CORAL("#CD5B45"),
	DARK_CYAN("#008B8B"),
	DARK_ELECTRIC_BLUE("#536878"),
	DARK_GOLDENROD("#B8860B"),
	DARK_GRAY("#A9A9A9"),
	DARK_GREEN("#013220"),
	DARK_GUNMETAL("#1F262A"),
	DARK_IMPERIAL_BLUE("#00416A"),
	DARK_JUNGLE_GREEN("#1A2421"),
	DARK_KHAKI("#BDB76B"),
	DARK_LAVA("#483C32"),
	DARK_LAVENDER("#734F96"),
	DARK_LIVER("#534B4F"),
	DARK_MAGENTA("#8B008B"),
	DARK_MEDIUM_GRAY("#A9A9A9"),
	DARK_MIDNIGHT_BLUE("#003366"),
	DARK_MOSS_GREEN("#4A5D23"),
	DARK_OLIVE_GREEN("#556B2F"),
	DARK_ORANGE("#FF8C00"),
	DARK_ORCHID("#9932CC"),
	DARK_PASTEL_BLUE("#779ECB"),
	DARK_PASTEL_GREEN("#03C03C"),
	DARK_PASTEL_PURPLE("#966FD6"),
	DARK_PASTEL_RED("#C23B22"),
	DARK_PINK("#E75480"),
	DARK_POWDER_BLUE("#003399"),
	DARK_PUCE("#4F3A3C"),
	DARK_PURPLE("#301934"),
	DARK_RASPBERRY("#872657"),
	DARK_RED("#8B0000"),
	DARK_SALMON("#E9967A"),
	DARK_SCARLET("#560319"),
	DARK_SEA_GREEN("#8FBC8F"),
	DARK_SIENNA("#3C1414"),
	DARK_SKY_BLUE("#8CBED6"),
	DARK_SLATE_BLUE("#483D8B"),
	DARK_SLATE_GRAY("#2F4F4F"),
	DARK_SPRING_GREEN("#177245"),
	DARK_TAN("#918151"),
	DARK_TANGERINE("#FFA812"),
	DARK_TAUPE("#483C32"),
	DARK_TERRA_COTTA("#CC4E5C"),
	DARK_TURQUOISE("#00CED1"),
	DARK_VANILLA("#D1BEA8"),
	DARK_VIOLET("#9400D3"),
	DARK_YELLOW("#9B870C"),
	DARTMOUTH_GREEN("#00703C"),
	DAVYS_GREY("#555555"),
	DEBIAN_RED("#D70A53"),
	DEEP_AQUAMARINE("#40826D"),
	DEEP_CARMINE("#A9203E"),
	DEEP_CARMINE_PINK("#EF3038"),
	DEEP_CARROT_ORANGE("#E9692C"),
	DEEP_CERISE("#DA3287"),
	DEEP_CHAMPAGNE("#FAD6A5"),
	DEEP_CHESTNUT("#B94E48"),
	DEEP_COFFEE("#704241"),
	DEEP_FUCHSIA("#C154C1"),
	DEEP_GREEN("#056608"),
	DEEP_GREEN_CYAN_TURQUOISE("#0E7C61"),
	DEEP_JUNGLE_GREEN("#004B49"),
	DEEP_KOAMARU("#333366"),
	DEEP_LEMON("#F5C71A"),
	DEEP_LILAC("#9955BB"),
	DEEP_MAGENTA("#CC00CC"),
	DEEP_MAROON("#820000"),
	DEEP_MAUVE("#D473D4"),
	DEEP_MOSS_GREEN("#355E3B"),
	DEEP_PEACH("#FFCBA4"),
	DEEP_PINK("#FF1493"),
	DEEP_PUCE("#A95C68"),
	DEEP_RED("#850101"),
	DEEP_RUBY("#843F5B"),
	DEEP_SAFFRON("#FF9933"),
	DEEP_SKY_BLUE("#00BFFF"),
	DEEP_SPACE_SPARKLE("#4A646C"),
	DEEP_SPRING_BUD("#556B2F"),
	DEEP_TAUPE("#7E5E60"),
	DEEP_TUSCAN_RED("#66424D"),
	DEEP_VIOLET("#330066"),
	DEER("#BA8759"),
	DENIM("#1560BD"),
	DENIM_BLUE("#2243B6"),
	DESATURATED_CYAN("#669999"),
	DESERT("#C19A6B"),
	DESERT_SAND("#EDC9AF"),
	DESIRE("#EA3C53"),
	DIAMOND("#B9F2FF"),
	DIM_GRAY("#696969"),
	DINGY_DUNGEON("#C53151"),
	DIRT("#9B7653"),
	DODGER_BLUE("#1E90FF"),
	DOGWOOD_ROSE("#D71868"),
	DOLLAR_BILL("#85BB65"),
	DOLPHIN_GRAY("#828E84"),
	DONKEY_BROWN("#664C28"),
	DRAB("#967117"),
	DUKE_BLUE("#00009C"),
	DUST_STORM("#E5CCC9"),
	DUTCH_WHITE("#EFDFBB"),
	EARTH_YELLOW("#E1A95F"),
	EBONY("#555D50"),
	ECRU("#C2B280"),
	EERIE_BLACK("#1B1B1B"),
	EGGPLANT("#614051"),
	EGGSHELL("#F0EAD6"),
	EGYPTIAN_BLUE("#1034A6"),
	ELECTRIC_BLUE("#7DF9FF"),
	ELECTRIC_CRIMSON("#FF003F"),
	ELECTRIC_CYAN("#00FFFF"),
	ELECTRIC_GREEN("#00FF00"),
	ELECTRIC_INDIGO("#6F00FF"),
	ELECTRIC_LAVENDER("#F4BBFF"),
	ELECTRIC_LIME("#CCFF00"),
	ELECTRIC_PURPLE("#BF00FF"),
	ELECTRIC_ULTRAMARINE("#3F00FF"),
	ELECTRIC_VIOLET("#8F00FF"),
	ELECTRIC_YELLOW("#FFFF33"),
	EMERALD("#50C878"),
	EMINENCE("#6C3082"),
	ENGLISH_GREEN("#1B4D3E"),
	ENGLISH_LAVENDER("#B48395"),
	ENGLISH_RED("#AB4B52"),
	ENGLISH_VERMILLION("#CC474B"),
	ENGLISH_VIOLET("#563C5C"),
	ETON_BLUE("#96C8A2"),
	EUCALYPTUS("#44D7A8"),
	FALLOW("#C19A6B"),
	FALU_RED("#801818"),
	FANDANGO("#B53389"),
	FANDANGO_PINK("#DE5285"),
	FASHION_FUCHSIA("#F400A1"),
	FAWN("#E5AA70"),
	FELDGRAU("#4D5D53"),
	FELDSPAR("#FDD5B1"),
	FERN_GREEN("#4F7942"),
	FERRARI_RED("#FF2800"),
	FIELD_DRAB("#6C541E"),
	FIERY_ROSE("#FF5470"),
	FIREBRICK("#B22222"),
	FIRE_ENGINE_RED("#CE2029"),
	FLAME("#E25822"),
	FLAMINGO_PINK("#FC8EAC"),
	FLATTERY("#6B4423"),
	FLAVESCENT("#F7E98E"),
	FLAX("#EEDC82"),
	FLIRT("#A2006D"),
	FLORAL_WHITE("#FFFAF0"),
	FLUORESCENT_ORANGE("#FFBF00"),
	FLUORESCENT_PINK("#FF1493"),
	FLUORESCENT_YELLOW("#CCFF00"),
	FOLLY("#FF004F"),
	FOREST_GREEN("#014421"),
	FRENCH_BEIGE("#A67B5B"),
	FRENCH_BISTRE("#856D4D"),
	FRENCH_BLUE("#0072BB"),
	FRENCH_FUCHSIA("#FD3F92"),
	FRENCH_LILAC("#86608E"),
	FRENCH_LIME("#9EFD38"),
	FRENCH_MAUVE("#D473D4"),
	FRENCH_PINK("#FD6C9E"),
	FRENCH_PLUM("#811453"),
	FRENCH_PUCE("#4E1609"),
	FRENCH_RASPBERRY("#C72C48"),
	FRENCH_ROSE("#F64A8A"),
	FRENCH_SKY_BLUE("#77B5FE"),
	FRENCH_VIOLET("#8806CE"),
	FRENCH_WINE("#AC1E44"),
	FRESH_AIR("#A6E7FF"),
	FROSTBITE("#E936A7"),
	FUCHSIA("#FF00FF"),
	FUCHSIA_PINK("#FF77FF"),
	FUCHSIA_PURPLE("#CC397B"),
	FUCHSIA_ROSE("#C74375"),
	FULVOUS("#E48400"),
	FUZZY_WUZZY("#CC6666"),
	GAINSBORO("#DCDCDC"),
	GAMBOGE("#E49B0F"),
	GAMBOGE_ORANGE("#996600"),
	GARGOYLE_GAS("#FFDF46"),
	GENERIC_VIRIDIAN("#007F66"),
	GHOST_WHITE("#F8F8FF"),
	GIANTS_CLUB("#B05C52"),
	GIANTS_ORANGE("#FE5A1D"),
	GINGER("#B06500"),
	GLAUCOUS("#6082B6"),
	GLITTER("#E6E8FA"),
	GLOSSY_GRAPE("#AB92B3"),
	GO_GREEN("#00AB66"),
	GOLD("#D4AF37"),
	GOLD_FUSION("#85754E"),
	GOLDEN_BROWN("#996515"),
	GOLDEN_POPPY("#FCC200"),
	GOLDEN_YELLOW("#FFDF00"),
	GOLDENROD("#DAA520"),
	GRANITE_GRAY("#676767"),
	GRANNY_SMITH_APPLE("#A8E4A0"),
	GRAPE("#6F2DA8"),
	GRAY("#808080"),
	GRAY_ASPARAGUS("#465945"),
	GRAY_BLUE("#8C92AC"),
	GREEN("#00FF00"),
	GREEN_BLUE("#1164B4"),
	GREEN_CYAN("#009966"),
	GREEN_LIZARD("#A7F432"),
	GREEN_SHEEN("#6EAEA1"),
	GREEN_YELLOW("#ADFF2F"),
	GRIZZLY("#885818"),
	GRULLO("#A99A86"),
	GUPPIE_GREEN("#00FF7F"),
	GUNMETAL("#2a3439"),
	HAN_BLUE("#446CCF"),
	HAN_PURPLE("#5218FA"),
	HANSA_YELLOW("#E9D66B"),
	HARLEQUIN("#3FFF00"),
	HARLEQUIN_GREEN("#46CB18"),
	HARVARD_CRIMSON("#C90016"),
	HARVEST_GOLD("#DA9100"),
	HEART_GOLD("#808000"),
	HEAT_WAVE("#FF7A00"),
	HEIDELBERG_RED("#960018"),
	HELIOTROPE("#DF73FF"),
	HELIOTROPE_GRAY("#AA98A9"),
	HELIOTROPE_MAGENTA("#AA00BB"),
	HOLLYWOOD_CERISE("#F400A1"),
	HONEYDEW("#F0FFF0"),
	HONOLULU_BLUE("#006DB0"),
	HOOKERS_GREEN("#49796B"),
	HOT_MAGENTA("#FF1DCE"),
	HOT_PINK("#FF69B4"),
	HUNTER_GREEN("#355E3B"),
	ICEBERG("#71A6D2"),
	ICTERINE("#FCF75E"),
	IGUANA_GREEN("#71BC78"),
	ILLUMINATING_EMERALD("#319177"),
	IMPERIAL("#602F6B"),
	IMPERIAL_BLUE("#002395"),
	IMPERIAL_PURPLE("#66023C"),
	IMPERIAL_RED("#ED2939"),
	INCHWORM("#B2EC5D"),
	INDEPENDENCE("#4C516D"),
	INDIA_GREEN("#138808"),
	INDIAN_RED("#CD5C5C"),
	INDIAN_YELLOW("#E3A857"),
	INDIGO("#4B0082"),
	INDIGO_DYE("#091F92"),
	INFRA_RED("#FF496C"),
	INTERDIMENSIONAL_BLUE("#360CCC"),
	INTERNATIONAL_KLEIN_BLUE("#002FA7"),
	INTERNATIONAL_ORANGE("#FF4F00"),
	IRIS("#5A4FCF"),
	IRRESISTIBLE("#B3446C"),
	ISABELLINE("#F4F0EC"),
	ISLAMIC_GREEN("#009000"),
	ITALIAN_SKY_BLUE("#B2FFFF"),
	IVORY("#FFFFF0"),
	JADE("#00A86B"),
	JAPANESE_CARMINE("#9D2933"),
	JAPANESE_INDIGO("#264348"),
	JAPANESE_VIOLET("#5B3256"),
	JASMINE("#F8DE7E"),
	JASPER("#D73B3E"),
	JAZZBERRY_JAM("#A50B5E"),
	JELLY_BEAN("#DA614E"),
	JET("#343434"),
	JONQUIL("#F4CA16"),
	JORDY_BLUE("#8AB9F1"),
	JUNE_BUD("#BDDA57"),
	JUNGLE_GREEN("#29AB87"),
	KELLY_GREEN("#4CBB17"),
	KENYAN_COPPER("#7C1C05"),
	KEPPEL("#3AB09E"),
	KEY_LIME("#E8F48C"),
	KHAKI("#C3B091"),
	KIWI("#8EE53F"),
	KOBE("#882D17"),
	KOBI("#E79FC4"),
	KOBICHA("#6B4423"),
	KOMBU_GREEN("#354230"),
	KSU_PURPLE("#512888"),
	KU_CRIMSON("#E8000D"),
	LA_SALLE_GREEN("#087830"),
	LANGUID_LAVENDER("#D6CADD"),
	LAPIS_LAZULI("#26619C"),
	LASER_LEMON("#FFFF66"),
	LAUREL_GREEN("#A9BA9D"),
	LAVA("#CF1020"),
	LAVENDER("#B57EDC"),
	LAVENDER_BLUE("#CCCCFF"),
	LAVENDER_BLUSH("#FFF0F5"),
	LAVENDER_GRAY("#C4C3D0"),
	LAVENDER_INDIGO("#9457EB"),
	LAVENDER_MAGENTA("#EE82EE"),
	LAVENDER_MIST("#E6E6FA"),
	LAVENDER_PINK("#FBAED2"),
	LAVENDER_PURPLE("#967BB6"),
	LAVENDER_ROSE("#FBA0E3"),
	LAWN_GREEN("#7CFC00"),
	LEMON("#FFF700"),
	LEMON_CHIFFON("#FFFACD"),
	LEMON_CURRY("#CCA01D"),
	LEMON_GLACIER("#FDFF00"),
	LEMON_LIME("#E3FF00"),
	LEMON_MERINGUE("#F6EABE"),
	LEMON_YELLOW("#FFF44F"),
	LICORICE("#1A1110"),
	LIBERTY("#545AA7"),
	LIGHT_APRICOT("#FDD5B1"),
	LIGHT_BLUE("#ADD8E6"),
	LIGHT_BROWN("#B5651D"),
	LIGHT_CARMINE_PINK("#E66771"),
	LIGHT_COBALT_BLUE("#88ACE0"),
	LIGHT_CORAL("#F08080"),
	LIGHT_CORNFLOWER_BLUE("#93CCEA"),
	LIGHT_CRIMSON("#F56991"),
	LIGHT_CYAN("#E0FFFF"),
	LIGHT_DEEP_PINK("#FF5CCD"),
	LIGHT_FRENCH_BEIGE("#C8AD7F"),
	LIGHT_FUCHSIA_PINK("#F984EF"),
	LIGHT_GOLDENROD_YELLOW("#FAFAD2"),
	LIGHT_GRAY("#D3D3D3"),
	LIGHT_GRAYISH_MAGENTA("#CC99CC"),
	LIGHT_GREEN("#90EE90"),
	LIGHT_HOT_PINK("#FFB3DE"),
	LIGHT_KHAKI("#F0E68C"),
	LIGHT_MEDIUM_ORCHID("#D39BCB"),
	LIGHT_MOSS_GREEN("#ADDFAD"),
	LIGHT_ORANGE("#FED8B1"),
	LIGHT_ORCHID("#E6A8D7"),
	LIGHT_PASTEL_PURPLE("#B19CD9"),
	LIGHT_PINK("#FFB6C1"),
	LIGHT_RED_OCHRE("#E97451"),
	LIGHT_SALMON("#FFA07A"),
	LIGHT_SALMON_PINK("#FF9999"),
	LIGHT_SEA_GREEN("#20B2AA"),
	LIGHT_SKY_BLUE("#87CEFA"),
	LIGHT_SLATE_GRAY("#778899"),
	LIGHT_STEEL_BLUE("#B0C4DE"),
	LIGHT_TAUPE("#B38B6D"),
	LIGHT_THULIAN_PINK("#E68FAC"),
	LIGHT_YELLOW("#FFFFE0"),
	LILAC("#C8A2C8"),
	LILAC_LUSTER("#AE98AA"),
	LIME("#BFFF00"),
	LIME_GREEN("#32CD32"),
	LIMERICK("#9DC209"),
	LINCOLN_GREEN("#195905"),
	LINEN("#FAF0E6"),
	LISERAN_PURPLE("#DE6FA1"),
	LITTLE_BOY_BLUE("#6CA0DC"),
	LIVER("#674C47"),
	LIVER_CHESTNUT("#987456"),
	LIVID("#6699CC"),
	LUMBER("#FFE4CD"),
	LUST("#E62020"),
	MAASTRICHT_BLUE("#001C3D"),
	MACARONI_AND_CHEESE("#FFBD88"),
	MADDER_LAKE("#CC3336"),
	MAGENTA("#FF00FF"),
	MAGENTA_HAZE("#9F4576"),
	MAGENTA_PINK("#CC338B"),
	MAGIC_MINT("#AAF0D1"),
	MAGIC_POTION("#FF4466"),
	MAGNOLIA("#F8F4FF"),
	MAHOGANY("#C04000"),
	MAIZE("#FBEC5D"),
	MAJORELLE_BLUE("#6050DC"),
	MALACHITE("#0BDA51"),
	MANATEE("#979AAA"),
	MANDARIN("#F37A48"),
	MANGO_TANGO("#FF8243"),
	MANTIS("#74C365"),
	MARDI_GRAS("#880085"),
	MARIGOLD("#EAA221"),
	MAROON("#C32148"),
	MAUVE("#E0B0FF"),
	MAUVE_TAUPE("#915F6D"),
	MAUVELOUS("#EF98AA"),
	MAXIMUM_BLUE("#47ABCC"),
	MAXIMUM_BLUE_GREEN("#30BFBF"),
	MAXIMUM_BLUE_PURPLE("#ACACE6"),
	MAXIMUM_GREEN("#5E8C31"),
	MAXIMUM_GREEN_YELLOW("#D9E650"),
	MAXIMUM_PURPLE("#733380"),
	MAXIMUM_RED("#D92121"),
	MAXIMUM_RED_PURPLE("#A63A79"),
	MAXIMUM_YELLOW("#FAFA37"),
	MAXIMUM_YELLOW_RED("#F2BA49"),
	MAY_GREEN("#4C9141"),
	MAYA_BLUE("#73C2FB"),
	MEAT_BROWN("#E5B73B"),
	MEDIUM_AQUAMARINE("#66DDAA"),
	MEDIUM_BLUE("#0000CD"),
	MEDIUM_CANDY_APPLE_RED("#E2062C"),
	MEDIUM_CARMINE("#AF4035"),
	MEDIUM_CHAMPAGNE("#F3E5AB"),
	MEDIUM_ELECTRIC_BLUE("#035096"),
	MEDIUM_JUNGLE_GREEN("#1C352D"),
	MEDIUM_LAVENDER_MAGENTA("#DDA0DD"),
	MEDIUM_ORCHID("#BA55D3"),
	MEDIUM_PERSIAN_BLUE("#0067A5"),
	MEDIUM_PURPLE("#9370DB"),
	MEDIUM_RED_VIOLET("#BB3385"),
	MEDIUM_RUBY("#AA4069"),
	MEDIUM_SEA_GREEN("#3CB371"),
	MEDIUM_SKY_BLUE("#80DAEB"),
	MEDIUM_SLATE_BLUE("#7B68EE"),
	MEDIUM_SPRING_BUD("#C9DC87"),
	MEDIUM_SPRING_GREEN("#00FA9A"),
	MEDIUM_TAUPE("#674C47"),
	MEDIUM_TURQUOISE("#48D1CC"),
	MEDIUM_TUSCAN_RED("#79443B"),
	MEDIUM_VERMILION("#D9603B"),
	MEDIUM_VIOLET_RED("#C71585"),
	MELLOW_APRICOT("#F8B878"),
	MELLOW_YELLOW("#F8DE7E"),
	MELON("#FDBCB4"),
	METALLIC_SEAWEED("#0A7E8C"),
	METALLIC_SUNBURST("#9C7C38"),
	MEXICAN_PINK("#E4007C"),
	MIDDLE_BLUE("#7ED4E6"),
	MIDDLE_BLUE_GREEN("#8DD9CC"),
	MIDDLE_BLUE_PURPLE("#8B72BE"),
	MIDDLE_RED_PURPLE("#210837"),
	MIDDLE_GREEN("#4D8C57"),
	MIDDLE_GREEN_YELLOW("#ACBF60"),
	MIDDLE_PURPLE("#D982B5"),
	MIDDLE_RED("#E58E73"),
	MIDDLE_YELLOW("#FFEB00"),
	MIDDLE_YELLOW_RED("#ECB176"),
	MIDNIGHT("#702670"),
	MIDNIGHT_BLUE("#191970"),
	MIDNIGHT_GREEN("#004953"),
	MIKADO_YELLOW("#FFC40C"),
	MILK("#FDFFF5"),
	MIMI_PINK("#FFDAE9"),
	MINDARO("#E3F988"),
	MING("#36747D"),
	MINION_YELLOW("#F5E050"),
	MINT("#3EB489"),
	MINT_CREAM("#F5FFFA"),
	MINT_GREEN("#98FF98"),
	MISTY_MOSS("#BBB477"),
	MISTY_ROSE("#FFE4E1"),
	MOCCASIN("#FAEBD7"),
	MODE_BEIGE("#967117"),
	MOONSTONE_BLUE("#73A9C2"),
	MORDANT_RED("#AE0C00"),
	MORNING_BLUE("#8DA399"),
	MOSS_GREEN("#8A9A5B"),
	MOUNTAIN_MEADOW("#30BA8F"),
	MOUNTBATTEN_PINK("#997A8D"),
	MSU_GREEN("#18453B"),
	MUGHAL_GREEN("#306030"),
	MULBERRY("#C54B8C"),
	MUMMYS_TOMB("#828E84"),
	MUSTARD("#FFDB58"),
	MYRTLE_GREEN("#317873"),
	MYSTIC("#D65282"),
	MYSTIC_MAROON("#AD4379"),
	NADESHIKO_PINK("#F6ADC6"),
	NAPIER_GREEN("#2A8000"),
	NAPLES_YELLOW("#FADA5E"),
	NAVAJO_WHITE("#FFDEAD"),
	NAVY("#000080"),
	NAVY_PURPLE("#9457EB"),
	NEON_CARROT("#FFA343"),
	NEON_FUCHSIA("#FE4164"),
	NEON_GREEN("#39FF14"),
	NEW_CAR("#214FC6"),
	NEW_YORK_PINK("#D7837F"),
	NICKEL("#727472"),
	NON_PHOTO_BLUE("#A4DDED"),
	NORTH_TEXAS_GREEN("#059033"),
	NYANZA("#E9FFDB"),
	OCEAN_BLUE("#4F42B5"),
	OCEAN_BOAT_BLUE("#0077BE"),
	OCEAN_GREEN("#48BF91"),
	OCHRE("#CC7722"),
	OFFICE_GREEN("#008000"),
	OGRE_ODOR("#FD5240"),
	OLD_BURGUNDY("#43302E"),
	OLD_GOLD("#CFB53B"),
	OLD_HELIOTROPE("#563C5C"),
	OLD_LACE("#FDF5E6"),
	OLD_LAVENDER("#796878"),
	OLD_MAUVE("#673147"),
	OLD_MOSS_GREEN("#867E36"),
	OLD_ROSE("#C08081"),
	OLD_SILVER("#848482"),
	OLIVE("#808000"),
	OLIVE_DRAB("#6B8E23"),
	OLIVINE("#9AB973"),
	ONYX("#353839"),
	OPERA_MAUVE("#B784A7"),
	ORANGE("#FF7F00"),
	ORANGE_PEEL("#FF9F00"),
	ORANGE_RED("#FF4500"),
	ORANGE_SODA("#FA5B3D"),
	ORANGE_YELLOW("#F8D568"),
	ORCHID("#DA70D6"),
	ORCHID_PINK("#F2BDCD"),
	ORIOLES_ORANGE("#FB4F14"),
	OTTER_BROWN("#654321"),
	OUTER_SPACE("#414A4C"),
	OUTRAGEOUS_ORANGE("#FF6E4A"),
	OXFORD_BLUE("#002147"),
	OU_CRIMSON_RED("#990000"),
	PACIFIC_BLUE("#1CA9C9"),
	PAKISTAN_GREEN("#006600"),
	PALATINATE_BLUE("#273BE2"),
	PALATINATE_PURPLE("#682860"),
	PALE_AQUA("#BCD4E6"),
	PALE_BLUE("#AFEEEE"),
	PALE_BROWN("#987654"),
	PALE_CARMINE("#AF4035"),
	PALE_CERULEAN("#9BC4E2"),
	PALE_CHESTNUT("#DDADAF"),
	PALE_COPPER("#DA8A67"),
	PALE_CORNFLOWER_BLUE("#ABCDEF"),
	PALE_CYAN("#87D3F8"),
	PALE_GOLD("#E6BE8A"),
	PALE_GOLDENROD("#EEE8AA"),
	PALE_GREEN("#98FB98"),
	PALE_LAVENDER("#DCD0FF"),
	PALE_MAGENTA("#F984E5"),
	PALE_MAGENTA_PINK("#FF99CC"),
	PALE_PINK("#FADADD"),
	PALE_PLUM("#DDA0DD"),
	PALE_RED_VIOLET("#DB7093"),
	PALE_ROBIN_EGG_BLUE("#96DED1"),
	PALE_SILVER("#C9C0BB"),
	PALE_SPRING_BUD("#ECEBBD"),
	PALE_TAUPE("#BC987E"),
	PALE_TURQUOISE("#AFEEEE"),
	PALE_VIOLET("#CC99FF"),
	PALE_VIOLET_RED("#DB7093"),
	PALM_LEAF("#6F9940"),
	PANSY_PURPLE("#78184A"),
	PAOLO_VERONESE_GREEN("#009B7D"),
	PAPAYA_WHIP("#FFEFD5"),
	PARADISE_PINK("#E63E62"),
	PARIS_GREEN("#50C878"),
	PARROT_PINK("#D998A0"),
	PASTEL_BLUE("#AEC6CF"),
	PASTEL_BROWN("#836953"),
	PASTEL_GRAY("#CFCFC4"),
	PASTEL_GREEN("#77DD77"),
	PASTEL_MAGENTA("#F49AC2"),
	PASTEL_ORANGE("#FFB347"),
	PASTEL_PINK("#DEA5A4"),
	PASTEL_PURPLE("#B39EB5"),
	PASTEL_RED("#FF6961"),
	PASTEL_VIOLET("#CB99C9"),
	PASTEL_YELLOW("#FDFD96"),
	PATRIARCH("#800080"),
	PAYNES_GREY("#536878"),
	PEACH("#FFE5B4"),
	PEACH_ORANGE("#FFCC99"),
	PEACH_PUFF("#FFDAB9"),
	PEACH_YELLOW("#FADFAD"),
	PEAR("#D1E231"),
	PEARL("#EAE0C8"),
	PEARL_AQUA("#88D8C0"),
	PEARLY_PURPLE("#B768A2"),
	PERIDOT("#E6E200"),
	PERIWINKLE("#CCCCFF"),
	PERMANENT_GERANIUM_LAKE("#E12C2C"),
	PERSIAN_BLUE("#1C39BB"),
	PERSIAN_GREEN("#00A693"),
	PERSIAN_INDIGO("#32127A"),
	PERSIAN_ORANGE("#D99058"),
	PERSIAN_PINK("#F77FBE"),
	PERSIAN_PLUM("#701C1C"),
	PERSIAN_RED("#CC3333"),
	PERSIAN_ROSE("#FE28A2"),
	PERSIMMON("#EC5800"),
	PERU("#CD853F"),
	PEWTER_BLUE("#8BA8B7"),
	PHLOX("#DF00FF"),
	PHTHALO_BLUE("#000F89"),
	PHTHALO_GREEN("#123524"),
	PICTON_BLUE("#45B1E8"),
	PICTORIAL_CARMINE("#C30B4E"),
	PIGGY_PINK("#FDDDE6"),
	PINE_GREEN("#01796F"),
	PINEAPPLE("#563C5C"),
	PINK("#FFC0CB"),
	PINK_FLAMINGO("#FC74FD"),
	PINK_LACE("#FFDDF4"),
	PINK_LAVENDER("#D8B2D1"),
	PINK_ORANGE("#FF9966"),
	PINK_PEARL("#E7ACCF"),
	PINK_RASPBERRY("#980036"),
	PINK_SHERBET("#F78FA7"),
	PISTACHIO("#93C572"),
	PIXIE_POWDER("#391285"),
	PLATINUM("#E5E4E2"),
	PLUM("#8E4585"),
	PLUMP_PURPLE("#5946B2"),
	POLISHED_PINE("#5DA493"),
	POMP_AND_POWER("#86608E"),
	POPSTAR("#BE4F62"),
	PORTLAND_ORANGE("#FF5A36"),
	POWDER_BLUE("#B0E0E6"),
	PRINCESS_PERFUME("#FF85CF"),
	PRINCETON_ORANGE("#F58025"),
	PRUNE("#701C1C"),
	PRUSSIAN_BLUE("#003153"),
	PSYCHEDELIC_PURPLE("#DF00FF"),
	PUCE("#CC8899"),
	PUCE_RED("#722F37"),
	PULLMAN_BROWN("#644117"),
	PULLMAN_GREEN("#3B331C"),
	PUMPKIN("#FF7518"),
	PURPLE("#800080"),
	PURPLE_HEART("#69359C"),
	PURPLE_MOUNTAIN_MAJESTY("#9678B6"),
	PURPLE_NAVY("#4E5180"),
	PURPLE_PIZZAZZ("#FE4EDA"),
	PURPLE_PLUM("#9C51B6"),
	PURPLE_TAUPE("#50404D"),
	PURPUREUS("#9A4EAE"),
	QUARTZ("#51484F"),
	QUEEN_BLUE("#436B95"),
	QUEEN_PINK("#E8CCD7"),
	QUICK_SILVER("#A6A6A6"),
	QUINACRIDONE_MAGENTA("#8E3A59"),
	RACKLEY("#5D8AA8"),
	RADICAL_RED("#FF355E"),
	RAISIN_BLACK("#242124"),
	RAJAH("#FBAB60"),
	RASPBERRY("#E30B5D"),
	RASPBERRY_GLACE("#915F6D"),
	RASPBERRY_PINK("#E25098"),
	RASPBERRY_ROSE("#B3446C"),
	RAW_SIENNA("#D68A59"),
	RAW_UMBER("#826644"),
	RAZZLE_DAZZLE_ROSE("#FF33CC"),
	RAZZMATAZZ("#E3256B"),
	RAZZMIC_BERRY("#8D4E85"),
	REBECCA_PURPLE("#663399"),
	RED("#FF0000"),
	RED_BROWN("#A52A2A"),
	RED_DEVIL("#860111"),
	RED_ORANGE("#FF5349"),
	RED_PURPLE("#E40078"),
	RED_SALSA("#FD3A4A"),
	RED_VIOLET("#C71585"),
	REDWOOD("#A45A52"),
	REGALIA("#522D80"),
	REGISTRATION_BLACK("#000000"),
	RESOLUTION_BLUE("#002387"),
	RHYTHM("#777696"),
	RICH_BLACK("#004040"),
	RICH_BRILLIANT_LAVENDER("#F1A7FE"),
	RICH_CARMINE("#D70040"),
	RICH_ELECTRIC_BLUE("#0892D0"),
	RICH_LAVENDER("#A76BCF"),
	RICH_LILAC("#B666D2"),
	RICH_MAROON("#B03060"),
	RIFLE_GREEN("#444C38"),
	ROAST_COFFEE("#704241"),
	ROBIN_EGG_BLUE("#00CCCC"),
	ROCKET_METALLIC("#8A7F80"),
	ROMAN_SILVER("#838996"),
	ROSE("#FF007F"),
	ROSE_BONBON("#F9429E"),
	ROSE_DUST("#9E5E6F"),
	ROSE_EBONY("#674846"),
	ROSE_GOLD("#B76E79"),
	ROSE_MADDER("#E32636"),
	ROSE_PINK("#FF66CC"),
	ROSE_QUARTZ("#AA98A9"),
	ROSE_RED("#C21E56"),
	ROSE_TAUPE("#905D5D"),
	ROSE_VALE("#AB4E52"),
	ROSEWOOD("#65000B"),
	ROSSO_CORSA("#D40000"),
	ROSY_BROWN("#BC8F8F"),
	ROYAL_AZURE("#0038A8"),
	ROYAL_BLUE("#002366"),
	ROYAL_FUCHSIA("#CA2C92"),
	ROYAL_PURPLE("#7851A9"),
	ROYAL_YELLOW("#FADA5E"),
	RUBER("#CE4676"),
	RUBINE_RED("#D10056"),
	RUBY("#E0115F"),
	RUBY_RED("#9B111E"),
	RUDDY("#FF0028"),
	RUDDY_BROWN("#BB6528"),
	RUDDY_PINK("#E18E96"),
	RUFOUS("#A81C07"),
	RUSSET("#80461B"),
	RUSSIAN_GREEN("#679267"),
	RUSSIAN_VIOLET("#32174D"),
	RUST("#B7410E"),
	RUSTY_RED("#DA2C43"),
	SACRAMENTO_STATE_GREEN("#00563F"),
	SADDLE_BROWN("#8B4513"),
	SAFETY_ORANGE("#FF7800"),
	SAFETY_YELLOW("#EED202"),
	SAFFRON("#F4C430"),
	SAGE("#BCB88A"),
	ST_PATRICKS_BLUE("#23297A"),
	SALMON("#FA8072"),
	SALMON_PINK("#FF91A4"),
	SAND("#C2B280"),
	SAND_DUNE("#967117"),
	SANDSTORM("#ECD540"),
	SANDY_BROWN("#F4A460"),
	SANDY_TAN("#FDD9B5"),
	SANDY_TAUPE("#967117"),
	SANGRIA("#92000A"),
	SAP_GREEN("#507D2A"),
	SAPPHIRE("#0F52BA"),
	SAPPHIRE_BLUE("#0067A5"),
	SASQUATCH_SOCKS("#FF4681"),
	SATIN_SHEEN_GOLD("#CBA135"),
	SCARLET("#FF2400"),
	SCHAUSS_PINK("#FF91AF"),
	SCHOOL_BUS_YELLOW("#FFD800"),
	SCREAMIN__GREEN("#66FF66"),
	SEA_BLUE("#006994"),
	SEA_FOAM_GREEN("#9FE2BF"),
	SEA_GREEN("#2E8B57"),
	SEA_SERPENT("#4BC7CF"),
	SEAL_BROWN("#59260B"),
	SEASHELL("#FFF5EE"),
	SELECTIVE_YELLOW("#FFBA00"),
	SEPIA("#704214"),
	SHADOW("#8A795D"),
	SHADOW_BLUE("#778BA5"),
	SHAMPOO("#FFCFF1"),
	SHAMROCK_GREEN("#009E60"),
	SHEEN_GREEN("#8FD400"),
	SHIMMERING_BLUSH("#D98695"),
	SHINY_SHAMROCK("#5FA778"),
	SHOCKING_PINK("#FC0FC0"),
	SIENNA("#882D17"),
	SILVER("#C0C0C0"),
	SILVER_CHALICE("#ACACAC"),
	SILVER_LAKE_BLUE("#5D89BA"),
	SILVER_PINK("#C4AEAD"),
	SILVER_SAND("#BFC1C2"),
	SINOPIA("#CB410B"),
	SIZZLING_RED("#FF3855"),
	SIZZLING_SUNRISE("#FFDB00"),
	SKOBELOFF("#007474"),
	SKY_BLUE("#87CEEB"),
	SKY_MAGENTA("#CF71AF"),
	SLATE_BLUE("#6A5ACD"),
	SLATE_GRAY("#708090"),
	SMALT("#003399"),
	SLIMY_GREEN("#299617"),
	SMASHED_PUMPKIN("#FF6D3A"),
	SMITTEN("#C84186"),
	SMOKE("#738276"),
	SMOKEY_TOPAZ("#832A0D"),
	SMOKY_BLACK("#100C08"),
	SMOKY_TOPAZ("#933D41"),
	SNOW("#FFFAFA"),
	SOAP("#CEC8EF"),
	SOLID_PINK("#893843"),
	SONIC_SILVER("#757575"),
	SPARTAN_CRIMSON("#9E1316"),
	SPACE_CADET("#1D2951"),
	SPANISH_BISTRE("#807532"),
	SPANISH_BLUE("#0070B8"),
	SPANISH_CARMINE("#D10047"),
	SPANISH_CRIMSON("#E51A4C"),
	SPANISH_GRAY("#989898"),
	SPANISH_GREEN("#009150"),
	SPANISH_ORANGE("#E86100"),
	SPANISH_PINK("#F7BFBE"),
	SPANISH_RED("#E60026"),
	SPANISH_SKY_BLUE("#00FFFF"),
	SPANISH_VIOLET("#4C2882"),
	SPANISH_VIRIDIAN("#007F5C"),
	SPICY_MIX("#8B5f4D"),
	SPIRO_DISCO_BALL("#0FC0FC"),
	SPRING_BUD("#A7FC00"),
	SPRING_FROST("#87FF2A"),
	SPRING_GREEN("#00FF7F"),
	STAR_COMMAND_BLUE("#007BB8"),
	STEEL_BLUE("#4682B4"),
	STEEL_PINK("#CC33CC"),
	STEEL_TEAL("#5F8A8B"),
	STIL_DE_GRAIN_YELLOW("#FADA5E"),
	STIZZA("#990000"),
	STORMCLOUD("#4F666A"),
	STRAW("#E4D96F"),
	STRAWBERRY("#FC5A8D"),
	SUGAR_PLUM("#914E75"),
	SUNBURNT_CYCLOPS("#FF404C"),
	SUNGLOW("#FFCC33"),
	SUNNY("#F2F27A"),
	SUNRAY("#E3AB57"),
	SUNSET("#FAD6A5"),
	SUNSET_ORANGE("#FD5E53"),
	SUPER_PINK("#CF6BA9"),
	SWEET_BROWN("#A83731"),
	TAN("#D2B48C"),
	TANGELO("#F94D00"),
	TANGERINE("#F28500"),
	TANGERINE_YELLOW("#FFCC00"),
	TANGO_PINK("#E4717A"),
	TART_ORANGE("#FB4D46"),
	TAUPE("#483C32"),
	TAUPE_GRAY("#8B8589"),
	TEA_GREEN("#D0F0C0"),
	TEA_ROSE("#F88379"),
	TEAL("#008080"),
	TEAL_BLUE("#367588"),
	TEAL_DEER("#99E6B3"),
	TEAL_GREEN("#00827F"),
	TELEMAGENTA("#CF3476"),
	TERRA_COTTA("#E2725B"),
	THISTLE("#D8BFD8"),
	THULIAN_PINK("#DE6FA1"),
	TICKLE_ME_PINK("#FC89AC"),
	TIFFANY_BLUE("#0ABAB5"),
	TIGERS_EYE("#E08D3C"),
	TIMBERWOLF("#DBD7D2"),
	TITANIUM_YELLOW("#EEE600"),
	TOMATO("#FF6347"),
	TOOLBOX("#746CC0"),
	TOPAZ("#FFC87C"),
	TRACTOR_RED("#FD0E35"),
	TROLLEY_GREY("#808080"),
	TROPICAL_RAIN_FOREST("#00755E"),
	TROPICAL_VIOLET("#CDA4DE"),
	TRUE_BLUE("#0073CF"),
	TUFTS_BLUE("#3E8EDE"),
	TULIP("#FF878D"),
	TUMBLEWEED("#DEAA88"),
	TURKISH_ROSE("#B57281"),
	TURQUOISE("#40E0D0"),
	TURQUOISE_BLUE("#00FFEF"),
	TURQUOISE_GREEN("#A0D6B4"),
	TURQUOISE_SURF("#00C5CD"),
	TURTLE_GREEN("#8A9A5B"),
	TUSCAN("#FAD6A5"),
	TUSCAN_BROWN("#6F4E37"),
	TUSCAN_RED("#7C4848"),
	TUSCAN_TAN("#A67B5B"),
	TUSCANY("#C09999"),
	TWILIGHT_LAVENDER("#8A496B"),
	TYRIAN_PURPLE("#66023C"),
	UA_BLUE("#0033AA"),
	UA_RED("#D9004C"),
	UBE("#8878C3"),
	UCLA_BLUE("#536895"),
	UCLA_GOLD("#FFB300"),
	UFO_GREEN("#3CD070"),
	ULTRAMARINE("#3F00FF"),
	ULTRAMARINE_BLUE("#4166F5"),
	ULTRA_PINK("#FF6FFF"),
	ULTRA_RED("#FC6C85"),
	UMBER("#635147"),
	UNBLEACHED_SILK("#FFDDCA"),
	UNITED_NATIONS_BLUE("#5B92E5"),
	UNIVERSITY_OF_CALIFORNIA_GOLD("#B78727"),
	UNMELLOW_YELLOW("#FFFF66"),
	UP_FOREST_GREEN("#014421"),
	UP_MAROON("#7B1113"),
	UPSDELL_RED("#AE2029"),
	UROBILIN("#E1AD21"),
	USAFA_BLUE("#004F98"),
	USC_CARDINAL("#990000"),
	USC_GOLD("#FFCC00"),
	UNIVERSITY_OF_TENNESSEE_ORANGE("#F77F00"),
	UTAH_CRIMSON("#D3003F"),
	VAN_DYKE_BROWN("#664228"),
	VANILLA("#F3E5AB"),
	VANILLA_ICE("#F38FA9"),
	VEGAS_GOLD("#C5B358"),
	VENETIAN_RED("#C80815"),
	VERDIGRIS("#43B3AE"),
	VERMILION("#E34234"),
	VERONICA("#A020F0"),
	VERY_LIGHT_AZURE("#74BBFB"),
	VERY_LIGHT_BLUE("#6666FF"),
	VERY_LIGHT_MALACHITE_GREEN("#64E986"),
	VERY_LIGHT_TANGELO("#FFB077"),
	VERY_PALE_ORANGE("#FFDFBF"),
	VERY_PALE_YELLOW("#FFFFBF"),
	VIOLET("#8F00FF"),
	VIOLET_BLUE("#324AB2"),
	VIOLET_RED("#F75394"),
	VIRIDIAN("#40826D"),
	VIRIDIAN_GREEN("#009698"),
	VISTA_BLUE("#7C9ED9"),
	VIVID_AMBER("#CC9900"),
	VIVID_AUBURN("#922724"),
	VIVID_BURGUNDY("#9F1D35"),
	VIVID_CERISE("#DA1D81"),
	VIVID_CERULEAN("#00AAEE"),
	VIVID_CRIMSON("#CC0033"),
	VIVID_GAMBOGE("#FF9900"),
	VIVID_LIME_GREEN("#A6D608"),
	VIVID_MALACHITE("#00CC33"),
	VIVID_MULBERRY("#B80CE3"),
	VIVID_ORANGE("#FF5F00"),
	VIVID_ORANGE_PEEL("#FFA000"),
	VIVID_ORCHID("#CC00FF"),
	VIVID_RASPBERRY("#FF006C"),
	VIVID_RED("#F70D1A"),
	VIVID_RED_TANGELO("#DF6124"),
	VIVID_SKY_BLUE("#00CCFF"),
	VIVID_TANGELO("#F07427"),
	VIVID_TANGERINE("#FFA089"),
	VIVID_VERMILION("#E56024"),
	VIVID_VIOLET("#9F00FF"),
	VIVID_YELLOW("#FFE302"),
	VOLT("#CEFF00"),
	WAGENINGEN_GREEN("#34B233"),
	WARM_BLACK("#004242"),
	WATERSPOUT("#A4F4F9"),
	WELDON_BLUE("#7C98AB"),
	WENGE("#645452"),
	WHEAT("#F5DEB3"),
	WHITE("#FFFFFF"),
	WHITE_SMOKE("#F5F5F5"),
	WILD_BLUE_YONDER("#A2ADD0"),
	WILD_ORCHID("#D470A2"),
	WILD_STRAWBERRY("#FF43A4"),
	WILD_WATERMELON("#FC6C85"),
	WILLPOWER_ORANGE("#FD5800"),
	WINDSOR_TAN("#A75502"),
	WINE("#722F37"),
	WINE_DREGS("#673147"),
	WINTER_SKY("#FF007C"),
	WINTER_WIZARD("#A0E6FF"),
	WINTERGREEN_DREAM("#56887D"),
	WISTERIA("#C9A0DC"),
	WOOD_BROWN("#C19A6B"),
	XANADU("#738678"),
	YALE_BLUE("#0F4D92"),
	YANKEES_BLUE("#1C2841"),
	YELLOW("#FFFF00"),
	YELLOW_GREEN("#9ACD32"),
	YELLOW_ORANGE("#FFAE42"),
	YELLOW_ROSE("#FFF000"),
	YELLOW_SUNSHINE("#FFF700"),
	ZAFFRE("#0014A8"),
	ZINNWALDITE_BROWN("#2C1608"),
	ZOMP("#39A78E");

	private String hex;

	//Makes the Colour with field hex as a string.
	Colour(String hex) {
		this.hex = hex;
	}

	//Returns a list of all the colours except VOID.
	public static List<Colour> allColours() {
		List<Colour> colours = new ArrayList<Colour>();
		for (Colour c : Colour.values()) {
			if (!(c == Colour.VOID)) {
				colours.add(c);
			}
		}
		return colours;
	}

	public static Colour random() {
		Random random = new Random();
		int temp = 0;
		while (temp == 0) {
			temp += random.nextInt(Colour.values().length);
		}
		return Colour.values()[temp];
	}

	//Returns the hex string.
	public String getHex() {
		return hex;
	}
}


	

