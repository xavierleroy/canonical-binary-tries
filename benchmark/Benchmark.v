From Coq Require Import List String ZArith POrderedType FMaps FMapAVL.
From Tries.MMaps Require RBT.
From Tries Require Import String2pos StringOrder PositiveOrder.
From Tries Require Original Canonical Sigma Node01 GADT Patricia CharTrie.

Local Open Scope string_scope.
Local Open Scope list_scope.

Fixpoint iterate {A: Type} (n: nat) (f: A -> A) (x: A) : A :=
  match n with
  | O => x
  | S m => iterate m f (f x)
  end. 

Fixpoint repeat {A: Type} (n: nat) (f: A -> bool) (x: A) : bool :=
  match n with
  | O => true
  | S m => xorb (f x) (repeat m f x)   (* make it strict in both computations *)
  end. 

Set Implicit Arguments.

Definition benchgen (K A: Type)
                    (empty: A)
                    (set: K -> unit -> A -> A)
                    (get: K -> A -> option unit)
                    (l: list K) : bool :=
  let fix insert m l :=
    match l with
    | nil => m
    | w :: l => insert (set w tt m) l
    end in
  let m := insert empty l in
  let fix lookup l (b: bool) :=
    match l with
    | nil => b
    | w :: l => lookup l (match get w m with
                          | None => false
                          | Some _ => true end)
    end in
  lookup l true.

Module Type BINARY_TRIE.
  Parameter t: Type -> Type.
  Parameter empty: forall (A: Type), t A.
  Parameter get: forall (A: Type), positive -> t A -> option A.
  Parameter set: forall (A: Type), positive -> A -> t A -> t A.
End BINARY_TRIE.

Module Test(PT: BINARY_TRIE).

(* Insert all positives from l, then look them up. *)

Definition bench1 (l: list positive) : bool :=
  benchgen (PT.empty unit) (@PT.set unit) (@PT.get unit) l.

(* Repeatedly insert the same 7 positives.
   A simpler variant of the original bench2 above. *)

Definition bench2gen (n: positive) :=
  let m :=
    Pos.iter
      (fun m =>
        PT.set 1%positive tt (
        PT.set 2%positive tt (
        PT.set 3%positive tt (
        PT.set 4%positive tt (
        PT.set 5%positive tt (
        PT.set 6%positive tt (
        PT.set 7%positive tt m)))))))
      (PT.empty unit) n
  in
    match PT.get 7%positive m with
    | Some _ => true
    | None => false
    end.

Definition bench2 (x: unit) := bench2gen 1000000%positive.

End Test.

Module TestOriginal := Test Original.PTree.
Module TestCanonical := Test Canonical.PTree.
Module TestSigma := Test Sigma.PTree.
Module TestNode01 := Test Node01.PTree.
Module TestGADT := Test GADT.PTree.
Module TestPatricia := Test Patricia.PTree.

(* Testing AVL maps with positives as keys *)

Module PositiveAVL := FMapAVL.Make OrderedPositive.

Module PositiveAVLTree <: BINARY_TRIE.
  Definition t := PositiveAVL.t.
  Definition empty := PositiveAVL.empty.
  Definition get := PositiveAVL.find.
  Definition set := PositiveAVL.add.
End PositiveAVLTree.

Module TestAVLPositive := Test PositiveAVLTree.

(* Testing red-black maps with positives as keys *)

Module PositiveRB := RBT.Make POrderedType.Positive_as_OT.

Module PositiveRBTree <: BINARY_TRIE.
  Definition t := PositiveRB.t.
  Definition empty := @PositiveRB.empty.
  Definition get := @PositiveRB.find.
  Definition set := @PositiveRB.add.
End PositiveRBTree.

Module TestRBPositive := Test PositiveRBTree.

(* Testing AVL maps with strings as keys *)

Module StringAVL := FMapAVL.Make OrderedString.

Module TestAVLString.

Definition bench1 (l: list string) : bool :=
  benchgen (StringAVL.empty unit) (@StringAVL.add unit) (@StringAVL.find unit) l.

End TestAVLString.

(* Testing red-black maps with strings as keys *)

Module StringRB := RBT.Make OrderedStringM.

Module TestRBString.

Definition bench1 (l: list string) : bool :=
  benchgen (@StringRB.empty unit) (@StringRB.add unit) (@StringRB.find unit) l.

End TestRBString.

(* Testing character tries *)

Module TestCharTrie.

Definition bench1 (l: list string) : bool :=
  benchgen (CharTrie.Stringmap.empty unit) (@CharTrie.Stringmap.set unit) (@CharTrie.Stringmap.get unit) l.

End TestCharTrie.

(* PTrees composed with string->positive conversion *)

Module TestPTreeAsStringmap (PT: BINARY_TRIE).

Definition bench1 (l: list string) : bool :=
  benchgen (PT.empty unit)
           (fun s v t => PT.set (pos_of_string s) v t)
           (fun s t => PT.get (pos_of_string s) t)
           l.

End TestPTreeAsStringmap.

Module TestOriginalAsStringmap := TestPTreeAsStringmap Original.PTree.
Module TestCanonicalAsStringmap := TestPTreeAsStringmap Canonical.PTree.
Module TestPatriciaAsStringmap := TestPTreeAsStringmap Patricia.PTree.

(* The benchmark data *)

(* All positives up to 2^n *)

Fixpoint enumerate (n: nat) (base: positive) (accu: list positive) : list positive :=
  match n with
  | O => base :: accu
  | S n => enumerate n (xO base) (enumerate n (xI base) (base :: accu))
  end.

Definition smallnumbers :=
  Eval vm_compute in enumerate 10%nat xH nil.

(* Encodings of strings (taken randomly from /usr/dict/words) *)

Definition words :=
"demitasse" :: "valuations" :: "finches" :: "holy" :: "vaunts" ::
"reinvests" :: "updating" :: "powdered" :: "incisively" :: "gardened" ::
"grassland" :: "gorier" :: "zones" :: "production" :: "juxtaposes" ::
"flabbier" :: "evangelism" :: "surmountable" :: "terminator" :: "Connie" ::
"battlefield" :: "submerges" :: "pastorate" :: "Connors" :: "archived" ::
"intersperses" :: "Highlander" :: "towering" :: "practiced" :: "henpecked" ::
"soaks" :: "Bruno" :: "Sheldon" :: "exhaling" :: "veneer" :: "lecterns" ::
"store" :: "mettle" :: "archest" :: "microsecond" :: "graveyard" ::
"necklaces" :: "Newtonian" :: "ovulated" :: "turquoises" :: "lobe" ::
"excellent" :: "dinged" :: "annulment" :: "cervical" :: "housemaids" ::
"Zappa" :: "plod" :: "spas" :: "Tillich" :: "Hawkins" :: "kindest" ::
"conglomerated" :: "Gay" :: "hackles" :: "recast" :: "lurch" :: "maneuver" ::
"distinctiveness" :: "Stacie" :: "Devon" :: "antihistamines" :: "shlocky" ::
"inflammable" :: "trike" :: "butters" :: "plaids" :: "magnitude" ::
"challenging" :: "millet" :: "slake" :: "gelled" :: "associate" ::
"cinematographer" :: "cockle" :: "showcased" :: "Himmler" :: "polemical" ::
"blueberries" :: "succulents" :: "wrinkly" :: "yoked" :: "Knight" ::
"interlarded" :: "henchman" :: "housewares" :: "Ting" :: "tower" ::
"pitifully" :: "carpeting" :: "vibratos" :: "posher" :: "spitefullest" ::
"midtown" :: "auspiciously" :: "knight" :: "Planck" :: "gaslight" ::
"verdant" :: "resuscitate" :: "laps" :: "Tethys" :: "hush" :: "bobsled" ::
"grousing" :: "Egyptology" :: "arborvitae" :: "passes" :: "perverted" ::
"workbench" :: "relapsed" :: "Deming" :: "pities" :: "freelancers" ::
"wackier" :: "transmits" :: "civilizes" :: "cacophonous" :: "Rotarian" ::
"mysteries" :: "Jordan" :: "marginally" :: "hardball" :: "oarsman" ::
"confuse" :: "indifferently" :: "largess" :: "materialists" :: "altruist" ::
"harped" :: "erroneous" :: "fastest" :: "predominate" :: "spryest" :: "Sc" ::
"flirtatiously" :: "lallygagged" :: "huntsmen" :: "fillip" :: "rattling" ::
"toxins" :: "cockiest" :: "rinse" :: "refiner" :: "visioned" ::
"Freemason" :: "Poisson" :: "Johnathon" :: "vitalizes" :: "Ethiopia" ::
"madam" :: "sententious" :: "pacts" :: "capitulate" :: "hum" :: "blackens" ::
"plied" :: "snowdrifts" :: "safflowers" :: "telethon" :: "corollaries" ::
"airfoil" :: "citrus" :: "welterweights" :: "ordains" :: "boondocks" ::
"nudism" :: "puzzle" :: "enchanting" :: "parkas" :: "insulting" ::
"envious" :: "schnauzers" :: "salubrious" :: "boars" :: "morocco" ::
"Sicilian" :: "elocutionist" :: "wittier" :: "unruliness" :: "sifting" ::
"ladled" :: "Valeria" :: "Nicaea" :: "terraria" :: "reappraising" ::
"uncertainty" :: "synthesizing" :: "qualm" :: "derbies" :: "Cassius" ::
"erratum" :: "haulers" :: "undies" :: "varicose" :: "antechambers" ::
"sillier" :: "shamelessly" :: "categorizes" :: "weary" :: "systematize" ::
"convertible" :: "dryads" :: "ill" :: "stepdaughters" :: "predominated" ::
"culminates" :: "gauged" :: "prating" :: "vectors" :: "misinformed" ::
"murmuring" :: "Barr" :: "miaowing" :: "figure" :: "held" :: "anecdotal" ::
"accreditation" :: "clippers" :: "holler" :: "barons" :: "gunnysack" ::
"ratchets" :: "fort" :: "literally" :: "celluloid" :: "chile" ::
"schemers" :: "detain" :: "slickers" :: "sicks" :: "wiliness" :: "codicil" ::
"debunked" :: "nicely" :: "Sandburg" :: "technocracy" :: "miner" ::
"fitly" :: "Seleucus" :: "suitability" :: "patsies" :: "systematic" ::
"triathlons" :: "brinier" :: "Indiana" :: "matured" :: "craps" ::
"barracks" :: "undeveloped" :: "accumulating" :: "assureds" :: "Dustin" ::
"Ionesco" :: "fed" :: "overgrowth" :: "bests" :: "Psalms" ::
"insurmountable" :: "tossing" :: "Porter" :: "solicitude" :: "reloads" ::
"racketeer" :: "whippersnapper" :: "Langmuir" :: "participles" ::
"Castries" :: "flowing" :: "anthill" :: "nonconductors" :: "maltreated" ::
"obsessive" :: "inflamed" :: "boudoir" :: "phobics" :: "suitor" ::
"merchandised" :: "sentient" :: "fibulae" :: "miscellanies" :: "champing" ::
"rambled" :: "stodgy" :: "Toledos" :: "locoweed" :: "inventoried" ::
"pusillanimity" :: "downstream" :: "hurraying" :: "Benet" :: "bloodbaths" ::
"semifinals" :: "addles" :: "insignificant" :: "nosedives" ::
"snowplowing" :: "amnesty" :: "attestation" :: "unobstructed" ::
"keynoted" :: "pits" :: "orthodontic" :: "horsiest" :: "seafarers" ::
"Milo" :: "Beardmore" :: "dusk" :: "effulgence" :: "Hecuba" ::
"disassociates" :: "injunction" :: "park" :: "Hyde" :: "bracket" ::
"retarded" :: "arrangers" :: "safeguarding" :: "Curtis" :: "fling" ::
"whips" :: "enacted" :: "anthropocentric" :: "marinas" :: "distinguish" ::
"Lt" :: "sybarite" :: "gyrated" :: "intangible" :: "bilinguals" ::
"hairless" :: "unpaid" :: "groaning" :: "ay" :: "greener" :: "account" ::
"Gothics" :: "nationalities" :: "bullock" :: "Simon" :: "warlock" ::
"paraffin" :: "oily" :: "clocking" :: "Mohammed" :: "Metternich" ::
"upchucked" :: "brusque" :: "tunelessly" :: "solidest" :: "frayed" ::
"petrel" :: "tenuously" :: "partnering" :: "outing" :: "distilleries" ::
"baneful" :: "captivity" :: "Carter" :: "sirocco" :: "seeker" :: "toxin" ::
"precincts" :: "molest" :: "intramural" :: "sugarcane" :: "rednecks" ::
"effigy" :: "chloroform" :: "depressives" :: "Carl" :: "gymnast" ::
"stenographic" :: "insensible" :: "glitter" :: "reimposes" ::
"Shakespeare" :: "aftershocks" :: "extermination" :: "hefted" ::
"elliptically" :: "moderated" :: "cleat" :: "hollowing" :: "waywardness" ::
"discreditable" :: "shire" :: "Dorthy" :: "chowder" :: "breeding" ::
"vindictive" :: "Cabinet" :: "showboats" :: "Saskatchewan" ::
"complaisant" :: "binaries" :: "colonialist" :: "episcopate" :: "sandbars" ::
"recidivists" :: "tongues" :: "glossiness" :: "sketchier" :: "postmen" ::
"tutor" :: "Gibson" :: "Nautilus" :: "circularized" :: "reevaluating" ::
"sedatives" :: "bade" :: "contradistinctions" :: "shut" :: "ghostwrites" ::
"diagonal" :: "fermenting" :: "shadows" :: "silky" :: "recapitulate" ::
"pales" :: "Augustan" :: "sasses" :: "Eileen" :: "player" :: "petard" ::
"steeliest" :: "broadly" :: "Abraham" :: "Everette" :: "cellulars" ::
"indecent" :: "plainest" :: "Talley" :: "dismantled" :: "economists" ::
"whim" :: "successor" :: "cryptography" :: "pullers" :: "wizards" ::
"oblongs" :: "annuity" :: "waterproofed" :: "Newton" :: "extol" ::
"soughs" :: "grovel" :: "weathermen" :: "sneaked" :: "parties" ::
"summarily" :: "auger" :: "cheeping" :: "place" :: "Am" :: "gardenias" ::
"seasonal" :: "sprouted" :: "surely" :: "inamorata" :: "braise" ::
"butterier" :: "ruined" :: "unbosom" :: "sicked" :: "angles" :: "stinging" ::
"mountains" :: "Tanya" :: "injures" :: "wipes" :: "Queen" :: "cuddles" ::
"soured" :: "defoliating" :: "Connolly" :: "headbands" :: "mainspring" ::
"writ" :: "collocate" :: "choosey" :: "seamiest" :: "strangulated" ::
"sisters" :: "misbegotten" :: "moveables" :: "halfheartedly" :: "Europa" ::
"collectables" :: "outlay" :: "interred" :: "Ziggy" :: "decays" ::
"prismatic" :: "reshuffled" :: "tartars" :: "sympathizing" :: "Cranmer" ::
"Leona" :: "twits" :: "beheads" :: "bombshell" :: "humanity" :: "frantic" ::
"withdrawals" :: "water" :: "consciousness" :: "benedictions" :: "geckoes" ::
"casual" :: "balsa" :: "tends" :: "entrails" :: "flirted" :: "radiator" ::
"enunciating" :: "favorites" :: "absenteeism" :: "influential" ::
"inhumanity" :: "tuck" :: "bights" :: "flit" :: "thralling" :: "alkalies" ::
"fixative" :: "beatific" :: "superintending" :: "dynamites" :: "wreath" ::
"firebugs" :: "ageism" :: "methane" :: "swivels" :: "turnstiles" ::
"Yugoslavia" :: "constitutionality" :: "Chongqing" :: "misting" ::
"Pissaro" :: "ductility" :: "advance" :: "huntsman" :: "sportswoman" ::
"parting" :: "accidentals" :: "imaginatively" :: "ratification" ::
"intrenched" :: "chap" :: "misinterprets" :: "terminators" :: "warmest" ::
"sevens" :: "Sanders" :: "metro" :: "testy" :: "attempted" :: "lifer" ::
"alternations" :: "strapless" :: "faultiness" :: "doubts" :: "Ulyanovsk" ::
"jabber" :: "spies" :: "Marseillaise" :: "variate" :: "pastured" ::
"incarcerating" :: "exploits" :: "resonators" :: "Cassandra" :: "colossus" ::
"unapproachable" :: "faintness" :: "Abner" :: "forecasting" :: "Indianans" ::
"euphemisms" :: "riffing" :: "Vespucci" :: "burro" :: "Sodom" ::
"salinity" :: "pathology" :: "bohemian" :: "dilettante" :: "stamen" ::
"flagstaffs" :: "mutation" :: "scanties" :: "louses" :: "umbel" ::
"biplanes" :: "scorpion" :: "indued" :: "envying" :: "whoosh" :: "pooled" ::
"twilled" :: "Darius" :: "suavest" :: "wispy" :: "unconditional" ::
"vociferous" :: "senility" :: "unneeded" :: "muster" :: "Woolworth" ::
"solacing" :: "Tahiti" :: "juiciness" :: "restudies" :: "lamaseries" ::
"Iapetus" :: "giggler" :: "divine" :: "mimicking" :: "oversee" ::
"interlace" :: "leaps" :: "lallygag" :: "Callas" :: "periled" :: "dollars" ::
"stochastic" :: "deaconesses" :: "Yvonne" :: "Ark" :: "flubs" ::
"possession" :: "tokenism" :: "ascents" :: "hyping" :: "Lynch" ::
"ingraining" :: "wheres" :: "entails" :: "qualifier" :: "macintosh" ::
"whiles" :: "Taft" :: "massively" :: "singsonging" :: "rampaged" ::
"elegance" :: "closeout" :: "shyly" :: "subterfuge" :: "allusion" ::
"septum" :: "mastered" :: "possessive" :: "wench" :: "Ryukyu" :: "Simone" ::
"addendum" :: "Vandyke" :: "lowers" :: "bitterness" :: "materially" ::
"simpers" :: "blue" :: "hailstone" :: "resoluteness" :: "sandblasted" ::
"plasticity" :: "saviour" :: "batted" :: "handbook" :: "Orlons" ::
"inclusive" :: "intrusted" :: "contrives" :: "fouled" :: "Villon" ::
"chainsawing" :: "uninterrupted" :: "showcases" :: "Pindar" :: "mewling" ::
"insulin" :: "twosome" :: "misdiagnosis" :: "exorbitantly" ::
"congruities" :: "dutiful" :: "deviance" :: "initially" :: "juxtaposition" ::
"sleeves" :: "facts" :: "schuss" :: "Gates" :: "nitroglycerin" ::
"proprietresses" :: "armsful" :: "preppies" :: "labium" :: "discoursed" ::
"removed" :: "incantation" :: "escalating" :: "palpitating" :: "hydrofoil" ::
"improbability" :: "depositing" :: "mimosa" :: "marauding" :: "ganders" ::
"invariable" :: "oldest" :: "whispers" :: "unavoidably" :: "sniffle" ::
"compute" :: "errors" :: "gabbing" :: "potties" :: "Sean" :: "Freda" ::
"glowering" :: "fifteens" :: "spellbinders" :: "pursue" :: "craftsmanship" ::
"referential" :: "undergarment" :: "vampire" :: "Titania" :: "Midwest" ::
"raid" :: "implies" :: "franking" :: "Laurie" :: "strait" :: "theologies" ::
"beware" :: "grassier" :: "postmodern" :: "pistillate" :: "bulb" ::
"docile" :: "haemoglobin" :: "virginity" :: "comfy" :: "blocs" ::
"lightheartedly" :: "overreact" :: "dislocated" :: "prediction" ::
"plenaries" :: "padres" :: "locksmiths" :: "prop" :: "rehash" ::
"unsurprising" :: "firefighter" :: "adhering" :: "discerned" ::
"prostitution" :: "toasty" :: "pecked" :: "coffee" :: "insolvency" ::
"iniquities" :: "affixed" :: "windows" :: "childbirth" :: "mammas" ::
"cannier" :: "stoney" :: "specifications" :: "Amsterdam" :: "hatchways" ::
"tardily" :: "desperado" :: "journalism" :: "pods" :: "hopelessness" ::
"Rachmaninoff" :: "Mississippi" :: "confrontational" :: "accelerates" ::
"Lambert" :: "polios" :: "bussed" :: "Shawna" :: "sneaky" :: "quahogs" ::
"piper" :: "Swansea" :: "seer" :: "energetically" :: "metamorphosis" ::
"polymath" :: "deeps" :: "concerto" :: "Nemesis" :: "scalpel" ::
"educator" :: "pitons" :: "miscegenation" :: "predicating" :: "Chagall" ::
"Kuhn" :: "rowing" :: "brashly" :: "ales" :: "antiquaries" :: "cascades" ::
"Yukon" :: "shanks" :: "furor" :: "refract" :: "season" :: "notarize" ::
"volleys" :: "everyone" :: "pause" :: "crosstown" :: "unfettered" ::
"Czech" :: "sunglasses" :: "budding" :: "musical" :: "Waring" :: "hornet" ::
"Selkirk" :: "importantly" :: "unconquerable" :: "hexagons" :: "chambray" ::
"dressed" :: "banishment" :: "televangelists" :: "pea" :: "Brandt" ::
"isinglass" :: "jackknifes" :: "resents" :: "styled" :: "slamming" ::
"hurry" :: "madras" :: "Milne" :: "unforgiving" :: "bladder" ::
"touchings" :: "tattering" :: "devilish" :: "dirtiest" :: "underpin" ::
"Mexico" :: "overstates" :: "cure" :: "recheck" :: "asexual" ::
"copyright" :: "sportsmen" :: "allergist" :: "loyaler" :: "Jeanette" ::
"validly" :: "conciliate" :: "pulsating" :: "enraptures" :: "dizzy" ::
"navigates" :: "Salvadorans" :: "Mongol" :: "departments" :: "Raphael" ::
"lunging" :: "Brueghel" :: "evanescent" :: "homeyness" :: "threnodies" ::
"AOL" :: "relativity" :: "whimsically" :: "formula" :: "esplanades" ::
"Secretary" :: "remembrance" :: "fetlocks" :: "numbness" :: "yolks" ::
"joining" :: "Diogenes" :: "forager" :: "molests" :: "nuthatch" ::
"pieces" :: "brainstorms" :: "Doppler" :: "falsify" :: "courser" ::
"consistently" :: "reining" :: "bladders" :: "Yangtze" :: "abysmally" ::
"regaled" :: "debentures" :: "askew" :: "epicure" :: "misunderstands" ::
"substantiation" :: "arrested" :: "opaqued" :: "foxholes" :: "mounted" ::
"halting" :: "sentimentalism" :: "exploit" :: "walker" :: "Leslie" :: "Wu" ::
"Manchurian" :: "stricture" :: "Surabaya" :: "chaste" :: "hunchbacked" ::
"Otto" :: "continuation" :: "neighborliness" :: "ids" :: "defect" ::
"Gulliver" :: "objects" :: "Mexicans" :: "Oxonian" :: "Janet" ::
"liberalization" :: "therefrom" :: "substratum" :: "freights" :: "wetter" ::
"type" :: "wealthier" :: "moralizing" :: "Masonic" :: "stammerers" ::
"wildfire" :: "Ora" :: "scandalized" :: "linguists" :: "Salvatore" ::
"Lassen" :: "domiciled" :: "venerable" :: "begrudgingly" :: "pollute" ::
"parfait" :: "spoor" :: "binomial" :: "Gagarin" :: "monograms" ::
"exculpating" :: "leitmotif" :: "charlatan" :: "cynicism" :: "breast" ::
"athletics" :: "copious" :: "tidied" :: "shamefully" :: "infallible" ::
"eject" :: "ticketing" :: "outshines" :: "ensembles" :: "swabbed" ::
"unhooked" :: "mediation" :: "subprograms" :: "polices" :: "Hebrides" ::
"saltshaker" :: "backdating" :: "roundup" :: "dicey" :: "Vuitton" ::
"downplaying" :: "tax" :: "recycled" :: "intoxicants" :: "fortes" ::
"Sensurround" :: "Seljuk" :: "iguanas" :: "guiltier" :: "patella" ::
"cooperative" :: "vanquishing" :: "unfurled" :: "adepts" :: "Turner" ::
"paradise" :: "unscientific" :: "surtaxes" :: "rapt" :: "fornicate" ::
"concerti" :: "Fitch" :: "dithering" :: "monoliths" :: "unhurried" ::
"Jenna" :: "impressionistic" :: "eventful" :: "bronchial" :: "enforce" ::
"gentrifying" :: "heard" :: "east" :: "sacristies" :: "permute" ::
"Yekaterinburg" :: "tummies" :: "frieze" :: "discriminatory" :: "memorize" ::
"digging" :: "arbitration" :: "chamomiles" :: "illuminate" :: "prophecy" ::
"bawdiness" :: "knees" :: "alterable" :: "agitations" :: "reanimated" ::
"widowing" :: "airstrips" :: "Melanesian" :: "schtick" :: "cageyness" ::
"hyperventilating" :: "potters" :: "matted" :: "asthma" :: "steeplejacks" ::
"chug" :: "illustrative" :: "giants" :: "rusks" :: "Guadalajara" ::
"persuaded" :: "travelog" :: "surtaxing" :: "removing" :: "bullhorns" ::
"steels" :: "allege" :: "retrorockets" :: "Goudas" :: "saddlebags" ::
"fruits" :: "loaning" :: "Merle" :: "sherberts" :: "heedful" ::
"Fairbanks" :: "bribe" :: "McPherson" :: "calyxes" :: "Muir" :: "anneal" ::
"Antaeus" :: "spacecrafts" :: "rookies" :: "larynx" :: "toked" ::
"establishes" :: "Lethe" :: "disenchanted" :: "regions" :: "expecting" ::
"agate" :: "murmured" :: "counterfeiter" :: "replenish" :: "evangelistic" ::
"newsletters" :: "charters" :: "constructor" :: "impassivity" ::
"Priestley" :: "indorses" :: "dewdrop" :: "Carrier" :: "approbation" ::
"quadruplicating" :: "jellybeans" :: "salivary" :: "warding" :: "Paul" ::
"inwardly" :: "Amundsen" :: "lieutenants" :: "Zuni" :: "airier" ::
"assembler" :: "Lila" :: "preordained" :: "polluter" :: "liners" ::
"deadbolts" :: "truce" :: "Noemi" :: "jigs" :: "cellists" :: "battening" ::
"rodeos" :: "colonists" :: "Howells" :: "anthropoids" :: "Assad" ::
"looming" :: "Durant" :: "bearers" :: "inkblots" :: "Mooney" ::
"Democritus" :: "Cepheus" :: "alleges" :: "bumpkin" :: "sensationally" ::
"meanest" :: "creamers" :: "dollop" :: "Sundas" :: "twisted" ::
"routinizing" :: "vulgarism" :: "luminary" :: "chinning" ::
"aforementioned" :: "hasting" :: "communicants" :: "pullover" :: "healthy" ::
"clothe" :: "squeaking" :: "classrooms" :: "halyards" :: "awnings" ::
"occurring" :: "wands" :: "scatterbrain" :: "goldenrod" :: "draperies" ::
"employe" :: "dive" :: "colloquialisms" :: "isotopic" :: "Whipple" ::
"idler" :: "bated" :: "cockles" :: "lintel" :: "Seinfeld" :: "Kagoshima" ::
"anterior" :: "traveler" :: "yeshivas" :: "endowments" :: "shingled" ::
"patchier" :: "spritz" :: "smog" :: "slaking" :: "wiggle" :: "devises" ::
"squadrons" :: "potholder" :: "usurpers" :: "goldbricked" :: "Oceania" ::
"decades" :: "hydrogenate" :: "firestorm" :: "ascertain" :: "desiring" ::
"gadflies" :: "subtitled" :: "pigtail" :: "talent" :: "baselines" ::
"motorizing" :: "godchild" :: "wordier" :: "chintzier" :: "Josue" ::
"Elsa" :: "alining" :: "squeezes" :: "usurper" :: "Creation" ::
"ventriloquist" :: "acres" :: "canine" :: "potentials" :: "call" ::
"eighth" :: "gushing" :: "dogma" :: "peafowl" :: "infiltrator" ::
"formalize" :: "Jerry" :: "Walls" :: "bounder" :: "convertor" ::
"retrospect" :: "Frontenac" :: "jab" :: "differ" :: "reward" ::
"sheltered" :: "mobbed" :: "tireder" :: "disenchant" :: "Virgil" ::
"awaked" :: "abolishes" :: "putts" :: "freshens" :: "Filipinos" ::
"underused" :: "affrays" :: "pagans" :: "coexisting" :: "inoculates" ::
"Lepus" :: "calibrating" :: "bonus" :: "gangly" :: "zap" ::
"gratifications" :: "unpopular" :: "kelp" :: "neurological" :: "ignition" ::
"torturing" :: "declamation" :: "firefights" :: "lids" :: "Woolite" ::
"Avior" :: "seduced" :: "Tolkien" :: "shellacs" :: "courtrooms" ::
"appeased" :: "Branden" :: "reenactment" :: "superstars" :: "tolerates" ::
"cubit" :: "Sinai" :: "prosody" :: "shoehorn" :: "impositions" ::
"wistfully" :: "bombarded" :: "Sagittarius" :: "glossies" :: "Consuelo" ::
"preserve" :: "abashes" :: "isolate" :: "thermos" :: "refutation" ::
"tether" :: "tract" :: "valedictorians" :: "redeveloping" :: "expensive" ::
"Amur" :: "minor" :: "rearranged" :: "depot" :: "masses" :: "barbarously" ::
"heeling" :: "guardianship" :: "tepees" :: "shredding" :: "husker" ::
"streaky" :: "Hendrix" :: "Namibians" :: "bistro" :: "noblewoman" ::
"Kyoto" :: "dingy" :: "squalidest" :: "narrowness" :: "theater" :: "fist" ::
"activates" :: "target" :: "Naugahyde" :: "functionally" :: "shipload" ::
"cox" :: "Perez" :: "squaw" :: "appositive" :: "coronations" ::
"statuettes" :: "Pfizer" :: "plank" :: "static" :: "whizzing" ::
"penniless" :: "Lajos" :: "glean" :: "melodramatic" :: "grimed" ::
"shreds" :: "trammels" :: "crystalizing" :: "regrouping" :: "entomology" ::
"Muhammadanism" :: "prisoner" :: "underacts" :: "quiche" :: "Jekyll" ::
"triglyceride" :: "submerge" :: "westernized" :: "wealthiest" ::
"allegiance" :: "excommunications" :: "executioner" :: "statisticians" ::
"rebukes" :: "attachments" :: "prudent" :: "started" :: "impresarios" ::
"preservation" :: "egocentrics" :: "debtor" :: "hardhearted" ::
"meningitis" :: "chopper" :: "duelling" :: "wishers" :: "Republican" ::
"naturally" :: "Marianas" :: "godparents" :: "cupped" :: "trilateral" ::
"seventeenths" :: "mature" :: "chowing" :: "spokespeople" :: "consultants" ::
"hairpin" :: "yaps" :: "procurators" :: "blazing" :: "rigors" :: "Darnell" ::
"unbinding" :: "recanted" :: "pelagic" :: "mites" :: "solenoids" ::
"Burberry" :: "errant" :: "laciest" :: "lark" :: "additions" :: "Grus" ::
"quests" :: "strange" :: "airmailed" :: "landlady" :: "handsome" ::
"congratulations" :: "Slackware" :: "bonded" :: "hurdled" :: "mosquitos" ::
"Eltanin" :: "buckram" :: "weakens" :: "glowing" :: "bedtimes" ::
"constipates" :: "vacuumed" :: "noses" :: "inexperience" :: "tom" ::
"revert" :: "hire" :: "hypothesize" :: "sandblasts" :: "overindulged" ::
"trashed" :: "gained" :: "interferon" :: "concocts" :: "whereas" ::
"blogging" :: "caching" :: "gone" :: "pinker" :: "tapering" ::
"chiaroscuro" :: "subcontinent" :: "catastrophic" :: "lolled" :: "seventy" ::
"engrave" :: "Ann" :: "Fern" :: "cinched" :: "Worcestershire" :: "picking" ::
"sanitation" :: "goat" :: "crusty" :: "ospreys" :: "downgrading" ::
"wrecked" :: "Caribbean" :: "lobsters" :: "Riga" :: "prioritize" ::
"ineluctable" :: "strolls" :: "mudslide" :: "rewarded" :: "pickaback" ::
"systems" :: "degradation" :: "wainscotting" :: "footnoted" :: "alive" ::
"appointing" :: "upscale" :: "shuddered" :: "purled" :: "fondly" ::
"serums" :: "overcrowd" :: "undercover" :: "copper" :: "Legendre" ::
"polygon" :: "plow" :: "smuggled" :: "Menuhin" :: "Angelia" ::
"televangelist" :: "Randell" :: "chooses" :: "lamas" :: "probably" ::
"refinishes" :: "bailed" :: "adverb" :: "provides" :: "dominating" ::
"treadmill" :: "hod" :: "elusive" :: "Pius" :: "detonation" :: "Styx" ::
"school" :: "Kirghistan" :: "disgruntle" :: "terrorists" :: "redone" ::
"Beaumarchais" :: "deifies" :: "tempos" :: "Bettye" :: "diagnosing" ::
"misdiagnoses" :: "carped" :: "aquifer" :: "tweet" :: "crossover" ::
"parqueted" :: "swanky" :: "brutalized" :: "kited" :: "forest" :: "rots" ::
"verisimilitude" :: "Neal" :: "inebriation" :: "Katy" :: "curtsy" ::
"labyrinth" :: "last" :: "avatar" :: "rabbles" :: "unremitting" ::
"sieving" :: "deadens" :: "kindergartener" :: "credulous" :: "hindered" ::
"paddocking" :: "twitch" :: "losses" :: "fluoroscopes" :: "wadi" ::
"coherently" :: "obstruction" :: "Morin" :: "Izanami" :: "proceed" ::
"contrivance" :: "ti" :: "forgotten" :: "audience" :: "displays" ::
"balling" :: "firsthand" :: "Frenches" :: "scherzo" :: "headers" :: "jug" ::
"headrest" :: "foghorns" :: "scrappier" :: "borsch" :: "receptiveness" ::
"partook" :: "permissible" :: "Keller" :: "typhus" :: "sottish" ::
"slavery" :: "metros" :: "coops" :: "Roche" :: "idolize" :: "Manila" ::
"shallower" :: "lessens" :: "reimpose" :: "jingles" :: "deacon" ::
"lioness" :: "rascal" :: "limelight" :: "paternally" :: "gurgled" ::
"ineffectively" :: "declamations" :: "amalgamated" :: "mansion" ::
"audios" :: "landslides" :: "fossilized" :: "grandstanding" :: "fathoms" ::
"royalist" :: "assemblies" :: "lawbreakers" :: "Pilcomayo" :: "Charleston" ::
"planar" :: "Sherri" :: "bronchos" :: "rehires" :: "demo" :: "shah" ::
"divots" :: "rho" :: "someones" :: "pauper" :: "ado" :: "knocks" ::
"petulant" :: "whittles" :: "sicken" :: "Navahos" :: "daytime" :: "Ewing" ::
"imbedding" :: "recliners" :: "latter" :: "relativistic" :: "bum" ::
"adores" :: "honeybees" :: "identical" :: "summation" :: "naturalism" ::
"sawing" :: "unripe" :: "umbels" :: "nonstop" :: "yammer" :: "satanically" ::
"Eumenides" :: "martyrdom" :: "Goldsmith" :: "coated" :: "Harte" ::
"whorl" :: "orphanage" :: "Angie" :: "huskily" :: "Fleming" ::
"insolvable" :: "to" :: "traffics" :: "awls" :: "mangoes" ::
"subcommittee" :: "Vaughn" :: "matures" :: "Eaton" :: "God" :: "bolt" ::
"transplanting" :: "Burgundies" :: "tagged" :: "detoxify" :: "thumbnail" ::
"condiment" :: "Bristol" :: "televised" :: "notoriety" :: "freckle" ::
"poxes" :: "gluttony" :: "Audi" :: "blackballs" :: "dandles" :: "catcall" ::
"premeditating" :: "disembarkation" :: "predictive" :: "ginseng" ::
"dawdler" :: "furbelow" :: "narrative" :: "afloat" :: "emerged" ::
"uneven" :: "Rabelais" :: "diphthongs" :: "Sabbath" :: "perilously" ::
"sharing" :: "proclamation" :: "omnibus" :: "booze" :: "sweepings" ::
"Ronda" :: "factorial" :: "tribunes" :: "Madeiras" :: "itchy" :: "hertz" ::
"wasteful" :: "booths" :: "radioisotope" :: "apiece" :: "purchase" ::
"juniors" :: "Rambo" :: "balloting" :: "quenched" :: "vitalize" :: "Basho" ::
"banged" :: "tarnishing" :: "skylark" :: "crystalline" :: "craning" ::
"imperiously" :: "pleasanter" :: "scrunches" :: "Lilly" :: "bankbook" ::
"newsprint" :: "Latoya" :: "catechises" :: "unsupported" :: "Al" ::
"oftentimes" :: "bodkin" :: "unsay" :: "Elysian" :: "Zhukov" ::
"millepede" :: "brawling" :: "radioactive" :: "kids" :: "putty" ::
"hither" :: "hopefully" :: "sell" :: "surrendered" :: "nicest" ::
"overstated" :: "hominess" :: "relocates" :: "Seiko" :: "grammatically" ::
"decaffeinate" :: "reelecting" :: "refuting" :: "Barnard" :: "suntan" ::
"contaminates" :: "sequel" :: "Rabat" :: "habituated" :: "numbest" ::
"aggravations" :: "rectangles" :: "barber" :: "bowmen" :: "Sirius" ::
"rubes" :: "Amado" :: "Mafioso" :: "UCLA" :: "clumped" :: "posting" ::
"toots" :: "niches" :: "stitch" :: "postwar" :: "smoldered" :: "stillest" ::
"Mick" :: "Pogo" :: "caryatids" :: "refrigerating" :: "reprieved" ::
"stroked" :: "preconditioning" :: "disapproving" :: "discussed" ::
"abstracting" :: "phonying" :: "advertiser" :: "mandates" :: "hypocrisy" ::
"microsurgery" :: "horizontal" :: "paucity" :: "gladder" :: "outsized" ::
"hooding" :: "sternum" :: "solved" :: "Reynolds" :: "bestseller" :: "jowl" ::
"coincided" :: "obtrusive" :: "surmounted" :: "slovens" :: "hobnobbing" ::
"entombing" :: "reorder" :: "exerted" :: "speeders" :: "iridescence" ::
"pushcart" :: "byelaws" :: "structurally" :: "referendums" :: "synchs" ::
"eyes" :: "confusedly" :: "blitz" :: "overcrowds" :: "marvels" :: "legacy" ::
"backpack" :: "typewrites" :: "chairpersons" :: "diminuendo" :: "anxious" ::
"aggressiveness" :: "plagiarize" :: "elide" :: "catalyze" :: "pacemakers" ::
"beholds" :: "overlap" :: "sharpening" :: "vatting" :: "Nova" ::
"hedonists" :: "histrionic" :: "mousetrapping" :: "feebleness" ::
"grandstands" :: "victim" :: "July" :: "wishes" :: "wristband" :: "poetry" ::
"preconceiving" :: "nail" :: "obtrude" :: "unfairness" :: "Job" ::
"prophetically" :: "disordering" :: "surveyor" :: "Merlin" ::
"uncultivated" :: "nappies" :: "reinitialized" :: "Iraqi" :: "roadster" ::
"chromes" :: "Eritrea" :: "burgeon" :: "outstretched" :: "wood" ::
"chapters" :: "Hensley" :: "edited" :: "sweepstake" :: "advantaged" ::
"estuary" :: "crossest" :: "Asquith" :: "categorized" :: "angered" ::
"twinklings" :: "Roslyn" :: "cursorily" :: "earns" :: "trains" ::
"mortuaries" :: "eight" :: "dachshund" :: "boulevards" :: "interleaved" ::
"denude" :: "disinherit" :: "stenches" :: "northeastern" :: "millimeter" ::
"martyred" :: "priorities" :: "sessions" :: "commonplaces" :: "suffragan" ::
"enrols" :: "godmother" :: "adoptive" :: "surfboarded" :: "slaked" ::
"generalizing" :: "squirt" :: "platen" :: "misgoverning" :: "yellowest" ::
"blenders" :: "carrying" :: "equinoctial" :: "Kermit" :: "fibber" ::
"selecting" :: "Poussin" :: "Benghazi" :: "dunked" :: "mentors" ::
"heeding" :: "orate" :: "scarfed" :: "knottiest" :: "obstacles" ::
"carafe" :: "formless" :: "somnambulists" :: "plagiarisms" :: "pan" ::
"bored" :: "rosebush" :: "grittier" :: "confesses" :: "Jenner" ::
"decimate" :: "industrialized" :: "referent" :: "doctorates" :: "sterna" ::
"Aussies" :: "grimes" :: "Urban" :: "retrace" :: "interfaces" :: "newel" ::
"episcopacy" :: "Tahitians" :: "gryphons" :: "Jodie" :: "gaucher" ::
"Justine" :: "disbursement" :: "conscripts" :: "loafing" :: "joints" ::
"unswerving" :: "tensely" :: "fraud" :: "Beck" :: "certifications" ::
"burp" :: "thundershower" :: "chasten" :: "reinsert" :: "exacerbating" ::
"wallflowers" :: "brooch" :: "Alan" :: "compacter" :: "Lauder" ::
"betting" :: "attainable" :: "defecated" :: "befell" :: "mat" :: "Goren" ::
"bolas" :: "pealed" :: "mustiness" :: "disestablished" :: "rhymes" ::
"reverberating" :: "stairway" :: "accumulative" :: "blondness" :: "phloem" ::
"instruments" :: "roweled" :: "Nimitz" :: "Mathias" :: "attraction" ::
"reemerges" :: "endearingly" :: "cuttlefish" :: "narked" :: "giddiest" ::
"spaceman" :: "altruistically" :: "Gipsies" :: "swigs" :: "driving" ::
"unsnarls" :: "valor" :: "disparaged" :: "slavered" :: "synthesize" ::
"intermediate" :: "onward" :: "inversion" :: "mammary" :: "slays" ::
"comparably" :: "impregnating" :: "presently" :: "deeds" :: "blindest" ::
"praline" :: "quailing" :: "safer" :: "gruff" :: "monkeying" :: "caged" ::
"Pernod" :: "reciprocity" :: "evils" :: "thickens" :: "Hampshire" ::
"nonpolitical" :: "isometrics" :: "unquotes" :: "dustless" :: "Ferguson" ::
"degenerative" :: "sesames" :: "obliges" :: "zippers" :: "curlycues" ::
"businessmen" :: "grayed" :: "Appleton" :: "Sampson" :: "sunflowers" ::
"deal" :: "septa" :: "spectroscopes" :: "myself" :: "warrants" ::
"motherfucking" :: "veggies" :: "uncivil" :: "counterexamples" :: "strap" ::
"pattern" :: "restraints" :: "Mallomars" :: "consensus" :: "indigent" ::
"conservationists" :: "Sheetrock" :: "dispirits" :: "daydreamers" ::
"devour" :: "famished" :: "mellowed" :: "obliterating" :: "feathered" ::
"opalescence" :: "pancaking" :: "Occident" :: "oviduct" :: "gambol" ::
"actuators" :: "circumstances" :: "bricked" :: "harelip" ::
"whippersnappers" :: "subtrahends" :: "propensities" :: "Hertzsprung" ::
"bloody" :: "disappearing" :: "Scrooge" :: "deism" :: "validated" ::
"cornrowed" :: "wetness" :: "hidebound" :: "interposing" :: "retirements" ::
"epigrams" :: "unmindful" :: "dangerous" :: "secondly" :: "vicarages" ::
"Reynaldo" :: "unification" :: "diskette" :: "wonderland" :: "roamed" ::
"averaged" :: "fury" :: "unsafe" :: "routines" :: "popovers" :: "leafless" ::
"pampas" :: "kilts" :: "Baptists" :: "dikes" :: "bawdier" :: "whiplash" ::
"strawing" :: "moire" :: "Wedgwood" :: "enhance" :: "impenetrable" ::
"reprobates" :: "spurts" :: "state" :: "racing" :: "tomfoolery" ::
"blastoffs" :: "Cotton" :: "overqualified" :: "conspirator" ::
"oversleeping" :: "observed" :: "reoccurs" :: "needing" :: "Ricky" ::
"stalwart" :: "pilings" :: "effigies" :: "Nicaragua" :: "restrooms" ::
"Vaseline" :: "missteps" :: "knighthood" :: "reunited" :: "blondes" ::
"knottier" :: "Scandinavia" :: "foresees" :: "Apollos" :: "Stockholm" ::
"whipped" :: "dismal" :: "victory" :: "collegian" :: "godchildren" ::
"sleazy" :: "extricate" :: "Europe" :: "capriciousness" :: "infinite" ::
"potentially" :: "ruder" :: "ventriloquism" :: "tort" :: "Mathis" ::
"perilling" :: "jabbing" :: "schoolyard" :: "drew" :: "galls" :: "hutzpa" ::
"Castillo" :: "transponder" :: "homeopathic" :: "adherent" :: "supporters" ::
"endangered" :: "middle" :: "Spica" :: "Shanna" :: "constabulary" ::
"Torah" :: "vacuously" :: "lugged" :: "enfold" :: "purser" ::
"alternating" :: "ambiences" :: "flicker" :: "pompously" :: "Macon" ::
"betroths" :: "bloodier" :: "surmounts" :: "urbanest" :: "piggish" ::
"rescinds" :: "community" :: "libertarians" :: "Robert" :: "exaggerated" ::
"mast" :: "Tagore" :: "professor" :: "pantheists" :: "placidity" ::
"chipmunks" :: "Pacino" :: "employable" :: "asphalting" :: "grands" ::
"bereave" :: "Juneau" :: "wheezy" :: "retypes" :: "Quisling" :: "respired" ::
"waffles" :: "glaziers" :: "chatterers" :: "accelerations" :: "scumming" ::
"exchanged" :: "wilts" :: "querulously" :: "tyrannosaur" :: "Schlesinger" ::
"footman" :: "nub" :: "badness" :: "aerate" :: "recaps" :: "empaneled" ::
"prattled" :: "intimations" :: "narwhal" :: "viscount" :: "thickest" ::
"belayed" :: "announcements" :: "unsatisfying" :: "incontestable" ::
"markup" :: "ended" :: "definitely" :: "Bettie" :: "cricks" :: "Swede" ::
"tries" :: "wistful" :: "rack" :: "requested" :: "Bohemia" :: "oldies" ::
"reactivate" :: "lipreads" :: "criers" :: "conscience" :: "clandestinely" ::
"thermoses" :: "hobby" :: "semicircular" :: "Misty" :: "bootblack" ::
"Mirzam" :: "Kalashnikov" :: "mismanaged" :: "Thorazine" :: "suggests" ::
"cruller" :: "inactivity" :: "salesmen" :: "Garza" :: "celibates" ::
"limos" :: "hatter" :: "persists" :: "heterodox" :: "Knuth" :: "gruffer" ::
"laces" :: "trickles" :: "rewinding" :: "biographers" :: "homogeneously" ::
"overprotective" :: "demonstrators" :: "tollgate" :: "Saxony" ::
"attempts" :: "sullenest" :: "mockeries" :: "contretemps" :: "laxative" ::
"galosh" :: "Janissary" :: "masticated" :: "deed" :: "taxpayer" :: "boot" ::
"sises" :: "woodworking" :: "Douay" :: "gynecologist" :: "goblin" ::
"cute" :: "rangers" :: "cutter" :: "proposed" :: "interweaving" ::
"Nukualofa" :: "monickers" :: "idiotic" :: "migratory" :: "insulators" ::
"seraph" :: "compel" :: "abortion" :: "participants" :: "coeducation" ::
"touring" :: "Jillian" :: "multicolored" :: "floppier" :: "Fernando" ::
"Abby" :: "tyrants" :: "basked" :: "break" :: "Epictetus" :: "transcripts" ::
"couch" :: "adequately" :: "bashful" :: "washtubs" :: "kindliest" ::
"steppingstone" :: "helmsmen" :: "extradites" :: "rhetorically" ::
"gentry" :: "impure" :: "Sephardi" :: "gibbet" :: "optimal" :: "tuneless" ::
"extenuate" :: "mutton" :: "pollinated" :: "overpopulated" :: "spumoni" ::
"psychedelics" :: "devote" :: "spitball" :: "herein" :: "clipboards" ::
"pilaw" :: "mystified" :: "gaiters" :: "ventricles" :: "sweeping" ::
"Ursula" :: "deterioration" :: "fogs" :: "typifies" :: "membership" ::
"convert" :: "beachheads" :: "noting" :: "quintuplets" :: "bacchanalian" ::
"rationalizations" :: "harem" :: "narrators" :: "Stern" :: "cherubim" ::
"Huntley" :: "passkey" :: "Kiel" :: "aeries" :: "tummy" :: "spasms" ::
"wooliest" :: "proofreads" :: "Arthur" :: "Labrador" :: "untidiness" ::
"bankruptcies" :: "Jew" :: "gizmo" :: "holes" :: "kopeck" :: "pads" ::
"Adler" :: "lull" :: "nonevent" :: "adviser" :: "Tabitha" :: "Mazama" ::
"bunker" :: "paintbrush" :: "spent" :: "exude" :: "wintriest" ::
"shuttlecocks" :: "skates" :: "Jody" :: "pedantry" :: "mural" :: "Lola" ::
"Pompey" :: "greats" :: "anxieties" :: "pudgy" :: "devilry" :: "summerier" ::
"partridge" :: "diurnally" :: "sprucing" :: "ambitiously" :: "arenas" ::
"slaughtering" :: "coins" :: "searchlight" :: "pelleted" :: "dissection" ::
"shades" :: "amoral" :: "market" :: "gunrunners" :: "misquotations" ::
"startle" :: "virginals" :: "piggies" :: "Cubans" :: "brevity" ::
"auspice" :: "plutocratic" :: "smelter" :: "summonsing" :: "videotaping" ::
"scribbling" :: "escalations" :: "Euler" :: "Brianna" :: "Brandeis" ::
"freestyle" :: "explicitly" :: "searching" :: "Kamchatka" :: "visitations" ::
"crescendos" :: "gobbing" :: "Monet" :: "blacktop" :: "technology" ::
"desalinated" :: "predicts" :: "hypnotizes" :: "operative" :: "climaxes" ::
"ewers" :: "Adenauer" :: "dude" :: "forbore" :: "Formicas" :: "Ernst" ::
"inveigh" :: "strings" :: "ingrained" :: "mulches" :: "loopy" ::
"enslaving" :: "anchorwoman" :: "Westerns" :: "encompass" :: "Stolypin" ::
"Arab" :: "bubbles" :: "besotted" :: "butterflied" :: "concluded" ::
"quartets" :: "sociological" :: "contiguous" :: "goalpost" :: "knitwear" ::
"bunches" :: "animatedly" :: "industrially" :: "surly" :: "nonalcoholic" ::
"aridity" :: "schoolbook" :: "Marlin" :: "hart" :: "decapitated" ::
"intake" :: "aftereffect" :: "devil" :: "wretches" :: "superconductivity" ::
"skims" :: "scoured" :: "rectors" :: "whippoorwill" :: "disallows" ::
"Twizzlers" :: "cabooses" :: "retrograding" :: "larches" :: "vehement" ::
"catechised" :: "crossroads" :: "harvest" :: "isthmus" :: "peccadillos" ::
"slurps" :: "insurgent" :: "mason" :: "Ramona" :: "nationalizes" ::
"rashest" :: "annihilates" :: "Utopias" :: "notches" :: "inedible" ::
"dispassionate" :: "matriculated" :: "Ward" :: "reckon" :: "repackages" ::
"bilaterally" :: "Dutchman" :: "fording" :: "grimmer" :: "aced" ::
"astronauts" :: "fieldwork" :: "lunchrooms" :: "scurried" :: "surges" ::
"consensual" :: "unstabler" :: "stroking" :: "disk" :: "rigor" ::
"Capetown" :: "unholiest" :: "Kaufman" :: "quarters" :: "deferments" ::
"ambitious" :: "Meyers" :: "amazon" :: "cranky" :: "raped" :: "persuades" ::
"stiles" :: "cookie" :: "senate" :: "impressively" :: "Leroy" ::
"paltrier" :: "superbest" :: "gratings" :: "tackler" :: "Guayaquil" ::
"pasteurization" :: "showy" :: "iambics" :: "repel" :: "hilarious" ::
"Pena" :: "disbelieved" :: "Frigidaire" :: "withstood" :: "periwinkle" ::
"misconceived" :: "frostbites" :: "calcium" :: "showmen" :: "quarantining" ::
"Sigismund" :: "mergers" :: "psychics" :: "menstrual" :: "afterburners" ::
"revelry" :: "carnally" :: "pulses" :: "member" :: "Tameka" :: "moonstone" ::
"insensate" :: "campground" :: "vitality" :: "rediscovered" :: "trivet" ::
"junked" :: "holiest" :: "moustaches" :: "Washingtonian" :: "beating" ::
"fourscore" :: "reemerge" :: "freebasing" :: "Scot" :: "coital" :: "bulge" ::
"documentaries" :: "banister" :: "mead" :: "candlestick" :: "palsied" ::
"roasters" :: "recreating" :: "interfered" :: "polity" :: "Maupassant" ::
"herbal" :: "transmissions" :: "pettifogging" :: "raring" :: "overexposed" ::
"clumsiness" :: "straights" :: "unmanageable" :: "Chatterton" :: "dulls" ::
"erotica" :: "soundproof" :: "flying" :: "didactic" :: "surveyed" ::
"inundates" :: "rouge" :: "hoagie" :: "tenderizes" :: "page" :: "written" ::
"integuments" :: "denies" :: "appendages" :: "amongst" :: "lathes" ::
"fricasseed" :: "springs" :: "conjectural" :: "south" :: "plastered" ::
"Aruba" :: "tubed" :: "promulgates" :: "groggiest" :: "rebellious" ::
"mail" :: "eater" :: "viragos" :: "heavenliest" :: "Sec" ::
"sanctimoniously" :: "evicting" :: "omnipotent" :: "voyaged" ::
"agitation" :: "Dominguez" :: "chaise" :: "relics" :: "syringing" ::
"takeovers" :: "bogeying" :: "trading" :: "tamping" :: "ascendents" ::
"muses" :: "motivating" :: "skirted" :: "Aztec" :: "scurf" ::
"reconstitute" :: "tickets" :: "motorcade" :: "straitjacketing" ::
"gosling" :: "plinths" :: "bellybutton" :: "thrones" :: "jeering" ::
"rhubarb" :: "weighty" :: "communicant" :: "grandiloquence" :: "Btu" ::
"bruises" :: "gull" :: "modifiable" :: "Figueroa" :: "spooks" :: "upgrade" ::
"swellest" :: "cussed" :: "revolutions" :: "Laurence" :: "approximation" ::
"revolved" :: "rare" :: "device" :: "frowsy" :: "objective" :: "fore" ::
"scruffy" :: "urinal" :: "assassination" :: "palsying" :: "moral" ::
"giblet" :: "resemblances" :: "futzing" :: "fearlessly" :: "rabbinical" ::
"conductors" :: "fallowed" :: "canvasbacks" :: "longing" :: "gravitation" ::
"populist" :: "wheedled" :: "defuse" :: "slogs" :: "hyphened" ::
"travellers" :: "wisteria" :: "woes" :: "escapist" :: "bluebirds" ::
"profiling" :: "screwing" :: "troll" :: "clergymen" :: "fixture" ::
"understudied" :: "Songhua" :: "perfuming" :: "posters" :: "velour" ::
"power" :: "deploy" :: "exigencies" :: "pluperfects" :: "arithmetically" ::
"Marduk" :: "Irishman" :: "congested" :: "emery" :: "certifying" ::
"bloodshed" :: "raged" :: "fished" :: "lymphomata" :: "Valentino" ::
"Birdseye" :: "basic" :: "panchromatic" :: "oversupply" :: "transliterate" ::
"amendment" :: "Martha" :: "ravels" :: "impregnation" :: "Bismarck" ::
"Talmuds" :: "toppling" :: "nosiness" :: "woodpiles" :: "Ruskin" ::
"dorkier" :: "empresses" :: "progressions" :: "atrocities" :: "shrinkage" ::
"shoplifter" :: "mash" :: "spokesmen" :: "gelds" :: "eviscerate" ::
"shortcomings" :: "terrify" :: "woodsy" :: "convey" :: "abodes" ::
"solicitation" :: "hydroplaning" :: "Orlon" :: "adverting" ::
"microprocessors" :: "bassoonists" :: "dynamic" :: "Lycurgus" ::
"nonunion" :: "Malory" :: "quandary" :: "cambia" :: "crock" :: "hassle" ::
"Lulu" :: "alibi" :: "excretions" :: "adjective" :: "honoring" ::
"nebulous" :: "shining" :: "pitchmen" :: "spurring" :: "conversion" ::
"salvation" :: "zinc" :: "warred" :: "Azov" :: "barbarians" :: "mindless" ::
"felts" :: "abbreviates" :: "abruptest" :: "empanels" :: "andantes" ::
"stowaways" :: "Charlie" :: "granny" :: "Gothic" :: "fixating" ::
"midriff" :: "diarrhea" :: "program" :: "callowest" :: "counterfeiting" ::
"concavity" :: "treble" :: "awarded" :: "Glaxo" :: "cholera" :: "brownish" ::
"clarification" :: "avalanche" :: "emboss" :: "subsequently" :: "abrasion" ::
"tarnishes" :: "rills" :: "indistinctly" :: "discontented" :: "Laurent" ::
"missiles" :: "elitists" :: "delicious" :: "overwhelm" :: "idealistic" ::
"than" :: "bisexuality" :: "Moe" :: "dismounting" :: "retype" ::
"anecdote" :: "Gaziantep" :: "understandably" :: "mines" :: "napalm" ::
"horsed" :: "Harbin" :: "granddads" :: "pandas" :: "unsteadiness" ::
"overflow" :: "convention" :: "camellia" :: "occludes" :: "Claiborne" ::
"leggings" :: "tzarinas" :: "sleepily" :: "accommodates" :: "accustoming" ::
"allowing" :: "fiercer" :: "undaunted" :: "unexceptionable" :: "civilian" ::
"potpie" :: "House" :: "dunned" :: "flypapers" :: "priestlier" ::
"aerials" :: "establishing" :: "caraways" :: "watt" :: "inhalers" ::
"sidelights" :: "emptying" :: "monolingual" :: "piratical" :: "proud" ::
"dependents" :: "signalize" :: "irrational" :: "appealed" ::
"fraudulently" :: "zings" :: "typography" :: "stinkers" :: "earthenware" ::
"fridge" :: "skip" :: "steamrollered" :: "accompaniment" :: "quads" ::
"yups" :: "unsatisfied" :: "gainsaying" :: "monstrance" :: "Ceausescu" ::
"fantasies" :: "Sadie" :: "mislay" :: "hate" :: "doling" :: "castigator" ::
"seedy" :: "confederacy" :: "ratted" :: "departed" :: "Bangor" ::
"flatterer" :: "Freya" :: "stilettoes" :: "intellectualize" :: "dredger" ::
"misuse" :: "lathed" :: "buddies" :: "fountainhead" :: "falsest" ::
"prerecording" :: "cuticles" :: "sooth" :: "bequeathed" :: "sharpshooters" ::
"kindly" :: "sundered" :: "generosities" :: "scaring" :: "preached" ::
"legalistic" :: "blithest" :: "Roeg" :: "paroxysms" :: "inspiring" ::
"commemorative" :: "Viacom" :: "hammerhead" :: "radiologists" ::
"contagious" :: "occupations" :: "Gullah" :: "encroachments" :: "dwindles" ::
"portfolio" :: "lidded" :: "generation" :: "curves" :: "barricade" ::
"cornet" :: "upraising" :: "debilitates" :: "Clapeyron" :: "martini" ::
"supervisor" :: "appreciated" :: "stridently" :: "Ungava" :: "historic" ::
"envelopes" :: "operate" :: "rhyme" :: "plainness" :: "ravishingly" ::
"donates" :: "chest" :: "Flemish" :: "compulsion" :: "copyrights" ::
"navigators" :: "lampshades" :: "godfather" :: "sacramental" :: "Caleb" ::
"supernaturals" :: "met" :: "summoning" :: "hemp" :: "scrubs" :: "roach" ::
"milligram" :: "chateaus" :: "forgetful" :: "perquisites" :: "beepers" ::
"depopulating" :: "dissolute" :: "Chandrasekhar" :: "Fowler" ::
"parsimonious" :: "radicals" :: "magma" :: "gentlewoman" :: "madhouses" ::
"grouted" :: "litterbugs" :: "bootee" :: "tornados" :: "scholar" ::
"matronly" :: "Barbara" :: "Borodin" :: "Ringling" :: "gaming" ::
"syphilitic" :: "Mouthe" :: "motile" :: "worriers" :: "dirties" ::
"insulation" :: "accomplish" :: "Ginger" :: "mattering" :: "career" ::
"polishers" :: "platform" :: "deepens" :: "campanili" :: "saucy" ::
"presides" :: "mushiest" :: "dairying" :: "nonresidents" :: "enduring" ::
"indignantly" :: "minnow" :: "Passover" :: "bulletproofs" ::
"mimeographed" :: "pricking" :: "overgrown" :: "reales" :: "sobbing" ::
"containing" :: "Jaxartes" :: "girt" :: "justifications" :: "explore" ::
"intent" :: "advocate" :: "consultations" :: "Boeing" :: "unconditionally" ::
"insistence" :: "suitcases" :: "Alexandria" :: "pedicures" :: "moisten" ::
"filters" :: "elected" :: "sympathize" :: "revolver" :: "Daniel" ::
"Mattel" :: "reeving" :: "digesting" :: "pettiest" :: "unpunished" ::
"hurdle" :: "herring" :: "tidewaters" :: "pearly" :: "pinching" ::
"Carina" :: "weather" :: "perturbation" :: "seemingly" :: "Prada" ::
"develop" :: "centennial" :: "coccyges" :: "ham" :: "flux" :: "sidewalls" ::
"docketing" :: "scraper" :: "pitchers" :: "amplify" :: "tedium" ::
"incognitos" :: "Eskimo" :: "dibbling" :: "obliviousness" :: "seismically" ::
"franchising" :: "chewed" :: "excellence" :: "bedraggles" :: "romaine" ::
"providential" :: "onyx" :: "cablecasts" :: "Sankara" :: "resinous" ::
"enumerate" :: "librettists" :: "reunion" :: "Bardeen" :: "angioplasty" ::
"steward" :: "veil" :: "artless" :: "simulator" :: "confederating" ::
"seducers" :: "reciprocally" :: "investigative" :: "Rangoon" :: "astuter" ::
"lusciousness" :: "Hobbes" :: "snowstorm" :: "courteousness" :: "leagued" ::
"preferred" :: "floss" :: "Philippines" :: "outset" :: "incompatibility" ::
"sensuous" :: "slipcover" :: "modifies" :: "therapists" :: "instruction" ::
"intermarry" :: "enacting" :: "fight" :: "ensnaring" :: "commercializes" ::
"illiterates" :: "oinks" :: "reconditions" :: "bite" :: "flinging" ::
"drunker" :: "instantly" :: "vesicle" :: "flared" :: "propounds" ::
"womenfolk" :: "lampblack" :: "extradite" :: "crazier" :: "faring" ::
"comeuppance" :: "darkly" :: "rehabs" :: "minstrels" :: "obnoxious" ::
"Formosa" :: "special" :: "slags" :: "Gupta" :: "grossing" ::
"withstanding" :: "espy" :: "legislators" :: "gavotte" :: "ptarmigans" ::
"Pribilof" :: "cloudbursts" :: "Rosenberg" :: "cauterizes" :: "respelt" ::
"smokers" :: "wakening" :: "Leo" :: "chimney" :: "Vesta" :: "Zaire" ::
"transgresses" :: "alchemist" :: "changing" :: "differentiated" ::
"vamoose" :: "boiling" :: "weeders" :: "base" :: "portrayals" ::
"comradeship" :: "raw" :: "lamb" :: "understated" :: "reams" :: "rubies" ::
"pulsing" :: "summoned" :: "reconquers" :: "unflattering" :: "bridegrooms" ::
"exclaiming" :: "clunked" :: "swordsmen" :: "apoplectic" :: "motocross" ::
"midst" :: "hydroplaned" :: "Mongoloid" :: "coagulated" :: "equinoxes" ::
"eccentric" :: "freely" :: "sinfully" :: "waltz" :: "hackneying" ::
"Celeste" :: "Hormel" :: "Clausewitz" :: "expunged" :: "Hogarth" ::
"prepay" :: "transmuting" :: "Marcie" :: "Hegelian" :: "perpetually" ::
"unclearest" :: "symbolize" :: "domes" :: "bride" :: "buffalos" :: "lags" ::
"timidity" :: "lawfully" :: "humorous" :: "guesstimates" :: "masqueraders" ::
"lactates" :: "undulating" :: "Felipe" :: "shootings" :: "infantrymen" ::
"slumbrous" :: "Tunney" :: "Brighton" :: "schusses" :: "Persia" ::
"requisitions" :: "thoughts" :: "ramparts" :: "assembling" :: "Melva" ::
"Malagasy" :: "tottered" :: "riddle" :: "adorns" :: "dawns" :: "Mason" ::
"sheeting" :: "swarthy" :: "slipperier" :: "appealing" :: "Dulles" ::
"serially" :: "legends" :: "sectionals" :: "affirmation" :: "acetate" ::
"deaths" :: "inpatient" :: "ghosts" :: "Basel" :: "woodmen" :: "travesty" ::
"prank" :: "yawns" :: "Jayne" :: "decorate" :: "corkscrewing" :: "vow" ::
"fibula" :: "tattoo" :: "deodorizing" :: "nutriments" :: "busby" ::
"vogues" :: "disconnecting" :: "ruffians" :: "preexist" :: "eerie" ::
"clergywomen" :: "handedness" :: "Patricia" :: "taxying" ::
"neighborhoods" :: "afterbirths" :: "reprogram" :: "purports" ::
"uncommunicative" :: "shed" :: "discourses" :: "doodler" :: "expense" ::
"ambassadorial" :: "fakir" :: "undervalues" :: "animator" :: "interludes" ::
"ascent" :: "per" :: "sols" :: "immunize" :: "deign" :: "belled" ::
"gunshots" :: "Mendez" :: "evidenced" :: "modernizes" :: "briefing" ::
"Qatar" :: "pained" :: "castration" :: "twaddling" :: "conjoining" ::
"suffragettes" :: "assuring" :: "elemental" :: "Goldman" ::
"retrospection" :: "Microsoft" :: "sulfate" :: "cowgirl" :: "bye" ::
"stacking" :: "rinses" :: "foolhardiness" :: "Prof" :: "untidy" ::
"seating" :: "globally" :: "safest" :: "shoeshines" :: "prettied" ::
"spouting" :: "gnats" :: "Smithsonian" :: "Tampa" :: "wore" ::
"parenthesize" :: "installs" :: "gonged" :: "Barnabas" :: "shore" ::
"nineteen" :: "discreeter" :: "carried" :: "acetic" :: "acquiesce" ::
"admirers" :: "Yves" :: "microcode" :: "masquerading" :: "climatic" ::
"Melton" :: "deadline" :: "crustier" :: "riverbed" :: "Frankfort" ::
"swiveling" :: "ligaturing" :: "trimester" :: "finitely" :: "Smetana" ::
"rushing" :: "seminarian" :: "tidies" :: "Vilnius" :: "craftier" ::
"porpoises" :: "depreciation" :: "bedfellow" :: "usherette" ::
"cannonball" :: "Horn" :: "hymns" :: "inkier" :: "Whitehead" ::
"overburdened" :: "pitching" :: "nailed" :: "maniac" :: "sex" ::
"masturbated" :: "kinswomen" :: "Bergson" :: "samurai" :: "frequent" ::
"mummers" :: "snoopier" :: "perihelia" :: "burgle" :: "Rb" :: "willowiest" ::
"gladiolus" :: "polymer" :: "infliction" :: "insufferably" :: "skeins" ::
"incomprehensibly" :: "vacillations" :: "palmettos" :: "unholier" ::
"beds" :: "Linda" :: "pyorrhea" :: "abhorrence" :: "desired" :: "reigned" ::
"deer" :: "gladiator" :: "unsatisfactory" :: "loofah" :: "linkages" ::
"Queens" :: "pedagogy" :: "Arius" :: "wavering" :: "decamped" :: "jackdaw" ::
"permanently" :: "poisoned" :: "nerved" :: "belabored" :: "imitated" ::
"spritzes" :: "chaotic" :: "gametes" :: "halfbacks" :: "robed" ::
"megaphones" :: "chinstrap" :: "predilections" :: "pest" :: "impeaches" ::
"mannikins" :: "fads" :: "Gasser" :: "ricking" :: "reestablishes" ::
"immolates" :: "sprinters" :: "commence" :: "stabling" :: "Bursa" ::
"Uriel" :: "unafraid" :: "encloses" :: "gobblers" :: "crossways" ::
"rededicate" :: "disburses" :: "suppression" :: "ciphering" ::
"uninterpreted" :: "masturbates" :: "titan" :: "pepped" :: "coloration" ::
"combats" :: "turnovers" :: "Kohinoor" :: "Atlanta" :: "Haas" :: "leaned" ::
"divergence" :: "categorization" :: "folio" :: "dalliances" :: "allures" ::
"vignetting" :: "thankfulness" :: "shinnied" :: "derails" :: "Permalloy" ::
"mawkishly" :: "slightest" :: "tortoiseshell" :: "vital" :: "batten" ::
"oversexed" :: "copperheads" :: "Soddy" :: "Ananias" :: "tread" ::
"entomological" :: "deadpanning" :: "ineffable" :: "outstayed" ::
"stabilized" :: "jauntiest" :: "Semarang" :: "constraint" ::
"uninstallers" :: "infractions" :: "Raoul" :: "devout" :: "climbs" ::
"Eton" :: "thermoplastics" :: "cages" :: "sticker" :: "costlier" ::
"tabled" :: "reoccupied" :: "exhort" :: "heros" :: "sensation" ::
"immunity" :: "sexist" :: "turnabout" :: "Thornton" :: "untiringly" ::
"Maalox" :: "panhandler" :: "costumed" :: "bottom" :: "particulate" ::
"espressos" :: "embarkation" :: "dyestuff" :: "cocoas" :: "motocrosses" ::
"gratis" :: "swellhead" :: "immodesty" :: "Barclay" :: "proven" ::
"isolationist" :: "tomes" :: "bankbooks" :: "underplays" :: "acrostic" ::
"concourses" :: "Belushi" :: "conditioner" :: "potions" :: "fitness" ::
"Slavonic" :: "budgies" :: "rifles" :: "disqualifications" :: "impression" ::
"Loire" :: "frostily" :: "applauded" :: "forging" :: "doggoning" ::
"disarm" :: "pummeling" :: "wards" :: "mooch" :: "Euclidean" :: "fluxed" ::
"canonized" :: "wizard" :: "Miss" :: "glottis" :: "synergism" ::
"Montezuma" :: "touched" :: "chicks" :: "unhorse" :: "manicuring" ::
"specific" :: "Jezebels" :: "endearments" :: "sobs" :: "Moldova" ::
"bullfinches" :: "intensest" :: "welters" :: "incubated" :: "durability" ::
"coccyx" :: "chinos" :: "Fabian" :: "ochre" :: "Harrisburg" :: "farmyard" ::
"mavericks" :: "fraction" :: "preset" :: "waded" :: "ingestion" ::
"tintinnabulation" :: "nostrums" :: "aim" :: "period" :: "remonstrance" ::
"hoot" :: "pile" :: "Terence" :: "fauns" :: "ridicules" :: "hoards" ::
"Muscovy" :: "underplay" :: "lagniappe" :: "abrogations" :: "knave" ::
"Yahtzee" :: "extractors" :: "undersigns" :: "whores" :: "encases" ::
"statistics" :: "gentrified" :: "Waikiki" :: "shrieked" :: "interluding" ::
"branches" :: "abutment" :: "Maimonides" :: "agitates" :: "sporadically" ::
"gentling" :: "mamboed" :: "daunts" :: "uterus" :: "begs" :: "miscalls" ::
"Parks" :: "identifying" :: "nonproductive" :: "cartridges" :: "editions" ::
"Perelman" :: "cataracts" :: "shelling" :: "subway" :: "medical" ::
"nestled" :: "Mariano" :: "leaved" :: "asseverating" :: "plasterboard" ::
"lugubrious" :: "patch" :: "obligated" :: "Carney" :: "disillusionment" ::
"marries" :: "housewife" :: "pluckier" :: "assorted" :: "invents" ::
"innkeeper" :: "stimuli" :: "orchestration" :: "conduction" :: "Mar" ::
"responsibilities" :: "polled" :: "saffrons" :: "preludes" :: "propane" ::
"plaintively" :: "Sundays" :: "Carver" :: "gigolo" :: "declines" ::
"Marat" :: "depletion" :: "syndrome" :: "tampons" :: "horsey" :: "japan" ::
"telecasting" :: "Atropos" :: "beautifier" :: "Keenan" :: "seedlings" ::
"iconoclastic" :: "trunk" :: "crackpot" :: "rinks" :: "effervesces" ::
"oboes" :: "incredulously" :: "scriptural" :: "drenches" :: "headstone" ::
"barricaded" :: "sourer" :: "documents" :: "ulna" :: "polarizes" ::
"brunched" :: "chintz" :: "leprosy" :: "reapportioning" :: "strangers" ::
"horn" :: "authorize" :: "Gerardo" :: "aromatherapy" :: "replicating" ::
"gentlest" :: "queasiness" :: "ignominy" :: "snoozing" :: "praying" ::
"project" :: "kneel" :: "smelts" :: "surer" :: "jocularity" :: "Concord" ::
"brutish" :: "proposals" :: "Premyslid" :: "mire" :: "unfrocking" ::
"unclothed" :: "Northwests" :: "sonnies" :: "beatnik" :: "rarely" ::
"Bayer" :: "butting" :: "jocose" :: "timbre" :: "Luigi" :: "disobediently" ::
"timelier" :: "emirs" :: "Fomalhaut" :: "triplicated" :: "squandering" ::
"crematoriums" :: "Scotswomen" :: "shame" :: "drunkards" :: "amorously" ::
"pushes" :: "loanword" :: "thanklessly" :: "Punch" :: "learn" ::
"lathered" :: "teats" :: "bucket" :: "careen" :: "mammon" :: "drabness" ::
"insatiable" :: "binocular" :: "Bethlehem" :: "Chartres" :: "solidly" ::
"dachas" :: "tomfooleries" :: "gooseberry" :: "fame" ::
"mispronunciations" :: "sugary" :: "fledgling" :: "prepositions" ::
"Terkel" :: "sedated" :: "quivers" :: "livelier" :: "whitewashing" ::
"limousine" :: "simmers" :: "absurdest" :: "immigrants" :: "unearned" ::
"Sequoya" :: "roughhousing" :: "unsuccessfully" :: "scooter" :: "planters" ::
"Boltzmann" :: "enterprising" :: "rewind" :: "engendering" :: "gashing" ::
"baths" :: "notable" :: "suffusing" :: "Cara" :: "networked" :: "steeply" ::
"beanbag" :: "sourdoughs" :: "sere" :: "raveling" :: "responses" ::
"keepsake" :: "Suharto" :: "incrusts" :: "saturating" :: "Mayas" ::
"impurest" :: "casein" :: "widowhood" :: "sanctified" :: "Jamestown" ::
"segregating" :: "Clifton" :: "annulled" :: "newscasters" :: "yodelled" ::
"connecting" :: "dextrous" :: "gammas" :: "discus" :: "neurologists" ::
"leapfrog" :: "Bernoulli" :: "fishnet" :: "complies" :: "Alisha" ::
"reinserted" :: "verdigrising" :: "Freida" :: "fiddling" :: "fourths" ::
"sky" :: "emailing" :: "alinement" :: "flow" :: "gurney" :: "butcheries" ::
"omelet" :: "typesetters" :: "imminent" :: "habitat" :: "protector" ::
"misprint" :: "impairs" :: "reconsidered" :: "outposts" :: "recriminates" ::
"delimiters" :: "Makarios" :: "shifted" :: "grill" :: "pipits" ::
"hemline" :: "overworked" :: "tinglings" :: "Ndjamena" :: "uppers" ::
"femur" :: "shenanigan" :: "invocation" :: "defilement" ::
"counterbalance" :: "windpipe" :: "Thai" :: "overlie" :: "Haman" ::
"multifaceted" :: "Stefanie" :: "misfortunes" :: "unconsidered" :: "yon" ::
"geographic" :: "outmoded" :: "hemispheric" :: "windfalls" :: "defeatists" ::
"evolving" :: "thank" :: "hardheartedness" :: "brim" :: "heterosexuality" ::
"concoction" :: "mimetic" :: "loyallest" :: "Sheryl" :: "conjuror" ::
"factional" :: "tempest" :: "keenest" :: "chaplaincy" :: "firebombed" ::
"answer" :: "redirecting" :: "Mauritius" :: "tonnage" :: "recognizes" ::
"devastate" :: "cantos" :: "stepfathers" :: "privier" :: "attitudinized" ::
"irregularly" :: "Cindy" :: "callers" :: "recurring" :: "cantaloups" ::
"mingles" :: "pericardium" :: "Muhammad" :: "fatality" :: "telecaster" ::
"Studebaker" :: "unfetters" :: "signpost" :: "stinks" :: "conclaves" ::
"monologue" :: "radioisotopes" :: "prigs" :: "clewing" :: "dean" ::
"resurrections" :: "Coleman" :: "amniocenteses" :: "unlicensed" ::
"perfectionists" :: "mortising" :: "Matilda" :: "Swanee" :: "weep" ::
"regarded" :: "meanly" :: "arroyo" :: "Paula" :: "flatulence" :: "hijacks" ::
"affiliations" :: "handiness" :: "bided" :: "collectors" :: "theorize" ::
"hostage" :: "Carlton" :: "fudged" :: "misinterpreted" :: "reconstructed" ::
"Lincoln" :: "shipwrights" :: "noisome" :: "distends" :: "renounces" ::
"bowlders" :: "whorls" :: "crawlspace" :: "Glaswegian" :: "heater" ::
"chalkboard" :: "stragglers" :: "colleen" :: "waged" :: "jumped" ::
"shambling" :: "clubbing" :: "advice" :: "Tull" :: "crimped" ::
"backhanded" :: "pacesetters" :: "unbuckles" :: "supplicated" ::
"peninsular" :: "cleverer" :: "Kwanzaas" :: "override" :: "diffuse" ::
"ell" :: "punters" :: "carsickness" :: "Maritain" :: "gazes" ::
"congealed" :: "gain" :: "Grotius" :: "tantrum" :: "compunction" ::
"leggin" :: "expounded" :: "commission" :: "squints" :: "recognize" ::
"victors" :: "heterogeneity" :: "edition" :: "tared" :: "restrictive" ::
"equalizing" :: "ceremonious" :: "warts" :: "distills" :: "incurring" ::
"inhalant" :: "dullness" :: "seven" :: "polka" :: "Bessemer" ::
"waterfall" :: "Basra" :: "volcanos" :: "Amoco" :: "sarcomas" :: "dented" ::
"sure" :: "Lieberman" :: "imperils" :: "creeps" :: "gamest" :: "pinkest" ::
"Roseann" :: "indigo" :: "cricked" :: "righteousness" :: "narrow" ::
"aisle" :: "Flores" :: "bumptious" :: "Xiaoping" :: "Harris" :: "Faustino" ::
"retroactively" :: "rejoinders" :: "vastly" :: "sensitization" ::
"liquidating" :: "meekest" :: "Starbucks" :: "sculptures" :: "antigen" ::
"thorougher" :: "Rorschach" :: "resistance" :: "impediment" :: "callipers" ::
"Hamburgs" :: "compassionately" :: "represented" :: "imputed" ::
"invalidates" :: "frippery" :: "rumination" :: "formals" ::
"miniaturizing" :: "narcissists" :: "filigrees" :: "shingle" :: "comes" ::
"guarantied" :: "friendlier" :: "cowhide" :: "groupies" :: "crust" ::
"branched" :: "pizzas" :: "windsurf" :: "nonesuches" :: "rheumatism" ::
"jackets" :: "cooler" :: "finnier" :: "empowering" :: "Sylvie" ::
"trickling" :: "overnight" :: "throats" :: "imagined" :: "springier" ::
"phlebitis" :: "jettisoned" :: "Korean" :: "superabundance" :: "adoringly" ::
"Etna" :: "revenue" :: "Masaryk" :: "munching" :: "cheapening" :: "Sucre" ::
"sabbaticals" :: "mitigate" :: "aficionados" :: "splendid" :: "bulled" ::
"strand" :: "validness" :: "bulking" :: "Chimu" :: "saprophytes" ::
"prognoses" :: "upholds" :: "Karo" :: "casino" :: "vowels" :: "sissiest" ::
"zircon" :: "optimization" :: "happenings" :: "Page" :: "Chuvash" ::
"comforters" :: "rustproofs" :: "discomforts" :: "mood" :: "trumpets" ::
"taxiing" :: "peccaries" :: "freedoms" :: "bucketed" :: "fliers" :: "ems" ::
"clatter" :: "Patrica" :: "stargazer" :: "coughed" :: "perambulates" ::
"tonal" :: "officiously" :: "oddness" :: "substantially" :: "sniffed" ::
"pullet" :: "superabundances" :: "referees" :: "Joann" :: "splendidest" ::
"looked" :: "riff" :: "emanating" :: "dolly" :: "verifying" :: "beverage" ::
"streams" :: "Khomeini" :: "bellying" :: "raining" :: "sades" ::
"carjacks" :: "reforesting" :: "smooths" :: "fetchingly" :: "safe" ::
"Egypt" :: "baleen" :: "ornamental" :: "conglomerates" :: "wetlands" ::
"sluts" :: "Daimler" :: "saunas" :: "lumberman" :: "whistler" ::
"concertinaing" :: "lead" :: "ashram" :: "microfiches" :: "procreates" ::
"nominated" :: "unnecessarily" :: "Bolshevism" :: "scripts" :: "governor" ::
"Englisher" :: "griped" :: "noontime" :: "dense" :: "apprehended" ::
"bolero" :: "flotations" :: "unhesitating" :: "Quakers" :: "affability" ::
"charts" :: "ionizers" :: "nestle" :: "unpick" :: "hided" ::
"undercharges" :: "November" :: "home" :: "reptiles" :: "extrusion" ::
"Jess" :: "quoted" :: "snobs" :: "puffer" :: "snoopers" :: "accouterments" ::
"sometime" :: "jubilantly" :: "off" :: "unproven" :: "undiscriminating" ::
"pretends" :: "legible" :: "squirrels" :: "Os" :: "cultivating" ::
"candidacies" :: "dissociated" :: "banality" :: "chaperoning" :: "bounces" ::
"curtailments" :: "besting" :: "fluffy" :: "trot" :: "glided" :: "maroons" ::
"Riefenstahl" :: "radiotelephones" :: "Ivan" :: "malingered" :: "emigrant" ::
"preacher" :: "seismograph" :: "punctuates" :: "blacklists" ::
"resurfaces" :: "alienable" :: "carbines" :: "rings" :: "thousandth" ::
"salsa" :: "Kurdistan" :: "Elway" :: "posthumous" :: "premises" ::
"fabric" :: "diabetes" :: "critiques" :: "coasts" :: "arbitrators" ::
"cratered" :: "meant" :: "cheerier" :: "towhead" :: "toddled" :: "corneas" ::
"acquirable" :: "attentive" :: "England" :: "gumdrops" :: "scared" ::
"lectures" :: "Scriabin" :: "semicircles" :: "recessives" ::
"anthologists" :: "cripples" :: "reckoned" :: "oafs" :: "keystroke" ::
"recompensing" :: "itchiness" :: "Goff" :: "Maurine" :: "paddle" ::
"barrage" :: "shapelessness" :: "finagling" :: "identity" :: "westerlies" ::
"hobbyists" :: "overproduce" :: "graphed" :: "mechanized" :: "instigator" ::
"privy" :: "incalculably" :: "infrequent" :: "phantasy" :: "generators" ::
"outbuilding" :: "mutual" :: "fluky" :: "budge" :: "agglomerate" ::
"mashed" :: "decries" :: "toils" :: "Murchison" :: "vanished" ::
"babysits" :: "battens" :: "Mavis" :: "overs" :: "impotence" :: "slinking" ::
"mintier" :: "wilfulness" :: "heartwarming" :: "Eugenie" :: "upstaged" ::
"jaunts" :: "roof" :: "gigantic" :: "exuded" :: "rampart" :: "Gail" ::
"spanks" :: "granulating" :: "orientate" :: "unbolted" :: "ski" ::
"troubleshoot" :: "languorous" :: "abstention" :: "urbanity" :: "gerbil" ::
"canceled" :: "entwining" :: "bicycle" :: "farted" :: "humanized" ::
"speedways" :: "shotgunning" :: "settlements" :: "Kr" :: "deferring" ::
"conditionals" :: "miles" :: "dawdles" :: "gangs" :: "seconding" ::
"landfill" :: "defoliated" :: "dancer" :: "viva" :: "Springfield" ::
"thrifts" :: "disorder" :: "yucca" :: "Calderon" :: "cosmetically" ::
"uninterested" :: "sward" :: "tenet" :: "fishbowls" :: "soloist" ::
"usurer" :: "invigoration" :: "humps" :: "acclaims" :: "making" ::
"probate" :: "revery" :: "prosy" :: "Lara" :: "thrasher" :: "loins" ::
"appertain" :: "Taurus" :: "Halley" :: "prestigious" :: "inhalations" ::
"foreman" :: "vector" :: "empathetic" :: "reflected" :: "realign" ::
"thorax" :: "buccaneers" :: "bonny" :: "Avicenna" :: "hindrance" ::
"positions" :: "contented" :: "jugglers" :: "exhibitors" :: "limits" ::
"telemarketing" :: "acorn" :: "particulates" :: "cooties" :: "subsoil" ::
"stoutness" :: "midwived" :: "dropsy" :: "enfranchisement" :: "unpainted" ::
"retraced" :: "GTE" :: "Viola" :: "curtsied" :: "ridiculously" ::
"contests" :: "available" :: "Rhodes" :: "feud" :: "imprisoning" ::
"compliment" :: "somethings" :: "stirrers" :: "forswears" :: "tacky" ::
"Celtic" :: "iconoclast" :: "deflecting" :: "slung" :: "alliterative" ::
"loop" :: "iPad" :: "solecism" :: "unconsciously" :: "daintily" ::
"diminuendoes" :: "shepherding" :: "walkouts" :: "toning" :: "clarinetist" ::
"fragmented" :: "withers" :: "outwore" :: "Demerol" :: "madwoman" ::
"Belgium" :: "shirker" :: "internal" :: "corresponded" :: "prefixes" ::
"hayseeds" :: "unfailing" :: "Alamogordo" :: "guardian" :: "truant" ::
"Beach" :: "cozens" :: "Lamar" :: "confessed" :: "give" :: "afford" ::
"anonymous" :: "squandered" :: "quasi" :: "officers" :: "drivel" ::
"masterfully" :: "mosaics" :: "behaved" :: "blandly" :: "Nickelodeon" ::
"boleros" :: "hardware" :: "textural" :: "Kenny" :: "Poseidon" ::
"treasonable" :: "insupportable" :: "Genaro" :: "virgules" :: "swearer" ::
"mutilations" :: "relocation" :: "popularizes" :: "pug" :: "fixtures" ::
"swishing" :: "manservant" :: "macro" :: "backfields" :: "detail" ::
"brisks" :: "citadel" :: "coffining" :: "callipered" :: "merinos" ::
"coolness" :: "leasehold" :: "malignancy" :: "melanoma" :: "employing" ::
"coyote" :: "dumbwaiters" :: "cardinals" :: "facilities" :: "awaits" ::
"venison" :: "Babylons" :: "rainier" :: "elasticity" :: "sacs" ::
"multiplexors" :: "eggbeaters" :: "irrelevances" :: "Felicity" :: "gabled" ::
"wiretapped" :: "chronicler" :: "remorseful" :: "vamping" :: "sachem" ::
"Burton" :: "enact" :: "wattage" :: "unruliest" :: "prerecords" ::
"calculuses" :: "doubtlessly" :: "snuggle" :: "casework" :: "kaftans" ::
"Gog" :: "gunners" :: "evolved" :: "Yangon" :: "misspelling" :: "fishwife" ::
"hedges" :: "ungrammatical" :: "shatters" :: "pioneers" :: "Fez" ::
"lifeblood" :: "quieted" :: "Pei" :: "godliness" :: "ravened" ::
"squeezing" :: "banishing" :: "finalizing" :: "steams" :: "dreariest" ::
"inconsequentially" :: "blockading" :: "llama" :: "sandiness" ::
"ramification" :: "Proserpine" :: "reapportioned" :: "archaeologist" ::
"yesteryear" :: "Listerine" :: "administrated" :: "Haldane" ::
"alphabetize" :: "disenfranchised" :: "status" :: "embrace" :: "Reuben" ::
"trendier" :: "disgorges" :: "barbell" :: "regimented" :: "embroiled" ::
"espies" :: "sexually" :: "cherry" :: "intermezzos" :: "physiognomies" ::
"podiatrist" :: "Judson" :: "foliage" :: "exposing" :: "druids" ::
"Tasman" :: "infallibly" :: "Melinda" :: "Romanian" :: "crusading" ::
"humanoids" :: "clappers" :: "turtledove" :: "skinnier" :: "talked" ::
"zanier" :: "heterogeneous" :: "lymphoma" :: "guiltiness" :: "Soviet" ::
"Myrtle" :: "flagella" :: "insecurity" :: "workplaces" :: "lamebrain" ::
"cymbals" :: "avionics" :: "recalled" :: "Liverpool" :: "slipping" ::
"McCoy" :: "imbroglios" :: "chorister" :: "parents" :: "feebly" ::
"uprisings" :: "respite" :: "foldaway" :: "talons" :: "lexicographers" ::
"clover" :: "fiesta" :: "scamper" :: "prepossessing" :: "patterned" ::
"Wednesdays" :: "disdainfully" :: "pillaging" :: "parleying" :: "messes" ::
"precipitously" :: "Unilever" :: "suds" :: "airwaves" :: "fiver" ::
"accessed" :: "goiter" :: "vanity" :: "enrolled" :: "primers" ::
"Richmond" :: "caesurae" :: "spiraea" :: "underselling" :: "kidnappings" ::
"outgrowing" :: "betrothing" :: "iced" :: "lechers" :: "allusively" ::
"mimicries" :: "Lobachevsky" :: "Jaime" :: "Rosalie" :: "Kewpie" :: "offs" ::
"hobos" :: "injections" :: "carpi" :: "groom" :: "flushing" ::
"revolution" :: "Irrawaddy" :: "gangrenous" :: "channeled" :: "fiber" ::
"chimeras" :: "ditch" :: "lifeforms" :: "actualizing" :: "Spencer" ::
"heartaches" :: "Rachel" :: "reinstating" :: "gunsmith" :: "cucumbers" ::
"outcropping" :: "slide" :: "cardsharp" :: "declension" :: "Suez" ::
"Maillol" :: "postgraduate" :: "turbulence" :: "maledictions" ::
"unclasping" :: "Taichung" :: "Agni" :: "trigger" :: "Aaliyah" ::
"bounden" :: "medically" :: "Jeroboam" :: "Elliott" :: "comedown" ::
"Gnosticism" :: "wilful" :: "pester" :: "L" :: "imputation" :: "humbugs" ::
"alleged" :: "baron" :: "tangy" :: "preponderances" :: "sacrifices" ::
"sweaty" :: "sunbathe" :: "politicians" :: "abortionist" :: "constricts" ::
"unstopping" :: "elaborateness" :: "scam" :: "unsheathed" :: "sonny" ::
"jolts" :: "zeros" :: "belief" :: "redwood" :: "ceramic" :: "hangings" ::
"Maori" :: "barrel" :: "Atlases" :: "caterwauling" :: "Farragut" ::
"harrying" :: "sanserif" :: "Tracy" :: "bloodmobiles" :: "border" ::
"constrictor" :: "lie" :: "Midway" :: "podding" :: "potpies" :: "mauve" ::
"farina" :: "outfoxed" :: "transepts" :: "hair" :: "staying" :: "witless" ::
"Polish" :: "patrolled" :: "rover" :: "seem" :: "unkinder" :: "Muslims" ::
"dejected" :: "Conway" :: "accorded" :: "lighter" :: "masturbate" ::
"grandparents" :: "mystique" :: "bootleg" :: "migrating" :: "Brice" ::
"coauthors" :: "scoreboards" :: "matchsticks" :: "jotted" :: "dogfight" ::
"industries" :: "Orion" :: "vacant" :: "merchandises" :: "Assisi" ::
"globetrotters" :: "intergalactic" :: "censoring" :: "watchwords" ::
"archipelago" :: "portrayed" :: "jeered" :: "tonality" :: "untimely" ::
"nominating" :: "albinos" :: "snarl" :: "mongering" :: "kilowatts" ::
"Cousteau" :: "grunted" :: "collectivizing" :: "earlobes" ::
"transliterations" :: "isolation" :: "greases" :: "fairest" :: "essential" ::
"chimera" :: "otters" :: "organists" :: "Malraux" :: "promulgating" ::
"appraiser" :: "revoke" :: "Vanessa" :: "hived" :: "Hildebrand" ::
"unanswered" :: "sidesaddle" :: "universes" :: "trillions" :: "rattiest" ::
"podiatry" :: "spelt" :: "Christendom" :: "peddling" :: "bushel" ::
"idiosyncrasies" :: "deb" :: "Senior" :: "viability" :: "bulldozed" ::
"prognosticate" :: "spindles" :: "laughingstocks" :: "gatecrashers" ::
"Xmases" :: "laborers" :: "attest" :: "Hank" :: "shelves" :: "browses" ::
"husked" :: "detaching" :: "edifices" :: "swellheaded" :: "persist" ::
"Larson" :: "archaeological" :: "convalescing" :: "Tuesday" :: "barbering" ::
"redevelopment" :: "unaccepted" :: "exalting" :: "doweling" :: "railways" ::
"Oersted" :: "pedicuring" :: "punctuated" :: "sleet" :: "ninetieth" ::
"semiautomatic" :: "sprucest" :: "fir" :: "possesses" :: "brr" ::
"cunningest" :: "interposed" :: "standbys" :: "autopsy" :: "geezers" ::
"jibbed" :: "actuality" :: "Jedi" :: "anchorpersons" :: "suspiciously" ::
"decongestant" :: "ancillaries" :: "tramp" :: "pukes" :: "piebald" ::
"silicon" :: "radiations" :: "apple" :: "microorganisms" :: "fryers" ::
"wineglasses" :: "fullbacks" :: "testates" :: "lotion" :: "Latvian" ::
"spryly" :: "shaded" :: "hand" :: "coconut" :: "leaked" :: "funicular" ::
"Petrarch" :: "aggrandized" :: "gagging" :: "quantities" :: "Thomistic" ::
"androgynous" :: "Pliny" :: "dedicate" :: "reinterpretations" ::
"figurative" :: "toggled" :: "rumored" :: "missing" :: "Thrace" ::
"eccentricities" :: "overproduction" :: "procurers" :: "Kirinyaga" ::
"finagle" :: "endeavors" :: "repayable" :: "jaunt" :: "pubescence" ::
"backless" :: "ornament" :: "stifling" :: "Asia" :: "Lewinsky" ::
"hypersensitivities" :: "caucussed" :: "Leach" :: "Cain" :: "homeroom" ::
"grateful" :: "Frankel" :: "provost" :: "measureless" :: "pastiches" ::
"Maoisms" :: "rowdiest" :: "silver" :: "Lockwood" :: "ramps" ::
"ghastliest" :: "clerk" :: "entreat" :: "constriction" :: "biochemist" ::
"befriend" :: "truth" :: "childless" :: "pleasuring" :: "unjustified" ::
"stunts" :: "penetrable" :: "phased" :: "positivism" :: "Congo" :: "sirup" ::
"ensconces" :: "patrolwoman" :: "woodcutting" :: "designer" :: "Esther" ::
"stunning" :: "coordinates" :: "appreciative" :: "interscholastic" ::
"popgun" :: "haughty" :: "Sawyer" :: "emptier" :: "ripen" :: "brushing" ::
"Jacqueline" :: "Ecuadoran" :: "fluoridated" :: "descendant" ::
"equalling" :: "snowflake" :: "divvies" :: "concerning" :: "squirm" ::
"antiseptically" :: "jangling" :: "poulticing" :: "inflation" ::
"profligate" :: "confessedly" :: "pyramiding" :: "ethnologist" ::
"jousting" :: "lithographing" :: "headdress" :: "universals" :: "mollusks" ::
"grommets" :: "nuances" :: "littered" :: "nits" :: "prostituting" ::
"circumscription" :: "Xenakis" :: "pharmacologist" :: "tankfuls" ::
"guineas" :: "arming" :: "tells" :: "inclusively" :: "unwilling" ::
"Guillermo" :: "mumps" :: "programmables" :: "brakemen" :: "awkwarder" ::
"marvelling" :: "twinning" :: "resubmitting" :: "unloading" :: "falconer" ::
"bedpans" :: "doomed" :: "inseparability" :: "Waite" :: "croquette" ::
"vegetation" :: "overreached" :: "joist" :: "humanoid" :: "nihilists" ::
"flutist" :: "catalogue" :: "enthralls" :: "trebles" :: "hillier" ::
"unionizes" :: "knotholes" :: "twists" :: "covering" :: "scrubber" ::
"Surinam" :: "predispositions" :: "Aztecan" :: "hawking" :: "Domitian" ::
"hurriedly" :: "retooling" :: "carburetor" :: "Blockbuster" :: "resettled" ::
"scathingly" :: "vogue" :: "gamier" :: "verandah" :: "standout" ::
"disarmed" :: "spatially" :: "carnivorous" :: "deforest" :: "cushioned" ::
"indulging" :: "calories" :: "Hun" :: "Geronimo" :: "storks" :: "fob" ::
"disorientation" :: "stifle" :: "retailed" :: "Snead" :: "our" ::
"palmiest" :: "Wuhan" :: "cavorting" :: "backfiring" :: "underprivileged" ::
"Koran" :: "Bach" :: "guilty" :: "paramecium" :: "fiestas" :: "commissary" ::
"gaseous" :: "figures" :: "slightly" :: "Whiteley" :: "defeat" ::
"parrots" :: "Casals" :: "musicologists" :: "shootouts" :: "sally" ::
"flyweight" :: "receipted" :: "rhymed" :: "jittery" :: "Odyssey" ::
"sundown" :: "winged" :: "honeysuckles" :: "gnarlier" :: "sweetbriars" ::
"enthrones" :: "kamikaze" :: "swilled" :: "postponed" :: "cotter" ::
"courage" :: "adolescence" :: "clarioned" :: "tendinitis" :: "scheme" ::
"secrets" :: "funkiest" :: "copyrighted" :: "Bert" :: "podium" ::
"preserver" :: "begin" :: "birdcage" :: "abounded" :: "Bulganin" ::
"erupt" :: "equivocates" :: "personable" :: "bop" :: "cloakroom" ::
nil.

Definition poswords :=
  Eval vm_compute in List.map pos_of_string words.

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.

Extraction "benchmark/benchmark.ml"
  TestOriginal TestCanonical TestSigma TestNode01 TestGADT TestPatricia
  TestAVLString TestRBString TestAVLPositive TestRBPositive TestCharTrie
  TestOriginalAsStringmap TestCanonicalAsStringmap TestPatriciaAsStringmap
  words poswords smallnumbers.
