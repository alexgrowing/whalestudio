import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.A6supp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Et

structure SlopeTestRemainingChoices : Prop where
  sheaf : type_of% @GlobalTheory.T.etaleSheafSections_ext_and_glue
  resol : type_of% @GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness
  freeS : type_of% @GlobalTheory.T.free_sections_ext_res_map
  evs : type_of% @GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties
  rep : type_of% @GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff
  sec : type_of% @GlobalTheory.T.degreeZeroSectionClass_properties
  aw : type_of% @GlobalTheory.T.cup_eq_class_of_isAW
  twist : type_of% @GlobalTheory.T.tateTwist_sections_locally_generated
  pair : type_of% @GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique
  unit : type_of% @GlobalTheory.T.tateTwistUnitClass_rootClass_spec

section Site
variable {C : Type 1} [Category.{0} C] {S : Type 1} [CommRing S]

abbrev PM (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] : Type 2 := Cᵒᵖ ⥤ ModuleCat.{1} S

abbrev pmAp {F G : PM C S} (φ : F ⟶ G) {U : C} (x : F.obj (op U)) : G.obj (op U) := (φ.app (op U)).hom x

abbrev pmRs {F : PM C S} {V U : C} (g : V ⟶ U) (x : F.obj (op U)) : F.obj (op V) := (F.map g.op).hom x

def LocG (J : GrothendieckTopology C) (U : C) (P : ∀ V : C, (V ⟶ U) → Prop) : Prop :=
  ∃ T : Presieve U, Sieve.generate T ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), T g → P V g

def InjSh (J : GrothendieckTopology C) (F : PM C S) : Prop := Injective F ∧ Presheaf.IsSheaf J F

def piP {ι : Type} (F : ι → PM C S) : PM C S where
  obj U := ModuleCat.of S (∀ b, (F b).obj U)
  map f := ModuleCat.ofHom (LinearMap.pi fun b => ((F b).map f).hom ∘ₗ LinearMap.proj b)
  map_id U := by ext x b; simp
  map_comp f g := by ext x b; simp

structure Dat (C : Type 1) [Category.{0} C] (S : Type 1) [CommRing S] (ι : Type) where
  P : ι → ℤ → PM C S
  dP : ∀ b s t, P b s ⟶ P b t
  Q : ℤ → PM C S
  dQ : ∀ s t, Q s ⟶ Q t
  e : ι → ℤ
  φ : ∀ b s, P b (s - e b) ⟶ Q s
  ddP : ∀ b s t u, dP b s t ≫ dP b t u = 0
  ddQ : ∀ s t u, dQ s t ≫ dQ t u = 0
  comm : ∀ b s t, s + 1 = t → φ b s ≫ dQ s t = dP b (s - e b) (t - e b) ≫ φ b t

variable {ι : Type} [Fintype ι] (D : Dat C S ι)

def Dat.sm {U : C} (s : ℤ) (a : ∀ b, (D.P b (s - D.e b)).obj (op U)) : (D.Q s).obj (op U) := ∑ b, pmAp (D.φ b s) (a b)

def Dat.Hit {V : C} (s : ℤ) (y : (D.Q s).obj (op V)) : Prop :=
  ∃ (a : ∀ b, (D.P b (s - D.e b)).obj (op V)) (y' : (D.Q (s - 1)).obj (op V)),
    (∀ b, pmAp (D.dP b (s - D.e b) (s + 1 - D.e b)) (a b) = 0) ∧ y = D.sm s a + pmAp (D.dQ (s - 1) s) y'

def Dat.Dies {V : C} (s : ℤ) (a : ∀ b, (D.P b (s - D.e b)).obj (op V)) : Prop :=
  ∀ b, ∃ a' : (D.P b (s - 1 - D.e b)).obj (op V), pmAp (D.dP b (s - 1 - D.e b) (s - D.e b)) a' = a b

def Dat.Ker {V : C} (s : ℤ) (a : ∀ b, (D.P b (s - D.e b)).obj (op V)) : Prop :=
  (∀ b, pmAp (D.dP b (s - D.e b) (s + 1 - D.e b)) (a b) = 0) ∧ ∃ y' : (D.Q (s - 1)).obj (op V), D.sm s a = pmAp (D.dQ (s - 1) s) y'

def Dat.LSurj (J : GrothendieckTopology C) (s : ℤ) : Prop :=
  ∀ (U : C) (y : (D.Q s).obj (op U)), pmAp (D.dQ s (s + 1)) y = 0 → LocG J U fun _ g => D.Hit s (pmRs g y)

def Dat.LInj (J : GrothendieckTopology C) (s : ℤ) : Prop :=
  ∀ (U : C) (a : ∀ b, (D.P b (s - D.e b)).obj (op U)), D.Ker s a → LocG J U fun _ g => D.Dies s fun b => pmRs g (a b)

def Dat.GSurj (s : ℤ) : Prop := ∀ (U : C) (y : (D.Q s).obj (op U)), pmAp (D.dQ s (s + 1)) y = 0 → D.Hit s y

def Dat.GInj (s : ℤ) : Prop := ∀ (U : C) (a : ∀ b, (D.P b (s - D.e b)).obj (op U)), D.Ker s a → D.Dies s a

end Site

def PtLoc (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∀ u : U, ∃ (V : Scheme.{0}) (g : V ⟶ U), Etale g ∧ u ∈ Set.range g ∧ P V g

section Rep
variable {R : Type} [CommRing R]

def Rep {I : Cx R} {U : Scheme.{0}} {n : ℤ} (z : Sec (I.X n) U) (c : CohomologyClass ((chains R).obj (sch.obj U)) I n) : Prop :=
  ∃ α : Cocycle ((chains R).obj (sch.obj U)) I n, CohomologyClass.mk α = c ∧ ev α.1 0 n (by simp) U (𝟙 U) = z

def SecCont (K : Cx R) {I : Type} [SmallCategory I] {G : I ⥤ Scheme.{0}} (c : Cone G) : Prop :=
  ∀ m n k : ℤ, m + 1 = n → n + 1 = k →
    (∀ z : Sec (K.X n) c.pt, Sec.map (K.d n k) z = 0 → ∃ (i : I) (a : Sec (K.X n) (G.obj i)) (y : Sec (K.X m) c.pt),
      Sec.map (K.d n k) a = 0 ∧ Sec.res (c.π.app i) a = z + Sec.map (K.d m n) y) ∧
    ∀ (i : I) (a : Sec (K.X n) (G.obj i)), Sec.map (K.d n k) a = 0 →
      (∃ y : Sec (K.X m) c.pt, Sec.res (c.π.app i) a = Sec.map (K.d m n) y) →
      ∃ (j : I) (f : j ⟶ i) (b : Sec (K.X m) (G.obj j)), Sec.map (K.d m n) b = Sec.res (G.map f) a

def MVsq (F : Shv R) {W A B Z : Scheme.{0}} (a : W ⟶ A) (b : W ⟶ B) (f : A ⟶ Z) (g : B ⟶ Z) : Prop :=
  a ≫ f = b ≫ g ∧ (∀ z : Sec F Z, Sec.res f z = 0 → Sec.res g z = 0 → z = 0) ∧
  (∀ (x : Sec F A) (y : Sec F B), Sec.res a x = Sec.res b y → ∃ z : Sec F Z, Sec.res f z = x ∧ Sec.res g z = y) ∧
  ∀ w : Sec F W, ∃ (x : Sec F A) (y : Sec F B), w = Sec.res a x - Sec.res b y

variable {S Y : Scheme.{0}} (p' : Y ⟶ S)

def bm {U V : Scheme.{0}} {u : U ⟶ S} {v : V ⟶ S} (g : V ⟶ U) (h : g ≫ u = v) : pullback v p' ⟶ pullback u p' :=
  ((Over.pullback p').map (Over.homMk g h : Over.mk v ⟶ Over.mk u)).left

@[reassoc (attr := simp)]
theorem bm_fst {U V : Scheme.{0}} {u : U ⟶ S} {v : V ⟶ S} (g : V ⟶ U) (h : g ≫ u = v) :
    bm p' g h ≫ pullback.fst u p' = pullback.fst v p' ≫ g := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem bm_snd {U V : Scheme.{0}} {u : U ⟶ S} {v : V ⟶ S} (g : V ⟶ U) (h : g ≫ u = v) :
    bm p' g h ≫ pullback.snd u p' = pullback.snd v p' := pullback.lift_snd _ _ _

abbrev onS (S : Scheme.{0}) (F : Shv R) : PM (Over S) (ULift.{1} R) := (Over.forget S).op ⋙ F.obj

abbrev onY (F : Shv R) : PM (Over S) (ULift.{1} R) := (Over.pullback p' ⋙ Over.forget Y).op ⋙ F.obj

def mulZ {I J K : Cx R} (μ : Pair I J K) {r e s : ℤ} (h : r + e = s) (z : Sec (J.X e) Y) : onS S (I.X r) ⟶ onY p' (K.X s) where
  app U := ModuleCat.ofHom ((μ.mul (pullback U.unop.hom p') r e s h).flip (Sec.res (pullback.snd U.unop.hom p') z) ∘ₗ
    ((I.X r).obj.map (pullback.fst U.unop.hom p').op).hom)
  naturality U V f := by
    ext a
    have h1 : ((Over.pullback p').map f.unop).left ≫ pullback.fst U.unop.hom p' = pullback.fst V.unop.hom p' ≫ f.unop.left := pullback.lift_fst _ _ _
    have h2 : ((Over.pullback p').map f.unop).left ≫ pullback.snd U.unop.hom p' = pullback.snd V.unop.hom p' := pullback.lift_snd _ _ _
    have hn := μ.nat ((Over.pullback p').map f.unop).left r e s h (Sec.res (pullback.fst U.unop.hom p') a) (Sec.res (pullback.snd U.unop.hom p') z)
    have e1 : ∀ {F : Shv R} {A B E : Scheme.{0}} (k : A ⟶ B) (l : B ⟶ E) (x : Sec F E), Sec.res k (Sec.res l x) = Sec.res (k ≫ l) x := by
      intro F A B E k l x
      simp [Sec.res]
    erw [e1, e1, h1, h2, ← e1] at hn
    exact hn.symm

def kdat {I J K : Cx R} (μ : Pair I J K) {ι : Type} (e : ι → ℤ) (z : ∀ b, Sec (J.X (e b)) Y)
    (hz : ∀ b, Sec.map (J.d (e b) (e b + 1)) (z b) = 0) : Dat (Over S) (ULift.{1} R) ι where
  P _ s := onS S (I.X s)
  dP _ s t := Functor.whiskerLeft _ (I.d s t).hom
  Q s := onY p' (K.X s)
  dQ s t := Functor.whiskerLeft _ (K.d s t).hom
  e := e
  φ b s := mulZ p' μ (sub_add_cancel s (e b)) (z b)
  ddP _ s t u := by
    rw [← Functor.whiskerLeft_comp]
    have : (I.d s t).hom ≫ (I.d t u).hom = 0 := congrArg (fun f => f.hom) (I.d_comp_d s t u)
    rw [this]; rfl
  ddQ s t u := by
    rw [← Functor.whiskerLeft_comp]
    have : (K.d s t).hom ≫ (K.d t u).hom = 0 := congrArg (fun f => f.hom) (K.d_comp_d s t u)
    rw [this]; rfl
  comm b s t h := by
    subst h
    ext U a
    have hl := μ.leibniz (pullback U.unop.hom p') (s - e b) (e b) s (sub_add_cancel s (e b))
      (Sec.res (pullback.fst U.unop.hom p') a) (Sec.res (pullback.snd U.unop.hom p') (z b))
    have e2 : ∀ {F G : Shv R} (φ : F ⟶ G) {A B : Scheme.{0}} (k : A ⟶ B) (x : Sec F B), Sec.map φ (Sec.res k x) = Sec.res k (Sec.map φ x) := by
      intro F G φ A B k x
      exact ConcreteCategory.congr_hom (φ.hom.naturality k.op) x
    have e3 : ∀ (t : ℤ) (ht : s - e b + 1 = t) (x : Sec (I.X (s - e b)) (pullback U.unop.hom p')) y,
        μ.mul _ (s - e b + 1) (e b) (s + 1) (by omega) (Sec.map (I.d _ _) x) y = μ.mul _ t (e b) (s + 1) (by omega) (Sec.map (I.d _ t) x) y := by
      intro t ht x y; subst ht; rfl
    have e4 : Sec.res (pullback.snd U.unop.hom p') (0 : Sec (J.X (e b + 1)) Y) = 0 := map_zero _
    rw [e2 (J.d _ _), hz, e4, map_zero, smul_zero, add_zero, e3 (s + 1 - e b) (by omega)] at hl
    erw [e2 (I.d _ _)] at hl
    exact hl

end Rep

section Classes
variable (q : ℕ) {S Y : Scheme.{0}} (p' : Y ⟶ S) {ι : Type} [Fintype ι] {e : ι → ℤ} {j : ℤ} (w : ∀ b, Ht q (sch.obj Y) (e b) j)

def kmap {X : Scheme.{0}} (p : X ⟶ S) (n i : ℤ) (x : ∀ b, Ht q (sch.obj X) (n - e b) i) : Ht q (sch.obj (pullback p p')) n (i + j) :=
  ∑ b, (cup q (pull _ (sch.map (pullback.fst p p')) _ _ (x b)) (pull _ (sch.map (pullback.snd p p')) _ _ (w b))).cast (sub_add_cancel n (e b)) rfl

def comb (s : ℤ) (c : ι → ℕ) : Ht q (sch.obj Y) s j := ∑ b, if h : e b = s then c b • (w b).cast h rfl else 0

def IsBasisTo (N : ℤ) : Prop :=
  (∀ (s : ℤ) (c : ι → ℕ), comb q w s c = 0 → ∀ b, e b = s → q ∣ c b) ∧ ∀ s ≤ N, ∀ y : Ht q (sch.obj Y) s j, ∃ c, comb q w s c = y

def genFam {X : Scheme.{0}} {i : ℤ} (e : ι → ℤ) (g : Ht q (sch.obj X) 0 i) (s : ℤ) (c : ι → ℕ) (b : ι) : Ht q (sch.obj X) (s - e b) i :=
  if h : e b = s then c b • g.cast (by omega) rfl else 0

def KLSurj (s i : ℤ) : Prop := ∀ (U : Scheme.{0}) (u : U ⟶ S) (y : Ht q (sch.obj (pullback u p')) s (i + j)),
  PtLoc U fun _ g => ∃ x, kmap q p' w (g ≫ u) s i x = pull _ (sch.map (bm p' g rfl)) _ _ y

def KLInj (s i : ℤ) : Prop := ∀ (U : Scheme.{0}) (u : U ⟶ S) (x : ∀ b, Ht q (sch.obj U) (s - e b) i), kmap q p' w u s i x = 0 →
  PtLoc U fun _ g => ∀ b, pull _ (sch.map g) _ _ (x b) = 0

end Classes

abbrev spA (k A : Type) [CommRing k] [CommRing A] [Algebra k A] : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k A))

def LH : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {Y : Scheme.{0}} (p' : Y ⟶ Spec (CommRingCat.of k)) [IsProper p'] {ι : Type} [Fintype ι] {e : ι → ℤ} {j : ℤ}
    (w : ∀ b, Ht q (sch.obj Y) (e b) j) (N : ℤ), IsBasisTo q w N →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (n i : ℤ), n ≤ N → Function.Bijective (kmap q p' w p n i)

def SHex : Prop := ∀ (A : Type) [CommRing A] (𝔭 : PrimeSpectrum A), ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (c : Cocone D) (_ : IsColimit c),
  (∀ j, (s.app j).hom.Etale) ∧ SH c.pt ∧ ∀ j, ∃ P : PrimeSpectrum (D.obj j), P.asIdeal.comap (s.app j).hom = 𝔭.asIdeal

end UpperTheory.Et

end
