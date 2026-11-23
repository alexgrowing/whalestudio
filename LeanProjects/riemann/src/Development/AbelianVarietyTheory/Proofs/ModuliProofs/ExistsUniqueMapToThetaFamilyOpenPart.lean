import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemRangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasThStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsSatisfyClosureEquationsOfDenseClasStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.UnivProp

set_option backward.isDefEq.respectTransparency false

variable {o : Type} [CommRing o] {g n N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}

theorem span_eq_top_of_coset {R : Type} [CommRing R] {v : Ix g (N' ^ 2) → R}
    (h : ∀ q : Ideal R, q.IsPrime → Coset n N' v q) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨c, hc⟩ := h m hm.isPrime 0
  exact hc (hle (Ideal.subset_span ⟨_, rfl⟩))

theorem pt_eq_of_secCoord {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)} (Y : MMPre n N' I) {R : Type} [CommRing R]
    {x x' : Sp R ⟶ Y.MM} {v : Ix g (N' ^ 2) → R} (e : x ≫ Y.s = x' ≫ Y.s) (h : SecCoord Y.de Y.th x v)
    (h' : SecCoord Y.de Y.th x' v) : x = x' := by
  obtain ⟨β, hβ⟩ := exists_spMap (x ≫ Y.s)
  exact (Y.pts R β v (Y.loc R β x v hβ h)).unique ⟨hβ, h⟩ ⟨e.symm.trans hβ, h'⟩

theorem exists_thetaMap (hL : Out.Laws) (hL2 : Out.Laws2) (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N') {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} (Y : MMPre n N' (thIdeal em C)) {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (hS : IsReduced S) (hD : Dense (fromSet em C t)) :
    ∃ f : S ⟶ Y.MM, f ≫ Y.s = s ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ S),
      ∃ v, t.HasTh y v ∧ SecCoord Y.de Y.th (y ≫ f) v := by
  classical
  have hloc := fun p : S => GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g N' J b S s t ho p
  choose R hR x v hx hp hth using hloc
  have hβ' : ∀ p, ∃ β : o →+* R p, x p ≫ s = spMap β := fun p => exists_spMap (x p ≫ s)
  choose β hβ using hβ'
  have hin : ∀ p, InMM n N' (thIdeal em C) (β p) (v p) := fun p =>
    GlobalTheory.T.thetaConstants_satisfy_closure_equations_of_dense_class hL hL2 o g n N' J b em C S s t (R p) (β p) (x p) (v p) hn hd ho hS hD (hx p) (hβ p) (hth p)
  have hpt : ∀ p, ∃ y : Sp (R p) ⟶ Y.MM, y ≫ Y.s = spMap (β p) ∧ SecCoord Y.de Y.th y (v p) :=
    fun p => (Y.pts (R p) (β p) (v p) (hin p)).exists
  choose f hf using hpt
  obtain ⟨F, hF⟩ := exists_glue (fun p => Sp (R p)) x hx (fun p => ⟨p, hp p⟩) f (by
    intro i j T _ z z' hz
    obtain ⟨φ, rfl⟩ := exists_spMap z
    obtain ⟨φ', rfl⟩ := exists_spMap z'
    have h1 := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t (R i) T φ (x i) (v i) (hth i)
    have h2 := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t (R j) T φ' (x j) (v j) (hth j)
    rw [hz] at h1
    have hsp : Ideal.span (Set.range fun a => φ (v i a)) = ⊤ :=
      span_eq_top_of_coset (n := n) fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n T _ _ q hn hd h1 hq
    obtain ⟨u, hu⟩ := GlobalTheory.hasTh_unique_unit hL hL2 o g N' J b S s t T _ _ _ h1 h2 hsp
    have c1 : SecCoord Y.de Y.th (spMap φ ≫ f i) fun a => φ' (v j a) := by
      have e : (fun a => φ' (v j a)) = fun a => (u : T) * φ (v i a) := funext fun a => hu a
      rw [e]
      exact GlobalTheory.ZM.Coord.scale (GlobalTheory.ZM.Coord.baseChange (hf i).2 φ) u
    have c2 := GlobalTheory.ZM.Coord.baseChange (hf j).2 φ'
    refine pt_eq_of_secCoord Y ?_ c1 c2
    have e := congrArg (· ≫ s) hz
    simp only [Category.assoc, hβ] at e
    simp only [Category.assoc, (hf i).1, (hf j).1]
    exact e)
  refine ⟨F, ?_, ?_⟩
  · refine hom_ext_affine _ _ fun p => ⟨Sp (R p), x p, hx p, hp p, ?_⟩
    rw [← Category.assoc, hF p, (hf p).1, hβ p]
  · intro K _ y
    obtain ⟨p, hyp⟩ : ∃ p, p ∈ Set.range y := ⟨_, IsLocalRing.closedPoint K, rfl⟩
    have := hx p
    obtain ⟨z, hz⟩ := exists_lift_field (x p) y hyp (hp p)
    obtain ⟨φ, rfl⟩ := exists_spMap z
    subst hz
    refine ⟨fun a => φ (v p a), ?_, ?_⟩
    · exact GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t (R p) K φ (x p) (v p) (hth p)
    · rw [Category.assoc, hF]
      exact GlobalTheory.ZM.Coord.baseChange (hf p).2 φ

private theorem exists_tObj_transport_of_eq {o₁ : Type} [CommRing o₁] {g₁ k₁ : ℕ} {J₁ : Type} {b₁ : TBase o₁ k₁}
    {S₁ : Scheme.{0}} {s₁ s₂ : S₁ ⟶ Sp o₁} (h : s₁ = s₂) (u : TObj g₁ k₁ J₁ b₁ s₁) :
    ∃ u' : TObj g₁ k₁ J₁ b₁ s₂, ∀ P : ∀ s : S₁ ⟶ Sp o₁, TObj g₁ k₁ J₁ b₁ s → Prop, P s₁ u → P s₂ u' := by
  subst h
  exact ⟨u, fun _ hP => hP⟩

theorem existsUnique_map_of_wFam : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (F : WFam n em C Mat κ) (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → t.FibShape Mat κ → ∃! f : S ⟶ F.U.toScheme, f ≫ F.U.ι ≫ F.Y.s = s' ∧ TMap t F.univ f := by
  intro hL hL2 g J _ Mat κ n w w' hnp hno
  refine ⟨2, fun j hj o _ b em C d _ _ F S s' t hS hD hFib => ?_⟩
  have hn : 2 ≤ n := hnp.two_le
  have hd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hd2 : n ^ 2 ∣ n ^ j := pow_dvd_pow n hj
  have ho : Odd (n ^ j) := hno.pow
  obtain ⟨f0, hf0s, hf0⟩ := exists_thetaMap hL hL2 hn hd ho F.Y t hS hD
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (u : TObj g ((n ^ j) ^ 2) J b (y ≫ s')),
      TMap u t y → ∃ x' : Sp K ⟶ F.U.toScheme, x' ≫ F.U.ι = y ≫ f0 ∧ TMap u F.univ x' := by
    intro K _ _ y u hu
    obtain ⟨v, hvt, hvs⟩ := hf0 K y
    have hsh := hFib K y u hu
    have hth : u.HasTh (𝟙 _) v :=
      (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b S s' t (Sp K) (y ≫ s') u y K (𝟙 _) v hu).2 (by simpa using hvt)
    obtain ⟨u', hu'⟩ := exists_tObj_transport_of_eq (show y ≫ s' = (y ≫ f0) ≫ F.Y.s by rw [Category.assoc, hf0s]) u
    obtain ⟨h1, h2, h3⟩ := hu' (fun _ w => w.Shape Mat κ ∧ w.HasTh (𝟙 _) v ∧
      ∀ x' : Sp K ⟶ F.U.toScheme, TMap w F.univ x' → TMap u F.univ x') ⟨hsh, hth, fun _ h => h⟩
    obtain ⟨x', hx'1, hx'2⟩ := F.obj K (y ≫ f0) u' v h1 h2 hvs
    exact ⟨x', hx'1, h3 x' hx'2⟩
  have hrange : Set.range f0 ⊆ Set.range F.U.ι := by
    rintro q ⟨p, rfl⟩
    obtain ⟨K, _, _, y, p0, hp0⟩ := exists_geomPt S p
    obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b S (Sp K) s' (y ≫ s') y t rfl
    obtain ⟨x', hx', -⟩ := key K y u hu
    refine ⟨x' p0, ?_⟩
    rw [← hp0, ← Scheme.Hom.comp_apply, hx', Scheme.Hom.comp_apply]
  set f := IsOpenImmersion.lift F.U.ι f0 hrange with hfdef
  have hfι : f ≫ F.U.ι = f0 := IsOpenImmersion.lift_fac _ _ _
  have hfs : f ≫ F.U.ι ≫ F.Y.s = s' := by rw [← Category.assoc, hfι, hf0s]
  have hmap : ∀ f' : S ⟶ F.U.toScheme, f' ≫ F.U.ι ≫ F.Y.s = s' → TMap t F.univ f' → ∀ (R : Type) [CommRing R]
      (x : Sp R ⟶ S) (v : Ix g ((n ^ j) ^ 2) → R), t.HasTh x v → SecCoord F.Y.de F.Y.th ((x ≫ f') ≫ F.U.ι) v :=
    fun f' _ hT R _ x v hth =>
      (F.th R (x ≫ f') v).1 ((GlobalTheory.hasTh_iff_of_tmap o g _ J b F.U.toScheme _ F.univ S s' t f' R x v hT).1 hth)
  have hT : TMap t F.univ f := by
    obtain ⟨t2, ht2⟩ := GlobalTheory.tObj_pull o g _ J b F.U.toScheme S (F.U.ι ≫ F.Y.s) s' f F.univ hfs
    have := hS
    have hid : TMap t t2 (𝟙 S) := by
      refine tMap_id_of_geomPt hL hL2 hn hd2 ho fun K _ _ y u hu => ?_
      obtain ⟨x', hx', hxu⟩ := key K y u hu
      have e : x' = y ≫ f := by rw [← cancel_mono F.U.ι, hx', Category.assoc, hfι]
      rw [e] at hxu
      exact TMap.cancel ht2 hxu
    simpa using TMap.comp hid ht2
  refine ⟨f, ⟨hfs, hT⟩, ?_⟩
  rintro f' ⟨hf's, hf'T⟩
  refine hom_ext_affine _ _ fun p => ?_
  obtain ⟨R, _, x, v, hx, hp, hth⟩ := GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g (n ^ j) J b S s' t ho p
  refine ⟨Sp R, x, hx, hp, (cancel_mono F.U.ι).1 ?_⟩
  refine pt_eq_of_secCoord F.Y ?_ (hmap f' hf's hf'T R x v hth) (hmap f hfs hT R x v hth)
  simp only [Category.assoc, hf's, hfs]

end GlobalTheory.ZM.UnivProp
