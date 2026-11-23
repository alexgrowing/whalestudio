import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.ExistsTwoTorsionWeilDegenerate
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.ExistsDimOne
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.WeilIsUniqueOfLocal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenWeilModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def ext {ξ : Spec (CommRingCat.of Ω) ⟶ X} {k : Type} [Field k] (i : Ω →+* k) :
    Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap i) rfl

theorem unique {G : Over X} [GrpObj G] {L : LB G.left} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {n : ℕ}
    {e e' : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ} (h : GenWeil G L ξ n e) (h' : GenWeil G L ξ n e')
    {x g : Over.mk ξ ⟶ G} (hx : x ^ n = 1) (hg : g ^ n = 1) : e x g = e' x g := by
  let i := algebraMap Ω (AlgebraicClosure Ω)
  let c : (AlgebraicClosure Ω)ˣ := Units.map i.toMonoidHom (e x g)
  have h1 := (h.weil x g hx hg _ i (ext i ≫ x) (ext i ≫ g) c rfl rfl).2 rfl
  have h2 := (h'.weil x g hx hg _ i (ext i ≫ x) (ext i ≫ g) c rfl rfl).1 h1
  exact Units.ext (i.injective h2)

theorem not_of_all {G : Over X} [GrpObj G] {L : LB G.left} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {n : ℕ}
    (hL : ∀ (T : Over X) (x y : T ⟶ G) (c : Γ(T.left, ⊤)ˣ), WeilIs G L n x y c)
    (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ) : ¬ GenWeil G L ξ n e := by
  classical
  intro h
  let i := algebraMap Ω (AlgebraicClosure Ω)
  have key : ∀ c : (AlgebraicClosure Ω)ˣ, (c : AlgebraicClosure Ω) = i (e 1 1) := fun c =>
    (h.weil 1 1 (one_pow n) (one_pow n) _ i (ext i ≫ 1) (ext i ≫ 1) c rfl rfl).1 (hL _ _ _ _)
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (AlgebraicClosure Ω))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact ha.2 ((key (Units.mk0 a ha.1)).trans (key 1).symm)

theorem unitOn_ext {k : Type} [Field k] (i : Ω →+* k) (u : Ωˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map i.toMonoidHom u) := by
  ext
  exact congrArg (fun f => f.hom (u : Ω)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i)).symm

theorem unitOn_bij {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.toMulEquiv).bijective

theorem unitOn_mul {R : Type} [CommRing R] (a b : Rˣ) : unitOn (a * b) = unitOn a * unitOn b := map_mul _ _ _

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

theorem exists_of_polAV (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Spec (CommRingCat.of K)))
    (n : ℕ) (hn : 1 ≤ n) : ∃ e, GenWeil P.A P.L (𝟙 (Spec (CommRingCat.of K))) n e := by
  classical
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  haveI : IsCommMonObj P.A := P.isAb.comm
  obtain ⟨hu, hm, -, -⟩ := GlobalTheory.PairingLawZeroCounterexample.laws.1 _ P n (baseOver _)
  have hex : ∀ x g : baseOver _ ⟶ P.A, ∃ c : Kˣ, x ^ n = 1 → g ^ n = 1 → WeilIs P.A P.L n x g (unitOn c) := by
    intro x g
    by_cases h : x ^ n = 1 ∧ g ^ n = 1
    · obtain ⟨c, hc, -⟩ := hu x g h.1 h.2
      obtain ⟨d, rfl⟩ := (unitOn_bij (R := K)).2 c
      exact ⟨d, fun _ _ => hc⟩
    · exact ⟨1, fun a b => (h ⟨a, b⟩).elim⟩
  choose e he using hex
  have huq : ∀ (x g : baseOver _ ⟶ P.A) (c : Kˣ), x ^ n = 1 → g ^ n = 1 → WeilIs P.A P.L n x g (unitOn c) →
      c = e x g := fun x g c hx hg h =>
    (unitOn_bij (R := K)).1 ((hu x g hx hg).unique h (he x g hx hg))
  have hmulT : ∀ x y : baseOver _ ⟶ P.A, x ^ n = 1 → y ^ n = 1 → (x * y) ^ n = 1 := fun x y hx hy => by
    rw [mul_pow, hx, hy, _root_.mul_one]
  have hl : ∀ x x' g, x ^ n = 1 → x' ^ n = 1 → g ^ n = 1 → e (x * x') g = e x g * e x' g := fun x x' g a b c =>
    (huq _ _ _ (hmulT _ _ a b) c (by rw [unitOn_mul]; exact hm _ _ _ _ _ (he x g a c) (he x' g b c))).symm
  have hr : ∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g' := fun x g g' a b c =>
    (huq _ _ _ a (hmulT _ _ b c)
      (by rw [unitOn_mul]; exact GlobalTheory.PairingLawZeroCounterexample.mul_right P n (he x g a b) (he x g' a c))).symm
  have hnl : ∀ x, x ^ n = 1 → (∀ g, g ^ n = 1 → e x g = 1) → x = 1 := fun x hx h =>
    GlobalTheory.PairingLawZeroCounterexample.laws.2.1 K P n hnK x hx fun y hy => by
      have := he x y hx hy
      rwa [h y hy, unitOn_one] at this
  have hnr : ∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1 := fun g hg h =>
    GlobalTheory.PairingLawZeroCounterexample.laws.2.1 K P n hnK g hg fun y hy => by
      have := he y g hy hg
      rw [h y hy, unitOn_one] at this
      simpa using GlobalTheory.PairingLawZeroCounterexample.skew P n this
  have hfin : Finite {x : baseOver _ ⟶ P.A // x ^ n = 1} := by
    apply Nat.finite_of_card_ne_zero
    rw [show Nat.card {x : baseOver _ ⟶ P.A // x ^ n = 1} = _ from
      (GlobalTheory.MulLawTest.mulN _ P n hn).2.2.2.2 K (𝟙 _) hnK]
    positivity
  refine ⟨e, hfin, hl, hr, ?_, hnr, ?_⟩
  · intro χ hχ
    let T : Subgroup (baseOver (Spec (CommRingCat.of K)) ⟶ P.A) := (powMonoidHom n).ker
    haveI : Finite T := hfin
    let ch : T → (T →* Kˣ) := fun x => MonoidHom.mk' (fun g => e x g) fun g g' => hr _ _ _ x.2 g.2 g'.2
    let Φ : T →* (T →* Kˣ) := MonoidHom.mk' ch fun x x' => by
      ext g : 1
      exact hl _ _ _ x.2 x'.2 g.2
    have hinj : Function.Injective Φ := (injective_iff_map_eq_one Φ).2 fun x hx =>
      Subtype.ext (hnl x x.2 fun g hg => DFunLike.congr_fun hx ⟨g, hg⟩)
    haveI : NeZero ((Monoid.exponent T : ℕ) : K) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
    have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T K
    haveI : Finite (T →* Kˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
    have hbij := hinj.bijective_of_nat_card_le hcard.le
    obtain ⟨x, hx⟩ := hbij.2 (MonoidHom.mk' (fun g : T => χ g) fun g g' => hχ _ _ g.2 g'.2)
    exact ⟨x, x.2, fun g hg => (DFunLike.congr_fun hx ⟨g, hg⟩).symm⟩
  · intro x g hx hg k _ _ i xk gk c hxk hgk
    obtain rfl : xk = ext i ≫ x := Over.OverMorphism.ext hxk
    obtain rfl : gk = ext i ≫ g := Over.OverMorphism.ext hgk
    have hp := (GlobalTheory.weilIs_alternating_skew_natural GlobalTheory.laws_without_cohomology.1 GlobalTheory.PairingLawZeroCounterexample.lifts
      _ P n _).2.2 _ (ext i) x g _ (he x g hx hg)
    have hp' : WeilIs P.A P.L n (ext i ≫ x) (ext i ≫ g) (unitOn (Units.map i.toMonoidHom (e x g))) :=
      unitOn_ext i (e x g) ▸ hp
    have hx' : (ext i ≫ x) ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have hg' : (ext i ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    constructor
    · intro h
      have := (unitOn_bij (R := k)).1
        (((GlobalTheory.PairingLawZeroCounterexample.laws.1 _ P n _).1 _ _ hx' hg').unique h hp')
      rw [this]; rfl
    · intro h
      obtain rfl : c = Units.map i.toMonoidHom (e x g) := Units.ext h
      exact hp'

theorem nontrivial : ∃ (P : PolAV (Spec (CommRingCat.of ℂ))) (e : _),
    P.g = 1 ∧ GenWeil P.A P.L (𝟙 (Spec (CommRingCat.of ℂ))) 2 e ∧ ∃ x g, x ^ 2 = 1 ∧ g ^ 2 = 1 ∧ e x g ≠ 1 := by
  obtain ⟨P, g, hP, hg, hg2⟩ := GlobalTheory.PairingLawZeroCounterexample.exists_order_two ℂ (by norm_num)
  obtain ⟨e, he⟩ := exists_of_polAV ℂ P 2 (by norm_num)
  have := mt (he.nondeg g hg2) hg
  push Not at this
  obtain ⟨x, hx, hne⟩ := this
  exact ⟨P, e, hP, he, x, g, hx, hg2, hne⟩

theorem not_const : ∃ P : PolAV (Spec (CommRingCat.of ℂ)),
    ¬ GenWeil P.A P.L (𝟙 (Spec (CommRingCat.of ℂ))) 2 fun _ _ => 1 := by
  obtain ⟨P, e, -, he, x, g, hx, hg, hne⟩ := nontrivial
  exact ⟨P, fun h => hne (unique he h hx hg)⟩

theorem not_noCharts {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {n : ℕ}
    (e : (Over.mk ξ ⟶ G) → (Over.mk ξ ⟶ G) → Ωˣ) : ¬ GenWeil G ⟨PEmpty, PEmpty.elim, fun i => i.elim⟩ ξ n e :=
  not_of_all (fun _ x y c => GlobalTheory.ThetaGroupTest.weilIs_noCharts _ x y c) e

end GlobalTheory.CompanionTheory.Ar.GenWeilModel
