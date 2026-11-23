import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionFieldExt

variable {S : Scheme.{0}}

theorem comp_injective {K Ω : Type} [Field K] [Field Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S}
    (u : Over.mk x' ⟶ Over.mk x) (A : Over S) : Function.Injective (fun y : Over.mk x ⟶ A => u ≫ y) := by
  let v : Sp Ω ⟶ Sp K := u.left
  have : Surjective v := ⟨fun z => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi v := Flat.epi_of_flat_of_surjective v
  intro a b h
  have h' : v ≫ a.left = v ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi v).1 h')

theorem card_torsion (hL : Out.Laws) (P : Out.PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) {n : ℕ}
    (hn : (n : K) ≠ 0) : Nat.card {y : Over.mk x ⟶ P.A // y ^ n = 1} = n ^ (2 * P.g) := by
  have hn' : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hL.polBaseChange S _ x P
  have c := (hL.mulN _ P' n hn').2.2.2.2 K (𝟙 _) hn
  let Φ : (Over.mk (𝟙 (Sp K)) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ x) ⟶ P.A) :=
    MonoidHom.mk' (fun y => Out.toBase hg.w y) (hmul _)
  have hΦ : Function.Bijective Φ :=
    ⟨fun a b e => Over.OverMorphism.ext
      (hg.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z =>
      ⟨Over.homMk (hg.lift z.left (𝟙 _) (Over.w z)) (hg.lift_snd _ _ _), Over.OverMorphism.ext (hg.lift_fst _ _ _)⟩⟩
  have e : Nat.card {y : Over.mk (𝟙 (Sp K)) ⟶ P'.A // y ^ n = 1} =
      Nat.card {y : Over.mk (𝟙 _ ≫ x) ⟶ P.A // y ^ n = 1} :=
    Nat.card_congr ((Equiv.ofBijective Φ hΦ).subtypeEquiv fun y => by
      show _ ↔ Φ y ^ n = 1
      rw [← map_pow, map_eq_one_iff Φ hΦ.1])
  rw [Category.id_comp] at e
  rw [← e, ← hdim]
  exact c

theorem exists_of_isAlgClosed (hL : Out.Laws) (P : Out.PolAV S) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [IsAlgClosed Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S} (u : Over.mk x' ⟶ Over.mk x) {n : ℕ} (hK : (n : K) ≠ 0)
    (hΩ : (n : Ω) ≠ 0) (z : Over.mk x' ⟶ P.A) (hz : z ^ n = 1) :
    ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ u ≫ y = z := by
  have hn' : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hK Nat.cast_zero)
  have c₁ := card_torsion hL P x hK
  have c₂ := card_torsion hL P x' hΩ
  have : Finite {y : Over.mk x' ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {y : Over.mk x ⟶ P.A // y ^ n = 1} → {y : Over.mk x' ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨u ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (comp_injective u _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

end GlobalTheory.TorsionFieldExt

namespace GlobalTheory

open TorsionFieldExt in

theorem torsion_points_field_extension : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) (x : Sp K ⟶ S), Function.Injective (fun y : Over.mk x ⟶ P.A => (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ∧ ∀ (n : ℕ) (z : Over.mk (spMap i ≫ x) ⟶ P.A), (n : K) ≠ 0 → z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y = z := by
  intro hL S P K Ω _ _ _ i x
  refine ⟨comp_injective _ _, fun n z hn hz => ?_⟩
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let v : Over.mk (spMap j ≫ spMap i ≫ x) ⟶ Over.mk (spMap i ≫ x) := Over.homMk (spMap j) rfl
  have hn' : (n : AlgebraicClosure Ω) ≠ 0 := by
    rw [← map_natCast (j.comp i)]
    exact (map_ne_zero _).2 hn
  obtain ⟨y, hy, e⟩ := exists_of_isAlgClosed hL P
    (v ≫ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x)) hn hn' (v ≫ z)
    (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
  exact ⟨y, hy, comp_injective v _ ((Category.assoc _ _ _).symm.trans e)⟩

end GlobalTheory
