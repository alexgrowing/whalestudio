import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsSemiPosHerm (M : HermLine ι) : Prop :=
  ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ v : (Σ k, ι k) → ℂ,
    0 ≤ Δ (fun t : ℂ => Real.log (M.h (z + t • v))) 0

def De (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι) : ℝ :=
  ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (logNorm A' s')) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s)) -
    ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s'}) W : ℝ) * ptsIntegral W (pot L) (logNorm A s)) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s'))

theorem De_swap (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι)
    (s s' : MRing ι) : De P L A' A s' s = -De P L A A' s s' := by
  unfold De
  ring

end Objects

def DeSlotAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (j : Fin n) (M N A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ i, IsSmoothHerm (L i)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P (Function.update L j (M.tensor N)) A A' s s' =
      De P (Function.update L j M) A A' s s' + De P (Function.update L j N) A A' s s'

def SemiPosTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (M : HermLine ι),
    IsSmoothHerm M → ∃ T : HermLine ι, IsSmoothHerm T ∧ IsSemiPosHerm T ∧ IsSemiPosHerm (M.tensor T)

def DeLeSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSemiPosHerm (L j)) →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P L A A' s s' ≤ 0

theorem isSectionOn_coordinate_plane (i : Fin 3) : IsSectionOn (⊥ : Ideal (MRing (PBlk 3))) (fsLine 3) (Xc 3 i) := by
  refine ⟨fun _ => 1, fun _ => rfl, fun m hm k => ?_, ?_⟩
  · rw [support_X, Finset.mem_singleton] at hm
    subst hm
    simp [Finsupp.single_apply]
  · rw [Submodule.mem_bot]
    exact X_ne_zero _

end GroundTheory.Heights₂.Heights.Inter
