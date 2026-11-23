import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.CasimirKKhwVec
import Lemmata.SimultaneousEigenvectors.BlSimeig

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section KUnit

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}

def IsKUnitary (ε : Fin n → Bool) (A : Fin n → Fin n → Module.End ℂ X) : Prop :=
  ∀ a b, ε a = ε b → ∀ x y : X, inner ℂ (A a b x) y = inner ℂ x (A b a y)

theorem isKUnitary_of_isInfUnitary (hU : IsInfUnitary ε A) : IsKUnitary ε A := by
  intro a b h x y
  rw [hU a b x y]
  simp [adjSign, h]

def kUnitNatB (a b : Fin 2) : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  LinearMap.smulRight (EuclideanSpace.proj b : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).toLinearMap
    (EuclideanSpace.single a 1)

theorem kUnit_diag_comm (hA : IsGlRep A) (a c : Fin n) (v : X) :
    A a a (A c c v) = A c c (A a a v) := by
  have h := LinearMap.congr_fun (hA a a c c) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  by_cases hac : a = c
  · subst hac; rfl
  · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
    exact h

theorem kUnit_weight_shift (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X} (hw : ∀ c, A c c w = (μ c : ℂ) • w)
    {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
  have h := LinearMap.congr_fun (hA c c a b) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
  by_cases hca : c = a
  · subst hca
    simp [hab, Ne.symm hab] at h ⊢
    linear_combination (norm := module) h
  · by_cases hcb : c = b
    · subst hcb
      simp [hca] at h ⊢
      linear_combination (norm := module) h
    · simp [hca, hcb, Ne.symm hcb] at h ⊢
      linear_combination (norm := module) h

theorem kUnit_exists_joint (hA : IsGlRep A) (s : Finset (Fin n)) :
    ∀ T : Submodule ℂ X, FiniteDimensional ℂ T → (∀ c, ∀ v ∈ T, A c c v ∈ T) → T ≠ ⊥ →
      ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  first | exact Bl.SimultaneousEigenvectors.goal1 .. | (apply Bl.SimultaneousEigenvectors.goal1 <;> assumption) | (intros; apply Bl.SimultaneousEigenvectors.goal1 <;> assumption)

theorem kUnit_eig_real (hU : IsKUnitary ε A) {c : Fin n} {w : X} (hw0 : w ≠ 0) {z : ℂ}
    (hw : A c c w = z • w) : z = ((z.re : ℝ) : ℂ) := by
  have h := hU c c rfl w w
  rw [hw, inner_smul_left, inner_smul_right] at h
  have hne : inner ℂ w w ≠ (0 : ℂ) := inner_self_ne_zero.mpr hw0
  have h2 : (starRingEnd ℂ) z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm

def kUnitWtLin (μ : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((n : ℝ) - ((c : ℕ) : ℝ)) * μ c

theorem kUnitWtLin_shift (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    kUnitWtLin μ < kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have h : kUnitWtLin (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) =
      kUnitWtLin μ + ((n : ℝ) - ((a : ℕ) : ℝ)) - ((n : ℝ) - ((b : ℕ) : ℝ)) := by
    simp only [kUnitWtLin, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  linarith

theorem exists_khw (hA : IsGlRep A) (hU : IsKUnitary ε A) {S : Submodule ℂ X}
    (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := kUnit_exists_joint hA Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact kUnit_eig_real hU hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => kUnit_weight_shift hA hμ (ne_of_lt hab) c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))

theorem orthogonal_kStable (hU : IsKUnitary ε A) {S : Submodule ℂ X} (hS : IsKStableSub ε A S) :
    IsKStableSub ε A Sᗮ := by
  intro a b hab v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← hU b a hab.symm u v]
  exact hv _ (hS b a hab.symm u hu)

theorem starProjection_comm (hU : IsKUnitary ε A) {S : Submodule ℂ X} [S.HasOrthogonalProjection]
    (hS : IsKStableSub ε A S) {a b : Fin n} (hab : ε a = ε b) (x : X) :
    S.starProjection (A a b x) = A a b (S.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hS a b hab _ (Submodule.starProjection_apply_mem S x)
  · intro w hw
    rw [← map_sub]
    have h1 : x - S.starProjection x ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have h2 := orthogonal_kStable hU hS a b hab _ h1
    rw [Submodule.mem_orthogonal] at h2
    rw [inner_eq_zero_symm]
    exact h2 w hw

end KUnit

end ReciprocityTheory.ChartRestriction.DS
