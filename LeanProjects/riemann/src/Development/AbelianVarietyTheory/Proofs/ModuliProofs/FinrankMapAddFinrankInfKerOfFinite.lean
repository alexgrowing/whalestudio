import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolynomialFinrankHomogeneousSubmoduleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open MvPolynomial

theorem finrank_map_add_finrank_inf_ker_of_finite {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (P : Submodule K M) [Module.Finite K P] :
    Module.finrank K ↥(P.map f) + Module.finrank K ↥(P ⊓ LinearMap.ker f) = Module.finrank K P := by
  have h := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq P, Submodule.map_comap_subtype] at h
  exact h

theorem mem_homogeneousSubmodule_mul_of_add {K σ : Type*} [Field K] {m n : ℕ}
    {F : MvPolynomial σ K} (hF : F.IsHomogeneous (m + n)) :
    F ∈ homogeneousSubmodule σ K m * homogeneousSubmodule σ K n := by
  rw [← homogeneousSubmodule_one_pow K m, ← homogeneousSubmodule_one_pow K n, ← pow_add,
    homogeneousSubmodule_one_pow]
  exact hF

theorem sub_rename_mem_span_degree {K σ : Type*} [Field K] (t : σ → σ)
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ F, F - rename t F ∈ I) {d : ℕ} (hd : 1 ≤ d)
    {e : ℕ} (he : d ≤ e) : ∀ F : MvPolynomial σ K, F.IsHomogeneous e →
      F - rename t F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  have hk : ∀ (l : MvPolynomial σ K), l.IsHomogeneous 1 → l ∈ I → ∀ n, d ≤ n →
      ∀ H : MvPolynomial σ K, H.IsHomogeneous n →
      l * H ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    intro l hl hlI n hn H hH
    have hn' : n = (d - 1) + (n - (d - 1)) := by omega
    rw [hn'] at hH
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hH) ?_ ?_
    · intro A hA B _
      rw [← _root_.mul_assoc]
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Ideal.mul_mem_right _ _ hlI, ?_⟩)
      have h := hl.mul hA
      rwa [show 1 + (d - 1) = d by omega] at h
    · intro x y hx hy
      rw [mul_add]
      exact add_mem hx hy
  induction e, he using Nat.le_induction with
  | base =>
    intro F hF
    exact Ideal.subset_span ⟨hI F, hF.sub hF.rename_isHomogeneous⟩
  | succ n hn ih =>
    intro F hF
    rw [add_comm] at hF
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hF) ?_ ?_
    · intro l hl G hG
      have hl' : l.IsHomogeneous 1 := hl
      have hG' : G.IsHomogeneous n := hG
      have : l * G - rename t (l * G) =
          l * (G - rename t G) + (l - rename t l) * rename t G := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ (ih G hG'))
        (hk _ (hl'.sub hl'.rename_isHomogeneous) (hI l) n hn _ hG'.rename_isHomogeneous)
    · intro x y hx hy
      have : x + y - rename t (x + y) = (x - rename t x) + (y - rename t y) := by
        rw [map_add]; ring
      rw [this]
      exact add_mem hx hy

theorem regularity_comap_rename_of_surjective :
    ∀ (σ σ₀ : Type) [Finite σ] [Finite σ₀] [Nonempty σ₀] (r : σ → σ₀) (Q₀ : Polynomial ℚ), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (I₀ : Ideal (MvPolynomial σ₀ K)) (I : Ideal (MvPolynomial σ K)) (d : ℕ), I = I₀.comap (MvPolynomial.rename r) → 1 ≤ d → ∀ e ≥ d, (((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ₀ K e ⊓ (I₀).restrictScalars K) : ℕ) : ℚ) = Q₀.eval (e : ℚ) → ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ (I).restrictScalars K) : ℕ) : ℚ) = Q.eval (e : ℚ)) ∧ ((∀ F ∈ I₀, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I₀ ∧ G.IsHomogeneous d}) → ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}) := by
  intro σ σ₀ _ _ _ r Q₀ hr
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  haveI : Nonempty σ := ⟨s (Classical.arbitrary _)⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule σ
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule σ₀
  refine ⟨Q₀ + P - P₀, ?_⟩
  intro K _ I₀ I d hI hd e he
  have hrs : ∀ G : MvPolynomial σ₀ K, rename r (rename s G) = G := by
    intro G
    rw [rename_rename, hs.comp_eq_id, rename_id_apply]
  have hmem : ∀ F, F ∈ I ↔ rename r F ∈ I₀ := by
    intro F
    rw [hI]; exact Ideal.mem_comap
  constructor
  · intro h
    haveI : Module.Finite K (homogeneousSubmodule σ K e) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
    haveI : Module.Finite K ↥(homogeneousSubmodule σ K e ⊓ I.restrictScalars K) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have h1 := finrank_map_add_finrank_inf_ker_of_finite
      (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap (homogeneousSubmodule σ K e)
    have h2 := finrank_map_add_finrank_inf_ker_of_finite
      (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap
      (homogeneousSubmodule σ K e ⊓ I.restrictScalars K)
    have e1 : (homogeneousSubmodule σ K e).map
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ₀ K e := by
      apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        exact IsHomogeneous.rename_isHomogeneous hF
      · intro G hG
        exact ⟨rename s G, IsHomogeneous.rename_isHomogeneous hG, hrs G⟩
    have e2 : (homogeneousSubmodule σ K e ⊓ I.restrictScalars K).map
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ₀ K e ⊓ I₀.restrictScalars K := by
      apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        exact ⟨IsHomogeneous.rename_isHomogeneous hF.1, (hmem F).1 hF.2⟩
      · intro G hG
        refine ⟨rename s G, ⟨IsHomogeneous.rename_isHomogeneous hG.1, (hmem _).2 ?_⟩, hrs G⟩
        rw [hrs]; exact hG.2
    have e3 : homogeneousSubmodule σ K e ⊓ I.restrictScalars K ⊓ LinearMap.ker
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ K e ⊓ LinearMap.ker
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap := by
      apply le_antisymm
      · exact inf_le_inf_right _ inf_le_left
      · intro F hF
        refine ⟨⟨hF.1, (hmem F).2 ?_⟩, hF.2⟩
        have : rename r F = 0 := hF.2
        rw [this]; exact zero_mem _
    rw [e1] at h1
    rw [e2, e3] at h2
    rw [Polynomial.eval_sub, Polynomial.eval_add, ← h, ← hP K e, ← hP₀ K e, ← h1, ← h2]
    push_cast
    ring
  · intro h F hF hFe
    have hA := sub_rename_mem_span_degree (s ∘ r) I (fun G => by
      rw [hmem, map_sub, ← rename_rename, hrs, sub_self]; exact zero_mem _) hd he F hFe
    have hB : Ideal.span {G | G ∈ I₀ ∧ G.IsHomogeneous d} ≤
        (Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}).comap (rename s) := by
      rw [Ideal.span_le]
      intro G hG
      refine Ideal.mem_comap.mpr (Ideal.subset_span ⟨(hmem _).2 ?_, hG.2.rename_isHomogeneous⟩)
      rw [hrs]; exact hG.1
    have hC := Ideal.mem_comap.mp (hB (h _ ((hmem F).1 hF) hFe.rename_isHomogeneous))
    rw [rename_rename] at hC
    simpa using add_mem hA hC

end GlobalTheory
