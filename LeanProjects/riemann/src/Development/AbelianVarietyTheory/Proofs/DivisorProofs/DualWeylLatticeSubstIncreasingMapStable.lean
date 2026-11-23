import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

def colPull {k N : ℕ} (τ : Fin k → Fin N) : (Fin N → ℕ) →+ (Fin k → ℕ) where
  toFun g := g ∘ τ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colPull_single_mem {k N : ℕ} {τ : Fin k → Fin N} (hτ : Function.Injective τ) (s : Fin k) :
    colPull τ (Pi.single (τ s) 1) = Pi.single s 1 := by
  funext t
  change (Pi.single (τ s) 1 : Fin N → ℕ) (τ t) = _
  by_cases h : t = s
  · subst h; simp
  · rw [Pi.single_eq_of_ne (fun h' => h (hτ h')), Pi.single_eq_of_ne h]

theorem colPull_single_not {k N : ℕ} {τ : Fin k → Fin N} {y : Fin N} (hy : y ∉ Set.range τ) :
    colPull τ (Pi.single y 1) = 0 := by
  funext t
  change (Pi.single y 1 : Fin N → ℕ) (τ t) = 0
  exact Pi.single_eq_of_ne (fun h => hy ⟨t, h⟩) _

theorem mem_dualWeyl_iff' {R : Type} [CommRing R] {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} :
    f ∈ dualWeyl R r n ν ↔ IsWeightedHomogeneous (colW r n) f ν ∧
      ∀ l j : Fin n, l < j → colAddGen R l j f = rename some f := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, mem_weightedHomogeneousSubmodule,
    LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero]

theorem aeval_isWeightedHomogeneous {R σ ι Mo : Type} [CommRing R] [AddCommMonoid Mo] (w : ι → Mo)
    (φ : σ → MvPolynomial ι R) (ω : σ → Mo) (hφ : ∀ v, IsWeightedHomogeneous w (φ v) (ω v))
    (x : MvPolynomial σ R) (κ : Mo) (hx : IsWeightedHomogeneous ω x κ) :
    IsWeightedHomogeneous w (aeval φ x) κ := by
  conv => enter [2, 2]; rw [x.as_sum]
  rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial, ← hx (mem_support_iff.mp hd), Finsupp.weight_apply, MvPolynomial.algebraMap_eq]
  refine IsWeightedHomogeneous.C_mul ?_ _
  unfold Finsupp.prod Finsupp.sum
  exact IsWeightedHomogeneous.prod _ _ _ fun v _ => (hφ v).pow _

theorem isWeightedHomogeneous_map_weight {R σ M M' : Type} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']
    (π : M →+ M') (w : σ → M) (x : MvPolynomial σ R) (κ : M) (hx : IsWeightedHomogeneous w x κ) :
    IsWeightedHomogeneous (fun v => π (w v)) x (π κ) := by
  intro d hd
  rw [← hx hd, Finsupp.weight_apply, Finsupp.weight_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [map_nsmul]

theorem substMem : SubstMem := by
  intro R _ k N τ hτ ψ h1 h2 h3 ν f hf
  rw [mem_dualWeyl_iff'] at hf ⊢
  have hinj := hτ.injective
  refine ⟨?_, fun l j hlj => ?_⟩
  · have hvar : ∀ v : Fin N × Fin N,
        IsWeightedHomogeneous (colW k k) (ψ v) (colPull τ (colW N N v)) := by
      rintro ⟨x, y⟩
      change IsWeightedHomogeneous _ _ (colPull τ (Pi.single y 1))
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        rw [colPull_single_mem hinj]
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1]
          exact isWeightedHomogeneous_X _ _ _
        · rw [h2 x s hx]
          exact isWeightedHomogeneous_zero _ _ _
      · rw [colPull_single_not hy]
        obtain ⟨c, hc⟩ := h3 x y hy
        rw [hc]
        exact isWeightedHomogeneous_C _ _
    exact aeval_isWeightedHomogeneous (colW k k) ψ _ hvar f _
      (isWeightedHomogeneous_map_weight (colPull τ) _ f ν hf.1)
  · let ψO : Option (Fin N × Fin N) → MvPolynomial (Option (Fin k × Fin k)) R :=
      fun o => o.elim (X none) fun v => rename some (ψ v)
    have hA : (aeval ψO).comp (rename some) = (rename some).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      simp [ψO]
    have hB : (aeval ψO).comp (colAddGen R (r := N) (τ l) (τ j)) = (colAddGen R l j).comp (aeval ψ) := by
      refine MvPolynomial.algHom_ext fun v => ?_
      obtain ⟨x, y⟩ := v
      simp only [AlgHom.comp_apply, aeval_X]
      rw [colAddGen, aeval_X]
      by_cases hy : y ∈ Set.range τ
      · obtain ⟨s, rfl⟩ := hy
        by_cases hx : x ∈ Set.range τ
        · obtain ⟨a, rfl⟩ := hx
          rw [h1, colAddGen, aeval_X]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h1]
          · simp [ψO, h1]
        · rw [h2 x s hx, map_zero]
          simp only [hinj.eq_iff]
          split_ifs with hs
          · subst hs; simp [ψO, h2 x _ hx]
          · simp [ψO, h2 x _ hx]
      · obtain ⟨c, hc⟩ := h3 x y hy
        have hyj : y ≠ τ j := fun h => hy ⟨j, h.symm⟩
        rw [if_neg hyj, hc]
        simp [ψO, hc]
    have e1 := congrArg (fun φ => φ f) hA
    have e2 := congrArg (fun φ => φ f) hB
    simp only [AlgHom.comp_apply] at e1 e2
    rw [← e2, hf.2 (τ l) (τ j) (hτ hlj), e1]

end GlobalTheory.LeviCut
