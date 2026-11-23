import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegCombOfMemPsdCone

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.CoverSuper

theorem mul_evalR_le {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {e : X ≃ₗ[O] X} {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hγ : IsCell bar φ γ) (hc : ∀ i, 0 ≤ c i)
    (hB : pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) (f : X ≃ₗ[O] X) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hℓ : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (N : ℝ) * φ.evalZ β ≤ ℓ β) :
    (N : ℝ) * evalR φ B ≤ ∑ i, c i * (ℓ (pull (f.trans e.symm).toLinearMap (γ i)) : ℝ) ∧
      pullR f.toLinearMap B = ∑ i, c i • toReal (pull (f.trans e.symm).toLinearMap (γ i)) := by
  have hB' : ∀ a b, B (e a) (e b) = ∑ i, c i * (γ i a b : ℝ) := fun a b => by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hB a b
  have hev : evalR φ B = ∑ i, c i * φ.evalZ (γ i) :=
    hγ.linear.eval_eq_sum (r := e.toLinearMap) e.surjective hc hB'
  refine ⟨?_, LinearMap.ext₂ fun a b => ?_⟩
  · rw [hev, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hℓ _ (pull_mem (f.trans e.symm).toLinearMap (hγ.mem i)) (fun y => hγ.nonneg i _)
    rw [evalZ_pull φ (f.trans e.symm).surjective] at h1
    calc (N : ℝ) * (c i * φ.evalZ (γ i)) = c i * (N * φ.evalZ (γ i)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (hc i)
  · have := hB' (e.symm (f a)) (e.symm (f b))
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearMap.sum_apply, this]

theorem add_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}
    (hB : B ∈ psdCone bar X) (hB' : B' ∈ psdCone bar X) : B + B' ∈ psdCone bar X := by
  obtain ⟨m₁, γ₁, c₁, h1, h2, h3, rfl⟩ := ConeSpan.exists_nonneg_comb_of_mem_psdCone O bar X B hB
  obtain ⟨m₂, γ₂, c₂, k1, k2, k3, rfl⟩ := ConeSpan.exists_nonneg_comb_of_mem_psdCone O bar X B' hB'
  have := ConeSub.sum_smul_toReal_mem_psdCone O bar X (m₁ + m₂) (Fin.append γ₁ γ₂) (Fin.append c₁ c₂)
    (fun i => Fin.addCases (fun j => by simpa using h1 j) (fun j => by simpa using k1 j) i)
    (fun i => Fin.addCases (fun j => by simpa using h2 j) (fun j => by simpa using k2 j) i)
    (fun i => Fin.addCases (fun j => by simpa using h3 j) (fun j => by simpa using k3 j) i)
  simpa [Fin.sum_univ_add] using this

theorem superadd_of_cover : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X],
    (∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ),
      IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) →
    ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X, evalR φ B + evalR φ B' ≤ evalR φ (B + B') := by
  intro O _ _ _ _ bar φ X _ _ _ hcov B hB B' hB'
  have hBB := add_mem_psdCone O bar X hB hB'
  obtain ⟨e₁, m₁, γ₁, c₁, hγ₁, hc₁, h₁⟩ := hcov B hB
  obtain ⟨e₂, m₂, γ₂, c₂, hγ₂, hc₂, h₂⟩ := hcov B' hB'
  obtain ⟨e₃, m₃, γ₃, c₃, hγ₃, hc₃, h₃⟩ := hcov (B + B') hBB
  obtain ⟨N, ℓ, hN, hℓ1, hℓ2, -⟩ := hγ₃.strict
  obtain ⟨i1, j1⟩ := mul_evalR_le hγ₁ hc₁ h₁ e₃ hℓ2
  obtain ⟨i2, j2⟩ := mul_evalR_le hγ₂ hc₂ h₂ e₃ hℓ2
  have hev3 : evalR φ (B + B') = ∑ i, c₃ i * φ.evalZ (γ₃ i) :=
    hγ₃.linear.eval_eq_sum (r := e₃.toLinearMap) e₃.surjective hc₃ fun a b => by
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h₃ a b
  have hN3 : (N : ℝ) * evalR φ (B + B') = ∑ i, c₃ i * (ℓ (γ₃ i) : ℝ) := by
    rw [hev3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hℓ1 i]; ring
  have hpull : pullR e₃.toLinearMap (B + B') = pullR e₃.toLinearMap B + pullR e₃.toLinearMap B' :=
    LinearMap.ext₂ fun a b => by simp
  have rel := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
    (β := Sum.elim (Sum.elim (fun i => pull (e₃.trans e₁.symm).toLinearMap (γ₁ i))
      (fun i => pull (e₃.trans e₂.symm).toLinearMap (γ₂ i))) γ₃)
    (c := Sum.elim (Sum.elim c₁ c₂) (-c₃)) (by
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul,
        Finset.sum_neg_distrib]
      rw [← j1, ← j2, ← h₃, hpull]
      abel)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at rel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * (evalR φ B + evalR φ B') ≤ N * evalR φ (B + B') := by
    rw [mul_add, hN3]
    linarith
  exact le_of_mul_le_mul_left key hNpos

end GlobalTheory.PolFan.CoverSuper
