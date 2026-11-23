import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.OddPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.EvenPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DSigma

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n : ℕ}

private theorem dA_ev {a : ℕ} (N : Matrix (Fin n) (Fin n) F) :
    N ∈ Ev F F n a ↔ ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → N i j = 0 := by
  change (∀ i j : Fin n, _) ↔ _
  simp

private theorem dA_od {a : ℕ} (N : Matrix (Fin n) (Fin n) F) :
    N ∈ Od F F n a ↔ ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → N i j = 0 := by
  change (∀ i j : Fin n, _) ↔ _
  simp

private theorem dA_oo {a : ℕ} {N N' : Matrix (Fin n) (Fin n) F} (h : N ∈ Od F F n a)
    (h' : N' ∈ Od F F n a) : N * N' ∈ Ev F F n a := by
  rw [dA_od] at h h'
  rw [dA_ev]
  intro i j e
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases c : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [h i k c, zero_mul]
  · rw [h' k j (by tauto), mul_zero]

private theorem dA_eo {a : ℕ} {N N' : Matrix (Fin n) (Fin n) F} (h : N ∈ Ev F F n a)
    (h' : N' ∈ Od F F n a) : N * N' ∈ Od F F n a := by
  rw [dA_od] at h' ⊢
  rw [dA_ev] at h
  intro i j e
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases c : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [h' k j (by tauto), mul_zero]
  · rw [h i k c, zero_mul]

private theorem dA_oe {a : ℕ} {N N' : Matrix (Fin n) (Fin n) F} (h : N ∈ Od F F n a)
    (h' : N' ∈ Ev F F n a) : N * N' ∈ Od F F n a := by
  rw [dA_od] at h ⊢
  rw [dA_ev] at h'
  intro i j e
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases c : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
  · rw [h i k c, zero_mul]
  · rw [h' k j (by tauto), mul_zero]

end SlopeTestRemainingChoices

private theorem smul_commutator_conj_mul_eq_add_add {F : Type} [Field F] {n : ℕ}
    (P Pi Q Qi K1 K2 PoissonCutoffFormula Y L PQ PQi : Matrix (Fin n) (Fin n) F) (a b : F)
    (hP : Pi * P = 1) (hK : PoissonCutoffFormula = K1 + P * K2 * Pi) (hL : L = b • (Q * Y * Qi) - Y)
    (hPQ : PQ = P * Q) (hPQi : PQi = Qi * Pi) :
    (a * b) • (PoissonCutoffFormula * (PQ * Y * PQi) - PQ * Y * PQi * PoissonCutoffFormula) =
      a • (K1 * (P * L * Pi) - P * L * Pi * K1) + a • (K1 * (P * Y * Pi) - P * Y * Pi * K1) +
        (a * b) • (P * (K2 * (Q * Y * Qi) - Q * Y * Qi * K2) * Pi) := by
  subst hK hL hPQ hPQi
  have e : ∀ X : Matrix (Fin n) (Fin n) F, Pi * (P * X) = X := fun X => by
    rw [← mul_assoc, hP, one_mul]
  simp only [mul_sub, sub_mul, add_mul, mul_add, smul_sub, mul_smul_comm, smul_mul_assoc, mul_assoc, e,
    smul_smul, smul_add]
  abel

theorem UpperTheory.V.Pa.Det.detAlg :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) {m : ℕ} (κ la : Fin m → G → Matrix (Fin n) (Fin n) F) (s : F) (ph : G → Matrix (Fin n) (Fin n) F), D.IsKap κ → D.IsTw κ s ph la → ∃ (Y₀ : Matrix (Fin n) (Fin n) F) (Y : Fin m → Matrix (Fin n) (Fin n) F), Y₀ ∈ Ev F F n D.a ∧ s • Y₀ᵀ = Y₀ ∧ (∀ k, Y k ∈ Od F F n D.a ∧ s • (Y k)ᵀ = Y k ∧ ∀ g, la k g = dTw D.χF D.r (Y k) g) ∧ ∀ g, ph g = dTw D.χF D.r Y₀ g + D.χF g • ∑ k, (κ k g * (D.r g * Y k * D.r g⁻¹) - (D.r g * Y k * D.r g⁻¹) * κ k g) := by
  intro F G _ _ n D m κ la s ph hK hT
  choose Y hYod hYs hYla using Det.oddPart D κ la s ph hK hT
  have rinv : ∀ g, D.r g⁻¹ * D.r g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have χmul : ∀ g h, D.χF (g * h) = D.χF g * D.χF h := fun g h => by simp [DetFr.χF]
  let c : G → Matrix (Fin n) (Fin n) F := fun g =>
    ∑ k, (κ k g * (D.r g * Y k * D.r g⁻¹) - (D.r g * Y k * D.r g⁻¹) * κ k g)
  let ψ : G → Matrix (Fin n) (Fin n) F := fun g => ph g - D.χF g • c g
  have hcoc : TwCoc D.χF D.r Set.univ ψ := by
    intro g _ h _
    have hcgh : (D.χF g * D.χF h) • c (g * h) =
        D.χF g • ∑ k, (κ k g * (D.r g * la k h * D.r g⁻¹) - D.r g * la k h * D.r g⁻¹ * κ k g) +
          D.χF g • c g + (D.χF g * D.χF h) • (D.r g * c h * D.r g⁻¹) := by
      simp only [c, Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact smul_commutator_conj_mul_eq_add_add _ _ _ _ _ _ _ _ _ _ _ _ _ (rinv g)
        (by have := (hK.coc k) g trivial h trivial; simpa using this)
        (by rw [hYla k h]; rfl) (map_mul _ _ _) (by rw [_root_.mul_inv_rev, map_mul])
    show ph (g * h) - D.χF (g * h) • c (g * h) = ph g - D.χF g • c g + D.χF g • (D.r g * (ph h - D.χF h • c h) * D.r g⁻¹)
    rw [χmul, hcgh, hT.ph_mul g h]
    simp only [mul_sub, sub_mul, smul_sub, smul_add, mul_smul_comm, smul_mul_assoc, smul_smul]
    abel
  have rinvEv : ∀ g, D.r g⁻¹ ∈ Ev F F n D.a := fun g => D.ev _
  have hRod : ∀ k g, D.r g * Y k * D.r g⁻¹ ∈ Od F F n D.a := fun k g =>
    dA_oe (dA_eo (D.ev g) (hYod k)) (rinvEv g)
  have hcEv : ∀ g, c g ∈ Ev F F n D.a := fun g =>
    Submodule.sum_mem _ fun k _ =>
      Submodule.sub_mem _ (dA_oo (hK.od k g) (hRod k g)) (dA_oo (hRod k g) (hK.od k g))
  have hψEv : ∀ g, ψ g ∈ Ev F F n D.a := fun g =>
    Submodule.sub_mem _ (hT.ev g) (Submodule.smul_mem _ _ (hcEv g))
  have hYT : ∀ k, (Y k)ᵀ = s • Y k := fun k => by
    conv_rhs => rw [← hYs k]
    rw [smul_smul, hT.sq, one_smul]
  have hRσ : ∀ k g, D.r (D.σ g) * Y k * D.r (D.σ g)⁻¹ = s • (D.r g * Y k * D.r g⁻¹)ᵀ := fun k g => by
    have := Det.dSigma D (fun _ => 1) (Y k) g (fun _ => rfl)
    simp only [dTw, one_smul] at this
    rw [hYT k] at this
    rw [sub_eq_iff_eq_add] at this
    rw [this, Matrix.transpose_sub, Matrix.transpose_smul, hYs, sub_add_cancel, mul_smul_comm,
      smul_mul_assoc, Matrix.transpose_smul]
  have hχσ : ∀ g, D.χF (D.σ g) = D.χF g := fun g => by simp [DetFr.χF, D.χσ]
  have hpol : ∀ g, ψ (D.σ g) = s • (ψ g)ᵀ := fun g => by
    show ph (D.σ g) - D.χF (D.σ g) • c (D.σ g) = s • (ph g - D.χF g • c g)ᵀ
    rw [hT.ph_pol, hχσ]
    have hc : c (D.σ g) = s • (c g)ᵀ := by
      simp only [c, hRσ, hK.pol, Matrix.transpose_sum, Finset.smul_sum, Matrix.transpose_sub,
        Matrix.transpose_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [neg_mul, mul_neg, mul_smul_comm, smul_mul_assoc, smul_sub, sub_neg_eq_add, neg_smul,
        one_smul, smul_neg]
      abel
    rw [hc, Matrix.transpose_sub, Matrix.transpose_smul, smul_sub, smul_comm s (D.χF g)]
  have htr : ∀ g ∈ D.G', (ψ g * D.r g).trace = 0 := fun g hg => by
    have h1 : D.χF g = 1 := by simp [DetFr.χF, D.χ_triv g hg]
    have hell := hT.ell g hg
    show ((ph g - D.χF g • c g) * D.r g).trace = 0
    rw [h1, one_smul, sub_mul, Matrix.trace_sub, ← hell, sub_eq_add_neg, add_right_inj]
    simp only [c, Finset.sum_mul, Matrix.trace_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hYla k g, dTw, h1, one_smul]
    have hc : (κ k g * (D.r g * Y k)).trace = (Y k * (κ k g * D.r g)).trace := by
      rw [Matrix.trace_mul_comm (Y k), mul_assoc]
    simp only [sub_mul, Matrix.trace_sub, mul_assoc, rinv, mul_one]
    rw [hc]
    abel
  obtain ⟨Y₀, hY₀, hY₀s, hY₀ψ⟩ := Det.evenPart D s ψ hT.sq hcoc hψEv hpol htr
  refine ⟨Y₀, Y, hY₀, hY₀s, fun k => ⟨hYod k, hYs k, hYla k⟩, fun g => ?_⟩
  rw [← hY₀ψ g]
  show ph g = ph g - D.χF g • c g + D.χF g • c g
  abel
