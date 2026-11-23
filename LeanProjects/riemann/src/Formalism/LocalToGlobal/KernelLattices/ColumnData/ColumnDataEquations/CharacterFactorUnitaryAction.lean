import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.NormOneUnitIdealAlt

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H

theorem iopSelf (D : Car) : IopSelf D := by
  intro T N N' La' G hG
  funext z
  have hq : ∀ q : ↥La' ⧸ La'.addSubgroupOf La', q = 0 := by
    intro q
    refine QuotientAddGroup.induction_on q fun x => ?_
    exact (QuotientAddGroup.eq_zero_iff x).2 (by simp [AddSubgroup.addSubgroupOf_self])
  have hidx : (La'.addSubgroupOf La').index = 1 := by
    rw [AddSubgroup.addSubgroupOf_self, AddSubgroup.index_top]
  simp only [TaylorLogMetric.Iop, hidx, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul]
  rw [finsum_eq_single _ 0 (fun q hq' => absurd (hq q) hq')]
  exact hG.2 _ (Quotient.out (0 : ↥La' ⧸ La'.addSubgroupOf La')).2 z

section Chi

variable {D : Car}

theorem character_factor_change_right (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN' : Even N')
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h1 : SD D L') (h2 : SD D L'') :
    Cd.Base.chiFac χ N N' L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Cd.Base.chiFac χ N N' L L' := by
  unfold Cd.Base.chiFac
  rw [hM N' (StandardLatticesGL3.stdL D N') L' L'' hN' (sd0 N') h1 h2,
    hχ.1 _ _ (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' (sd0 N') h1)
      (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ _ hN' h1 h2), mul_zpow]
  ring

theorem character_factor_change_left (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hM : DetMul D) {N N' : ℕ} (hN : Even N)
    {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (h1 : SD D L) (h2 : SD D L₁) :
    Cd.Base.chiFac χ N N' L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Cd.Base.chiFac χ N N' L L' := by
  unfold Cd.Base.chiFac
  rw [hM N (StandardLatticesGL3.stdL D N) L L₁ hN (sd0 N) h1 h2,
    hχ.1 _ _ (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (sd0 N) h1)
      (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN h1 h2), mul_zpow]
  ring

theorem emb_star_unit (τ : D.what₂.Tau) (x : D.host.E) (hx : letI := D.host.cmStar; x * star x = 1) :
    (letI := D.host.cmStar; TaylorLogMetric.embT D τ (star x)) = (TaylorLogMetric.embT D τ x)⁻¹ := by
  letI := D.host.cmStar
  have h := congrArg (TaylorLogMetric.embT D τ) hx
  rw [map_mul, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

private theorem inv_mul_zpow_mul_inv_mul_zpow_neg (a b P Q : ℂ) (m n : ℕ) :
    (P⁻¹ * a) ^ (m : ℤ) * (Q⁻¹ * b) ^ (-(n : ℤ)) = a ^ (m : ℤ) * b ^ (-(n : ℤ)) * (P⁻¹ ^ m * Q ^ n) := by
  rw [mul_zpow, mul_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    inv_pow, inv_pow, inv_inv]
  ring

theorem character_factor_unitary_action (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hS : DetSmul D) (hU : NormOneUnitIdeal D) {N N' : ℕ}
    (hN : Even N) (hN' : Even N') :
    letI := D.host.cmStar
    ∀ (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E), SD D L → SD D L' →
    Cd.Base.chiFac χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L') =
      Cd.Base.chiFac χ N N' L L' *
        ((∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) *
          (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) ^ (N / 2)) := by
  intro L L' γ γ' hL hL'
  letI := D.host.cmStar
  have hd : (γ : Matrix (Fin N) (Fin N) D.host.E).det ∈ unitary D.host.E :=
    Matrix.det_of_mem_unitary γ.2
  have hd' : (γ' : Matrix (Fin N') (Fin N') D.host.E).det ∈ unitary D.host.E :=
    Matrix.det_of_mem_unitary γ'.2
  have e1 := hS N (StandardLatticesGL3.stdL D N) L γ hN (sd0 N) hL
  have e2 := hS N' (StandardLatticesGL3.stdL D N') L' γ' hN' (sd0 N') hL'
  have c1 := hχ.1 (𝓞 D.host.E ∙ (γ : Matrix (Fin N) (Fin N) D.host.E).det) _ (hU ⟨_, hd⟩)
    (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N _ L hN (sd0 N) hL)
  have c2 := hχ.1 (𝓞 D.host.E ∙ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) _ (hU ⟨_, hd'⟩)
    (Formalism.L2.Ker.Cd.IntegralLatticeDensity.relative_determinant_norm_one D N' _ L' hN' (sd0 N') hL')
  have u1 : χ (𝓞 D.host.E ∙ (γ : Matrix (Fin N) (Fin N) D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ := hχ.2 ⟨_, hd⟩
  have u2 : χ (𝓞 D.host.E ∙ (γ' : Matrix (Fin N') (Fin N') D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det)⁻¹ := hχ.2 ⟨_, hd'⟩
  have s1 : ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det) =
      ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det)⁻¹ :=
    Finset.prod_congr rfl fun τ _ => emb_star_unit τ _ hd.2
  simp only [Cd.Base.chiFac]
  rw [e1, e2, c1, c2, u1, u2, s1, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  exact inv_mul_zpow_mul_inv_mul_zpow_neg _ _ _ _ _ _

end Chi

section Pull

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem pull_smul (T : TaylorLogMetric.Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D T γ γ' (c • G) = c • TaylorLogMetric.pull D T γ γ' G := rfl

theorem pull_comp {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ γ' G =
      TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) γ 1 (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) 1 γ' G) := by
  funext z
  simp only [TaylorLogMetric.pull, TaylorLogMetric.tor0]
  congr 1
  funext τ
  simp [Matrix.map_one, Matrix.mul_assoc]
  rfl

end Pull

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
