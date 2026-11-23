import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

private theorem zpow_apply_eig {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (x : M) (c : F)
    (hc : c ≠ 0) (hx : (u : End F M) x = c • x) (n : ℤ) : ((u ^ n : (End F M)ˣ) : End F M) x = c ^ n • x := by
  have hi : ((u⁻¹ : (End F M)ˣ) : End F M) x = c⁻¹ • x := by
    rw [eq_inv_smul_iff₀ hc, ← map_smul, ← hx, ← End.mul_apply, Units.inv_mul, End.one_apply]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Units.val_mul, End.mul_apply, hx, map_smul, ih, smul_smul,
      zpow_add_one₀ hc, mul_comm]
  | pred n ih => rw [zpow_sub_one, Units.val_mul, End.mul_apply, hi, map_smul, ih, smul_smul,
      zpow_sub_one₀ hc, mul_comm]

private theorem key {F M : Type} [Field F] [AddCommGroup M] [Module F M] (u : (End F M)ˣ) (φ a : End F M)
    (hu : (u : End F M) = φ) (hcm : φ * a = a * φ) (x : M) (c s : F) (hc : c ≠ 0) (f : ℕ) (hφ : (φ ^ f) x = c • x)
    (hs : a x = s • x) (n : ℕ) (d : ℤ) :
    (a * ((u ^ (-((f : ℤ) * d)) : (End F M)ˣ) : End F M)) ((φ ^ n) x) = (c ^ (-d) * s) • (φ ^ n) x := by
  have hφ' : (φ ^ f) ((φ ^ n) x) = c • (φ ^ n) x := by
    rw [← End.mul_apply, ← pow_add, add_comm, pow_add, End.mul_apply, hφ, map_smul]
  have hs' : a ((φ ^ n) x) = s • (φ ^ n) x := by
    have hcm' : Commute φ a := hcm
    rw [← End.mul_apply, ← (hcm'.pow_left n).eq, End.mul_apply, hs, map_smul]
  have hz := zpow_apply_eig (u ^ f) _ c hc (by rw [Units.val_pow_eq_pow_val, hu]; exact hφ') (-d)
  rw [End.mul_apply, ← mul_neg, zpow_mul, zpow_natCast, hz, map_smul, hs', mul_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem UpperTheory.weil_deligne_rank_one_line :
    UpperTheory.V.Af.Wd.Line := by
  intro F Ω _ _ _ _ _ l _ P ι w A h O _ _ _ Bw hj L V _ _ _ _ _ ρ h1 hV x hx0 c hc hφ σ s hs y
  have hfin := hV.finite
  have hd : finrank ℂ (WDSpace P ι ρ) = 1 := by
    rw [LetterDim.finrank_wdSpace l P ι _ L _ _ hV, h1]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x) ≠ 0 := by
    by_contra hh
    exact hx0 (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L _ _ _ fun n => by_contra fun h0 => hh ⟨n, h0⟩)
  have hw : weilD Bw h P ρ σ ((phiD P ρ ^ n) x) = (c ^ (-deg σ) * s) • (phiD P ρ ^ n) x := by
    rw [weilD_apply]
    exact key (phiU P ρ) (phiD P ρ) _ (coe_phiU P ρ) (phiD_actD P ρ _) x c s hc _ hφ hs n _
  obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℂ) _ hn).mp hd y
  rw [map_smul, wdRho_mk, hw, wdMk_smul, smul_comm]
