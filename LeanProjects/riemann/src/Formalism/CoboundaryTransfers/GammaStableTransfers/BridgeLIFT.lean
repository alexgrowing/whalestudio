import Formalism.CoboundaryTransfers.StatementBridge
import Formalism.LagrangeIdealLifts.CocyclePolynomialDivision.CoeffSumXPowMulExpand

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

theorem pow_smul_bijective {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (Q : A)
    (h : Function.Bijective (fun x : D => Q • x)) (M : ℕ) :
    Function.Bijective (fun x : D => Q ^ M • x) := by
  have e : (fun x : D => Q ^ M • x) = (fun x : D => Q • x)^[M] := by
    funext x
    induction M with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ← ih, pow_succ', mul_smul]
  rw [e]
  exact h.iterate M

theorem lift_gamma_invariant_lattice : LIFTGammaQN := by
  intro ℓ _ A _ _ B M D _ _ _ _ W y hy
  obtain ⟨t, hv, hγQ⟩ := B.γQ
  obtain ⟨n, hn, hγn⟩ := W.γ_N _ hy
  obtain ⟨w, hw⟩ := hv.exists_left_inv
  have hX : B.X ∣ w - 1 := ⟨-(w * t), by linear_combination hw⟩
  obtain ⟨r, hr⟩ : B.X ∣ w ^ M - 1 := by
    have h := sub_dvd_pow_sub_pow w 1 M
    rw [one_pow] at h
    exact dvd_trans hX h
  have hw' : w ^ M = B.X * r + 1 := by rw [← hr]; ring
  have h1 : W.γ (B.Q ^ M • y) = B.Q ^ M • ((1 + B.X * t) ^ M • W.γ y) := by
    rw [W.γ_smul, map_pow, hγQ, mul_pow, mul_smul]
  have h2 : w ^ M • W.γ (B.Q ^ M • y) = B.Q ^ M • W.γ y := by
    rw [h1, smul_comm (w ^ M) (B.Q ^ M), ← mul_smul (w ^ M), ← mul_pow, hw, one_pow, one_smul]
  have h3 : W.γ (B.Q ^ M • y) = B.Q ^ M • y + B.X • n := by rw [← hγn]; abel
  have key : B.Q ^ M • (W.γ y - y) = B.X • (r • B.Q ^ M • y + w ^ M • n) := by
    rw [smul_sub, ← h2, h3, hw']
    module
  have hb := pow_smul_bijective B.Q W.Q_bij M
  obtain ⟨y', hy'⟩ := hb.2 (r • B.Q ^ M • y + w ^ M • n)
  simp only at hy'
  refine ⟨y', ?_, ?_⟩
  · rw [hy']
    exact W.N.add_mem (W.N.smul_mem _ hy) (W.N.smul_mem _ hn)
  · apply hb.1
    simp only
    rw [key, smul_comm (B.Q ^ M) B.X y', hy']

def sesOfLIFT {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
    {B : LIFT.Base ℓ A} {M : ℕ} {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : LIFT.WD B M D₀} {W₁ : LIFT.WD B M D₁} {W₂ : LIFT.WD B M D₂}
    (S : LIFT.SES W₀ W₁ W₂) :
    SES (ofLIFT W₀ (lift_gamma_invariant_lattice ℓ A B M D₀ W₀)) (ofLIFT W₁ (lift_gamma_invariant_lattice ℓ A B M D₁ W₁))
      (ofLIFT W₂ (lift_gamma_invariant_lattice ℓ A B M D₂ W₂)) where
  ι := ⟨S.ι.f, S.ι.φ_comm, S.ι.γ_comm, S.ι.N_le⟩
  π := ⟨S.π.f, S.π.φ_comm, S.π.γ_comm, S.π.N_le⟩
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat

theorem wach_lattice_nonempty_unramified : NonemptyU := by
  intro p _ u
  obtain ⟨B, W, hu, hN, hX⟩ := LIFT.wDNonempty_proof p u
  subst hu
  refine ⟨baseOfLIFT B, ofLIFT W (lift_gamma_invariant_lattice p _ B 0 _ W), rfl, hN, hX, B.γX, ?_⟩
  obtain ⟨t, ht, h⟩ := B.γQ
  refine ⟨1 + B.X * t, ht, ⟨t, rfl⟩, ?_⟩
  show B.γA B.Q = (1 + B.X * t) * B.Q
  rw [h, mul_comm]

end Formalism.CoboundaryTransfers
