import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth

set_option autoImplicit false

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HTLat.KernelDim

section

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C]
  [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem range_alC (h : CokernelBound P) : LinearMap.range P.alC = ⊤ := by
  have hp : ((p : C) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine eq_top_iff.2 fun y hy => ?_
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul c f =>
    obtain ⟨x, hx⟩ := h f
    refine ⟨(c / (p : C) ^ 2) • P.inclT x, ?_⟩
    rw [map_smul, P.alC_inclT, hx, Point.inclOm, TensorProduct.mk_apply, ← TensorProduct.smul_tmul,
      TensorProduct.smul_tmul', Algebra.smul_def ((p : O) ^ 2), map_pow, map_natCast, smul_eq_mul,
      _root_.mul_one, div_mul_cancel₀ _ hp]

theorem finrank_OmC : Module.finrank C P.OmC = P.A.g := by
  haveI := P.isLocalRing
  haveI := (Point.omega_free_finite_bijective p C v O Λ P).1
  rw [Module.finrank_baseChange, OmegaRank.finrank_omega_Gt p C v O Λ P]

end

theorem finrank_W : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), CokernelBound P → Module.finrank C P.W = P.A.g := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P h
  have h₁ := LinearMap.finrank_range_add_finrank_ker P.alC
  rw [range_alC P h, finrank_top, finrank_OmC, P.finrank_V] at h₁
  change Module.finrank C (LinearMap.ker P.alC) = _
  omega

end GlobalTheory.HTLat.KernelDim
