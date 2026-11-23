import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HTLat.KerPerp

theorem eq_zero_of_forall_dual {O C M : Type} [CommRing O] [CommRing C] [Algebra O C]
    [AddCommGroup M] [Module O M] [Module.Free O M] (z : C ⊗[O] M)
    (h : ∀ l : Module.Dual O M, (Algebra.linearMap O C ∘ₗ l).liftBaseChange C z = 0) : z = 0 := by
  let b := Module.Free.chooseBasis O M
  refine (b.baseChange C).ext_elem fun i => ?_
  have e : (b.baseChange C).coord i = (Algebra.linearMap O C ∘ₗ b.coord i).liftBaseChange C := by
    refine LinearMap.ext fun w => ?_
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c m =>
      rw [Module.Basis.coord_apply, Module.Basis.baseChange_repr_tmul,
        LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, Algebra.linearMap_apply,
        Module.Basis.coord_apply, Algebra.smul_def, smul_eq_mul, mul_comm]
  rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply, e]
  exact h _

theorem mem_W_iff : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∀ x : P.V, x ∈ P.W ↔ ∀ y, P.pairV (P.bLie y) x = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P x
  obtain ⟨hf, -, hb⟩ := Point.omega_free_finite_bijective p C v O Λ P
  have key : ∀ y (w : P.V), P.pairV (P.bLie y) w =
      (Algebra.linearMap O C ∘ₗ ((LinearMap.proj y : (_ → O) →ₗ[O] O) ∘ₗ
        (omega P.Gt).subtype)).liftBaseChange C (P.alC w) := by
    intro y w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c t =>
      have e : (c ⊗ₜ[ℤ_[p]] t : P.V) = c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Point.alC_tmul, LinearMap.liftBaseChange_tmul, e, map_smul, Point.pairV_bLie]
      rfl
  constructor
  · intro hx y
    rw [key, show P.alC x = 0 from hx, map_zero]
  · intro h
    refine eq_zero_of_forall_dual (P.alC x) fun l => ?_
    obtain ⟨y, rfl⟩ := hb.2 l
    exact (key y x).symm.trans (h y)

end GlobalTheory.HTLat.KerPerp
