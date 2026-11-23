import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddEquivOfCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitPairK

open Matrix Formalism.MainNotions.S GlobalTheory.RowLev
open scoped TensorProduct

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

variable (I : AutInst)

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [AutInst.fmat]

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [AutInst.fmat]

theorem hAf_unitary (x : I.Gf) (v w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x *ᵥ v) (I.fmat x *ᵥ w) = hAf I v w := by
  unfold hAf
  rw [hform_mulVec_mulVec]
  have h : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
      I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  rw [h]

theorem hAf_move (x : I.Gf) (v w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I v (I.fmat x *ᵥ w) = hAf I (I.fmat x⁻¹ *ᵥ v) w := by
  rw [← hAf_unitary I x (I.fmat x⁻¹ *ᵥ v) w, mulVec_mulVec, fmat_mul_inv, one_mulVec]

theorem hAf_smul_right (v w : Fin I.n → I.E ⊗[I.F] Af I.F) (c : I.E ⊗[I.F] Af I.F) :
    hAf I v (c • w) = c * hAf I v w := by
  simp only [hAf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hAf_smul_left (v w : Fin I.n → I.E ⊗[I.F] Af I.F) (c : I.E ⊗[I.F] Af I.F) :
    hAf I (c • v) w = sigA I c * hAf I v w := by
  simp only [hAf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hAf_sub_right (u v w : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u (v - w) = hAf I u v - hAf I u w := by
  simp only [hAf, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hAf_sub_left (u u' w : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I (u - u') w = hAf I u w - hAf I u' w := by
  simp only [hAf, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lf_iff {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    (y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    y ∈ I.Lf ↔ ∀ i, (((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
      *ᵥ y) i ∈ IntAf I.F I.E := by
  have e : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
    show Submodule.span _ _ = Submodule.span _ _
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
  rw [← e]
  exact hβ y

theorem eps_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (hx : ∀ i j, ε * ((β₀⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    ε • ((I.fmat x - 1) *ᵥ y) ∈ I.Lf := by
  rw [lf_iff I hβ] at hy ⊢
  intro i
  set Bi : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
    ((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) with hBi
  set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
    ((β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) with hB
  have hBB : B * Bi = 1 := by rw [hB, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM : ∀ i j, ε * (Bi * I.fmat x * B) i j ∈ IntAf I.F I.E := by
    intro i j
    have := hx i j
    rwa [Units.val_mul, Units.val_mul] at this
  have key : Bi *ᵥ ((I.fmat x - 1) *ᵥ y) = (Bi * I.fmat x * B) *ᵥ (Bi *ᵥ y) - Bi *ᵥ y := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Bi * I.fmat x), hBB, Matrix.mul_one, Matrix.mul_sub,
      Matrix.mul_one, sub_mulVec]
  rw [mulVec_smul, key]
  generalize Bi *ᵥ y = z at hy ⊢
  show ε * ((Bi * I.fmat x * B) *ᵥ z - z) i ∈ IntAf I.F I.E
  rw [Pi.sub_apply, mul_sub]
  refine sub_mem ?_ (mul_mem hεi (hy i))
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem (hM i j) (hy j)

theorem sig_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (hxi : ∀ i j, ε * ((β₀⁻¹ * ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    sigA I ε • ((I.fmat x - 1) *ᵥ y) ∈ I.Lf := by
  rw [GlobalTheory.AdelicLattice.adelicLattice_selfDual]
  intro y' hy'
  have h1 := eps_mem I hβ hεi x⁻¹ hxi hy'
  have h2 := (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy _ h1
  have e : hAf I y' (sigA I ε • ((I.fmat x - 1) *ᵥ y)) = hAf I (ε • ((I.fmat x⁻¹ - 1) *ᵥ y')) y := by
    rw [hAf_smul_right, hAf_smul_left, sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, hAf_sub_right,
      hAf_sub_left, hAf_move]
  rw [e]
  exact h2

theorem mv_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (h1 : ∀ i j, (1 - ε - sigA I ε) * (I.fmat x - 1) i j = 0)
    (hx : ∀ i j, ε * ((β₀⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    (hxi : ∀ i j, ε * ((β₀⁻¹ * ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf := by
  set w := (I.fmat x - 1) *ᵥ y with hw
  have hxy : I.fmat x *ᵥ y = y + w := by
    rw [hw, sub_mulVec, one_mulVec]
    abel
  have h0 : (1 - ε - sigA I ε) • w = 0 := by
    funext i
    simp only [hw, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Finset.mul_sum, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_assoc, h1 i j, zero_mul]
  have hsplit : w = ε • w + sigA I ε • w + (1 - ε - sigA I ε) • w := by
    rw [← add_smul, ← add_smul, show ε + sigA I ε + (1 - ε - sigA I ε) = 1 by ring, one_smul]
  rw [hxy, hsplit, h0, add_zero, ← add_assoc]
  exact add_mem (add_mem hy (eps_mem I hβ hεi x hx hy)) (sig_mem I hβ hεi x hxi hy)

end GlobalTheory.SplitPairK

open GlobalTheory.SplitPairK in

theorem GlobalTheory.SplitPairK.mem_kset_of_split : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), ε * ε = ε → ε * Formalism.L2.SG.HidaSetting.sigA I ε = 0 → ε ∈ Formalism.MainNotions.S.IntAf I.F I.E → ∀ (k : I.Gf), (∀ i j, (1 - ε - Formalism.L2.SG.HidaSetting.sigA I ε) * (I.fmat k - 1) i j = 0) → (∀ i j, ε * ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (∀ i j, ε * ((β₀⁻¹ * ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → k ∈ I.Kset := by
  intro I β₀ hβ ε _ _ hεi k h1 h2 h3
  have h1' : ∀ i j, (1 - ε - sigA I ε) * (I.fmat k⁻¹ - 1) i j = 0 := by
    intro i j
    have e : I.fmat k⁻¹ - 1 = -(I.fmat k⁻¹ * (I.fmat k - 1)) := by
      rw [Matrix.mul_sub, fmat_inv_mul, Matrix.mul_one]
      abel
    rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum, neg_eq_zero]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [mul_left_comm, h1 l j, mul_zero]
  have h3' : ∀ i j, ε * ((β₀⁻¹ * ((k⁻¹⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ :
      GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈
      Formalism.MainNotions.S.IntAf I.F I.E := by
    simpa only [inv_inv] using h2
  show ((k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  intro y
  refine ⟨fun hy => mv_mem I hβ hεi k h1 h2 h3 hy, fun hy => ?_⟩
  have := mv_mem I hβ hεi k⁻¹ h1' h3 h3' hy
  rwa [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec] at this

end
