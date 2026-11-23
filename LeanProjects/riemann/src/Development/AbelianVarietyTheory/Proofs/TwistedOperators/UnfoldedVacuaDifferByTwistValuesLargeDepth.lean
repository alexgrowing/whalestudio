import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacuumBasePointFamilyEveryTupleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuplesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistCharacterMemTwistFiniteValueProductSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingJointDataTwistRatioAtDetRootsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVacTw

theorem circ_id (A B A' B' : Circle) : A'⁻¹ * B' = (A⁻¹ * B) * ((A' * A⁻¹)⁻¹ * (B' * B⁻¹)) := by
  apply Circle.ext
  have := Circle.coe_ne_zero A
  have := Circle.coe_ne_zero B
  have := Circle.coe_ne_zero A'
  have := Circle.coe_ne_zero B'
  simp only [Circle.coe_mul, Circle.coe_inv]
  field_simp

set_option maxHeartbeats 1600000 in

theorem vacTw : Big fun ch => VacTw ch := by
  obtain ⟨C, h⟩ := Big.and (Big.and GlobalTheory.T.exists_vacuumBasePointFamily_every_tuple GlobalTheory.T.vacuumBasePoint_unique_all_tuples) (Big.and GlobalTheory.T.twistCharacter_mem_twistFiniteValueProductSubgroup GlobalTheory.T.unfoldingJointData_twist_ratio_at_detRoots)
  refine ⟨C, fun ε CF hC => ?_⟩
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨⟨hex, hun⟩, hxv, hcon⟩ := h D large₂ he hx Γ Pl0 T A Ks R F s ch hi ha
  have hL := s.core.lev
  classical
  let xr : ∀ k, GA D (ch.G.V (.grid D.R.m k)) → (AE D)ˣ := fun k g => (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose
  have hxr : ∀ k g, IsDetRoot _ g (xr k g) := fun k g => (GlobalTheory.RecDict.exists_isDetRoot D _ g).choose_spec
  let bb : T → Pts ch.G := fun t => (hex t).choose
  have hbb : ∀ t, IsBase t ch.S.B (bb t) := fun t => (hex t).choose_spec
  let w : T → ℕ → Circle := fun t j =>
    (R.toLevCh.xi t (xr j (bb t j)))⁻¹ * R.toLevCh.xi t (xr (j + 2) (bb t (j + 2)))
  refine ⟨hex, fun t j => Circle.toUnits (w t j), fun t j => ?_, ?_⟩
  · simp only [w, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hxv t _)) (hxv t _)
  intro t t' M M' hM hM' b b' hb hb' P p hp j hj hjm
  have e1 : b = bb t := hun t t b (bb t) hb (hbb t)
  have e2 : b' = bb t := hun t' t b' (bb t) hb' (hbb t)
  have e3 : bb t' = bb t := hun t' t _ _ (hbb t') (hbb t)
  subst e1 e2
  have hfin : ∀ k, ∃ y : (AE D)ˣ, finPart D (y : AE D) = 1 ∧ IsDetRoot _ (p k) y := fun k =>
    GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ (p k) (hp.1 k) _ (hxr k (p k))
  choose y hy1 hy using hfin
  have hx : ∀ k, IsDetRoot _ ((p * bb t) k) (y k * xr k (bb t k)) := fun k =>
    GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ (hy k) (hxr k (bb t k))
  have hm2 := D.R.two_le_m
  have hmi : D.R.m ∉ idx D := fun h' => by
    simp only [idx, List.mem_range'_1] at h'
    omega
  have hm : (p * bb t) D.R.m = 1 := by
    rw [Pi.mul_apply, hp.2 _ hmi, (hbb t).2.2 _ (by omega) hmi, one_mul]
  rw [hcon t t' M M' hM hM' P (p * bb t) _ hx hm j hj hjm, smul_smul]
  congr 1
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  obtain ⟨n', hn0', hn'⟩ := hL.xi_fin t'
  have h1 : ∀ k, R.toLevCh.xi t (y k) = 1 := fun k => GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (hy1 k)
  have h1' : ∀ k, R.toLevCh.xi t' (y k) = 1 := fun k => GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t') hn0' hn' _ (hy1 k)
  have hw : w t' j = w t j * (((R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (y j * xr j (bb t j)))⁻¹ *
      (R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (y (j + 2) * xr (j + 2) (bb t (j + 2)))) := by
    simp only [w, e3, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, h1, h1', inv_one, one_mul]
    exact circ_id _ _ _ _
  show ((Circle.toUnits (w t' j) : ℂˣ) : ℂ) = ((Circle.toUnits (w t j) : ℂˣ) : ℂ) * _
  rw [hw, map_mul, Units.val_mul]
  rfl

end GlobalTheory.RowVacTw

end
