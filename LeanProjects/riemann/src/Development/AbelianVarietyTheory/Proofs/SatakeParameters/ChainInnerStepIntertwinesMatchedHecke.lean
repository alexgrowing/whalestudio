import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHeckeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevelsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainStepHecke

theorem haar_fd {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (t : T) (j : ℕ)
    (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · have := hM.νY t j h
    exact ⟨this.1.1, this.2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    have := hM.νY' t
    exact ⟨this.1.1, this.2⟩

theorem step_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P k, Good R t P → k + 1 < D.R.m → VacFix R.ψ (R.ωY t k) P → ∀ cS cT, Match R.ψ (R.ωY t k) P cS (dualC cT) → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P cT (U.1 v)) → ∀ v, (R.ioY t k U').1 v = hk _ P cS ((R.ioY t k U).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS t P k hG hkk hF cS cT hM U U' hU v
  classical
  have hθ : IsInfFam R.θ := hC.models.inf
  have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev).2.1 t P hG).1
  have hio := hC.chain.ioY t k (by omega)
  obtain ⟨hνH, hνF⟩ := haar_fd R hC.models t (k + 1) hkk
  obtain ⟨hμH, hμF⟩ := haar_fd R hC.models t k (by omega)
  have lo : ∀ j, j < D.R.m → (∀ κ ∈ hyp (Yc D j) P, κ ∈ levG _ (R.βY j) (R.datYt t j R.triv) ∧
        levChi _ (R.βY j) (R.datYt t j R.triv) κ = 1) ∧
      ∀ c, ∀ U ∈ Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)),
        postOn (R.MY j) (hk _ P c) U ∈ Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv)) (levChi _ (R.βY j) (R.datYt t j R.triv)) := by
    intro j hj
    obtain ⟨c, hb⟩ := hC.lev.βY j hj
    have h := GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D j) (R.βY j) (R.ΛY j) _ (R.datYt t j R.triv) hb P (by
      rw [Nat.cast_pow]
      exact fun h => hN (P.isPrime.mem_of_pow_mem _ h)) hG
    exact ⟨h.1, fun c U hU => h.2.2.2.2 _ R.θ (R.MY j) c hθ U hU⟩

  have hwm := (lo k (by omega)).2 cS _ ((mem_multT R.θ _ _ _ _).1 (R.ioY t k U).2)
  let w : R.CC t k := ⟨PiTensorProduct.lift (postOn (R.MY k) (hk _ P cS) (PiTensorProduct.lift.symm (R.ioY t k U).1)),
    (mem_multT R.θ _ _ _ _).2 (by simpa using hwm)⟩
  have hw : ∀ x, w.1 x = hk _ P cS ((R.ioY t k U).1 x) := by
    intro x
    have : w.1 = (hk _ P cS) ∘ₗ (R.ioY t k U).1 := PiTensorProduct.ext (MultilinearMap.ext fun y => by
      simp [w, postOn_apply])
    rw [this]; rfl
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT R.θ _ _ _ _).1 U.2)
  have key : ∀ φ x, (R.ioY t k U').1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) = w.1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) := by
    intro φ x
    have hvac := (GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t P hG).1 k hkk φ
    have e' : (R.ioY t k U').1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) =
        Lift.liftInt (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k φ) (U'.1 (PiTensorProduct.tprod ℂ x)) :=
      funext fun g => (hio.eq U' φ _ g).symm
    have e : (R.ioY t k U).1 (R.ItY k φ (PiTensorProduct.tprod ℂ x)) =
        Lift.liftInt (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k φ) (U.1 (PiTensorProduct.tprod ℂ x)) :=
      funext fun g => (hio.eq U φ _ g).symm
    have haut : IsAutFunSm R.θ _ (U.1 (PiTensorProduct.tprod ℂ x)) := by simpa using hmap.aut x
    have hcusp : IsCuspFun _ (U.1 (PiTensorProduct.tprod ℂ x)) := by simpa using hmap.cusp x
    have hlev : ∀ κ ∈ levS _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv), ∀ g, U.1 (PiTensorProduct.tprod ℂ x) (g * κ) =
        levChi _ (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) κ * U.1 (PiTensorProduct.tprod ℂ x) g := by
      simpa using hmap.lev x
    rw [hw, e', e, hU]
    refine GlobalTheory.T.thetaIntegral_vacuum_intertwines_sphericalHecke R.ψ _ _ _ _ (R.ωY t k) P (hC.chain.ωY t k hkk) _ _ hνH hνF hF cS cT hM _ hvac _ haut.left ?_ ?_
    · intro κ hκ h
      obtain ⟨h1, h2⟩ := (lo (k + 1) hkk).1 κ hκ
      rw [hlev κ h1, h2, one_mul]
    · intro g y hy
      refine hI _ _ R.θ R.ψ _ _ (R.ωY t k) hθ (hC.chain.ωY t k hkk) _ _ hνH hνF _ (rTr _ y (U.1 (PiTensorProduct.tprod ℂ x))) hvac.1
        (GlobalTheory.SphericalOps.isAutFunSm_rTr hy haut) ?_ g
      intro r C hC' μ 𝓕 hμ h𝓕 g'
      simp only [rTr, mul_assoc]
      exact hcusp r C hC' μ 𝓕 hμ h𝓕 (g' * y)
  obtain ⟨φ, x, hx⟩ : ∃ φ x, R.ItY k φ (PiTensorProduct.tprod ℂ x) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (hC.chain.ItY t k hkk).ne (LinearMap.ext fun φ => PiTensorProduct.ext (MultilinearMap.ext fun x => ?_))
    simpa using h φ x
  have h0 := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY k) _ _ _ _ hθ hμH hμF (hS.1 t k (by omega)) (R.ioY t k U' - w).1 (R.ioY t k U' - w).2 _ hx
    (by simp [key φ x])
  have h1 : (R.ioY t k U').1 = w.1 := sub_eq_zero.1 h0
  rw [h1, hw]

end GlobalTheory.ChainStepHecke
