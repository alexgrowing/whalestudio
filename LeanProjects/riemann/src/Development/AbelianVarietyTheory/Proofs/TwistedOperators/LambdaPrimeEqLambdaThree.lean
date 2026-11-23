import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAdjointAtLiftEqLowestKTypeRestriction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateLiftLinearIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThGEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GWEqChiSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtVMemLevSubVOfLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.LamPrimeTransport

open Formalism.IndefR.RecTie

section ScaleIP

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isMultiplicityInner_smul_measure_iff (M : DSModel V S) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ)
    (hc : 0 < c) (k : ℂ) :
    IsMultIP M (ENNReal.ofReal c • ν) 𝓕 T T' ((c : ℂ) * k) ↔ IsMultIP M ν 𝓕 T T' k := by
  have hc0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  have hcT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold IsMultIP
  refine forall_congr' fun v => forall_congr' fun v' => ?_
  simp only [IntegrableOn, Measure.restrict_smul, integrable_smul_measure hc0 hcT, integral_smul_measure,
    ENNReal.toReal_ofReal hc.le, Complex.real_smul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, mul_left_cancel₀ hcC ?_⟩
    rw [h2, mul_assoc]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2, mul_assoc]

theorem exists_vec_ne (M : DSModel V S) : ∃ v : M.Vec, ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ ≠ 0 := by
  have hu : ∀ τ, ∃ x : M.sm τ, x ∈ lowT M τ ∧ x ≠ 0 := fun τ =>
    Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.LowTypeRestriction.lowT_ne_bot M τ)
  choose u _ hu2 using hu
  refine ⟨u, Finset.prod_ne_zero_iff.2 fun τ _ => ?_⟩
  rw [Ne, inner_self_eq_zero]
  intro h
  exact hu2 τ (Subtype.ext h)

theorem ipM_smul_meas (M : DSModel V S) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ)
    (hc : 0 < c) : ipM M (ENNReal.ofReal c • ν) 𝓕 T T' = (c : ℂ) * ipM M ν 𝓕 T T' := by
  obtain ⟨v, hv⟩ := exists_vec_ne M
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  by_cases h : ∃ k, IsMultIP M ν 𝓕 T T' k
  · have h2 : IsMultIP M (ENNReal.ofReal c • ν) 𝓕 T T' ((c : ℂ) * ipM M ν 𝓕 T T') :=
      (isMultiplicityInner_smul_measure_iff M ν 𝓕 T T' c hc _).2 (ipM_spec M ν 𝓕 T T' h)
    exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, h2⟩) h2
  · have h' : ¬ ∃ k, IsMultIP M (ENNReal.ofReal c • ν) 𝓕 T T' k := by
      rintro ⟨k, hk⟩
      apply h
      refine ⟨k / c, (isMultiplicityInner_smul_measure_iff M ν 𝓕 T T' c hc _).1 ?_⟩
      rwa [mul_div_cancel₀ _ hcC]
    unfold ipM
    rw [dif_neg h, dif_neg h', mul_zero]

end ScaleIP

end GlobalTheory.LamPrimeTransport

namespace GlobalTheory.LamPrimeTransport

open Formalism.IndefR.RecTie

section Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem ipWc_lift (R : RealDat D A Ks) (hW : R.models_HW) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m)
    (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)) (i : Fin D.R.m) (a b : (R.HW i (sg0 D A)).H) :
    (toLiftReal R F tupT hm hTop hinj).ipWc i (PiTensorProduct.lift ((R.HW i (sg0 D A)).e a))
      (PiTensorProduct.lift ((R.HW i (sg0 D A)).e b)) = (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪a, b⟫_ℂ := by
  have e1 : (toLiftReal R F tupT hm hTop hinj).measW i = ENNReal.ofReal (RealDat.nP F false)⁻¹ • R.νW i := rfl
  have e2 : ∀ τ, (toLiftReal R F tupT hm hTop hinj).κ i τ = kapAt (Wc D i) (sg0 D A) τ := fun _ => rfl
  rw [LiftReal.ipWc, e1]
  simp only [e2]
  change (∏ τ, _) * ipMT (R.MW i (sg0 D A)) _ (R.fdW i) _ _ = _
  unfold ipMT
  erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  rw [
    ipM_smul_meas _ _ _ _ _ _ (inv_pos.2 (RealDat.nP_pos false)), (hW i (sg0 D A)).2.2 a b, ipAt]
  have hP : ∀ (P P' c I : ℂ), P = P' → P * (c * I) = c * (P' * I) := fun P P' c I h => by rw [h]; ring
  exact hP _ _ _ _ rfl

theorem ipVia_self' {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · have h1 : h.1.choose = u := he h.1.choose_spec
    have h2 : h.2.choose = v := he h.2.choose_spec
    rw [h1, h2]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h

set_option maxHeartbeats 1000000 in

theorem ipA_ext (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m)
    (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)) (μ : D.what₂.Tup) (i : Fin D.R.m)
    (a b : (R.HV i (tupT μ)).H) :
    (toLiftReal R F tupT hm hTop hinj).ipA μ i (R.extV i (tupT μ) a) (R.extV i (tupT μ) b) =
      (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪a, b⟫_ℂ := by
  change (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ipVia (R.extV i (tupT μ)) _ _ = _
  rw [ipVia_self' _ (hinj i (tupT μ)) a b]

def pre (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m)
    (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)) (μ : D.what₂.Tup) (i : Fin D.R.m)
    (f : (toLiftReal R F tupT hm hTop hinj).Amt μ i) : (R.HV i (tupT μ)).H :=
  (LinearEquiv.ofInjective _ (hinj i (tupT μ))).symm (Submodule.inclusion inf_le_left f)

theorem ext_pre (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m)
    (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)) (μ : D.what₂.Tup) (i : Fin D.R.m)
    (f : (toLiftReal R F tupT hm hTop hinj).Amt μ i) :
    R.extV i (tupT μ) (pre R F tupT hm hTop hinj μ i f) = f.1 := by
  have h := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective (R.extV i (tupT μ)) (hinj i (tupT μ)))
    (Submodule.inclusion inf_le_left f)
  exact congrArg Subtype.val h

theorem lift_postOn' {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (X : MMap M) :
    PiTensorProduct.lift (postOn M L X) = L ∘ₗ PiTensorProduct.lift X := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp [postOn]

set_option maxHeartbeats 4000000 in

theorem thetaP_read (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m)
    (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)) (hlev : R.toLevCh.Is A.μ0) (hgrp : R.IsGrp F)
    (hM : R.IsModels) (hE : R.IsThP) (IL : LiftIds (toLiftReal R F tupT hm hTop hinj))
    (hT : LiftTie (toLiftReal R F tupT hm hTop hinj) IL) (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m)
    (x : D.what₂.Mt μ ((i : ℕ) + 1)) :
    ((IL.jMj i (D.what₂.thetaP μ ((i : ℕ) + 1) x) : (toLiftReal R F tupT hm hTop hinj).Wc i) :
        (toLiftReal R F tupT hm hTop hinj).AmbW i) =
      PiTensorProduct.lift ((R.HW i (sg0 D A)).e (R.thG i (tupT μ) (pre R F tupT hm hTop hinj μ i (IL.jMt μ hμ i x)))) := by
  obtain ⟨w, hwM, hwK, hwW⟩ := GlobalTheory.ThetaFireLift.thetaFireL R F tupT hm hTop hinj hlev hgrp hM hE R.hv0 IL μ hμ i x
  have hth := hT.theta μ hμ i x w
    (GlobalTheory.ThetaPRead.isThetaP_toLiftReal R F tupT hm hTop hinj hE.thF μ i) hwM hwK hwW
  set z := pre R F tupT hm hTop hinj μ i (IL.jMt μ hμ i x) with hz
  let w' : (⨂[ℂ] τ, (R.MW i (sg0 D A)).sm τ) →ₗ[ℂ] (GA D (Wc D i) → ℂ) := w
  let U : MMap (R.MW i (sg0 D A)) := PiTensorProduct.lift.symm w'
  have hU : U ∈ R.Wall i (sg0 D A) :=
    GlobalTheory.HeckeParts.mult_le_triv _ ((mem_multT _ _ _ _ w').1 hwM)
  have hlow : ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, U (fun ρ => v ρ) = R.thF i (tupT μ) z (fun ρ => v ρ) := by
    intro v
    have e := LinearMap.congr_fun hwK (PiTensorProduct.tprod ℂ v)
    have e2 : w' (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) =
        PiTensorProduct.lift (R.thF i (tupT μ) z)
          (PiTensorProduct.map (fun τ => (lowT (R.MW i (sg0 D A)) τ).subtype) (PiTensorProduct.tprod ℂ v)) := by
      exact e.trans rfl
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod] at e2
    exact e2
  have hw0 : U - R.thF i (tupT μ) z = 0 :=
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D _ _ (R.MW i (sg0 D A)) R.θ hM.inf
      (GlobalTheory.LowTypeRestriction.lowT_ne_bot _) _ _ _ (Submodule.sub_mem _ hU (hE.thF_mem i (tupT μ) z)) (fun v => by
        show U (fun ρ => v ρ) - R.thF i (tupT μ) z (fun ρ => v ρ) = 0
        rw [hlow v, sub_self])
  have hUw : PiTensorProduct.lift U = w' := LinearEquiv.apply_symm_apply _ w'
  refine hth.trans ?_
  change R.eWf i (sg0 D A) ∘ₗ w' = _
  rw [← hUw, sub_eq_zero.1 hw0, ← lift_postOn', ← hE.thG i (tupT μ) z]

end Read

end GlobalTheory.LamPrimeTransport

namespace GlobalTheory.LamPrimeTransport

theorem adjoint_eigen {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (Θ : E →ₗ[ℂ] F) (S : E →ₗ[ℂ] E) (U : F →ₗ[ℂ] F) (hS : ∀ x, ‖S x‖ = ‖x‖) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (hΘ : ∀ x, Θ (S x) = U (Θ x)) {c : ℂ} {w : F} (hw : U w = c • w) :
    S (LinearMap.adjoint Θ w) = c • LinearMap.adjoint Θ w := by
  let Si : E →ₗᵢ[ℂ] E := { toLinearMap := S, norm_map' := hS }
  let Ui : F →ₗᵢ[ℂ] F := { toLinearMap := U, norm_map' := hU }
  have hsurj : Function.Surjective S := LinearMap.injective_iff_surjective.mp Si.injective
  apply ext_inner_right ℂ
  intro y
  obtain ⟨y', rfl⟩ := hsurj y
  have h1 : ⟪S (LinearMap.adjoint Θ w), S y'⟫_ℂ = ⟪LinearMap.adjoint Θ w, y'⟫_ℂ := Si.inner_map_map _ _
  have h2 : ⟪U w, U (Θ y')⟫_ℂ = ⟪w, Θ y'⟫_ℂ := Ui.inner_map_map _ _
  rw [inner_smul_left, h1, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hΘ, ← h2, hw,
    inner_smul_left]

set_option maxHeartbeats 400000 in

theorem adjoint_mem_levSubV {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hLev : R.toLevCh.Is A.μ0)
    (hMod : R.IsModels) (hThP : R.IsThP) (hgr : R.grp_record) (hv : A.v0 = InfinitePlace.mk D.what₂.embLL)
    (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (w : (R.HW i (sg0 D A)).H)
    (hw : (R.HW i (sg0 D A)).e w ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P.conj))
      (levChi _ (R.βW i) (R.datWp i P.conj))) :
    R.extV i t (LinearMap.adjoint (R.thG i t) w) ∈ RecTie.levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (RecTie.datVP R i t P))
      (levChi _ (R.βV i) (RecTie.datVP R i t P)) := by
  apply GlobalTheory.extV_mem_levSubV_of_lift R i t P
  intro g0 κ hκ h
  have hT := GlobalTheory.translate_lift_linear_isometry R hLev hMod i t g0.1 κ hκ
  rcases hT with ⟨S, hSn, hSe⟩
  have hL := (GlobalTheory.StepLifts.lifts_exist R hLev i).2 g0.1
  rcases hL with ⟨κ', hκ'⟩
  have hB := GlobalTheory.ThetaGoodEquiv.thG_equiv R hLev hMod hThP hgr hv i t g0.1 κ κ' hκ hκ' S hSe
  have hCw := GlobalTheory.FormEigenW.gW_eq_chi_smul R hLev hMod i (sg0 D A) P.conj w hw ⟨g0.1, g0.2⟩
  have hU : ∀ x, ‖R.gW i (sg0 D A) (R.eG.symm g0.1) x‖ = ‖x‖ :=
    GlobalTheory.gW_norm_eq R hMod.HW hMod.gW hMod.νW i _ _
  have hE := adjoint_eigen (R.thG i t) S _ hSn hU hB hCw
  have e1 := congrFun (congrArg (R.extV i t) hE) h
  have e2 := hSe (LinearMap.adjoint (R.thG i t) w) h
  have e3 : R.extV i t (((P.conj.chi ⟨g0.1, g0.2⟩ : ℂˣ) : ℂ) • LinearMap.adjoint (R.thG i t) w) h =
      ((P.conj.chi ⟨g0.1, g0.2⟩ : ℂˣ) : ℂ) • R.extV i t (LinearMap.adjoint (R.thG i t) w) h :=
    congrFun ((R.extV i t).map_smul _ _) h
  have hc : ((P.conj.chi ⟨g0.1, g0.2⟩ : ℂˣ) : ℂ) = (((P.chi g0 : ℂˣ) : ℂ))⁻¹ := by
    change (((P.chi⁻¹) g0 : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hlc : levChi _ (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := levChi_ne_zero _ _
  have e4 := e2.symm.trans (e1.trans e3)
  exact (smul_inv_smul₀ hlc _).symm.trans ((congrArg (levChi _ (R.βV i) (flagL (R.datVt i t)) κ • ·) e4).trans
    (congrArg (fun c : ℂ => levChi _ (R.βV i) (flagL (R.datVt i t)) κ • (c • R.extV i t (LinearMap.adjoint (R.thG i t) w) h)) hc))

set_option maxHeartbeats 1000000 in

theorem adjoint_mem_base_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Published.CuspRapidDecay → R.WeakCharacterisation F → R.toRealDat.ExAt → R.PGEquiv F → ∀ (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R.toRealDat) (hinj : ∀ i t, Function.Injective (R.toRealDat.extV i t)) (i : Fin D.R.m) (w : (R.HW i (sg0 D A3.A)).H), PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e w) ∈ (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj).Wc i → R.toRealDat.extV i (tupT D.what₂.mu0) (LinearMap.adjoint (R.thG i (tupT D.what₂.mu0)) w) ∈ (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj).Amt D.what₂.mu0 i := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F _hCusp hC hEx _hPG tupT hm hTop hinj i w hw
  have hLev := hC.base.lev
  have hMod := hC.base.models
  have hThP : R.toRealDat.IsThP := RealDat.thP_of_weak hC.base.thP hEx
  have hv : A3.A.v0 = InfinitePlace.mk D.what₂.embLL := R.hv0
  refine ⟨LinearMap.mem_range_self _ _, ?_⟩
  have hw' : PiTensorProduct.lift ((R.HW i (sg0 D A3.A)).e w) ∈ (Mult.goodPart R.θ (R.MW i (sg0 D A3.A))
      (levS _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A)))) (R.eWf i (sg0 D A3.A))).map
      (PiTensorProduct.lift : MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap := hw
  have hwM : (R.HW i (sg0 D A3.A)).e w ∈ Mult R.θ (R.MW i (sg0 D A3.A))
      (levS _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A)))) := by
    obtain ⟨X, hX, hXe⟩ := Submodule.mem_map.1 hw'
    have hXw : X = (R.HW i (sg0 D A3.A)).e w := PiTensorProduct.lift.injective hXe
    rw [← hXw]
    exact Mult.goodPart_le _ _ _ _ _ hX
  rw [GlobalTheory.Proof.LevelCharacterConjugate.liftLevel_fixedEmbedding_eq_conj_rowLevel R.toRealDat F.lv2 false hv] at hwM
  exact adjoint_mem_levSubV R.toRealDat hLev hMod hThP hC.base.grp.record hv i (tupT D.what₂.mu0) _ w hwM

end GlobalTheory.LamPrimeTransport

namespace GlobalTheory.LamPrimeTransport

open Formalism.IndefR.RecTie

end GlobalTheory.LamPrimeTransport

end
