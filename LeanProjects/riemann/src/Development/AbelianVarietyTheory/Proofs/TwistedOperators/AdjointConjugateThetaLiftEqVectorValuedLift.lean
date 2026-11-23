import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLiftFormsFiniteGroupAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLiftDatumOfConjugateLiftDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOfClassSums
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralGoodProjectorMovePeterssonStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExtendRestrictionFinitePointsEqStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAdjoint

theorem inner_eq_integral {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hH : R.models_HW)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (a b : (R.HW i σ).H) :
    inner ℂ a b = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) *
      ∫ g in R.fdW i, star ((R.HW i σ).e a (fun ρ => v ρ) g) * (R.HW i σ).e b (fun ρ => v ρ) g ∂(R.νW i) := by
  obtain ⟨-, -, hip⟩ := hH i σ
  have hc := ipM_spec (R.MW i σ) (R.νW i) (R.fdW i) _ _
    (GlobalTheory.LiftLower.IsMultIP₂ (R.HW i σ) (N := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) hip a b)
  rw [hip, ipAt, (hc (fun ρ => v ρ) (fun ρ => v ρ)).2]
  congr 1
  rw [Finset.prod_eq_one, mul_one]
  intro ρ _
  rw [inner_self_eq_norm_sq_to_K, hv ρ]
  simp

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint

theorem integrableOn_theta {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hI : GlobalTheory.LiftRows.InnerProductFormulaC R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (hL : GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io)
    (hM : IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0))
    (U : MMap (R.MW i σ)) (hU : U ∈ R.Wall i σ) (v : ∀ ρ, lowT (R.MW i σ) ρ) (h : GA D (Vc D i))
    (Q : PolF D (Wc D i).rank (Vc D i).rank) :
    IntegrableOn (fun g => Datum.thetaKO ω h g (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f Q) * starRingEnd ℂ (U (fun ρ => v ρ) g))
      (R.fdW i) (R.νW i) := by
  obtain ⟨μ, 𝓧, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (Vc D i) (Wc D i)
  obtain ⟨⟨Fr, hFr⟩, h2⟩ := (hL.1.models.νW i).1.2.2 R.θ hL.1.models.inf
  obtain ⟨mR, hmR⟩ := (h2 Fr hFr).1
  exact (hI i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL _ _ hM μ 𝓧 hμ Fr hFr mR hmR U hU U hU v v Q Q).1 h

end GlobalTheory.ConjAdjoint

namespace GlobalTheory.ConjAdjoint
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

set_option maxHeartbeats 400000 in

theorem adjoint_eq_upLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (th : H.H →ₗ[ℂ] (R.HW i σ).H),
  Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP →
  GlobalTheory.GalLift.IsProjOf R i σ thP th →
  ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W),
    inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hX hS hI hF hZ hR i σ s m μ' η' ω B f₀ f c io H hL hM hy hH v hv thP th hT hP y h w

  have hC : GlobalTheory.Hk3.Core R F := hL.1
  have hω := hL.2.2.2.2.2.1
  have hpt := hL.2.2.2.2.2.2.2.2.1
  have hc : c.Is := hL.2.2.2.2.2.2.2.2.2.1
  have hio := hL.2.2.2.2.2.2.2.2.2.2
  have hKc : starRingEnd ℂ (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun ρ _ => map_ratCast _ _
  let φ : c.W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := GlobalTheory.AdelicScalar.ptL R i σ B f (io (PiTensorProduct.tprod ℂ v))
  have hφ : ∀ w, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) (φ w) := fun w => hpt _
  have hinf : ∀ u ∈ GinfC (Vc D i), ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w) := fun u hu w => hio.1 u hu _ w
  have hlev : ∀ κ ∈ Lev.levA (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)), ∀ w,
      ω (κ, 1) (φ w) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) κ)⁻¹ • φ w :=
    fun κ hκ w => hS i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io hL κ hκ _
  have hWall : ∀ y' : (R.HW i σ).H, (R.HW i σ).e y' ∈ R.Wall i σ := fun y' =>
    GlobalTheory.AdelicScalar.HMod_mem (hC.models.HW i σ) y'
  have hth : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) *
      starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g)) (R.fdW i) (R.νW i) := fun y' w h =>
    integrableOn_theta R F hI i σ s m μ' η' ω B f₀ f c io hL hM _ (hWall y') v h (io (PiTensorProduct.tprod ℂ v) w)
  have hth' : ∀ y' : (R.HW i σ).H, ∀ w h, IntegrableOn (fun g => star (Datum.thetaKO ω h g (φ w)) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := fun y' w h => by
    have h1 := hth y' w h
    have h2 : IntegrableOn (fun g => starRingEnd ℂ (Datum.thetaKO ω h g (φ w) *
        starRingEnd ℂ ((R.HW i σ).e y' (fun ρ => v ρ) g))) (R.fdW i) (R.νW i) :=
      h1.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable h1.1) (Filter.Eventually.of_forall fun x => by simp)
    refine Integrable.congr h2 (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hcls : ∀ u g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j))) := by
    intro u g
    refine (hT.eq _ _ _).trans ?_
    exact GlobalTheory.AdelicScalar.theta_classSum hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev hM hy (GlobalTheory.AdelicScalar.HMod_mem hH u) g
  have hφw : ∀ w, φ w = ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w) := fun w => rfl
  clear_value φ
  have hex := GlobalTheory.AdelicScalar.exists_upVec hω c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) φ hφ hinf hlev (R.νW i) (R.fdW i)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ)) (hth _)
  have hΨ := hex.choose_spec.1
  have hlaw := hex.choose_spec.2
  have hzex := GlobalTheory.AdelicScalar.HMod_onto hH (GlobalTheory.AdelicScalar.upVec_mem c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw)
  have hz := hzex.choose_spec
  have hinv : ∀ u, ∀ γ ∈ GQ (Wc D i), ∀ g, thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) (γ * g) =
      thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g := by
    intro u γ hγ g
    refine (hcls u (γ * g)).trans (Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (hcls u g).symm)
    exact congrArg _ (GlobalTheory.T.thetaKO_mul_left_invariant_of_mem_GQ R i _ _ ω hω _ (hφ _) _ γ hγ g)
  have eF : ∀ u (y' : (R.HW i σ).H), (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e y' (fun ρ => v ρ) g) = fun g =>
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹ *
        (star (Datum.thetaKO ω (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j)) g
          (φ (H.e u ((R.B.L i A.μ0).pres.y j)))) * (R.HW i σ).e y' (fun ρ => v ρ) g) := by
    intro u y'
    funext g
    refine (congrArg (fun t => star t * (R.HW i σ).e y' (fun ρ => v ρ) g) (hcls u g)).trans ?_
    simp only [star_sum, Finset.sum_mul, star_mul', star_inv₀, star_natCast]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hintF : ∀ u (y' : (R.HW i σ).H), IntegrableOn (fun g => star (thP ((c.ext ∘ₗ H.e).rangeRestrict u)
      (PiTensorProduct.tprod ℂ v) g) * (R.HW i σ).e y' (fun ρ => v ρ) g) (R.fdW i) (R.νW i) := by
    intro u y'
    have hsum := integrable_finset_sum (μ := (R.νW i).restrict (R.fdW i)) Finset.univ fun j _ =>
      (hth' y' (H.e u ((R.B.L i A.μ0).pres.y j)) (GlobalTheory.AdelicScalar.finLift (Vc D i) ((R.B.L i A.μ0).pres.y j))).const_mul
        ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m)) ((R.B.L i A.μ0).pres.y j)) : ℂ))⁻¹
    exact hsum.congr (Filter.Eventually.of_forall fun g => (congrFun (eF u y') g).symm)
  have hpair : ∀ u, ∫ g in R.fdW i, star (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g) *
      (R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ) g ∂(R.νW i) = inner ℂ u hzex.choose := by
    intro u
    refine (congrArg (fun F => ∫ g in R.fdW i, F g ∂(R.νW i)) (eF u (GlobalTheory.LiftLower.projH R i σ y))).trans ?_
    refine (integral_finset_sum _ fun j _ => (hth' _ _ _).const_mul _).trans ?_
    refine Eq.trans ?_ (hH.2.2 u hzex.choose).symm
    refine Eq.trans ?_ (congrArg (Bridge.adInner _ _ _ (H.e u)) hz).symm
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (integral_const_mul _ _).trans (congrArg _ ?_)
    refine Eq.trans ?_ (inner_conj_symm _ _)
    refine Eq.trans ?_ (congrArg (starRingEnd ℂ) (hΨ _ _)).symm
    unfold GlobalTheory.AdelicScalar.l2 Lift.pet
    refine Eq.trans ?_ integral_conj
    refine congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) (funext fun g => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.star_def]
  have hadj : LinearMap.adjoint th y = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hzex.choose := by
    refine ext_inner_left ℂ fun u => ?_
    have e1 : (fun g => star ((R.HW i σ).e (th u) (fun ρ => v ρ) g) * (R.HW i σ).e y (fun ρ => v ρ) g) =
        fun g => star (R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict u) (PiTensorProduct.tprod ℂ v)) g) *
          (R.HW i σ).e y (fun ρ => v ρ) g :=
      funext fun g => congrArg (fun t : GA D (Wc D i) → ℂ => star (t g) * (R.HW i σ).e y (fun ρ => v ρ) g) (hP u v)
    refine (LinearMap.adjoint_inner_right th u y).trans ?_
    refine (inner_eq_integral R hC.models.HW i σ v hv (th u) y).trans ?_
    refine Eq.trans ?_ (inner_smul_right _ _ _).symm
    refine congrArg _ (Eq.trans ?_ (hpair u))
    refine (congrArg (fun F : GA D (Wc D i) → ℂ => ∫ g in R.fdW i, F g ∂(R.νW i)) e1).trans ?_
    exact GlobalTheory.T.integral_goodProjector_move_petersson R F hC hX i σ v _ (hinv u) (hintF u) y
  have e3 : c.ext (H.e (LinearMap.adjoint th y)) h = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) • hex.choose h := by
    refine (congrArg (fun x => c.ext (H.e x) h) hadj).trans ?_
    simp only [map_smul, Pi.smul_apply]
    exact congrArg _ ((congrArg (fun x => c.ext x h) hz).trans
      (GlobalTheory.T.extend_restriction_finitePoints_eq c hc (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) hex.choose hlaw h))
  refine (congrArg (fun a => inner ℂ a w) e3).trans ?_
  refine (inner_smul_left _ _ _).trans ?_
  refine congrArg₂ (· * ·) hKc ?_
  exact (hΨ h w).trans (congrArg (fun p => GlobalTheory.AdelicScalar.l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g p)
    ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) (fun ρ => v ρ))) (hφw w))

end GlobalTheory.ConjAdjoint
