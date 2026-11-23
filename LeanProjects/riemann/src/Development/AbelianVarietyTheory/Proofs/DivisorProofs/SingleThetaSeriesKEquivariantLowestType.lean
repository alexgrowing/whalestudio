import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsActFockVectorsAnyDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicRightTranslateFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtEqInfMat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.SeriesKEquiv

theorem singleSeries_kEquiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (Q' : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q' Ω φ' → ∀ (h : GA D (Vc D i)) (y : (R.cV i).W) (g0 : G) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y (Function.update v τ u)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y v)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK Q' Ω φ' hφ' h y g0 τ k hk v u hu
  have hθ : IsInfFam R.θ := hR.models.inf
  have hω := hR.thP.ωP

  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' := by
    obtain ⟨⟨hψ, h0⟩, e, -, hth⟩ := hφ'
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ hth h0.theta
  have hvφ : ∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ
      (cplxO 1 (cart (R.MW i (sg0 D A)) ρ)) φ' := by
    intro ρ
    obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hφ'
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf ho.conj.infPart_eq ho.conj.conj.infPart_eq hth hv.theta
      hthφ (hv.fock ρ)

  have hthv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i A.μ0) := by
    obtain ⟨⟨hψ, h0⟩, e, -, hth⟩ := hR.thP.vP i A.μ0
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ hth h0.theta
  have hvv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hR.thP.vP i A.μ0) hthv
  have hBS : ∀ ρ, (R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ = 1 := fun ρ =>
    GlobalTheory.JointHarm.onb_eq_one (hR.models.BV i ρ)
  have hBu : ∀ ρ, IsUnit (R.BV i ρ) := fun ρ => IsUnit.of_mul_eq_one_right _ (hBS ρ)
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hR.models.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ ρ, ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := fun ρ =>
    (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i ρ).rank.1.trans hrk.symm
  have hfr : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹ = 1 := fun ρ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))

  have hIT := GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T0 R.toLevCh A.μ0 hR.lev i A.μ0
  obtain ⟨n, hn, ho⟩ := hK.fin
  have hχ0 : ∀ ρ, HasInfExp D χ ρ 0 := fun ρ => GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ hK.chr hn ho ρ
  have h1 : ∀ ρ, HasInfExp D (R.mu0 ((i : ℕ) + 1)) ρ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ) := fun ρ => by
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hR.lev.mu0 i)
      (GlobalTheory.PairInfTypes.hasInfQ_tauE D (R.toLevCh.C.isMu0 i).inf) ρ
    simpa only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] using h
  have hcV : ∀ ρ, HasInfExp D (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1 ρ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ) :=
    fun ρ => by
      have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (h1 ρ) (hχ0 ρ)
      rw [add_zero] at this
      exact this
  have hcW : ∀ ρ, HasInfExp D (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ρ
      (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ - 1 / 2) := fun ρ => by
    rw [sub_eq_add_neg]
    exact GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hcV ρ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hIT ρ).eta)

  have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (GlobalTheory.JointHarm.conj_mem_UH (R.MW i (sg0 D A)) τ hk)
  have e : (fun ρ => (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
      (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹) = Pi.mulSingle τ k := by
    funext ρ
    rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hs.2.1, Pi.mulSingle_eq_same]
      calc _ = ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) * k *
            ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
    · rw [hs.2.2 ρ hρ, Pi.mulSingle_eq_of_ne hρ, Matrix.mul_one, hfr]
  have e' : (fun ρ => (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ) = 1 := by
    funext ρ
    rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ))]
    rfl
  have hKk : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
      (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ) := fun ρ => by
    rw [congrFun e ρ]
    by_cases hρ : ρ = τ
    · subst hρ; rwa [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hρ]; exact GlobalTheory.JointHarm.one_mem_K

  have aω := (GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ ω _ (R.MW i (sg0 D A)) (R.BV i) hK.weil hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _ hcV hcW x₁ x₂ x₃
    (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1) (fun ρ => (hx ρ).2.2.1) φ' hthφ hvφ 1 (one_mem _) _ hs.1 hKk).2
  have av := (GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) _ (R.MW i (sg0 D A)) (R.BV i) (hω i A.μ0) hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _ (fun ρ => (hIT ρ).chiV) (fun ρ => (hIT ρ).chiW)
    x₁ x₂ x₃ (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1) (fun ρ => (hx ρ).2.2.1) _ hthv hvv 1 (one_mem _) _ hs.1 hKk).2
  rw [e, e'] at aω av

  have hcVI : ∀ ρ, IsCartanInv (gramAt D (Vc D i) ρ)
      ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) ρ) := fun ρ => by
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ)
    have h1' := Matrix.mul_nonsing_inv _ hu'
    have hG : gramAt D (Vc D i) ρ = ((R.BV i ρ)⁻¹)ᴴ * (R.BV i ρ)⁻¹ := by
      calc gramAt D (Vc D i) ρ
          = ((R.BV i ρ)⁻¹)ᴴ * ((R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ) * (R.BV i ρ)⁻¹ := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1', Matrix.conjTranspose_one,
              Matrix.one_mul, Matrix.mul_assoc, h1', Matrix.mul_one]
        _ = _ := by rw [hBS ρ, Matrix.mul_one]
    refine ⟨Matrix.one_mul _, by simp, ?_⟩
    rw [Matrix.mul_one, hG]
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 (hBu ρ)))
  have hne : R.vP i A.μ0 ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βW i))
      (hrk.trans_le (r_le_V i)) (hR.thP.vP i A.μ0)
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hω i A.μ0).std hθ
    (fun _ => 1) (R.BV i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ hcVI
    (fun ρ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ ρ) (hR.models.BV i)
    (fun ρ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ ρ _ (hR.models.order i ρ))
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) hthv hvv hne

  have key := (hR.thP.ioP i A.μ0).2.1 τ k hk v u hu y
  unfold RealDat.ptP at key
  rw [av] at key
  have hfa := hinj key

  have hA := aω (R.ioP i (PiTensorProduct.tprod ℂ v) y)
  rw [hfa] at hA
  have hser : singleSeries R i ω φ' h y (Function.update v τ u) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (singleSeries R i ω φ' h y v) := by
    funext g
    simp only [singleSeries, Datum.thetaKO, Formalism.L2.Theta.rTr]
    rw [← hA, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [hser]
  funext g
  simp only [Formalism.IndefR.Links.actL, LinearMap.coe_mk, AddHom.coe_mk, Formalism.L2.Theta.rTr]
  by_cases hl : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) κ
  · have hc := GlobalTheory.FinTranslate.comm_fin_real (Wc D i) hl.choose_spec.1
      (GlobalTheory.FinTranslate.atTau_mem R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
    simp only [actG0, dif_pos hl, Formalism.L2.Theta.rTr]
    rw [mul_assoc g, hc, ← mul_assoc]
  · simp only [actG0, dif_neg hl, Pi.zero_apply]

end GlobalTheory.SeriesKEquiv

end
