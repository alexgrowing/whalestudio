import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLowestKTypeOfExtremalVectorCase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

noncomputable section

namespace GlobalTheory.RawLift.FockPair

open GlobalTheory.DefLift GlobalTheory.RawLift GlobalTheory.RawLift.RealLowRed Formalism.IndefR.FWT

variable {D : D7} {V W : HSp D} {S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {χV χW : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}

open Classical in
set_option maxHeartbeats 4000000 in

theorem pair_of_ext (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel W S') (hLS : LowSm M) (hLI : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M)
    (hω : IsWeilDatumO ψ V W χV χW ω) (hcv : IsCovolOne (ratL W V) μ 𝓕)
    (J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO V W → ℂ)) (hJ : ∀ v, IsThetaFunO ψ V W (J v))
    (hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) →
      J (Function.update v τ u) = ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (J v))
    (hX : ∀ v : (∀ ρ, lowT M ρ), IsExtVec M (fun ρ => (v ρ : M.sm ρ)) → ∀ u ∈ GinfC W,
      thetaIP μ 𝓕 (J v) (ω (1, u) (J v)) = thetaIP μ 𝓕 (J v) (J v) *
        ∏ ρ, ⟪((v ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) u) ((v ρ : M.sm ρ) : M.H ρ)⟫_ℂ) :
    ∃ N : ℂ, ∀ (v v' : ∀ ρ, lowT M ρ), ∀ g ∈ GinfC W, thetaIP μ 𝓕 (J v) (ω (1, g) (J v')) = N *
      ∏ ρ, ⟪((v ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v' ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
  have h1 : μ 𝓕 = 1 := hcv.2.2
  have hU : ∀ ρ, IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (M.rep ρ) := fun ρ =>
    (GlobalTheory.HolDict.ModelRep.model_rep D W S' M ρ).2.1
  have hXU : ∀ g ρ, infMat D.sp.cm.sig W.gram (θ ρ) g ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ) :=
    fun g ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W g ρ
  have hrep : ∀ ρ g h, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) (g * h)) =
      (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g)).comp (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) h)) :=
    fun ρ g h => by
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul]
      exact (hU ρ).1.2 _ (hXU g ρ) _ (hXU h ρ)
  have hrep1 : ∀ ρ, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) 1) = 1 := fun ρ => by
    rw [GlobalTheory.PointAtPlaceHom.infMat_one]
    exact (hU ρ).1.1
  have hωmul : ∀ g h f, ω (1, g) (ω (1, h) f) = ω (1, g * h) f := fun g h f => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

  have hA : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → ∀ ρ,
      (((Function.update v τ u ρ : lowT M ρ) : M.sm ρ) : M.H ρ) =
        M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) (atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)))
          ((v ρ : M.sm ρ) : M.H ρ) := by
    intro τ k hk v u hu ρ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D W τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D W τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D W τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D W τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ W τ hg
    by_cases c : ρ = τ
    · subst c
      rw [Function.update_self, hu, hs.2.1]
      unfold DSModel.rep
      rw [e2]
    · rw [Function.update_of_ne c, hs.2.2 ρ c, (hU ρ).1.1]
      rfl
  have hinv : ∀ ρ (a : GA D W) (y x : M.H ρ), ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y, x⟫_ℂ =
      ⟪y, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a) x⟫_ℂ := by
    intro ρ a y x
    let L : M.H ρ →ₗᵢ[ℂ] M.H ρ :=
      { toLinearMap := (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a)).toLinearMap,
        norm_map' := (hU ρ).2.1 _ (hXU a ρ) }
    have e : M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a) (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y) = y := by
      rw [← ContinuousLinearMap.comp_apply, ← hrep, mul_inv_cancel, hrep1]
      rfl
    calc ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y, x⟫_ℂ
        = ⟪L (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y), L x⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪y, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a) x⟫_ℂ := by
        rw [show L (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y) = y from e]
        rfl

  obtain ⟨e0, he0⟩ := exists_isExtVec M hLS
  let e : ∀ ρ, lowT M ρ := fun ρ => ⟨e0 ρ, (he0 ρ).2.1⟩
  have hext : IsExtVec M (fun ρ => (e ρ : M.sm ρ)) := he0
  have hne : ∀ ρ, e ρ ≠ 0 := fun ρ h => by
    have h' := (he0 ρ).1
    have h0 : ((e0 ρ : M.sm ρ) : M.H ρ) = 0 := by
      have := congrArg (fun x : lowT M ρ => ((x : M.sm ρ) : M.H ρ)) h
      simpa [e] using this
    rw [h0, norm_zero] at h'
    exact zero_ne_one h'

  have st1 : ∀ v', ∀ g ∈ GinfC W, thetaIP μ 𝓕 (J e) (ω (1, g) (J v')) = thetaIP μ 𝓕 (J e) (J e) *
      ∏ ρ, ⟪((e ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v' ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
    intro v'
    have key := GlobalTheory.DefLift.mem_of_translates hLS hLI
      (thR hω h1 J hJ (J e) (hJ e) - thetaIP μ 𝓕 (J e) (J e) • prodR θ M (fun ρ => ((e ρ : M.sm ρ) : M.H ρ)))
      (offReal W) e hne ?_ ?_ v'
    · intro g hg
      have := key g hg
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodR_apply, thR_apply] at this
      exact sub_eq_zero.1 this
    · intro g hg
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodR_apply, thR_apply]
      exact sub_eq_zero.2 (hX e hext g hg)
    · intro τ k hk v' u hu hv' g hg
      have := hv' (g * atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (mul_mem hg (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _))
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodR_apply, thR_apply] at this ⊢
      rw [hK τ k hk v' u hu, hωmul]
      have hp : ∏ ρ, ⟪((e ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g)
            (((Function.update v' τ u ρ : lowT M ρ) : M.sm ρ) : M.H ρ)⟫_ℂ =
          ∏ ρ, ⟪((e ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ)
            (g * atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ))) ((v' ρ : M.sm ρ) : M.H ρ)⟫_ℂ :=
        Finset.prod_congr rfl fun ρ _ => by rw [hA τ k hk v' u hu ρ, hrep]; rfl
      rw [hp]
      exact this

  have hconj : ∀ (x y : ∀ ρ, M.H ρ), ∏ ρ, ⟪y ρ, x ρ⟫_ℂ = star (∏ ρ, ⟪x ρ, y ρ⟫_ℂ) := fun x y => by
    rw [star_prod]
    exact Finset.prod_congr rfl fun ρ _ => (inner_conj_symm _ _).symm
  have st2 : ∀ v v', ∀ g ∈ GinfC W, thetaIP μ 𝓕 (J v) (ω (1, g) (J v')) = thetaIP μ 𝓕 (J e) (J e) *
      ∏ ρ, ⟪((v ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v' ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
    intro v v'
    have key := GlobalTheory.DefLift.mem_of_translates hLS hLI
      (thL hω h1 J hJ (J v') (hJ v') - star (thetaIP μ 𝓕 (J e) (J e)) •
        prodL θ M (fun ρ => ((v' ρ : M.sm ρ) : M.H ρ))) (offReal W) e hne ?_ ?_ v
    · intro g hg
      have := key g hg
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodL_apply, thL_apply] at this
      rw [sub_eq_zero, hconj, ← star_mul'] at this
      exact star_injective this
    · intro g hg
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodL_apply, thL_apply]
      rw [st1 v' g hg, star_mul', ← hconj, sub_self]
    · intro τ k hk v u hu hv g hg
      set a := atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ) with ha
      have := hv (a⁻¹ * g) (mul_mem (inv_mem (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _)) hg)
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodL_apply, thL_apply] at this ⊢
      have e1 : ω (1, g) (J v') = ω (1, a) (ω (1, a⁻¹ * g) (J v')) := by rw [hωmul, mul_inv_cancel_left]
      rw [hK τ k hk v u hu, e1, GlobalTheory.WeilPairing.thetaInner_weilRep D ψ V W χV χW ω μ 𝓕 hω hcv (1, a) _ _ (hJ v)
        (hω.om_pres _ _ (hJ v'))]
      have hp : ∏ ρ, ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v' ρ : M.sm ρ) : M.H ρ),
            (((Function.update v τ u ρ : lowT M ρ) : M.sm ρ) : M.H ρ)⟫_ℂ =
          ∏ ρ, ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) (a⁻¹ * g)) ((v' ρ : M.sm ρ) : M.H ρ),
            ((v ρ : M.sm ρ) : M.H ρ)⟫_ℂ :=
        Finset.prod_congr rfl fun ρ _ => by
          rw [hA τ k hk v u hu ρ, hrep, ContinuousLinearMap.comp_apply, hinv]
      rw [hp]
      exact this
  exact ⟨_, st2⟩

end GlobalTheory.RawLift.FockPair

namespace GlobalTheory.RawLift.FockPair

open GlobalTheory.DefLift GlobalTheory.RawLift Formalism.IndefR.FWT in

theorem coef_one_vector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), GlobalTheory.HolDict.HolShape M → (∃ wt, GlobalTheory.HolDict.WtIs M wt) → ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → GlobalTheory.RawLift.FockCoef.Killed om θ M (pt Δ) → ∀ w : c.W, ∃ N : ℂ, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w)) = N * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) := by
  intro D ψ θ S T χS χT om hθ hom Sp M hM hwt μ 𝓧 hcv c hc pt hpt Δ io hio hΔ w
  obtain ⟨wt, hw⟩ := hwt
  obtain ⟨hLS, hLI⟩ := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D T Sp M hM
  let J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO S T → ℂ) :=
    (pt.comp (io.flip w)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hJv : ∀ v, J v = pt (io (PiTensorProduct.tprod ℂ v) w) := fun _ => rfl
  have hJ : ∀ v, IsThetaFunO ψ S T (J v) := fun v => hpt _
  obtain ⟨N, hN⟩ := pair_of_ext θ hθ M hLS hLI hom hcv J hJ
    (fun τ k hk v u hu => (hio.2.1 τ k hk v u hu w).symm)
    (fun v hv u hu => GlobalTheory.RawLift.FockCoef.coef_eq hom hcv hθ M hM hw hv (hpt _)
      (fun a ha => GlobalTheory.RawLift.FockCoef.holAd_coef hom hcv hθ M hM hw c hc pt hpt Δ io hio hΔ v hv w ha) u hu)
  refine ⟨N, fun g hg e e' => ?_⟩
  have hmem : realElt θ T g ∈ GinfC T := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hy
    exact GlobalTheory.PointAtPlaceHom.atTau_mem _ τ _
  have hinf : ∀ ρ, infMat D.sp.cm.sig T.gram (θ ρ) (realElt θ T g) = g ρ := fun ρ => by
    rw [realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ g hg ρ _ (Finset.nodup_toList _),
      if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]
  have key := hN e' e _ hmem
  rw [hJv, hJv] at key
  simp only [hinf] at key
  rw [← key]
  show (∫ x in 𝓧, _ ∂μ) = ∫ x in 𝓧, _ ∂μ
  congr 1
  funext x
  rw [starRingEnd_apply, mul_comm]

end GlobalTheory.RawLift.FockPair

end
