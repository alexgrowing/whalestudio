import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.RealLowRed

open Formalism.IndefR.FWT

variable {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

theorem integrable_star_mul (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (h1 : μ 𝓕 = 1)
    {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    Integrable (fun w => star (f w) * g w) (μ.restrict 𝓕) := by
  haveI : BorelSpace (WO S T') := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hf
  obtain ⟨C', hC'⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hg
  refine Integrable.of_bound (hf.cont.star.mul hg.cont).aestronglyMeasurable (C * C')
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_mul (hC w) (hC' w) (norm_nonneg _) ((norm_nonneg _).trans (hC w))

theorem thetaInner_add_right (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (h1 : μ 𝓕 = 1)
    {f g h : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) (hh : IsThetaFunO ψ S T' h) :
    thetaIP μ 𝓕 f (g + h) = thetaIP μ 𝓕 f g + thetaIP μ 𝓕 f h := by
  unfold thetaIP
  rw [← integral_add (integrable_star_mul hψ h1 hf hg) (integrable_star_mul hψ h1 hf hh)]
  congr 1
  funext w
  simp only [Pi.add_apply, mul_add]

theorem thetaInner_add_left (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (h1 : μ 𝓕 = 1)
    {f g h : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) (hh : IsThetaFunO ψ S T' h) :
    thetaIP μ 𝓕 (f + g) h = thetaIP μ 𝓕 f h + thetaIP μ 𝓕 g h := by
  unfold thetaIP
  rw [← integral_add (integrable_star_mul hψ h1 hf hh) (integrable_star_mul hψ h1 hg hh)]
  congr 1
  funext w
  simp only [Pi.add_apply, star_add, add_mul]

end GlobalTheory.RawLift.RealLowRed

namespace GlobalTheory.RawLift.RealLowRed

open Formalism.IndefR.FWT

variable {D : D7}

def prodR {W : HSp D} {S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S') (a : ∀ ρ, M.H ρ) :
    MultilinearMap ℂ (fun ρ => lowT M ρ) (GA D W → ℂ) :=
  MultilinearMap.pi fun g => (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap fun ρ =>
    (innerₛₗ ℂ (a ρ)).comp ((M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g)).toLinearMap.comp
      ((M.sm ρ).subtype.comp (lowT M ρ).subtype))

theorem prodR_apply {W : HSp D} {S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S') (a : ∀ ρ, M.H ρ)
    (v : ∀ ρ, lowT M ρ) (g : GA D W) :
    prodR θ M a v g = ∏ ρ, ⟪a ρ, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
  simp [prodR, MultilinearMap.pi_apply, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

def prodL {W : HSp D} {S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S') (b : ∀ ρ, M.H ρ) :
    MultilinearMap ℂ (fun ρ => lowT M ρ) (GA D W → ℂ) :=
  MultilinearMap.pi fun g => (MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap fun ρ =>
    (innerₛₗ ℂ (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) (b ρ))).comp
      ((M.sm ρ).subtype.comp (lowT M ρ).subtype)

theorem prodL_apply {W : HSp D} {S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S') (b : ∀ ρ, M.H ρ)
    (v : ∀ ρ, lowT M ρ) (g : GA D W) :
    prodL θ M b v g = ∏ ρ, ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) (b ρ), ((v ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
  simp [prodL, MultilinearMap.pi_apply, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

def offReal (W : HSp D) : Submodule ℂ (GA D W → ℂ) where
  carrier := {f | ∀ g ∈ GinfC W, f g = 0}
  add_mem' := fun {a b} ha hb g hg => by
    show a g + b g = 0
    rw [ha g hg, hb g hg, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c f hf g hg => by
    show c • f g = 0
    rw [hf g hg, smul_zero]

end GlobalTheory.RawLift.RealLowRed

namespace GlobalTheory.RawLift.RealLowRed

open Formalism.IndefR.FWT

variable {D : D7} {V W : HSp D} {S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {χV χW : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}

def thR (hω : IsWeilDatumO ψ V W χV χW ω) (h1 : μ 𝓕 = 1) {M : DSModel W S'}
    (J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO V W → ℂ)) (hJ : ∀ v, IsThetaFunO ψ V W (J v))
    (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) : MultilinearMap ℂ (fun ρ => lowT M ρ) (GA D W → ℂ) where
  toFun v g := thetaIP μ 𝓕 f (ω (1, g) (J v))
  map_update_add' m ρ x y := by
    funext g
    simp only [Pi.add_apply]
    rw [J.map_update_add, map_add]
    exact thetaInner_add_right hω.std h1 hf (hω.om_pres _ _ (hJ _)) (hω.om_pres _ _ (hJ _))
  map_update_smul' m ρ a x := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [J.map_update_smul, map_smul]
    exact thetaInner_smul_right _ _ _ _ _

theorem thR_apply (hω : IsWeilDatumO ψ V W χV χW ω) (h1 : μ 𝓕 = 1) {M : DSModel W S'}
    (J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO V W → ℂ)) (hJ : ∀ v, IsThetaFunO ψ V W (J v))
    (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) (v : ∀ ρ, lowT M ρ) (g : GA D W) :
    thR hω h1 J hJ f hf v g = thetaIP μ 𝓕 f (ω (1, g) (J v)) := rfl

def thL (hω : IsWeilDatumO ψ V W χV χW ω) (h1 : μ 𝓕 = 1) {M : DSModel W S'}
    (J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO V W → ℂ)) (hJ : ∀ v, IsThetaFunO ψ V W (J v))
    (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) : MultilinearMap ℂ (fun ρ => lowT M ρ) (GA D W → ℂ) where
  toFun v g := star (thetaIP μ 𝓕 (J v) (ω (1, g) f))
  map_update_add' m ρ x y := by
    funext g
    simp only [Pi.add_apply]
    rw [J.map_update_add, thetaInner_add_left hω.std h1 (hJ _) (hJ _) (hω.om_pres _ _ hf), star_add]
  map_update_smul' m ρ a x := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [J.map_update_smul, thetaInner_smul_left, star_mul', star_star]

theorem thL_apply (hω : IsWeilDatumO ψ V W χV χW ω) (h1 : μ 𝓕 = 1) {M : DSModel W S'}
    (J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO V W → ℂ)) (hJ : ∀ v, IsThetaFunO ψ V W (J v))
    (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f) (v : ∀ ρ, lowT M ρ) (g : GA D W) :
    thL hω h1 J hJ f hf v g = star (thetaIP μ 𝓕 (J v) (ω (1, g) f)) := rfl

end GlobalTheory.RawLift.RealLowRed

namespace GlobalTheory.RawLift.RealLowRed

open Formalism.IndefR.FWT

variable {D : D7} {V W : HSp D} {S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {χV χW : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}

open Classical in
set_option maxHeartbeats 4000000 in

theorem of_ext (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel W S') (hLS : LowSm M) (hLI : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M)
    (hω : IsWeilDatumO ψ V W χV χW ω) (hcv : IsCovolOne (ratL W V) μ 𝓕)
    (J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO V W → ℂ)) (hJ : ∀ v, IsThetaFunO ψ V W (J v))
    (hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) →
      J (Function.update v τ u) = ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (J v))
    (hX : ∀ v : (∀ ρ, lowT M ρ), IsExtVec M (fun ρ => (v ρ : M.sm ρ)) → ∀ u ∈ GinfC W,
      thetaIP μ 𝓕 (J v) (ω (1, u) (J v)) = thetaIP μ 𝓕 (J v) (J v) *
        ∏ ρ, ⟪((v ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) u) ((v ρ : M.sm ρ) : M.H ρ)⟫_ℂ)
    (v : ∀ ρ, lowT M ρ) (hv : ∀ ρ, ‖((v ρ : M.sm ρ) : M.H ρ)‖ = 1) (u : GA D W) (hu : u ∈ GinfC W) :
    thetaIP μ 𝓕 (J v) (ω (1, u) (J v)) = thetaIP μ 𝓕 (J v) (J v) *
        ∏ ρ, ⟪((v ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) u) ((v ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
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

  have hn : thetaIP μ 𝓕 (J v) (J v) = thetaIP μ 𝓕 (J e) (J e) := by
    have P1 := st2 v v 1 (one_mem _)
    have h11 : ω ((1 : GA D V), (1 : GA D W)) = 1 := map_one ω
    rw [h11, Module.End.one_apply] at P1
    rw [P1]
    simp only [hrep1, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hv]
    simp
  rw [st2 v v u hu, hn]

end GlobalTheory.RawLift.RealLowRed

namespace GlobalTheory.RawLift.RealLowRed

open Formalism.IndefR.FWT

theorem realLow_of_ext : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∀ μ 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), Formalism.IndefR.FWT.IsExtVec (R.MW i (sg0 D A)) (fun ρ => ((v ρ : (R.MW i (sg0 D A)).sm ρ))) → ∀ w, ∀ u ∈ GinfC (Wc D i),
    thetaIP μ 𝓕 (jointVec R i t v w) (R.ωP i t (1, u) (jointVec R i t v w)) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) *
        ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
          (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
            ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) → RealLow R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hX μ 𝓕 hcv v hv w u hu
  have hs0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK (sg0 D A) := fun x _ =>
    congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) hs0
  obtain ⟨hLS, hLI⟩ := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)
  exact of_ext R.θ hL.models.inf (R.MW i (sg0 D A)) hLS hLI (hL.thP.ωP i t) hcv
    (((pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
      (onb (R.MW i (sg0 D A))) (R.vP i t)).comp ((R.ioP i).flip w)).compMultilinearMap (PiTensorProduct.tprod ℂ))
    (fun v => hL.thP.pt_theta i t _)
    (fun τ k hk v u hu' => ((hL.thP.ioP i t).2.1 τ k hk v u hu' w).symm)
    (fun v hv' u hu' => hX μ 𝓕 hcv v hv' w u hu') v hv u hu

end GlobalTheory.RawLift.RealLowRed

end
