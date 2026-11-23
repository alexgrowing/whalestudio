import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionRealPlaceFockVacuaScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAway
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor

noncomputable section

namespace GlobalTheory.RealVacScalar

variable {D : D7}

theorem sum_wAt_real {S T : HSp D} (w : WO S T) (hw : w.map (finPart D) = 0) :
    ∑ τ : D.what₂.Tau, wAt (.inr τ) w = w := by
  ext i j
  rw [Matrix.sum_apply]
  show ∑ τ : D.what₂.Tau, idem D (.inr τ) * w i j = w i j
  rw [← Finset.sum_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_mul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.2.2.2.1, one_mul]
  · have h0 : finPart D (w i j) = 0 := congrFun (congrFun hw i) j
    rw [RingHom.map_mul, h0, mul_zero]

theorem wAt_sum_real_notMem {S T : HSp D} (w : WO S T) {r : D.what₂.Tau} {P : Finset D.what₂.Tau} (hr : r ∉ P) :
    wAt (.inr r) (∑ τ ∈ P, wAt (.inr τ) w) = 0 := by
  rw [wAt_eq_smul, Finset.smul_sum]
  refine Finset.sum_eq_zero fun τ hτ => ?_
  rw [← wAt_eq_smul]
  exact GlobalTheory.PlaceStable.wAt_wAt_ne (fun h => hr (by rw [Sum.inr_injective h]; exact hτ)) w

theorem thetaIP_eq_ipO {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (a b : WO S T → ℂ) :
    thetaIP μ 𝓕 a b = ipO μ 𝓕 b a := by
  unfold thetaIP ipO
  congr 1
  funext x
  rw [Complex.star_def, mul_comm]

theorem ipO_conj {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (a b : WO S T → ℂ) :
    ipO μ 𝓕 a b = starRingEnd ℂ (ipO μ 𝓕 b a) := by
  unfold ipO
  rw [← integral_conj]
  congr 1
  funext x
  simp [mul_comm]

theorem ip_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (w : WO S T)
    (γ : D.what₂.Tau → ℂ)
    (hγ : ∀ τ (f g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g →
      ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ τ * ipO μ 𝓕 g f)
    (P : Finset D.what₂.Tau) : ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ipO μ 𝓕 g (heisO ψ S T (∑ τ ∈ P, wAt (.inr τ) w) f) = (∏ τ ∈ P, γ τ) * ipO μ 𝓕 g f := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro f g _ _ _ _
    rw [Finset.sum_empty, Finset.prod_empty, GlobalTheory.SplitScalar.heisO_zero, one_mul]
  | insert r P hr ih =>
    intro f g hf hg vf vg
    have h0 := wAt_sum_real_notMem w hr
    rw [Finset.sum_insert hr, Finset.prod_insert hr,
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (GlobalTheory.LocalPure.symplO_wAt S T w h0),
      hγ r _ g ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 _ _ hf) hg
        (GlobalTheory.PlaceStable.isFockVacAt_heisO hθ h0 (vf r)) (vg r),
      ih f g hf hg vf vg, mul_assoc]

theorem compress_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) →
    IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ w : WO S T, w.map (finPart D) = 0 → ∃ κ : ℂ, ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) h) →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) e) →
    thetaIP μ 𝓕 h (heisO ψ S T w e) = κ * thetaIP μ 𝓕 h e := by
  intro D ψ θ S T hψ hθ sS sT hsS hsT μ 𝓕 hμ w hw
  choose γ hγ using fun τ =>
    GlobalTheory.VacCompress.compress D ψ θ S T μ 𝓕 hψ hθ hμ τ (sS τ) (sT τ) (hsS τ) (hsT τ) w
  refine ⟨starRingEnd ℂ (∏ τ, γ τ), fun h e hh he vh ve => ?_⟩
  have key := ip_sum hψ hθ μ 𝓕 w γ hγ Finset.univ e h he hh ve vh
  rw [sum_wAt_real w hw] at key
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, ipO_conj, key, map_mul, ← ipO_conj]

end GlobalTheory.RealVacScalar

end
