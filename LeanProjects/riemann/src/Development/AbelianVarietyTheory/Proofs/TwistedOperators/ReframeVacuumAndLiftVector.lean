import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOnHomsReframeHomMatrixStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointMapReframedHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedLatticeReframeHomMatrixIffStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothThetaFunctionReframeFunctionOnHomsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtReframeFunctionOnHomsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeFunctionOnHomsNormOneCovolumeOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtSplitPlaceReframeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameFrameChangeInverseGLMulStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec

theorem L_lat : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T), u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔ reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := GlobalTheory.T.mem_completedLattice_reframeHomMatrix_iff

theorem L_sympl : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T), symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := GlobalTheory.T.symplecticFormOnHoms_reframeHomMatrix

theorem L_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := GlobalTheory.T.isSmoothThetaFunction_reframeFunctionOnHoms

theorem L_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ → (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := GlobalTheory.T.isFockVacuumAt_reframeFunctionOnHoms

theorem L_norm : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ), AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := GlobalTheory.T.reF_norm_one_of_norm_one_covolOne

theorem L_thetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → (∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) e Λ' c (reF S T b f₀) (fun x => Φ (reW S T b x)) (reF S T b f) := GlobalTheory.T.isThetaAtSplitPlace_reframe

theorem L_frMap : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO (reS S b) T), frMapAdj (reS S b) T (frPinvGL S b * βS) βT x = frMapAdj S T βS βT (reW S T b x) := GlobalTheory.T.frameAdjointMap_reframedHermitianSpace

theorem L_frame : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := GlobalTheory.T.isFrame_frameChangeInverseGL_mul

theorem pi_eq_stdL' (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) = stdL E n := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx a trivial)
    have : (Pi.single a (x a) : Fin n → E) = b • (Pi.single a 1 : Fin n → E) := by
      rw [← Pi.single_smul, ← hb, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩ j -
    by_cases h : j = a
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · simp [h]

theorem L_std : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), StdFrame.OrthFrame (reS S b) → L0c D (reS S b) = (stdL D.host.E (reS S b).rank : Set (Fin (reS S b).rank → D.host.E)) := by
  intro D S b hO
  ext x
  rw [SetLike.mem_coe, ← pi_eq_stdL', Submodule.mem_pi]
  exact (hO.mem_iff x).trans ⟨fun k a _ => k a, fun k a => k a trivial⟩

theorem reframe_thPVecOf : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), StdFrame.OrthFrame (reS S b) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Lt D.host.E S.rank) (ΛT : Set (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → IsThPVecOf ψ θ S T (fun _ => 1) sT (ΛS : Set (Fin S.rank → D.host.E)) ΛT βS βT Pg Q ξ f₀ f → ∃ βS' : GL (Fin (reS S b).rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βS' (stdL D.host.E (reS S b).rank) ∧ IsThPVecOf ψ θ (reS S b) T (fun _ => 1) sT (stdL D.host.E (reS S b).rank : Set (Fin (reS S b).rank → D.host.E)) ΛT βS' βT Pg Q ξ (reF S T b f₀) (reF S T b f) := by
  intro D S T b hO ψ θ sT ΛS ΛT βS βT Pg Q ξ f₀ f hΛ hfr hv
  have hL := L_std D S b hO
  refine ⟨frPinvGL S b * βS, L_frame D S b βS ΛS hO hΛ hfr, ?_⟩
  rw [← hL]
  rw [hΛ] at hv
  obtain ⟨⟨hstd, hvac⟩, e, he, hth⟩ := hv
  have hs := L_sympl D S T b
  have hlat := L_lat D S T b ΛT
  refine ⟨⟨hstd, ?_⟩, e, he, ?_⟩
  · exact
      { inf := hvac.inf
        theta := L_theta D ψ S T b hs f₀ hvac.theta
        lat := ⟨fun u hu => by
            rw [heisO_reF S T b ψ hs, reW_nsmul, hvac.lat.1 _ ((hlat u).1 hu)],
          fun e' he' u hu hh => by
            rw [heisO_reF S T b ψ hs, hvac.lat.2 e' he' _ ((hlat u).1 hu) ((isHalf_reW_iff S T b e' u).2 hh)]⟩
        fock := fun τ => L_fock D ψ θ S T b hvac.inf hs τ (sT τ) f₀ (hvac.fock τ)
        norm := L_norm D S T b f₀ hvac.norm }
  · refine (congrArg (fun Φ => IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) (cA D e)
      (latO (reS S b) T (L0c D (reS S b)) ΛT fun _ => True) 1 (reF S T b f₀) Φ (reF S T b f)) ?_).mpr
      (L_thetaAt D ψ S T b (cA D e) _ _ 1 f₀ _ f hs hlat hth)
    funext x
    simp only [L_frMap D S T b βS βT x]
    rw [isHalf_reW_iff S T b (cA D e) x]
    exact if_congr Iff.rfl rfl rfl

end GlobalTheory.AdSpan.ReVec

end
