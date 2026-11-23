import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.Imports
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ExistsWeilTransportAdelicSchwartzCmExtensionImpo
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.TransportedWeilDatumCMPreservesSchwartzHeisenber
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.WeilDatumTransportCmPreservesAdmissibleFormsImpo
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.IsUnitaryOnWeilDatumTransportAdelicSchwartz2
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ContinuousTransportWeilDatumCmExtensionImports
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.TargetDoubling
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsDblTarget

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem PositivityTheory.ThKW.S.exists_isUWeilPair_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω, Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∃ om, IsUWeilPair (cA σ) (adeleClass F) B.ψ ξ (incM F JA) (incM F JB) co χT χS om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ hLat χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ _ co hrat
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilTransport_adelicSchwartz_cmExtension F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat
  have h2 := GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h3 := GlobalTheory.T.weilDatumTransport_cm_preserves_admissibleForms F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h4 := GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h5 := GlobalTheory.T.continuous_transport_weil_datum_cm_extension F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h6 := PositivityTheory.ThKW.dblS_of_dblT PositivityTheory.ThKW.S.exists_dbl_target F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ hLat χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have h7 := PositivityTheory.ThKW.S.exists_dbl_target F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ hLat χS χT cS cT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
  have hsp : IsUSplitting (adeleClass F) B.ψ co (actAB (cA σ)) om := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  exact ⟨om, ⟨GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp, h6⟩,
    ⟨GlobalTheory.WeilSchrodinger.transD _ co, GlobalTheory.WeilSchrodinger.transD_e co, GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp, h7⟩, h5⟩
