import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.RowsStackRight
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.Imports
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsAlt
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.ExistsIsWeilDatumOF
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ExistsWeilTransportAdelicSchwartzCmExtensionImpo
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.TransportedWeilDatumCMPreservesSchwartzHeisenber
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.WeilDatumTransportCmPreservesAdmissibleFormsImpo
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.IsUnitaryOnWeilDatumTransportAdelicSchwartz2
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ContinuousTransportWeilDatumCmExtensionImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumDoubledTargetSiegelRuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledTargetWeilTransportRestrictFirstFactorStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW.S

theorem exists_dbl_target : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → PositivityTheory.ThKW.LatH σ JS JT ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∃ (dd : Darboux (symp (cA σ) ξ (incM F JB) (dbl (incM F JA))) (κ ⊕ κ))
                (omd : UG (cA σ) (dbl (incM F JA)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)),
                IsDblCoord (cA σ) ξ (incM F JB) (incM F JA) (GlobalTheory.WeilSchrodinger.transD (cA σ) co) dd ∧
                IsUWeilSplit (cA σ) (adeleClass F) B.ψ ξ (incM F JB) (dbl (incM F JA)) dd χS (diagCols (Fin nT)) omd ∧
                ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (dbl (incM F JA))),
                  gd.1.1 = Matrix.fromBlocks g.1.1 0 0 1 →
                  ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ hLat χS χT hS hT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  have hJTd := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hJT
  have h1 := GlobalTheory.WeilSchrodinger.DblTargetF.isHeckeCharF_one (F := F) (E := E)
  have r1 := GlobalTheory.WeilSchrodinger.DblTargetF.resEtaF_one_dbl h2 rT
  obtain ⟨ωd, hωd⟩ := PositivityTheory.ThKW.S.exists_isWeilDatumOF F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ (PositivityTheory.ThKW.LatH.dblT hLat) χS 1 hS h1 rS r1
  have hrat' := GlobalTheory.WeilSchrodinger.DblTargetF.coDbl_rat hA co hrat
  obtain ⟨omp, hmp⟩ := GlobalTheory.T.exists_weilTransport_adelicSchwartz_cmExtension F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat'
  have k2 := GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k3 := GlobalTheory.T.weilDatumTransport_cm_preserves_admissibleForms F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k4 := GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have k5 := GlobalTheory.T.continuous_transport_weil_datum_cm_extension F E σ B hB nS (nT + nT) JS _ hJS hJTd ξ₀ hξ0 hσξ χS 1 hS h1 rS r1 ωd hωd _ JB ξ rfl
    hBm (κ ⊕ κ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' omp hmp
  have hsp : IsUSplitting (adeleClass F) B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) (actAB (cA σ)) omp :=
    ⟨⟨k2.1, k2.2, k3⟩, k4, k5⟩
  have hsg := GlobalTheory.T.weilDatum_doubledTarget_siegelRule F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS hS rS JB ξ hBm (κ ⊕ κ)
    (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) hrat' ωd hωd omp hmp
  have t1 := GlobalTheory.WeilSchrodinger.DblTarget.isDblCoord_transD co
  have t2 : IsLagr (cA σ) (dbl (incM F JA)) (diagCols (Fin nT)) := isLagr_diagCols _ _
  have t4 := GlobalTheory.WeilSchrodinger.DblTarget.isUSplitting_reindex finSumFinEquiv
    (GlobalTheory.WeilSchrodinger.DblTarget.dblRows co) _ (GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM hA)
    (GlobalTheory.WeilSchrodinger.isUSplitting_inl hsp)
  have t5 := GlobalTheory.WeilSchrodinger.DblTarget.siegelRule_reindex finSumFinEquiv
    (GlobalTheory.WeilSchrodinger.DblTarget.dblRows co) _ (GlobalTheory.WeilSchrodinger.DblTargetF.reindex_dbl_incM hA) χS _ hsg
  refine ⟨_, _, t1, ⟨t2, t4, t5⟩, ?_⟩
  intro g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have key := GlobalTheory.T.doubled_target_weil_transport_restrict_first_factor F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hA hBm κ co hrat om hom
    ωd hωd omp hmp g (GlobalTheory.WeilSchrodinger.DblTargetF.ugDbl hA gd)
    (by rw [GlobalTheory.WeilSchrodinger.DblTargetF.ugDbl_coe, hgd]) φ₁ hφ₁ φ₂ hφ₂
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.inl_apply]
  exact key

end PositivityTheory.ThKW.S

end
