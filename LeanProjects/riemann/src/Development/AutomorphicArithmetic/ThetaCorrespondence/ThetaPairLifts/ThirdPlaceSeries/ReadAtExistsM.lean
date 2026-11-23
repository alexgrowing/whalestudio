import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExistsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRecLawsH
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIffStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TrueReading
open GlobalTheory.WeilDeligne GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem readAt_exists_m_alt (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hR : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) (i : D.nd.Loc)
    (s : SplitPlace D.host.E) :
    ∃ X : ReadAt P.T i s.w, X.rc = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w ∧
      (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s (X.row σ).toIrrRep) ∧
      (∀ Q, IsLocS (n := D.R.nV) (P.H.av.S i Q) s (X.rep Q).toIrrRep) ∧
      (∀ j : Fin D.R.m, j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) s.w X.mu) ∧
      IsComp P.cf.eta s.w X.eta := by
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have HR := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s.w)
  have hlaws : _root_.UpperTheory.One.M.RecLawsH (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w) := HR.recLaws
  have hrow : ∀ σ, ∃ τ : Irr (s.w.adicCompletion D.host.E) D.R.r,
      D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s τ.toIrrRep := by
    intro σ
    by_cases hσ : D.what₂.isot (D.nd.j i) σ ≠ ⊥
    · obtain ⟨τ, hτ⟩ := GlobalTheory.T.isotypic_row_local_split_exists D P.rep (D.nd.j i) (hR i).some σ hσ s
      exact ⟨Irr.ofIrrRep τ, fun _ => hτ⟩
    · exact ⟨default, fun h => absurd h hσ⟩
  choose row hrow using hrow
  have hrep : ∀ Q : D.naut.AV i, ∃ τ : Irr (s.w.adicCompletion D.host.E) (D.R.r + D.R.t),
      IsLocS (n := D.R.nV) (P.H.av.S i Q) s τ.toIrrRep := by
    intro Q
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
    exact ⟨Irr.ofIrrRep τ, hτ⟩
  choose rep hrep using hrep
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hmuC := P.chr.muC i j0 hj0
  obtain ⟨μ, hμ, -, hμu⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E (P.tp.tup (D.nd.mu i) j0) s.w
  have hμU : GlobalTheory.SmGL.IsUnitaryChar μ := hμu (hmuC ▸ (P.chr.e1 (D.naut.muC i)).2)
  have hμP : IsComp (P.chr.e1 (D.naut.muC i)).1 s.w μ := hmuC ▸ hμ
  have eμ := _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hAF hL D P (D.naut.muC i) s.w μ hμP
  obtain ⟨η, hη, -, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E P.cf.eta⁻¹ s.w
  have hηP : IsComp (P.chr.e1 D.naut.etaTinv).1 s.w η := P.chr.etaTinv ▸ hη
  have eη := _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hAF hL D P D.naut.etaTinv s.w η hηP
  have hun : GlobalTheory.SplitWeil.IsUnram η := by
    have := (hlaws.sph 1 (Irr.ofDet 1 η hηP.1)).1
      (by rw [← eη]; exact (P.T.unr s.w _).1 (D.naut.etaTinv_def s.w).1)
    intro x hx
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
    have hI : (fun _ : Fin 1 => x) ∈ torusO (s.w.adicCompletion D.host.E) (Fin 1) := fun _ => hx
    have h2 := hv ⟨_, iwahori_le_KO _ _ (diagT_mem_iwahori hI)⟩
    have h3 : Matrix.GeneralLinearGroup.det (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x) = x := by
      ext; simp [val_diagT]
    have h4 : (η x : ℂ) * (show ℂ from v) = (show ℂ from v) := by
      have h5 : detRep (Fin 1) η (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x) v = (show ℂ from v) := by
        exact h2.trans (by simp)
      have h6 := (ofChar_apply (detChar (Fin 1) η) (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x)
        (show ℂ from v)).symm.trans h5
      rw [detChar_apply, h3] at h6
      exact h6
    ext
    exact (mul_eq_right₀ hv0).1 h4
  refine ⟨⟨_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w, row, rep, μ, η⁻¹, ⟨hμ.1, hμU⟩, ⟨hηP.1.inv, fun x hx => by simp [hun x hx]⟩,
    fun σ hσ => (P.row i).1 σ s _ (hrow σ hσ), fun Q => ?_, fun c hc => ?_, fun c hc => ?_⟩,
    rfl, hrow, hrep, fun j hj => ?_, ⟨hη.1.inv, fun x => ?_⟩⟩
  · rw [D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ (hrep Q)
  · rw [eμ]; exact (_root_.UpperTheory.One.M.RecLawsH.isoMp hlaws 1 c (Irr.ofDet 1 μ hμP.1) hc).symm
  · rw [inv_inv] at hc
    rw [eη]; exact (_root_.UpperTheory.One.M.RecLawsH.isoMp hlaws 1 c (Irr.ofDet 1 η hηP.1) hc).symm
  · have : j = j0 := Fin.ext (by simp only [j0]; omega)
    subst this
    exact hμ
  · rw [MonoidHom.inv_apply, hη.2 x]
    exact inv_inv _
end GlobalTheory.TrueReading
end
