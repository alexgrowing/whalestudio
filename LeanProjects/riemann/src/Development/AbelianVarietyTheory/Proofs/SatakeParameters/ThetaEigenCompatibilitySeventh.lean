import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityNinthStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedBaseChangeEqOfSatakeEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StrInert

theorem not_isSplitPl_of_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hin : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) : ¬ IsSplitPl D.host w := by
  rw [GlobalTheory.ConjPlaceOff.isSplitPl_iff]
  rintro ⟨x, hx, hcx⟩
  apply hcx
  unfold Formalism.UG.IsInertAt at hin
  rw [← hin] at hx ⊢
  have key : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal ≤
      (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (w.under (𝓞 D.host.F)).asIdeal).comap
        (Formalism.HermitianLattices.Ext.L3.conjO D.host.E) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have e : Formalism.HermitianLattices.Ext.L3.conjO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) =
        algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
      apply RingOfIntegers.ext
      rw [Formalism.HermitianLattices.Ext.L3.conjO_coe]
      have : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F D.host.E (a : D.host.F) := rfl
      rw [this]
      exact Formalism.IndefR.Eqv.star_algebraMapF D _
    rw [e]
    exact Ideal.mem_map_of_mem _ ha
  exact key hx

theorem not_mem_badPl {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat D A Ks) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : GlobalTheory.Hk3.Good R t w)
    (hin : Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w) :
    w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  intro h
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl, Finset.mem_image, Finset.mem_union] at h
  obtain ⟨PP, hPP, he⟩ := h
  have hne := (hw PP hPP).1
  apply hne
  unfold Formalism.UG.IsInertAt at hin
  have hle : w.asIdeal ≤ PP.asIdeal := by
    rw [← hin, Ideal.map_le_iff_le_comap]
    intro a ha
    have : (PP.under (𝓞 D.host.F)).asIdeal = PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := rfl
    rw [← this, he]
    exact ha
  exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le PP.isPrime.ne_top hle)).symm

end GlobalTheory.StrInert

theorem GlobalTheory.StrInert.param_eq_ubc_satV : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ P', D.naut.ptV i P' = some x → (B w).map (fun a : ℂˣ => (a : ℂ)) = ubc D.R.nV (D.naut.satV i P' w) := by
  intro hA hL D P X hX h41 h7 htie i hμ j hj x hx f hf y hy hy0 h hh s B hs hB w hw hin P' hP'
  have hv := GlobalTheory.StrInert.not_mem_badPl X.R (X.tupT (D.nd.mu i)) w hw hin
  have hns := GlobalTheory.StrInert.not_isSplitPl_of_inert D w hin
  obtain ⟨P₀, hP₀, α₀, hsat, hev⟩ := GlobalTheory.T.theta_eigen_compatibility_ninth hA hL D P X hX h41 h7 htie i hμ j hj x hx f hf y hy hy0 h hh s hs w hw hin
  have hBw := hB _ hv w rfl
  rcases hBw with ⟨hsp, -⟩ | ⟨-, τ, ϖ, α, hU, hτ, hBeq, hc⟩
  · exact absurd hsp (GlobalTheory.LFun.not_isSplit_of_isInertAt hin)
  have hrank : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have key : (B w).map (fun a : ℂˣ => (a : ℂ)) = ubc (Formalism.IndefR.Links.Vc D j).rank (D.naut.satV i P₀ w) := by
    rw [hBeq, hsat]
    exact GlobalTheory.T.unramifiedBaseChange_eq_of_satake_eq _ ϖ τ _ _ hU α α₀ fun d t' hd ht' => (hc d t' hd ht').symm.trans (hev τ ϖ hU hτ d t' hd ht')
  rw [key, hrank]
  have h2 := ((h41 i).2.1 P₀ P' (by rw [hP₀]; exact Option.some_ne_none x) (hP₀.trans hP'.symm)).2 w
  exact (h2 (fun hS => hns (D.nd.SQ_split i w (Or.inl hS))) (fun hQ => hns (D.nd.SQ_split i w (Or.inr hQ)))).2 hns
