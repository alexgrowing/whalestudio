import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrameStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLinearFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftedCharactersAgreeStatement
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.ThetaTri.exists_thetaMod : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)), GlobalTheory.NJoin.IsCanon X j hj Y → Nonempty (ThetaMod D P.M i Y (P.tp.tup (D.nd.mu i) j) P.cf.eta) := by
  intro hHC hCR hL D P X A i j hj Y hc
  have hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hC := X.given.core
  have hth : ∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j)
      (GlobalTheory.ThetaTri.phi0 j (X.tupT (D.nd.mu i)) v) := fun v => hC.thP.pt_theta j _ _
  have h0 : GlobalTheory.ThetaTri.phi0 j (X.tupT (D.nd.mu i)) ∈ GlobalTheory.ThetaTri.OmI A i j hj hc hμ :=
    GlobalTheory.T.theta_lift_linear_form hHC hCR hL D P X A i j hj Y hc hμ _ hth
  refine ⟨{ Ω := ↥(GlobalTheory.ThetaTri.OmI A i j hj hc hμ)
            ω := GlobalTheory.ThetaTri.omI A i j hj hc hμ
            Λ := GlobalTheory.ThetaTri.lamL A i j hj hc hμ
            inv := fun h g φ F F' y y' hF hy => GlobalTheory.T.theta_lift_equivariance hL D P X A i j hj Y hc hμ h g φ.1 φ.2 F F' y y' hF hy
            φ₀ := ⟨_, h0⟩
            read := fun x y F hF => GlobalTheory.T.theta_lift_automorphic_form hL D P X A i j hj Y hc hμ x y F hF
            loc := ?_ }⟩
  intro s μw ηw hμw hηw
  obtain ⟨h1, h2⟩ := GlobalTheory.T.lifted_characters_agree hL D P X A i j hj
  have hv : ∀ v, GlobalTheory.ThetaTri.phi0 j (X.tupT (D.nd.mu i)) v ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.nV) (Fin D.R.r)
      (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ))
      (_ : IsLinAt (GlobalTheory.ThetaTri.omStd A j (X.tupT (D.nd.mu i))) s μw ηw ι ∧
        ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (ι Φ)),
      LinearMap.range ι := fun v =>
    GlobalTheory.T.thetaFunctions_spanned_heckeTwisted_standardFrame D X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) D.R.nV D.R.r (A.PV j) (X.PW j) A.hF
      (A.stdV j) (A.stdW j) _ _ (X.R.ωP j (X.tupT (D.nd.mu i))) (hC.thP.ωP j _) _ _ h1 h2 s μw ηw hμw hηw _ (hth v)
  have hlin := GlobalTheory.ThetaTri.mem_iSup_isLinAt_lin' (GlobalTheory.ThetaTri.omStd A j (X.tupT (D.nd.mu i)))
    (Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j))
    (· ∈ GlobalTheory.ThetaTri.OmI A i j hj hc hμ)
    (fun β f hf => GlobalTheory.T.theta_lift_linear_form hHC hCR hL D P X A i j hj Y hc hμ _ fun v => by
      simpa [GlobalTheory.ThetaTri.single1] using Formalism.IndefR.Fock.CCR.theta_smul hf (β v))
    s μw ηw _ hv
  exact GlobalTheory.ThetaTri.mem_iSup_isLinAt_omSub _ _ _ _ _ _ _ _ _ s μw ηw h0 hlin
