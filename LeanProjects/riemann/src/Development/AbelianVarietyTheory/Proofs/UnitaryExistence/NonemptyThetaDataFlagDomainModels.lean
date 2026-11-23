import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriodsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameFrames

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem nonempty_thetaData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, Nonempty (ThetaData e F M k) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hM hξ k
  obtain ⟨⟨idx, hty, -, hper⟩, hp0, hr, hcc, hpos, hφ⟩ :=
    GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hσ hM hξ k
  obtain ⟨Pf, hPf, -, hisPer, hdiff, -⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hσ hM hξ k
  have htf : IsTypeFn H (F.Di k).p (F.Di k).q (fun j => relab c σ (e j).1) := by
    rw [(F.sig k).1, (F.sig k).2]
    exact (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw g e
  obtain ⟨hg, -⟩ := (GlobalTheory.PeriodExists.typeFn_period_exist E H (F.Di k)).2.1 g _ htf
  obtain ⟨bas, hsym, had⟩ := GlobalTheory.exists_symplectic_basis_adapted_mod_eight E H (F.Di k) g hg
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hdom : (M.X k).dom = GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := by
    rw [← hp0]
  let co : (Fin (Module.finrank ℂ (Frame (M.X k).Ψ r)) → ℂ) ≃L[ℂ] Frame (M.X k).Ψ r :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨h, ta, c₁, c₂, hnorm, hhol, h1, h2, fr, hf1, hf2, hf3, hf4, hf5⟩ :=
    GlobalTheory.FrameTheta.exists_thetaFrame_frames E H Dw l Xo _ g _ F k r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ idx Pf
      (hM.type k).2 hty hcc hpos (hφ φ fun _ => rfl).2 hr (fun x v j => (hPf x v j).trans (hper x _ j))
      (hdom ▸ (GlobalTheory.frames_isConnected E r (M.X k)).isPreconnected) bas hsym _ co
  rw [← hdom] at hnorm hhol hf1 hf2 hf3 hf4 hf5
  exact ⟨{
    Pf := Pf
    per := hPf
    isPer := hisPer
    m := _
    co := co
    holPer := ⟨fun b hb => hisPer _ hb, fun v =>
      (hdiff v).comp co.differentiable.differentiableOn fun _ hb => hb⟩
    bas := bas
    sympl := hsym
    adapt := had
    h := h
    ta := ta
    norm := hnorm
    hol := hhol
    c₁ := c₁
    c₂ := c₂
    half₁ := h1
    half₂ := h2
    fr := fr
    fr_hol := hf1
    fr_ne := hf2
    fr_coc := hf3
    fr_rig := hf4
    fr_sec := hf5 }⟩

end GlobalTheory.FrameUnif
