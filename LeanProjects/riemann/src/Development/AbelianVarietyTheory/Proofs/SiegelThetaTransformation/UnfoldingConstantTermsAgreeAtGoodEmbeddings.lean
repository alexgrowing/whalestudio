import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapsClosed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortThetaStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesDominantWeightIsCuspFormStatement

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.Dict

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → l.A = 1 → (∀ σ, GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ σ, GoodEmb c σ → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → GlobalTheory.Dict.holSub0 (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU (U σ) '' (Formalism.L2.PjFree.cusp Xo c U a n : Set (Rul Xo c))) := by
  intro hC E _ _ _ H Dw l Xo c r U hr hA hU σ hσ hG hP a n hdom hlast hn hχ
  have hrk : r = Dw.p + Dw.q := (hU σ hσ).1
  have h1 : 1 ≤ Dw.p + Dw.q := hrk ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : Dw.p + Dw.q ≤ n := by
    have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r h0
    omega
  have hd : ∃ d : DeltaDat Xo c n, d.IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧ d.cδ = 1 ∧
      d.pd = 1 ∧ d.l₂.A = l.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev E H Dw l Xo c h1 n 1 ⊤ l Xo c rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l Xo c
  have hunit : UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    have h : ∀ z : FrPt d.Xo₂ d.c₂ K, evR d.Xo₂ d.c₂ d.cδ z = 1 := fun z => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : c.Fˣ) : c.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [h y, h y']
    simp
  have htot : ShortValTot Xo c nab 1 0 a n d :=
    GlobalTheory.shortValTot_of_pinned hL hC E H Dw l Xo c n d (GlobalTheory.levelMaps_closed hL E H Dw h1)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c)
      (GlobalTheory.Frames.algebraic_laws hB E H Dw _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
      nab 1 0 a
  refine (GlobalTheory.T.cuspForms_vanishing_off_frames_le_span_shortTheta hC E H Dw l Xo c n d σ r (U σ) hσ (hU σ hσ) hr hA hG hP hlev hnab hunit h3
    (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a Nat.one_pos hdom hn hχ htot).trans
    (Submodule.span_mono (Set.image_mono ?_))
  exact GlobalTheory.T.short_thetaSeries_dominant_weight_isCuspForm hC E H Dw l Xo c n d r U hr hU hlev hnab hunit (fun _ => ⟨ph, 1, x₀, hpin⟩) nab 1 0 a hdom hlast

end GlobalTheory.Dict
