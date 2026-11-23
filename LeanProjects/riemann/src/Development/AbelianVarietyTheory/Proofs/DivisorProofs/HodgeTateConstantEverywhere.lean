import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropZStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionFlatWeightStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section
namespace GlobalTheory.HTConstModel

theorem val_vw_eq_of_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ)
    {C : Type} [Field C] (v : Valuation C NNReal) {a b : C} (ha : a ≠ 0) (hb : b ≠ 0) {M : ℕ} (hM : 1 ≤ M) {n : ℤ}
    (h : v a ^ M = v b ^ n) {κ : ℝ} (hκ : val_vw la p v b = (κ : EReal)) :
    val_vw la p v a = (((n : ℝ) / M * κ : ℝ) : EReal) := by
  rw [val_vw_of_ne la p v hb, EReal.coe_eq_coe_iff] at hκ
  rw [val_vw_of_ne la p v ha, EReal.coe_eq_coe_iff, ← hκ]
  have hva : (0 : ℝ) < v a := by simpa [pos_iff_ne_zero] using ha
  have hvb : (0 : ℝ) < v b := by simpa [pos_iff_ne_zero] using hb
  have hl : (M : ℝ) * Real.log (v a) = n * Real.log (v b) := by
    have := congrArg (fun t : NNReal => Real.log (t : ℝ)) h
    simp only [NNReal.coe_pow, NNReal.coe_zpow] at this
    rwa [Real.log_pow, Real.log_zpow] at this
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have : Real.log (v a) = n / M * Real.log (v b) := by
    field_simp
    linarith
  rw [this]
  ring

end GlobalTheory.HTConstModel

theorem GlobalTheory.FlatCore.htConst_always : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne →
    GlobalTheory.Published.DeRhamCanonicalExtension → GlobalTheory.Published.PrismaticDieudonneHodge → Always fun U x => HTConst U x := by
  intro hP h1 h2 h3 E _ _ _ H Dw l Xo c r U x hL Z τ s la
  obtain ⟨O, _, _, _, _, ϖ, hϖ, Zs, f, D, hInt, hNorm, hProp, hFlat, hLB, hT, sig, κ, hsig, hw⟩ :=
    GlobalTheory.T.archimedean_section_flat_weight hP h1 h2 h3 E H Dw l Xo c r U x hL Z τ s la
  have hconn := GlobalTheory.T.special_fibre_connected O Zs f hInt hNorm hProp hFlat
  obtain ⟨M, n, hM, -, hV⟩ :=
    GlobalTheory.T.prop_z_statement O ϖ hϖ Zs f D ⟨hInt, hNorm, hProp, hFlat, hconn, hLB, hT⟩ sig hsig
  refine ⟨(n : ℝ) / M * κ, fun w hw' => ?_⟩
  obtain ⟨p, _, R, _, _, φ, hv, hφi, hφl, ybar, y, e, cc, hyb, hy, he, hco, hval, hκ⟩ := hw w hw'
  have h := (hV R ℂ_[p] NNReal (Valued.v : Valuation ℂ_[p] NNReal) hv φ hφi hφl ybar hyb y hy).2 e cc he hco
  have hb : algebraMap R ℂ_[p] (φ ϖ) ≠ 0 := fun h0 =>
    hϖ.ne_zero (hφi ((hv.hom_inj (h0.trans (map_zero _).symm)).trans (map_zero φ).symm))
  rw [hval]
  exact GlobalTheory.HTConstModel.val_vw_eq_of_pow la p _ cc.ne_zero hb hM h hκ
