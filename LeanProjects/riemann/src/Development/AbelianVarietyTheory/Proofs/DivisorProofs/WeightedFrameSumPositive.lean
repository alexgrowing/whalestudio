import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSupNormLePeterssonIntegralComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedDictionaryBoundStatement
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SupModel

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_nonneg₀ {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    0 ≤ X.pnorm la P y := by
  unfold Data.pnorm; positivity

theorem pnorm_lact_eq {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    X.pnorm la P (lact γ y) = X.pnorm la P y := by
  have hχ : ‖X.χ la γ‖ = 1 := by
    obtain ⟨n, hn, h⟩ := X.χ_fin la
    have := congrArg norm (h γ hγ)
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  unfold Data.pnorm dmin
  simp only [GlobalTheory.MajInv.gram_lact X (X.Γ_stab γ hγ)]
  rw [hP.2.2 γ hγ _ hy, norm_mul, hχ, one_mul]

theorem pnorm_piecewise_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r}
    (hy : y ∈ X.dom) : X.pnorm la (X.dom.piecewise P 0) y = X.pnorm la P y := by
  unfold Data.pnorm
  rw [Set.piecewise_eq_of_mem _ _ _ hy]

theorem epStar_eq_epsLev (d M : ℕ) (w M' k0 : ℝ) (hk : M' * k0 = 2 * (M : ℝ) * Real.sqrt d) :
    epStar M' (fdeg E) w k0 = epsLev E d M w := by
  unfold epsLev epStar
  congr 2
  rw [show M' * ((fdeg E : ℝ) * w + 2) * k0 * Real.log 2 = (M' * k0) * ((fdeg E : ℝ) * w + 2) * Real.log 2 by ring, hk]
  ring

theorem comp_bound {r : ℕ} (hr : 0 < r) (X : Data E r) (Xx : DataX E r) (hX : Xx.toData = X) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (hP : P ∈ X.SS la) (w : ℝ) (hw0 : 0 < w) (hw : (∑ τ, X.spread la τ) ≤ w)
    (hχ : ∀ γ ∈ X.Γ, X.χ la γ = 1) (d M : ℕ)
    (hL : ∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ Xx.L') (M' : ℝ) (hM' : 0 < M')
    (hk : M' * Xx.k0 = 2 * (M : ℝ) * Real.sqrt d)
    (hT : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ,
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M' : ℂ) * τ.1 b))
    (x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))) (ho : IsOrth X x0) (hF : IsFundSet X x0 FF) :
    ∀ y ∈ X.dom, ENNReal.ofReal (X.pnorm la P y ^ 2) ≤ ENNReal.ofReal (locConst E r w (epsLev E d M w)) *
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (X.dom.piecewise P 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(muF X x0) := by
  subst hX
  intro y hy
  have h := GlobalTheory.T.cuspForm_sup_norm_le_petersson_integral_component E r Xx la P M' w x0 FF hr hP hM' hw hw0 hL
    (fun v hv hiso b hb hbi => by
      obtain ⟨γ, hγ, he⟩ := hT v hv hiso b hb hbi
      exact ⟨γ, hγ, hχ γ hγ, he⟩) ho hF y hy
  rw [epStar_eq_epsLev d M w M' Xx.k0 hk] at h
  refine h.trans (mul_le_mul' le_rfl ?_)
  have hae : ∀ᵐ z ∂(muF Xx.toData x0), z ∈ OmF Xx.toData x0 := by
    have h1 : ∀ᵐ z ∂(volume.restrict (OmF Xx.toData x0)), z ∈ OmF Xx.toData x0 :=
      ae_restrict_mem (ExF.isOpen_OmF Xx.toData x0).measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le h1
  refine lintegral_mono_ae (ae_restrict_of_ae ?_)
  filter_upwards [hae] with z hz
  rw [pnorm_piecewise_eq Xx.toData la P hz]

end GlobalTheory.SupModel

open GlobalTheory.SupModel in

theorem GlobalTheory.supPet_principal : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (w : ℝ), 0 < w → (∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w) → (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) → ∀ P ∈ holSub (U σ).X la, supE (U σ).X la P ^ 2 ≤ ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
  classical
  intro hMB hTB D j H Dw l Xo c U dict hLw σ hσ la w hw0 hspread hχ P hP
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hcusp := abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ).X la hP
  have hdat := fun k => GlobalTheory.T.exists_selfDual_data_transvection_principal_level D j H Dw l Xo c U dict hLw σ hσ k
  choose Xx hXx hg hΛ hL' M' hM' hk hT using hdat
  have hfs : ∀ k, ∃ x0, IsOrth ((U σ).X k) x0 ∧ ∃ FF, IsFundSet ((U σ).X k) x0 FF := fun k => by
    obtain ⟨x0, ho, FF, hF, -⟩ := GlobalTheory.DriftCovolume.finMu_unconditional D.R.r ((U σ).X k)
    exact ⟨x0, ho, FF, hF⟩
  choose x0 ho FF hF using hfs

  set Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞ := fun k u =>
    ENNReal.ofReal (((U σ).X k).pnorm (la k) (((U σ).X k).dom.piecewise (P k) 0) u ^ 2) with hΦdef
  have hsec : ∀ k, ((U σ).X k).IsSec (la k) (P k) := fun k => (hcusp k).1.1
  have hΦm : ∀ k, Measurable (Φ k) := fun k => by
    have hm := GlobalTheory.PeterssonCompare.measurable_pnorm ((U σ).X k) (la k)
      (P := ((U σ).X k).dom.piecewise (P k) 0)
      ((hsec k).1.continuousOn.congr fun u hu => Set.piecewise_eq_of_mem _ _ _ hu)
      (fun u hu => by rw [Set.piecewise_eq_of_notMem _ _ _ hu]; rfl)
    exact ENNReal.measurable_ofReal.comp (hm.pow_const 2)
  have hΦΓ : ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x := by
    intro k γ hγ u hu
    have hu' := GlobalTheory.MajInv.lact_mem_dom ((U σ).X k) (((U σ).X k).Γ_stab γ hγ) hu
    simp only [hΦdef]
    rw [pnorm_piecewise_eq _ _ _ hu, pnorm_piecewise_eq _ _ _ hu', pnorm_lact_eq _ (hsec k) hγ hu]
  have hΦB : ∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x := by
    intro k b hb u hu
    have hu' := OrthogonalFrameDomain.rmul_mem_dom ((U σ).X k) hu hb
    simp only [hΦdef]
    rw [pnorm_piecewise_eq _ _ _ hu, pnorm_piecewise_eq _ _ _ hu',
      FrameDegreeData.pnorm_rmul ((U σ).X k) (la k) (P k) (hsec k).2.1 u hu b hb]
  obtain ⟨hS0, hStop, hΦeq⟩ := GlobalTheory.T.adelicProbability_eq_normalised_fundamentalSets D j H Dw l Xo c U dict hLw σ hσ x0 FF (fun k => ⟨ho k, hF k⟩)
  have heq := hΦeq Φ hΦm hΦΓ hΦB
  have hms := GlobalTheory.T.framed_dictionary_bound hMB hTB D j H Dw l Xo c U dict hLw σ hσ x0 FF (fun k => ⟨ho k, hF k⟩)

  obtain ⟨Kf, th, hr', -, -, hU, -⟩ := hLw.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := hU.2.2.2.1

  have hpet : (∫⁻ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 (D.sp.W j))) =
      petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
    rw [petE, eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
    refine lintegral_congr fun q => ?_
    simp only [hΦdef, ptN]
    rw [pnorm_piecewise_eq _ _ _ (hdom _), Real.enorm_eq_ofReal (pnorm_nonneg₀ _ _ _ _), ← ENNReal.ofReal_pow (pnorm_nonneg₀ _ _ _ _)]
  set S := ∑ k, muF ((U σ).X k) (x0 k) (FF k) with hSdef

  have hpt : ∀ p : Formalism.L2.Pj.FPt (U σ).X, ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P p.1) p.2) ^ 2 ≤
      ENNReal.ofReal (supConst D.host.E D.R.r D.host.d l.M w) * petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 := by
    rintro ⟨k, y, hy⟩
    rw [← ENNReal.ofReal_pow (pnorm_nonneg₀ _ _ _ _)]
    have h1 := GlobalTheory.SupModel.comp_bound hr ((U σ).X k) (Xx k) (hXx k) (la k) (P k) (hcusp k) w hw0 (hspread k) (hχ k)
      D.host.d l.M (hL' k) (M' k) (hM' k) (hk k) (hT k) (x0 k) (FF k) (ho k) (hF k) y hy
    have h2 : (∫⁻ z in FF k, Φ k (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k) (x0 k) z) ∂(muF ((U σ).X k) (x0 k))) ≤
        petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
      calc _ ≤ ∑ k', ∫⁻ z in FF k', Φ k' (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k') (x0 k') z) ∂(muF ((U σ).X k') (x0 k')) :=
            Finset.single_le_sum (f := fun k' => ∫⁻ z in FF k', Φ k' (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X k') (x0 k') z)
              ∂(muF ((U σ).X k') (x0 k'))) (fun _ _ => bot_le) (Finset.mem_univ k)
        _ = petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * S := by rw [← heq, hpet]
        _ ≤ _ := mul_le_mul' le_rfl hms
    by_cases hLc : 0 ≤ locConst D.host.E D.R.r w (epsLev D.host.E D.host.d l.M w)
    · calc _ ≤ ENNReal.ofReal (locConst D.host.E D.R.r w (epsLev D.host.E D.host.d l.M w)) * (petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) la P ^ 2 * ENNReal.ofReal (massLev D.host.E D.R.r l.M)) :=
            h1.trans (mul_le_mul' le_rfl h2)
        _ = _ := by
          rw [supConst, ENNReal.ofReal_mul hLc]
          ring
    · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hLc)), zero_mul] at h1
      exact (le_antisymm h1 bot_le) ▸ bot_le

  show (⨆ p : Formalism.L2.Pj.FPt (U σ).X, ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1) (P p.1) p.2)) ^ 2 ≤ _
  rcases isEmpty_or_nonempty (Formalism.L2.Pj.FPt (U σ).X) with hE | hN
  · rw [iSup_of_empty]; simp
  · rw [ENNReal.iSup_pow]
    exact iSup_le hpt
