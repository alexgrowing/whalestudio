import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicProbabilityEqNormalisedFundamentalSetsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLattices
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevPullNorm

theorem sum_mul_fibre {ι κ : Type} [Fintype ι] [Fintype κ] (π : ι → κ) (w : ι → ℕ) (N : ℕ) (I : κ → ℝ≥0∞)
    (h : ∀ k, ∑ᶠ i : {i // π i = k}, w i.1 = N) : ∑ i, (w i : ℝ≥0∞) * I (π i) = N * ∑ k, I k := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := h k
  rw [finsum_eq_sum_of_fintype] at hk
  rw [← hk, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_subtype _ (p := fun i => π i = k) (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [i.2]

theorem goodEmb_comp_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) :
    GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) ↔ GoodEmb d.c₂ σ₂ := by
  unfold GoodEmb
  rfl

theorem frame_tr {E : Type} [Field E] {r : ℕ} {A B : Finset (E →+* ℂ)} (h : A = B) (x : Frame A r) (ρ : E →+* ℂ)
    (h₁ : ρ ∈ B) (h₂ : ρ ∈ A) : (h ▸ x : Frame B r) ⟨ρ, h₁⟩ = x ⟨ρ, h₂⟩ := by
  subst h; rfl

theorem relab_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (τ : d.c₂.F →+* ℂ) :
    relab c (τ.comp (d.eF : c.F →+* d.c₂.F)) = relab d.c₂ τ := by
  funext ρ
  ext a
  rfl

theorem goodOf_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) :
    goodOf c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) = (goodOf d.c₂ σ₂).comp (d.eF : c.F →+* d.c₂.F) := by
  unfold goodOf
  by_cases h : GoodEmb d.c₂ σ₂
  · rw [if_pos ((goodEmb_comp_eF D d σ₂).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((goodEmb_comp_eF D d σ₂).1 h')), if_neg h]
    rfl

theorem pnorm_lact_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (δ : GL (Fin r) E) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r) (P : Frame X.Ψ r → ℂ) (P' : Frame X'.Ψ r → ℂ) (t : ℂ) (n : ℕ), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ v w, herm X.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X.Gm v w) → (∀ (τ : E →+* ℂ) (h : τ ∈ X'.Ψ) (i : Fin r), la' ⟨τ, h⟩ i = la ⟨τ, hΨ ▸ h⟩ i) → ‖t‖ = 1 → (∀ x ∉ X'.dom, P' x = 0) → (∀ x ∉ X.dom, P x = 0) → (∀ x ∈ X'.dom, P' x = t ^ n * P (lact δ (hΨ ▸ x))) → ∀ y : Frame X'.Ψ r, X'.pnorm la' P' y = X.pnorm la P (lact δ (hΨ ▸ y)) := by
  intro E _ _ _ r X X' hΨ δ la la' P P' t n hG hp hu hla ht h0' h0 hrel y
  cases X'
  cases hΨ
  cases hG
  cases hp
  have hla' : la' = la := funext fun τ => funext fun i => hla τ.1 τ.2 i
  subst hla'
  have hun : GlobalTheory.SW.IsUn X δ := hu
  have hd : ∀ (z : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm (lact δ z) τ i = dmin X.Gm z τ i :=
    fun z τ i => GlobalTheory.Dict.Extend.dmin_lact hun z τ i
  have hdom : ∀ z : Frame X.Ψ r, lact δ z ∈ X.dom → z ∈ X.dom := by
    intro z hz τ
    refine ⟨fun h => (hz τ).1 ?_, fun i => by rw [← hd z τ i]; exact (hz τ).2 i⟩
    show ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ).det = 0
    rw [Matrix.det_mul, h, mul_zero]
  show _ = X.pnorm _ P (lact δ y)
  unfold Data.pnorm
  by_cases hy : y ∈ X.dom
  · rw [hrel y hy, norm_mul, norm_pow, ht, one_pow, one_mul]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_)
    rw [hd, hd]
  · have hy' : lact δ y ∉ X.dom := fun h => hy (hdom y h)
    rw [h0' y hy, h0 _ hy', norm_zero, zero_mul, zero_mul]

theorem petE_sq_mul_vol : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (f : Rul Xo c), f ∈ cuspW Xo c U G → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ 0 ∧ (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ ⊤ ∧ petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) (modelWt (U σ) G) (rdU (U σ) f) ^ 2 * ∑ k, muF ((U σ).X k) (x0 k) (FF k) = ∑ k, ∫⁻ z in FF k, ENNReal.ofReal (((U σ).X k).pnorm (modelWt (U σ) G k) (rdU (U σ) f k) (cpt ((U σ).X k) (x0 k) z) ^ 2) ∂(muF ((U σ).X k) (x0 k)) := by
  intro D j H Dw l Xo c U dict hL σ hσ G f hf x0 FF hx
  have hsf : ∀ k, ((U σ).X k).IsSec (modelWt (U σ) G k) (rdU (U σ) f k) := fun k =>
    GlobalTheory.PeterssonCompare.isSec_of_mem_holSub _ _ ((mem_cuspW.1 hf).2 σ hσ) k
  obtain ⟨h0, hT, hI⟩ := GlobalTheory.T.adelicProbability_eq_normalised_fundamentalSets D j H Dw l Xo c U dict hL σ hσ x0 FF hx
  refine ⟨h0, hT, ?_⟩
  have := hI (fun k y => ENNReal.ofReal (((U σ).X k).pnorm (modelWt (U σ) G k) (rdU (U σ) f k) y ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _
      (hsf k).1.continuousOn (fun y hy => dif_neg hy)).pow_const 2))
    (fun k γ hγ y hy => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf k) hγ hy])
    (fun k b hb y hy => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf k).2.1 y hy b hb])
  rw [← this]
  congr 1
  unfold petE
  have e : eLpNorm (fun q => ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))) 2 (muQ1 (D.sp.W j)) ^ 2 =
      ∫⁻ q, ‖ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))‖ₑ ^ 2 ∂(muQ1 (D.sp.W j)) := by
    have := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (μ := muQ1 (D.sp.W j))
      (f := fun q => ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))) two_ne_zero
    simpa using this
  rw [e]
  refine lintegral_congr fun q => ?_
  have hnn : 0 ≤ ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q)) := by
    unfold ptN Data.pnorm
    positivity
  rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg hnn, ← ENNReal.ofReal_pow hnn]
  rfl

set_option maxHeartbeats 1600000 in

theorem petE_pull_good : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ (f g : _), f ∈ cuspW Xo c U (wtZ a n) → g ∈ cuspW d.Xo₂ d.c₂ U₂ (wtZ a n) → Pull d f g → ∀ τ : d.c₂.F →+* ℂ, GoodEmb d.c₂ τ →
    petE (D.sp.W j) (dict₂ τ) (muQ1 (D.sp.W j)) (modelWt (U₂ τ) (wtZ a n)) (rdU (U₂ τ) g) =
    petE (D.sp.W j) (dict (τ.comp (d.eF : c.F →+* d.c₂.F))) (muQ1 (D.sp.W j)) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n)) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f) := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn f g hf hg hp τ hτ
  have hσ : GoodEmb c (τ.comp (d.eF : c.F →+* d.c₂.F)) := (goodEmb_comp_eF D d τ).2 hτ
  obtain ⟨π, δ, N, hN, hcomp, hfib, t, ht1, hrel⟩ := GlobalTheory.T.levelCover_complexModels_components_isometries_degree D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd τ hτ
  have hex : ∀ (X : Data D.host.E D.R.r), ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF := fun X => by
    choose P _ hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ, GlobalTheory.MetricWeightTest.exists_fundSet_orth X (fun τ => hG τ)⟩
  choose x0 hx0 FF hFF using fun k => hex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k)
  choose x0₂ hx0₂ FF₂ hFF₂ using fun k => hex ((U₂ τ).X k)
  obtain ⟨hS0, hST, h1⟩ := petE_sq_mul_vol D j H Dw l Xo c U dict hL (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ (wtZ a n) f hf x0 FF (fun k => ⟨hx0 k, hFF k⟩)
  obtain ⟨hS0₂, hST₂, h2⟩ := petE_sq_mul_vol D j H Dw d.l₂ d.Xo₂ d.c₂ U₂ dict₂ hL₂ τ hτ (wtZ a n) g hg x0₂ FF₂
    (fun k => ⟨hx0₂ k, hFF₂ k⟩)
  have hΨ : ∀ k₂, ((U₂ τ).X k₂).Ψ = ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ := fun k₂ => Finset.ext fun ρ =>
    (((hL₂.unf τ hτ).2.1 k₂).2 ρ).trans (((hL.unf (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ).2.1 (π k₂)).2 ρ).symm
  have hp0 : ∀ k₂, ((U₂ τ).X k₂).p0 = ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).p0 := fun k₂ =>
    ((hL₂.unf τ hτ).2.1 k₂).1.trans ((hL.unf (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ).2.1 (π k₂)).1.symm
  have hsf : ∀ k, ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).IsSec (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) := fun k =>
    GlobalTheory.PeterssonCompare.isSec_of_mem_holSub _ _ ((mem_cuspW.1 hf).2 (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ) k
  have h0f : ∀ k, ∀ x ∉ ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).dom, rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k x = 0 := fun k x hx => dif_neg hx
  have h0g : ∀ k, ∀ x ∉ ((U₂ τ).X k).dom, rdU (U₂ τ) g k x = 0 := fun k x hx => dif_neg hx
  have hsecf : f ∈ sec Xo c a n := by
    have := cuspW_le_secZ (wtZ a n) hf
    rwa [GlobalTheory.AllWt.exZ_wtZ, secZ_nat] at this
  have hsecg : g ∈ sec d.Xo₂ d.c₂ a n := by
    have := cuspW_le_secZ (wtZ a n) hg
    rwa [GlobalTheory.AllWt.exZ_wtZ, secZ_nat] at this
  have hmeas : ∀ k, Measurable fun x => ENNReal.ofReal
      (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) x ^ 2) := fun k =>
    ENNReal.measurable_ofReal.comp
      ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _ (hsf k).1.continuousOn (h0f k)).pow_const 2)
  have hcint : ∀ k₂, ∫⁻ z in FF₂ k₂, ENNReal.ofReal (((U₂ τ).X k₂).pnorm (modelWt (U₂ τ) (wtZ a n) k₂)
        (rdU (U₂ τ) g k₂) (cpt ((U₂ τ).X k₂) (x0₂ k₂) z) ^ 2) ∂(muF ((U₂ τ).X k₂) (x0₂ k₂)) =
      ((((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ : ℝ≥0∞) *
        ∫⁻ z in FF (π k₂), ENNReal.ofReal (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) (π k₂))
        (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂)) (cpt ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂)) z) ^ 2) ∂(muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂))) ∧
      muF ((U₂ τ).X k₂) (x0₂ k₂) (FF₂ k₂) =
      ((((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ : ℝ≥0∞) *
        muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂)) (FF (π k₂)) := by
    intro k₂
    have hGm := (hcomp k₂).1
    have hu := (hcomp k₂).2.1
    have hle := (hcomp k₂).2.2.1
    have hidx := (hcomp k₂).2.2.2
    have hu' : ∀ v w, herm ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
        ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm v w := by
      rw [← hGm]; exact hu
    have hP := pnorm_lact_transport D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) (π k₂))
        (modelWt (U₂ τ) (wtZ a n) k₂) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂)) (rdU (U₂ τ) g k₂) (t k₂) n hGm (hp0 k₂) hu'
        (fun ρ h i => by simp only [modelWt, hp0 k₂, relab_eF])
        (ht1 k₂) (h0g k₂) (h0f (π k₂)) (fun x hx => by
          refine hrel a n ha f hsecf g hsecg hp k₂ x _ hx (fun ρ h₂ h₁ => ?_) hn
          show (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map ρ * mat (hΨ k₂ ▸ x) ⟨ρ, h₁⟩ = _
          congr 1
          unfold mat
          rw [frame_tr (hΨ k₂) x ρ h₁ h₂])
    refine ⟨?_, ?_⟩
    · simp_rw [hP]
      exact GlobalTheory.T.lintegral_fundamentalSet_conj_finiteIndex_subgroup D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (x0 (π k₂)) (x0₂ k₂)
        (FF (π k₂)) (FF₂ k₂) _ hGm (hp0 k₂) hu' hle hidx (hx0 _) (hx0₂ _) (hFF _) (hFF₂ _) (hmeas _)
        (fun γ hγ x hx => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf _) hγ hx])
        (fun b hb x hx => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf _).2.1 x hx b hb])
    · have := GlobalTheory.T.lintegral_fundamentalSet_conj_finiteIndex_subgroup D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (x0 (π k₂)) (x0₂ k₂)
        (FF (π k₂)) (FF₂ k₂) (fun _ => 1) hGm (hp0 k₂) hu' hle hidx (hx0 _) (hx0₂ _) (hFF _) (hFF₂ _)
        measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      simpa only [setLIntegral_one] using this
  set w : (U₂ τ).Comp → ℕ := fun k₂ =>
    (((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ with hw
  have hfib' : ∀ k, ∑ᶠ i : {i // π i = k}, w i.1 = N := fun k => by
    rw [← hfib k]
    exact finsum_congr fun i => by simp only [hw, i.2]
  have hA := sum_mul_fibre π w N (fun k => ∫⁻ z in FF k, ENNReal.ofReal (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k)
        (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) (cpt ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) z) ^ 2) ∂(muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k))) hfib'
  have hB := sum_mul_fibre π w N (fun k => muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k)) hfib'
  simp only [hw] at hA hB
  have e1 := h2
  simp only [fun k₂ => (hcint k₂).1, fun k₂ => (hcint k₂).2] at e1
  rw [hA, hB, ← h1] at e1
  have hNS0 : (N : ℝ≥0∞) * ∑ k, muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hN.ne') hS0
  have hNST : (N : ℝ≥0∞) * ∑ k, muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hST
  have e2 : petE (D.sp.W j) (dict₂ τ) (muQ1 (D.sp.W j)) (modelWt (U₂ τ) (wtZ a n)) (rdU (U₂ τ) g) ^ 2 =
      petE (D.sp.W j) (dict (τ.comp (d.eF : c.F →+* d.c₂.F))) (muQ1 (D.sp.W j)) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n)) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f) ^ 2 := by
    rw [← ENNReal.mul_left_inj hNS0 hNST, e1]
    ring
  have e3 : ∀ x y : ℝ≥0∞, x ^ 2 = y ^ 2 → x = y := fun x y h => by
    have h' : x ^ (2:ℝ) = y ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.rpow_natCast]; exact h
    exact ENNReal.rpow_left_injective two_ne_zero h'
  exact e3 _ _ e2

theorem levPull_normW : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ (f : cuspW Xo c U (wtZ a n)) (g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)), Pull d (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) → ∀ σ₂ : d.c₂.F →+* ℂ, normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ g = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp (d.eF : c.F →+* d.c₂.F)) f := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn f g hp σ₂
  simp only [normW, petW, petAt]
  rw [goodOf_eF D d σ₂, petE_pull_good D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn _ _ f.2 g.2 hp _
    (goodEmb_goodOf _ _)]

end GlobalTheory.LevPullNorm
