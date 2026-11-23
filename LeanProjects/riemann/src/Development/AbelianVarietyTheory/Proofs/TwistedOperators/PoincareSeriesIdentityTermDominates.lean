import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LongElementEmbeddingNormStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumProdNormLeOfProdNormLowerBoundStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRealPlacesMatrixCoefficientProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenCongruenceEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalImageRationalPointMulVecStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumLongVectorsDecayWeightLeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdDom

theorem eu_sub_le {n : ℕ} (u u' : Fin n → ℂ) : eu (u - u') ≤ eu u + eu u' := by
  have h : ∀ y : Fin n → ℂ, eu y = ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (Fin n))‖ := fun y => by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [h, h, h, WithLp.toLp_sub]; exact norm_sub_le _ _

theorem nrm_sub_le {D : D7} (θ : InfFam D) {V : HSp D} (B : Fr V) (g : GA D V) (τ : D.what₂.Tau)
    (y y' : Fin V.rank → D.host.E) : nrm θ B g τ (y - y') ≤ nrm θ B g τ y + nrm θ B g τ y' := by
  unfold nrm
  have e : (fun i => tauE D τ ((y - y') i)) = (fun i => tauE D τ (y i)) - fun i => tauE D τ (y' i) := by
    funext i; simp
  rw [e, mulVec_sub, mulVec_sub]; exact eu_sub_le _ _

theorem nrm_nonneg' {D : D7} (θ : InfFam D) {V : HSp D} (B : Fr V) (g : GA D V) (τ : D.what₂.Tau)
    (y : Fin V.rank → D.host.E) : 0 ≤ nrm θ B g τ y := Real.sqrt_nonneg _

set_option maxHeartbeats 1600000 in

theorem identity_dominates : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Base d → ∀ (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → ∀ (v : GlobalTheory.Unf.Vol Y) (φ : GA D Y → ℂ) (c : ℂ) (b s : ℝ) (x : GA D Y), GlobalTheory.Unf.IsContAut Y φ → (∀ h, ‖φ h‖ ≤ b) → b / 2 < ‖φ x‖ → 0 ≤ s → s ≤ 1 → Long θ p.A Λ x s → p.AdelicAt θ d Q (d.lat Λ fun _ => 1) 𝔪 v.μ φ c → 2 * Real.exp (Q + (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → 1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → ∫ h in v.𝓕, poin θ M (congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪) (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ ≠ 0 := by
  intro D θ hθ Y V d S S' M₀ M p Q hbase Λ 𝔪 hΛ h𝔪 v φ c b s x hφ hbnd hx hs0 hs1 hlong had hR2 hR1
  classical
  obtain ⟨ι, hι, hιc, hιi, hιQ, -, -, hιr, -, -⟩ := GlobalTheory.T.exists_unitary_embedding_stabilizer D θ hθ Y V 1 1 one_ne_zero d
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := v.haar
  set K := congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪 with hK
  set f : GA D V → ℂ := fun g => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * g) with hf
  have hcoef : Measurable (coef θ M K (p.v θ) (p.v θ)) := by
    have h1 := GlobalTheory.T.continuous_realPlacesMatrixCoefficientProduct D θ hθ V S M (p.v θ) (p.v θ)
    have h2 := GlobalTheory.T.isOpen_congruence_embedding D Y V d Λ 𝔪 hΛ h𝔪
    unfold coef
    exact Measurable.ite h2.measurableSet h1.measurable measurable_const
  have hfm : ∀ γ : GA D V, Measurable fun h => f (γ * ι h) := fun γ =>
    hcoef.comp (continuous_const.mul (continuous_const.mul hιc)).measurable
  have hcomap : (GQ V).comap ι = GQ Y := by ext h; simp [Subgroup.mem_comap, hιQ]
  have hfund : IsFundamentalDomain ((GQ V).comap ι) v.𝓕 v.μ := by rw [hcomap]; exact v.fund
  have hinv : ∀ γ ∈ (GQ V).comap ι, ∀ h, φ (γ * h) = φ h := fun γ hγ h =>
    hφ.1 γ (by rw [← hcomap]; exact hγ) h
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hbnd x)
  have hV1 : 1 ≤ V.rank := by have := d.rank; omega
  obtain ⟨hlongV, hz₀, hz1⟩ := GlobalTheory.T.long_element_embedding_norm D θ hθ Y V d p.A p.B hbase.adapted Λ x s hΛ hs0 hs1 hlong
  choose z hz using fun q : GQ V ⧸ ι.range.subgroupOf (GQ V) => GlobalTheory.T.exists_rational_image_rationalPoint_mulVec D V _ (q.out).2 (zv d)
  have hterm : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V),
      Integrable (fun h => f ((q.out : GA D V) * ι h)) v.μ ∧
      (∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ) * (∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q)) ^ (2 * V.rank + 5) ≤
        Real.exp Q * ‖c‖ ∧
      (z q - zv d ∉ 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) → ∀ h, f ((q.out : GA D V) * ι h) = 0) := by
    intro q
    have := had.term x _ (z q) (q.out).2 (hz q)
    simpa only [hf, hι, mul_assoc] using this
  have hmtm : ∀ a a' : GA D V, mt V (a * a') = mt V a * mt V a' := fun a a' => by simp [Formalism.L2.Theta.mt]
  have hmt1 : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  have hfix : ∀ g : GA D V, mt V g *ᵥ ratV (zv d) = ratV (zv d) → g ∈ ι.range := by
    intro g hg
    rw [hιr]
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have := congrFun hg i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, ratV, zv] using this
  have hcos : ∀ q q' : GQ V ⧸ ι.range.subgroupOf (GQ V),
      ((q.out : GA D V))⁻¹ * (q'.out : GA D V) ∈ ι.range → q = q' := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using h
  have hinj : ∀ q q', z q = z q' → q = q' := by
    intro q q' h
    refine hcos q q' (hfix _ ?_)
    rw [hmtm, ← Matrix.mulVec_mulVec, hz q', ← h, ← hz q, Matrix.mulVec_mulVec, ← hmtm, inv_mul_cancel, hmt1,
      Matrix.one_mulVec]
  set q₁ : GQ V ⧸ ι.range.subgroupOf (GQ V) := ((1 : GQ V) : GQ V ⧸ ι.range.subgroupOf (GQ V)) with hq₁
  have hq1 : ∀ q, z q = zv d → q = q₁ := by
    intro q h
    rw [← QuotientGroup.out_eq' q, hq₁, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hfix _ (by rw [hz, h])

  have hTle : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V), ‖∫ h, f ((q.out : GA D V) * ι h) * φ h ∂v.μ‖ ≤
      b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ := by
    intro q
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun h => norm_nonneg _)
      ((hterm q).1.norm.const_mul b) (Filter.Eventually.of_forall fun h => ?_)
    dsimp only
    rw [norm_mul, mul_comm b]
    exact mul_le_mul_of_nonneg_left (hbnd h) (norm_nonneg _)
  have hLle : ∀ q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GA D V) * ι h) * φ h‖ₑ ∂v.μ ≤
      ENNReal.ofReal (b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ) := by
    intro q
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal ((hterm q).1.norm.const_mul b)
      (Filter.Eventually.of_forall fun h => mul_nonneg hb0 (norm_nonneg _))]
    refine lintegral_mono fun h => ?_
    rw [← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, mul_comm b]
    exact mul_le_mul_of_nonneg_left (hbnd h) (norm_nonneg _)
  set β : (GQ V ⧸ ι.range.subgroupOf (GQ V)) → ℝ := fun q => b * ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ with hβ
  have hβ0 : ∀ q, 0 ≤ β q := fun q => mul_nonneg hb0 (integral_nonneg fun _ => norm_nonneg _)
  have hβle : ∀ q, β q ≤ b * (Real.exp Q * ‖c‖) := by
    intro q
    refine mul_le_mul_of_nonneg_left ?_ hb0
    have hP : 1 ≤ ∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q) := by
      simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
        (fun τ _ => hz1 _ (z q) (q.out).2 (hz q) τ)
    exact (le_mul_of_one_le_right (integral_nonneg fun _ => norm_nonneg _) (one_le_pow₀ hP)).trans (hterm q).2.1

  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  obtain ⟨Kx, hKx⟩ : ∃ Kx : ℝ, Kx = (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau := ⟨_, rfl⟩
  obtain ⟨Bt, hBt⟩ : ∃ Bt : ℝ, Bt = b * (Real.exp Q * ‖c‖) * (Real.exp Kx / R) := ⟨_, rfl⟩
  rw [← hRdef] at hR1 hR2
  rw [← hKx] at hR2
  have htail : ∀ t : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), ∑ q ∈ t.erase q₁, β q ≤ Bt := by
    intro t
    obtain ⟨L, hL⟩ : ∃ L : Lat V, L = 𝔪 • latAt (d.lat Λ fun _ => 1) (stabilizerEmbedding d x) := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : (GQ V ⧸ ι.range.subgroupOf (GQ V)) → (Fin V.rank → D.host.E), w = fun q => z q - zv d :=
      ⟨_, rfl⟩
    have hwq : ∀ q, w q = z q - zv d := fun q => by rw [hw]
    obtain ⟨t', ht'⟩ : ∃ t' : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), t' = (t.erase q₁).filter (fun q => w q ∈ L) :=
      ⟨_, rfl⟩
    have h1 : ∑ q ∈ t.erase q₁, β q = ∑ q ∈ t', β q := by
      rw [ht']
      refine (Finset.sum_filter_of_ne fun q _ hq => ?_).symm
      by_contra hL'
      apply hq
      have h0 := (hterm q).2.2 (fun h => hL' (by rw [hwq, hL]; exact h))
      simp [hβ, h0]
    have h2 : ∀ q ∈ t', β q ≤ b * (Real.exp Q * ‖c‖) *
        ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3) ^ (2 * V.rank + 5))⁻¹ := by
      intro q _
      have hτ : ∀ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 ≤ nrm θ p.B (stabilizerEmbedding d x) τ (z q) := by
        intro τ
        have a1 := nrm_sub_le θ p.B (stabilizerEmbedding d x) τ (z q) (zv d)
        have a2 := hz1 _ (z q) (q.out).2 (hz q) τ
        rw [hz₀ τ] at a1
        rw [hwq]
        linarith
      have hP' : 0 < ∏ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 :=
        Finset.prod_pos fun τ _ => by have := nrm_nonneg' θ p.B (stabilizerEmbedding d x) τ (w q); positivity
      have hPP : ∏ τ, (1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3 ≤ ∏ τ, nrm θ p.B (stabilizerEmbedding d x) τ (z q) :=
        Finset.prod_le_prod (fun τ _ => by have := nrm_nonneg' θ p.B (stabilizerEmbedding d x) τ (w q); positivity) fun τ _ => hτ τ
      have ha := (hterm q).2.1
      have ha0 : 0 ≤ ∫ h, ‖f ((q.out : GA D V) * ι h)‖ ∂v.μ := integral_nonneg fun _ => norm_nonneg _
      rw [Finset.prod_inv_distrib, Finset.prod_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hb0
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hP' _)]
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP'.le hPP _) ha0).trans ha
    have hw_inj : Set.InjOn w t' := by
      intro q _ q' _ h
      exact hinj q q' (sub_left_inj.1 (by rwa [hwq, hwq] at h))
    have hws : ∀ y ∈ t'.image w, y ∈ L ∧ y ≠ 0 := by
      intro y hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [ht', Finset.mem_filter, Finset.mem_erase] at hq
      exact ⟨hq.2, fun h0 => hq.1.1 (hq1 q (sub_eq_zero.1 (by rwa [hwq] at h0)))⟩
    have hsum := GlobalTheory.T.latticeSum_longVectors_decayWeight_le D θ V p.B (stabilizerEmbedding d x) L R hV1 hR1 (fun y hy hy0 => hRdef ▸ hlongV 𝔪 h𝔪 y (hL ▸ hy) hy0) (t'.image w) hws
    rw [← hKx] at hsum
    calc ∑ q ∈ t.erase q₁, β q = ∑ q ∈ t', β q := h1
      _ ≤ ∑ q ∈ t', b * (Real.exp Q * ‖c‖) * ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ (w q)) / 3) ^ (2 * V.rank + 5))⁻¹ :=
        Finset.sum_le_sum h2
      _ = b * (Real.exp Q * ‖c‖) * ∑ y ∈ t'.image w, ∏ τ, (((1 + nrm θ p.B (stabilizerEmbedding d x) τ y) / 3) ^ (2 * V.rank + 5))⁻¹ := by
        rw [Finset.sum_image hw_inj, Finset.mul_sum]
      _ ≤ Bt := by rw [hBt]; exact mul_le_mul_of_nonneg_left hsum (by positivity)

  have hall : ∀ t : Finset (GQ V ⧸ ι.range.subgroupOf (GQ V)), ∑ q ∈ t, β q ≤ b * (Real.exp Q * ‖c‖) + Bt := by
    intro t
    calc ∑ q ∈ t, β q ≤ ∑ q ∈ insert q₁ t, β q :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) fun q _ _ => hβ0 q
      _ = β q₁ + ∑ q ∈ (insert q₁ t).erase q₁, β q := (Finset.add_sum_erase _ _ (Finset.mem_insert_self _ _)).symm
      _ ≤ _ := add_le_add (hβle q₁) (htail _)
  have hβs : Summable β := summable_of_sum_le hβ0 hall
  have hfin : (∑' q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GQ V) * ι h) * φ h‖ₑ ∂v.μ) ≠ ⊤ := by
    have h1 : (∑' q : GQ V ⧸ ι.range.subgroupOf (GQ V), ∫⁻ h, ‖f ((q.out : GQ V) * ι h) * φ h‖ₑ ∂v.μ) ≤
        ∑' q, ENNReal.ofReal (β q) := ENNReal.tsum_le_tsum hLle
    have h2 : (∑' q, ENNReal.ofReal (β q)) = ENNReal.ofReal (∑' q, β q) := (ENNReal.ofReal_tsum_of_nonneg hβ0 hβs).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h1.trans h2.le)
  have hU := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (GA D Y) v.μ ι hιi (GQ V) v.𝓕 hfund f φ hfm hφ.2.measurable hinv hfin
  have htarget : (∫ h in v.𝓕, poin θ M K (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ) =
      ∫ h in v.𝓕, (∑' γ : GQ V, f (γ * ι h)) * φ h ∂v.μ := by
    congr 1; funext h; simp only [poin, hf, hι, mul_assoc]
  have h1r : ((q₁.out : GQ V) : GA D V) ∈ ι.range := by
    have := QuotientGroup.out_eq' q₁
    rw [hq₁, QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
    simpa using this
  obtain ⟨h₀, hh₀⟩ := h1r
  have hh₀Q : h₀ ∈ GQ Y := (hιQ h₀).1 (hh₀ ▸ (q₁.out).2)
  have hT1 : ∫ h, f ((q₁.out : GA D V) * ι h) * φ h ∂v.μ = c * φ x := by
    rw [← hh₀, ← had.one x]
    have e : (fun h => f (ι h₀ * ι h) * φ h) = fun h =>
        (fun h' => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h') * φ h') (h₀ * h) := by
      funext h
      show f (ι h₀ * ι h) * φ h = coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d (h₀ * h)) * φ (h₀ * h)
      rw [← map_mul, hφ.1 h₀ hh₀Q h]
      simp only [hf, hι]
    rw [e]
    exact integral_mul_left_eq_self (μ := v.μ)
      (fun h' => coef θ M K (p.v θ) (p.v θ) (stabilizerEmbedding d x⁻¹ * stabilizerEmbedding d h') * φ h') h₀
  rw [htarget]
  intro hI0
  have hH' := hU.2.update q₁ 0
  have hβ's : Summable (Function.update β q₁ 0) := hβs.update q₁ 0
  have hnorm := hH'.norm_le_of_bounded hβ's.hasSum (fun q => by
    by_cases hq : q = q₁
    · subst hq; simp
    · simp only [Function.update_apply, hq, if_false]; exact hTle q)
  have hts : ∑' q, Function.update β q₁ 0 q ≤ Bt := by
    refine hβ's.tsum_le_of_sum_le fun t => ?_
    rw [← Finset.sum_erase t (a := q₁) (by simp)]
    calc _ = ∑ q ∈ t.erase q₁, β q := Finset.sum_congr rfl fun q hq => by
            simp [Function.update_apply, Finset.ne_of_mem_erase hq]
      _ ≤ Bt := htail t
  rw [hI0, add_zero, zero_sub, norm_neg, hT1, norm_mul] at hnorm
  have hRpos : 0 < R := by linarith
  have hq' : Real.exp Q * Real.exp Kx / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hRpos, ← Real.exp_add]; linarith
  have hBt : Bt ≤ b * ‖c‖ / 2 := by
    calc Bt = (b * ‖c‖) * (Real.exp Q * Real.exp Kx / R) := by rw [hBt]; ring
      _ ≤ (b * ‖c‖) * (1 / 2) := mul_le_mul_of_nonneg_left hq' (by positivity)
      _ = _ := by ring
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 had.ne
  have := mul_lt_mul_of_pos_left hx hc0
  nlinarith

end GlobalTheory.IdDom

end
