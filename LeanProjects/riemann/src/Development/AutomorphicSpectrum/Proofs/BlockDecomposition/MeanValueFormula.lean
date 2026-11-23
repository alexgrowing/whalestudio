import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumNeZeroEqSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIntegralMultipleBoundedPlacesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteProductDifferenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TailSumOverPlacesSmallStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultipliableLocalFactorsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApproxStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductConvergenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedSumLimitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHaarMeasureSingletonStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem tendsto_of_sandwich {α : Type*} {l : Filter α} {f : α → ℝ} {L : ℝ}
    (h : ∀ η : ℝ, 0 < η → ∃ (a b : α → ℝ) (A B : ℝ), Tendsto a l (𝓝 A) ∧ Tendsto b l (𝓝 B) ∧
      (∀ᶠ x in l, a x ≤ f x ∧ f x ≤ b x) ∧ L - η ≤ A ∧ B ≤ L + η) : Tendsto f l (𝓝 L) := by
  rw [tendsto_order]
  constructor
  · intro c hc
    obtain ⟨a, b, A, B, ha, -, hab, hA, -⟩ := h ((L - c) / 2) (by linarith)
    have hcA : c < A := by linarith
    filter_upwards [(tendsto_order.1 ha).1 c hcA, hab] with x h1 h2
    exact lt_of_lt_of_le h1 h2.1
  · intro c hc
    obtain ⟨a, b, A, B, -, hb, hab, -, hB⟩ := h ((c - L) / 2) (by linarith)
    have hcB : B < c := by linarith
    filter_upwards [(tendsto_order.1 hb).2 c hcB, hab] with x h1 h2
    exact lt_of_le_of_lt h2.2 h1

theorem exists_small (a : ℝ) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ a * (1 + e) ^ n ≤ a + η ∧ a - η ≤ a * (1 - e) ^ n := by
  have c1 : Tendsto (fun t : ℝ => a * (1 + t) ^ n) (𝓝 0) (𝓝 a) := by
    have : Continuous fun t : ℝ => a * (1 + t) ^ n := by fun_prop
    simpa using this.tendsto 0
  have c2 : Tendsto (fun t : ℝ => a * (1 - t) ^ n) (𝓝 0) (𝓝 a) := by
    have : Continuous fun t : ℝ => a * (1 - t) ^ n := by fun_prop
    simpa using this.tendsto 0
  have e1 := c1.eventually_lt_const (show a < a + η by linarith)
  have e2 := c2.eventually_const_lt (show a - η < a by linarith)
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨min (r / 2) 1, lt_min (by linarith) one_pos, min_le_right _ _, ?_⟩
  have hd : dist (min (r / 2) 1) (0 : ℝ) < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by linarith) one_pos)]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨(hh hd).1.le, (hh hd).2.le⟩

theorem truncSum_tendsto (hE : Equi) (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (hli : IsStdInf li) (hlam : ∀ v, IsStdV v (lam v))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (C : ℝ) (hG : Continuous G) (hGc : HasCompactSupport G) (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (hgo : ∀ v, v ∉ S → GoodFac v (lam v) C (g v)) (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : S ⊆ T) :
    Tendsto (truncSum θ G T g) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))) := by
  have hI : 0 ≤ ∫ y, G y ∂li := integral_nonneg hG0
  have hP : 0 ≤ ∏ v ∈ S, ∫ s, g v s ∂(lam v) := Finset.prod_nonneg fun v _ => integral_nonneg (hg0 v)
  refine tendsto_of_sandwich fun η hη => ?_
  obtain ⟨e, he, he1, hup, hlo⟩ := exists_small ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v)) (T \ S).card hη
  have hex : ∀ v, ∃ lo up : Fv F v → ℝ, (v ∈ S → lo = g v ∧ up = g v) ∧ (v ∉ S → Continuous lo ∧
      HasCompactSupport lo ∧ Continuous up ∧ HasCompactSupport up ∧ (∀ s, 0 ≤ lo s) ∧
      (∀ s, s ≠ 0 → lo s ≤ g v s ∧ g v s ≤ up s) ∧ 1 - e ≤ ∫ s, lo s ∂(lam v) ∧ ∫ s, up s ∂(lam v) ≤ 1 + e) := by
    intro v
    by_cases hv : v ∈ S
    · exact ⟨g v, g v, fun _ => ⟨rfl, rfl⟩, fun h => absurd hv h⟩
    · obtain ⟨a, b, h⟩ := GlobalTheory.T.local_factor_sandwich_approx F v (lam v) C (g v) (hlam v) (hg0 v) (hgo v hv) e he
      exact ⟨a, b, fun h' => absurd h' hv, fun _ => h⟩
  choose lo up hS hO using hex
  have hcl : ∀ v ∈ T, Continuous (lo v) ∧ HasCompactSupport (lo v) := by
    intro v _
    by_cases hv : v ∈ S
    · rw [(hS v hv).1]; exact hgS v hv
    · exact ⟨(hO v hv).1, (hO v hv).2.1⟩
  have hcu : ∀ v ∈ T, Continuous (up v) ∧ HasCompactSupport (up v) := by
    intro v _
    by_cases hv : v ∈ S
    · rw [(hS v hv).2]; exact hgS v hv
    · exact ⟨(hO v hv).2.2.1, (hO v hv).2.2.2.1⟩
  have hpt : ∀ v (s : Fv F v), s ≠ 0 → 0 ≤ lo v s ∧ lo v s ≤ g v s ∧ g v s ≤ up v s := by
    intro v s hs
    by_cases hv : v ∈ S
    · rw [(hS v hv).1, (hS v hv).2]; exact ⟨hg0 v s, le_rfl, le_rfl⟩
    · have h := hO v hv
      exact ⟨h.2.2.2.2.1 s, (h.2.2.2.2.2.1 s hs).1, (h.2.2.2.2.2.1 s hs).2⟩
  have hemb : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : F), x ≠ 0 → algebraMap F (Fv F v) x ≠ 0 := by
    intro v x hx
    simpa using hx
  have hup0 : ∀ v, 0 ≤ ∫ s, up v s ∂(lam v) := by
    intro v
    refine integral_nonneg_of_ae ?_
    have h0 : ∀ᵐ s ∂(lam v), s ≠ (0 : Fv F v) := by
      rw [ae_iff]
      simpa using GlobalTheory.T.local_haar_measure_singleton F v (lam v) (hlam v)
    filter_upwards [h0] with s hs
    exact (hg0 v s).trans (hpt v s hs).2.2
  have hsplit : ∀ ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ,
      ∏ v ∈ T, ∫ s, ψ v s ∂(lam v) = (∏ v ∈ T \ S, ∫ s, ψ v s ∂(lam v)) * ∏ v ∈ S, ∫ s, ψ v s ∂(lam v) :=
    fun ψ => (Finset.prod_sdiff hT).symm
  have hSlo : ∏ v ∈ S, ∫ s, lo v s ∂(lam v) = ∏ v ∈ S, ∫ s, g v s ∂(lam v) :=
    Finset.prod_congr rfl fun v hv => by rw [(hS v hv).1]
  have hSup : ∏ v ∈ S, ∫ s, up v s ∂(lam v) = ∏ v ∈ S, ∫ s, g v s ∂(lam v) :=
    Finset.prod_congr rfl fun v hv => by rw [(hS v hv).2]
  have hlop : (1 - e) ^ (T \ S).card ≤ ∏ v ∈ T \ S, ∫ s, lo v s ∂(lam v) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by linarith)
      fun v hv => (hO v (Finset.mem_sdiff.1 hv).2).2.2.2.2.2.2.1
  have hupp : ∏ v ∈ T \ S, ∫ s, up v s ∂(lam v) ≤ (1 + e) ^ (T \ S).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun v _ => hup0 v)
      fun v hv => (hO v (Finset.mem_sdiff.1 hv).2).2.2.2.2.2.2.2
  refine ⟨truncSum θ G T lo, truncSum θ G T up, _, _,
    GlobalTheory.T.adelic_sandwich_approximation hE hC F hF θ hθ li lam hli hlam T G lo hG hGc hcl,
    GlobalTheory.T.adelic_sandwich_approximation hE hC F hF θ hθ li lam hli hlam T G up hG hGc hcu, ?_, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    have hsl := truncTerm_summable hC F hF θ hθ T G lo hGc (fun v hv => (hcl v hv).2) δ hδ0
    have hsu := truncTerm_summable hC F hF θ hθ T G up hGc (fun v hv => (hcu v hv).2) δ hδ0
    have hterm : ∀ β : {β : F // β ≠ 0},
        0 ≤ (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) β.1 := by
      intro β
      refine Set.indicator_nonneg (fun x _ => mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => hg0 v _)) _
    have hl : ∀ β : {β : F // β ≠ 0},
        (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, lo v (algebraMap F (Fv F v) x)) β.1 ≤
        (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) β.1 := by
      intro β
      by_cases hb : β.1 ∈ IntOut T
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _ => (hpt v _ (hemb v _ β.2)).1)
          fun v _ => (hpt v _ (hemb v _ β.2)).2.1) (hG0 _)
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    have hu : ∀ β : {β : F // β ≠ 0},
        (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) β.1 ≤
        (IntOut T).indicator (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, up v (algebraMap F (Fv F v) x)) β.1 := by
      intro β
      by_cases hb : β.1 ∈ IntOut T
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _ => hg0 v _)
          fun v _ => (hpt v _ (hemb v _ β.2)).2.2) (hG0 _)
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
    have hsg := Summable.of_nonneg_of_le hterm hu hsu
    have hpow : 0 ≤ δ ^ Module.finrank ℚ F := pow_nonneg hδ0.le _
    exact ⟨mul_le_mul_of_nonneg_left (hsl.tsum_le_tsum hl hsg) hpow,
      mul_le_mul_of_nonneg_left (hsg.tsum_le_tsum hu hsu) hpow⟩
  · rw [hsplit lo, hSlo]
    refine hlo.trans ?_
    have h2 := mul_le_mul_of_nonneg_left hlop (mul_nonneg hI hP)
    nlinarith [h2]
  · rw [hsplit up, hSup]
    refine le_trans ?_ hup
    have h2 := mul_le_mul_of_nonneg_left hupp (mul_nonneg hI hP)
    nlinarith [h2]

theorem exists_zero_place {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0) {x : F}
    (h : ¬ (x ∈ IntOut S ∧ ∀ v ∈ S, algebraMap F (Fv F v) x ∈ tsupport (g v))) :
    ∃ v, g v (algebraMap F (Fv F v) x) = 0 ∧ ∀ T, S ⊆ T → x ∈ IntOut T → v ∈ T := by
  by_cases h1 : x ∈ IntOut S
  · have h2 : ∃ v ∈ S, algebraMap F (Fv F v) x ∉ tsupport (g v) := by
      by_contra hcon
      exact h ⟨h1, fun v hv => by_contra fun hn => hcon ⟨v, hv, hn⟩⟩
    obtain ⟨v, hv, hvx⟩ := h2
    exact ⟨v, image_eq_zero_of_notMem_tsupport hvx, fun T hT _ => hT hv⟩
  · have h2 : ∃ v, v ∉ S ∧ algebraMap F (Fv F v) x ∉ v.adicCompletionIntegers F := by
      by_contra hcon
      exact h1 fun v hv => by_contra fun hn => hcon ⟨v, hv, hn⟩
    obtain ⟨v, hv, hvx⟩ := h2
    refine ⟨v, hz v hv _ hvx, fun T _ hxT => ?_⟩
    by_contra hvT
    exact hvx (hxT v hvT)

theorem err_bound (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hG : Continuous G)
    (hGc : HasCompactSupport G) (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0)
    (hb1 : ∀ v, v ∉ S → ∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ))
    (hb2 : ∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T₀ ∧ ∀ T, T₀ ⊆ T → ∀ δ : ℝ, 0 < δ →
      |fullSum θ G g δ - truncSum θ G T g δ| ≤ η := by
  obtain ⟨N, hN, hNx⟩ := GlobalTheory.T.exists_integral_multiple_bounded_places F S (fun v => tsupport (g v)) (fun v hv => (hgS v hv).2)
  obtain ⟨C', hC'0, hcount⟩ := GlobalTheory.T.euler_product_convergence_bound hC F hF θ hθ (tsupport G) hGc N hN
  obtain ⟨MG, hMG⟩ := hGc.exists_bound_of_continuous hG
  have hmex : ∀ v, ∃ m : ℝ, 0 ≤ m ∧ (v ∈ S → ∀ s, g v s ≤ m) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨m, hm⟩ := (hgS v hv).2.exists_bound_of_continuous (hgS v hv).1
      exact ⟨|m|, abs_nonneg _, fun _ s => ((le_abs_self _).trans (hm s)).trans (le_abs_self _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hv⟩
  choose m hm0 hm using hmex
  set M : ℝ := |MG| * ∏ v ∈ S, m v with hMdef
  have hM0 : 0 ≤ M := mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun v _ => hm0 v)
  have hden : 0 < M * C' + 1 := by positivity
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.T.tail_sum_over_places_small F C hC0 (η / (M * C' + 1)) (div_pos hη hden)
  refine ⟨T₁ ∪ S, Finset.subset_union_right, ?_⟩
  intro T hT δ hδ
  have hST : S ⊆ T := Finset.subset_union_right.trans hT
  have hT1 : T₁ ⊆ T := Finset.subset_union_left.trans hT
  have hfin := support_finite hC F hF θ hθ S (tsupport G) hGc (fun v => tsupport (g v))
    (fun v hv => (hgS v hv).2) δ hδ
  set B : Finset F := hfin.toFinset with hBdef
  have hBm : ∀ x ∈ B, x ≠ 0 ∧ x ∈ IntOut S ∧ θ δ * algebraMap F (Ainf F) x ∈ tsupport G ∧
      ∀ v ∈ S, algebraMap F (Fv F v) x ∈ tsupport (g v) := fun x hx => (hfin.mem_toFinset).1 hx
  have hB0 : ∀ x ∈ B, x ≠ 0 := fun x hx => (hBm x hx).1
  have hIT : ∀ x ∈ B, x ∈ IntOut T := fun x hx v hv => (hBm x hx).2.1 v (fun h => hv (hST h))
  have hMul : ∀ x : F, x ≠ 0 → Multipliable fun v => g v (algebraMap F (Fv F v) x) :=
    fun x hx => GlobalTheory.T.multipliable_local_factors F S C g hb2 x hx
  have hout : ∀ x, x ≠ 0 → x ∉ B → G (θ δ * algebraMap F (Ainf F) x) = 0 ∨
      ∃ v, g v (algebraMap F (Fv F v) x) = 0 ∧ ∀ T, S ⊆ T → x ∈ IntOut T → v ∈ T := by
    intro x hx hxB
    by_cases h1 : θ δ * algebraMap F (Ainf F) x ∈ tsupport G
    · right
      refine exists_zero_place S g hz fun h2 => hxB ?_
      exact (hfin.mem_toFinset).2 ⟨hx, h2.1, h1, h2.2⟩
    · left
      exact image_eq_zero_of_notMem_tsupport h1
  have e1 : ∑' β : {β : F // β ≠ 0}, G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1) =
      ∑ x ∈ B, G (θ δ * algebraMap F (Ainf F) x) * ∏' v, g v (algebraMap F (Fv F v) x) := by
    refine tsum_ne_zero_eq_sum (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏' v, g v (algebraMap F (Fv F v) x)) B hB0 ?_
    intro x hx hxB
    change G (θ δ * algebraMap F (Ainf F) x) * ∏' v, g v (algebraMap F (Fv F v) x) = 0
    rcases hout x hx hxB with h | ⟨v, hv, -⟩
    · rw [h, zero_mul]
    · rw [tprod_of_exists_eq_zero (f := fun v => g v (algebraMap F (Fv F v) x)) ⟨v, hv⟩, mul_zero]
  have e2 : ∑' β : {β : F // β ≠ 0}, (IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) β.1 =
      ∑ x ∈ B, G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x) := by
    rw [tsum_ne_zero_eq_sum ((IntOut T).indicator
      (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, g v (algebraMap F (Fv F v) x))) B hB0 ?_]
    · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (hIT x hx) _
    · intro x hx hxB
      by_cases hxT : x ∈ IntOut T
      · rw [Set.indicator_of_mem hxT]
        rcases hout x hx hxB with h | ⟨v, hv, hvT⟩
        · simp only [h, zero_mul]
        · rw [Finset.prod_eq_zero (hvT T hST hxT) hv, mul_zero]
      · exact Set.indicator_of_notMem hxT _
  have hpow : 0 ≤ δ ^ Module.finrank ℚ F := pow_nonneg hδ.le _

  have key : ∀ U : Finset (HeightOneSpectrum (𝓞 F)), T ⊆ U →
      δ ^ Module.finrank ℚ F * ∑ x ∈ B, |G (θ δ * algebraMap F (Ainf F) x) *
        (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))| ≤ η := by
    intro U hU
    have hsub : T \ S ⊆ U \ S := Finset.sdiff_subset_sdiff hU le_rfl
    have hx1 : ∀ x ∈ B, |G (θ δ * algebraMap F (Ainf F) x) *
        (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))| ≤
        M * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| := by
      intro x hx
      have hU' := Finset.prod_sdiff (f := fun v => g v (algebraMap F (Fv F v) x)) (hST.trans hU)
      have hT' := Finset.prod_sdiff (f := fun v => g v (algebraMap F (Fv F v) x)) hST
      have hexp := GlobalTheory.T.finite_product_difference_bound _ (fun v => g v (algebraMap F (Fv F v) x)) (T \ S) (U \ S) hsub
      have hfac : G (θ δ * algebraMap F (Ainf F) x) *
          (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x)) =
          (G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ S, g v (algebraMap F (Fv F v) x)) *
          (∏ v ∈ U \ S, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T \ S, g v (algebraMap F (Fv F v) x)) := by
        rw [← hU', ← hT']; ring
      have hGS0 : 0 ≤ G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ S, g v (algebraMap F (Fv F v) x) :=
        mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => hg0 v _)
      have hGS : G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ S, g v (algebraMap F (Fv F v) x) ≤ M := by
        refine mul_le_mul ?_ (Finset.prod_le_prod (fun v _ => hg0 v _) fun v hv => hm v hv _)
          (Finset.prod_nonneg fun v _ => hg0 v _) (abs_nonneg _)
        exact ((le_abs_self _).trans (hMG _)).trans (le_abs_self _)
      rw [hfac, abs_mul, abs_of_nonneg hGS0]
      exact mul_le_mul hGS hexp (abs_nonneg _) hM0
    have hfilter : ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S, ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ≤
        η / (M * C' + 1) := by
      refine le_trans (le_of_eq ?_) (hT₁ T hT1 (U \ S))
      refine Finset.sum_congr (Finset.filter_congr ?_) fun _ _ => rfl
      intro D hD
      have hDU := Finset.mem_powerset.1 hD
      refine not_congr ⟨fun h => h.trans Finset.sdiff_subset, fun h v hv => ?_⟩
      exact Finset.mem_sdiff.2 ⟨h hv, (Finset.mem_sdiff.1 (hDU hv)).2⟩
    have hcnt : ∀ D ∈ (U \ S).powerset.filter (fun D => ¬ D ⊆ T \ S),
        δ ^ Module.finrank ℚ F * ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| ≤
          C' * ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
      intro D hD
      have hDU := Finset.mem_powerset.1 (Finset.mem_filter.1 hD).1
      have hdis : Disjoint D S := by
        rw [Finset.disjoint_left]
        intro v hv hvS
        exact (Finset.mem_sdiff.1 (hDU hv)).2 hvS
      refine hcount S C g hC0 (fun v hv => ⟨hb1 v hv, hb2 v hv⟩) δ hδ D hdis B ?_
      intro x hx
      obtain ⟨h0, h1, h2, h3⟩ := hBm x hx
      exact ⟨h0, h1, hNx x h1 h3, h2⟩
    calc δ ^ Module.finrank ℚ F * ∑ x ∈ B, |G (θ δ * algebraMap F (Ainf F) x) *
          (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))|
        ≤ δ ^ Module.finrank ℚ F * ∑ x ∈ B, M * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S,
            ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hx1) hpow
      _ = M * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S, δ ^ Module.finrank ℚ F *
            ∑ x ∈ B, ∏ v ∈ D, |g v (algebraMap F (Fv F v) x) - 1| := by
          rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun D _ => ?_
          ring
      _ ≤ M * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S, C' *
            ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcnt) hM0
      _ = M * C' * ∑ D ∈ (U \ S).powerset with ¬ D ⊆ T \ S,
            ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ M * C' * (η / (M * C' + 1)) := mul_le_mul_of_nonneg_left hfilter (mul_nonneg hM0 hC'0)
      _ ≤ η := by
          rw [mul_div_assoc', div_le_iff₀ hden]
          nlinarith [mul_nonneg hM0 hC'0]

  have hlim : Tendsto (fun U : Finset (HeightOneSpectrum (𝓞 F)) => δ ^ Module.finrank ℚ F * ∑ x ∈ B,
      |G (θ δ * algebraMap F (Ainf F) x) *
        (∏ v ∈ U, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))|) atTop
      (𝓝 (δ ^ Module.finrank ℚ F * ∑ x ∈ B, |G (θ δ * algebraMap F (Ainf F) x) *
        (∏' v, g v (algebraMap F (Fv F v) x) - ∏ v ∈ T, g v (algebraMap F (Fv F v) x))|)) := by
    refine Tendsto.const_mul _ (tendsto_finset_sum _ fun x hx => ?_)
    exact (((hMul x (hB0 x hx)).hasProd.sub_const _).const_mul _).abs
  have hfinal := le_of_tendsto hlim ((eventually_ge_atTop T).mono fun U hU => key U hU)
  unfold fullSum truncSum
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_nonneg hpow, ← Finset.sum_sub_distrib]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hpow) ?_
  refine le_trans (le_of_eq ?_) hfinal
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_sub]

theorem ofReal_fullSum (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (C : ℝ)
    (hGc : HasCompactSupport G) (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0)
    (hb2 : ∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2)
    (δ : ℝ) (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ Module.finrank ℚ F) * ∑' β : {β : F // β ≠ 0},
        ENNReal.ofReal (G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1)) =
      ENNReal.ofReal (fullSum θ G g δ) := by
  have hfin := support_finite hC F hF θ hθ S (tsupport G) hGc (fun v => tsupport (g v))
    (fun v hv => (hgS v hv).2) δ hδ
  have hnn : ∀ β : {β : F // β ≠ 0},
      0 ≤ G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1) := by
    intro β
    refine mul_nonneg (hG0 _) ?_
    refine ge_of_tendsto' (GlobalTheory.T.multipliable_local_factors F S C g hb2 β.1 β.2).hasProd fun U => ?_
    exact Finset.prod_nonneg fun v _ => hg0 v _
  have hsum : Summable fun β : {β : F // β ≠ 0} =>
      G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1) := by
    refine summable_of_ne_finset_zero (s := hfin.toFinset.subtype (fun x => x ≠ 0)) ?_
    intro b hb
    have hb' : b.1 ∉ hfin.toFinset := by simpa [Finset.mem_subtype] using hb
    by_cases h1 : θ δ * algebraMap F (Ainf F) b.1 ∈ tsupport G
    · obtain ⟨v, hv, -⟩ := exists_zero_place (x := b.1) S g hz fun h2 =>
        hb' ((hfin.mem_toFinset).2 ⟨b.2, h2.1, h1, h2.2⟩)
      rw [tprod_of_exists_eq_zero (f := fun v => g v (algebraMap F (Fv F v) b.1)) ⟨v, hv⟩, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  unfold fullSum
  rw [ENNReal.ofReal_mul (pow_nonneg hδ.le _), ENNReal.ofReal_tsum_of_nonneg hnn hsum]

theorem meanVal_of_equi_countBd : Equi → CountBd → MeanVal := by
  intro hE hC F _ _ hF θ hθ li lam hli hlam S G g C hG hGc hG0 hg0 hgS hgo
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := fun v => Nat.cast_nonneg _
  have hb1 : ∀ v, v ∉ S → ∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 →
      |g v s - 1| ≤ |C| / (Ideal.absNorm v.asIdeal : ℝ) := fun v hv s hs h0 =>
    ((hgo v hv).2.2.1 s hs h0).trans (div_le_div_of_nonneg_right (le_abs_self C) (hq v))
  have hb2 : ∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 →
      |g v s - 1| ≤ |C| / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := fun v hv s hs =>
    ((hgo v hv).2.2.2.1 s hs).trans (div_le_div_of_nonneg_right (le_abs_self C) (pow_nonneg (hq v) 2))
  have hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0 := fun v hv => (hgo v hv).2.1
  have hgood : ∀ v, v ∉ S → GoodFac v (lam v) C (g v) := fun v hv => hgo v hv
  have hR : Tendsto (fullSum θ G g) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨T, hST, hT⟩ := err_bound hC F hF θ hθ S G g |C| (abs_nonneg C) hG hGc hG0 hg0 hgS hz hb1 hb2
      (half_pos hε)
    have htr := truncSum_tendsto hE hC F hF θ hθ li lam hli hlam S G g C hG hGc hG0 hg0 hgS hgood T hST
    filter_upwards [Metric.tendsto_nhds.1 htr (ε / 2) (half_pos hε), self_mem_nhdsWithin] with δ h1 h2
    have h3 := hT T subset_rfl δ h2
    rw [Real.dist_eq] at h1 ⊢
    have h4 := abs_sub_le (fullSum θ G g δ) (truncSum θ G T g δ)
      ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v))
    linarith
  have hL := (ENNReal.continuous_ofReal.tendsto _).comp hR
  refine hL.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (ofReal_fullSum hC F hF θ hθ S G g |C| hGc hG0 hg0 hgS hz hb2 δ hδ).symm

end GlobalTheory.CompanionTheory.Mass.MeanV

end
