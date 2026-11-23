import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapInitialVertex
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrd
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrdOne
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

local instance (priority := 2000) intAlg5 {Φ : Type} [Field Φ] : Algebra ℤ (RatFunc Φ) := Ring.toIntAlgebra _

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

open GroundTheory.Heights₂.Heights.Inter

theorem div_eq_of_local {P Δ : Ideal (MRing ι)} (hPp : P.IsPrime) (hΔp : Δ.IsPrime) (hrel : IsRelevant Δ)
    (hPΔ : P ≤ Δ) {g h : MRing ι} (hgP : g ∉ P) (hhΔ : h ∉ Δ) (hgΔ : g ∈ Δ)
    (hsat : ∀ d ∈ Δ, ∃ u ∉ Δ, u * d ∈ P ⊔ Ideal.span {g})
    (key : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → P ≤ W → ¬ Δ ≤ W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * g - v * h ∈ P) :
    divCycle P g = divCycle P h + Finsupp.single Δ 1 := by
  have hP : h ∉ P := fun hh => hhΔ (hPΔ hh)
  have hone : multAt (P ⊔ Ideal.span {g}) Δ = 1 := by
    unfold multAt
    rw [dif_pos hΔp, DiagonalOrderOne.length_eq_one_of_sat _ Δ
      (sup_le hPΔ ((Ideal.span_singleton_le_iff_mem _).2 hgΔ)) hsat]
    rfl
  have hJΔ : P ⊔ Ideal.span {g * h} ≤ Δ :=
    sup_le hPΔ ((Ideal.span_singleton_le_iff_mem _).mpr (Δ.mul_mem_right h hgΔ))
  have hΔ : Δ ∈ divSupp P (g * h) := by
    refine ⟨⟨⟨hΔp, hJΔ⟩, fun Q hQ hQΔ => ?_⟩, hrel⟩
    by_contra hΔQ
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    obtain ⟨u, v, huQ, hvQ, hm⟩ :=
      key Q hQ.1 (fun k => (hrel k).imp fun _ hi hq' => hi (hQΔ hq')) hPQ hΔQ
    have hhQ : h ∉ Q := fun hh' => hhΔ (hQΔ hh')
    have hgQ : g ∈ Q :=
      (hQ.1.mem_or_mem (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))).resolve_right hhQ
    have hvh : v * h ∈ Q := by
      have e : v * h = u * g - (u * g - v * h) := by ring
      rw [e]
      exact Q.sub_mem (Q.mul_mem_left u hgQ) (hPQ hm)
    rcases hQ.1.mem_or_mem hvh with h1 | h1
    exacts [hvQ h1, hhQ h1]
  ext W
  have hcg := DiagonalDivisor.divCycle_eq_ite (s := g) hP W
  have hch := DiagonalDivisor.divCycle_eq_ite (s := h) hgP W
  rw [mul_comm h g] at hch
  rw [Finsupp.add_apply, hcg, hch, Finsupp.single_apply]
  by_cases hW : W ∈ divSupp P (g * h)
  · rw [if_pos hW, if_pos hW]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hWΔ : Δ = W
    · rw [if_pos hWΔ, ← hWΔ, hone, DiagonalOrder.multAt_eq_zero_of_not_le hΔp
        (fun hle => hhΔ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))))]
    · rw [if_neg hWΔ, add_zero]
      have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
      have hΔW : ¬ Δ ≤ W := fun hle => hWΔ (le_antisymm hle (hW.1.2 ⟨hΔp, hJΔ⟩ hle))
      obtain ⟨u, v, hu, hv, hm⟩ := key W hWp hW.2 hPW hΔW
      exact DiagonalOrder.multAt_sup_span_eq hWp hPW hu hv hm
  · rw [if_neg hW, if_neg hW, if_neg (fun h' : Δ = W => hW (h' ▸ hΔ)), add_zero]

theorem exists_point (W : Ideal (MRing ι)) (hW : W.IsPrime) :
    ∃ (E : Type) (_ : Field E) (z : (Σ k, ι k) → E), ∀ f : MRing ι, aeval z f = 0 ↔ f ∈ W := by
  have gen : ∀ (E : Type) [Field E] (ρ : MRing ι →+* E) (f : MRing ι), aeval (fun q => ρ (X q)) f = ρ f := by
    intro E _ ρ f
    have e : (aeval (fun q => ρ (X q)) : MRing ι →ₐ[ℤ] E).toRingHom = ρ :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp
    exact RingHom.congr_fun e f
  let E := FractionRing (MRing ι ⧸ W)
  let ρ : MRing ι →+* E := (algebraMap (MRing ι ⧸ W) E).comp (Ideal.Quotient.mk W)
  refine ⟨E, inferInstance, fun q => ρ (X q), fun f => ?_⟩
  rw [gen E ρ f]
  exact (map_eq_zero_iff (algebraMap (MRing ι ⧸ W) E) (IsFractionRing.injective _ _)).trans
    Ideal.Quotient.eq_zero_iff_mem

def monoX (c : ∀ k, ι k) (d : K → ℕ) : MRing ι := ∏ k, X ⟨k, c k⟩ ^ d k

theorem isMultiHomog_monoX (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (monoX c d) d := by
  rw [← Bridge.isMultiHomog_iff]
  have := IsWeightedHomogeneous.prod (w := NumbersDVR.blockWeight ι) Finset.univ
    (fun k => (X ⟨k, c k⟩ : MRing ι) ^ d k) (fun k => d k • NumbersDVR.blockWeight ι ⟨k, c k⟩)
    (fun k _ => (isWeightedHomogeneous_X ℤ _ _).pow (d k))
  have e : ∑ k, d k • NumbersDVR.blockWeight ι ⟨k, c k⟩ = d := by
    funext k
    simp [NumbersDVR.blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at this
  exact this

theorem aeval_monoX (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval z (monoX c d) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [monoX]

theorem aeval_monoX_ne {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    aeval z (monoX c d) ≠ 0 := by
  rw [aeval_monoX]
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

theorem chartMono_mul {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {dg dh : K → ℕ} {e : K → ℤ}
    (he : ∀ k, (dg k : ℤ) - dh k = e k) : chartMono z c e * aeval z (monoX c dh) = aeval z (monoX c dg) := by
  rw [aeval_monoX, aeval_monoX, chartMono, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← he, ← zpow_natCast, ← zpow_add₀ (hc k), sub_add_cancel, zpow_natCast]

theorem chartMono_ne {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (e : K → ℤ) :
    chartMono z c e ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)

theorem exists_rel {w : (Σ k, ι k) → Φ} {z : (Σ k, ι k) → L} (hz : IsPt w z) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {σ : Φ} {e : K → ℤ} {v : L} (hv : HasVal w z (σ / chartMono w c e) v)
    {g h : MRing ι} {dg dh : K → ℕ} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (he : ∀ k, (dg k : ℤ) - dh k = e k) (hq : aeval w g = σ * aeval w h) :
    ∃ u u' : MRing ι, aeval z u ≠ 0 ∧ aeval z u' = v * chartMono z c e * aeval z u ∧
      u * g - u' * h ∈ mCoordIdeal w := by
  have hcw : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => hz.coord_ne (hc k)
  obtain ⟨d, n, m, hn, hm, h0, e1, e2⟩ := hv
  refine ⟨m * monoX c dh, n * monoX c dg, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero h0 (aeval_monoX_ne hc _)
  · rw [map_mul, map_mul, e2, ← chartMono_mul hc he]; ring
  · have hd : IsMultiHomog (m * monoX c dh * g - n * monoX c dg * h) (d + dh + dg) := by
      refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hm (isMultiHomog_monoX _ _)) hg) ?_
      rw [add_right_comm]
      exact isMultiHomog_mul (isMultiHomog_mul hn (isMultiHomog_monoX _ _)) hh
    rw [mem_iff_of_homog hd]
    simp only [map_sub, map_mul, e1, hq, ← chartMono_mul hcw he]
    have := chartMono_ne hcw e
    field_simp
    ring

theorem congr_aeval {σ : Type} (O : Subring Φ) (a b : σ → Φ) (V : Φ) (ha : ∀ q, a q ∈ O) (hb : ∀ q, b q ∈ O)
    (hab : ∀ q, ∃ ρ ∈ O, a q - b q = ρ * V) (f : MvPolynomial σ ℤ) :
    aeval a f ∈ O ∧ ∃ ρ ∈ O, aeval a f - aeval b f = ρ * V := by
  induction f using MvPolynomial.induction_on with
  | C n => exact ⟨by simp, 0, zero_mem _, by simp⟩
  | add f g hf hg =>
    obtain ⟨h1, ρ, h2, h3⟩ := hf
    obtain ⟨h1', ρ', h2', h3'⟩ := hg
    exact ⟨by rw [map_add]; exact add_mem h1 h1', ρ + ρ', add_mem h2 h2', by
      rw [map_add, map_add]; linear_combination h3 + h3'⟩
  | mul_X f q hf =>
    obtain ⟨h1, ρ, h2, h3⟩ := hf
    obtain ⟨ρ', h2', h3'⟩ := hab q
    refine ⟨by rw [map_mul, aeval_X]; exact mul_mem h1 (ha q), aeval a f * ρ' + ρ * b q,
      add_mem (mul_mem h1 h2') (mul_mem h2 (hb q)), ?_⟩
    rw [map_mul, map_mul, aeval_X, aeval_X]
    linear_combination (aeval a f) * h3' + b q * h3

variable {y : (Σ k, ι k) → Φ} {k₀ : K} {B : ι k₀ → Φ} {cf : Φ} {e : K → ℤ}

def totDeg (k₀ : K) (e : K → ℤ) : Option K → ℤ := fun o => o.elim 1 fun k => e k + if k = k₀ then 1 else 0

namespace PenFrame

variable {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e z c)

theorem αA : ∑ m, Fr.α m * y ⟨k₀, m⟩ = Fr.ε⁻¹ := by
  have h := Fr.αp
  simp only [Fr.p_eq, mul_left_comm _ Fr.ε, ← Finset.mul_sum] at h
  exact eq_inv_of_mul_eq_one_right h

theorem βA : ∑ m, Fr.β m * y ⟨k₀, m⟩ = 0 := by
  have h := Fr.βp
  simp only [Fr.p_eq, mul_left_comm _ Fr.ε, ← Finset.mul_sum] at h
  exact (mul_eq_zero.1 h).resolve_left Fr.ε_ne

theorem αB : ∑ m, Fr.α m * B m = -(Fr.δ * Fr.ε⁻¹ * Fr.γ⁻¹) := by
  have h := Fr.αr
  simp only [Fr.r_eq, mul_add, Finset.sum_add_distrib, mul_left_comm _ Fr.γ, mul_left_comm _ Fr.δ, ← Finset.mul_sum,
    Fr.αA] at h
  have := Fr.γ_ne
  have h' : ∑ m, Fr.α m * B m = Fr.γ⁻¹ * (Fr.γ * ∑ m, Fr.α m * B m) := by rw [inv_mul_cancel_left₀ this]
  rw [h', eq_neg_of_add_eq_zero_left h]; ring

theorem βB : ∑ m, Fr.β m * B m = Fr.γ⁻¹ := by
  have h := Fr.βr
  simp only [Fr.r_eq, mul_add, Finset.sum_add_distrib, mul_left_comm _ Fr.γ, mul_left_comm _ Fr.δ, ← Finset.mul_sum,
    Fr.βA, mul_zero, add_zero] at h
  exact eq_inv_of_mul_eq_one_right h

end PenFrame

theorem pen_lin (μ : ι k₀ → Φ) (A : ι k₀ → Φ) (t : RatFunc Φ) :
    ∑ m, algebraMap Φ (RatFunc Φ) (μ m) * penCo y k₀ A B t ⟨none, m⟩ =
      algebraMap Φ (RatFunc Φ) (∑ m, μ m * A m) + t * algebraMap Φ (RatFunc Φ) (∑ m, μ m * B m) := by
  simp only [penCo, mul_add, Finset.sum_add_distrib, mul_left_comm _ t, ← Finset.mul_sum, ← map_mul, ← map_sum]

theorem local_data {z : (Σ o : Option K, ι (o.getD k₀)) → L}
    (hz : IsPt (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z) {c : ∀ o, iW ι k₀ o} (hc : ∀ o, z ⟨o, c o⟩ ≠ 0)
    (Fr : PenFrame y k₀ B cf e (z ∘ v₀ k₀) fun k => c (some k)) :
    ∃ (η U V : RatFunc Φ) (Uv : L),
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z η
        (Fr.sv * ∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) ∧
      (∀ m, z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩ =
        Fr.pv m * ∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) ∧
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z U Uv ∧
      HasVal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) z V (∑ m, Fr.βv m * (z ⟨none, m⟩ / z ⟨none, c none⟩)) ∧
      (∀ m, penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X ⟨none, m⟩ /
          penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X ⟨none, c none⟩ =
        algebraMap Φ (RatFunc Φ) (Fr.p m) * U + algebraMap Φ (RatFunc Φ) (Fr.r m) * V) ∧
      RatFunc.X * algebraMap Φ (RatFunc Φ) cf /
        chartMono (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) c (totDeg k₀ e) = η * V := by
  set w := penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X with hw
  let φ := algebraMap Φ (RatFunc Φ)
  have hz0 : IsPt y (z ∘ v₀ k₀) := hz.comp (isBlockMap_initial_vertex k₀) φ rfl
  have pull : ∀ {s v}, HasVal y (z ∘ v₀ k₀) s v → HasVal w z (φ s) v := fun h => h.pull (isBlockMap_initial_vertex k₀) φ rfl
  have hcy : ∀ k, y ⟨k, c (some k)⟩ ≠ 0 := fun k => hz0.coord_ne (q := ⟨k, c (some k)⟩) (hc (some k))
  have hcw : w ⟨none, c none⟩ ≠ 0 := hz.coord_ne (hc none)
  have hε := Fr.ε_ne
  have hγ := Fr.γ_ne
  have hU₀ : HasVal y (z ∘ v₀ k₀) (∑ m, Fr.α m * (y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩))
      (∑ m, Fr.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c (some k₀)⟩)) :=
    HasVal.sum _ fun m _ => (Fr.hα m).mul (hasVal_ratio hz0 m (c (some k₀)) (hc (some k₀)))
  have eU₀ : (∑ m, Fr.α m * (y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩)) = Fr.ε⁻¹ / y ⟨k₀, c (some k₀)⟩ := by
    rw [← Fr.αA, Finset.sum_div]
    simp only [mul_div_assoc]
  rw [eU₀] at hU₀
  have lin : ∀ (μ : ι k₀ → Φ) (μv : ι k₀ → L), (∀ m, HasVal y (z ∘ v₀ k₀) (μ m) (μv m)) →
      HasVal w z ((φ (∑ m, μ m * y ⟨k₀, m⟩) + RatFunc.X * φ (∑ m, μ m * B m)) / w ⟨none, c none⟩)
        (∑ m, μv m * (z ⟨none, m⟩ / z ⟨none, c none⟩)) := fun μ μv h => by
    rw [← pen_lin (y := y), Finset.sum_div]
    simp only [mul_div_assoc]
    exact HasVal.sum _ fun m _ => (pull (h m)).mul (hasVal_ratio hz (k := none) m (c none) (hc none))
  have hU := lin _ _ Fr.hα
  have hV := lin _ _ Fr.hβ
  rw [Fr.αA, Fr.αB] at hU
  rw [Fr.βA, Fr.βB] at hV
  have hφε : φ Fr.ε ≠ 0 := (map_ne_zero φ).2 hε
  have hφγ : φ Fr.γ ≠ 0 := (map_ne_zero φ).2 hγ
  refine ⟨_, _, _, _, pull (Fr.hs.mul hU₀), fun m => ?_, hU, hV, fun m => ?_, ?_⟩
  · refine (hasVal_ratio hz0 m (c (some k₀)) (hc (some k₀))).unique hz0 ?_
    have := (Fr.hp m).mul hU₀
    rwa [Fr.p_eq, show Fr.ε * y ⟨k₀, m⟩ * (Fr.ε⁻¹ / y ⟨k₀, c (some k₀)⟩) = y ⟨k₀, m⟩ / y ⟨k₀, c (some k₀)⟩ by
      field_simp] at this
  · rw [Fr.p_eq, Fr.r_eq, show w ⟨none, m⟩ = φ (y ⟨k₀, m⟩) + RatFunc.X * φ (B m) from rfl]
    simp only [map_mul, map_add, map_neg, map_inv₀, map_zero]
    change _ = φ _ * φ _ * _ + (φ _ * φ _ + φ _ * φ _) * _
    field_simp
    ring
  · have e1 : chartMono w c (totDeg k₀ e) = w ⟨none, c none⟩ *
        (φ (chartMono y (fun k => c (some k)) e) * φ (y ⟨k₀, c (some k₀)⟩)) := by
      rw [chartMono, Fintype.prod_option, chartMono, map_prod]
      congr 1
      · exact zpow_one _
      · have : ∀ k, w ⟨some k, c (some k)⟩ ^ totDeg k₀ e (some k) = φ (y ⟨k, c (some k)⟩ ^ e k) *
            if k = k₀ then φ (y ⟨k₀, c (some k₀)⟩) else 1 := fun k => by
          show φ (y ⟨k, c (some k)⟩) ^ (e k + if k = k₀ then 1 else 0) = _
          rw [zpow_add₀ ((map_ne_zero φ).2 (hcy k)), map_zpow₀]
          split_ifs with h
          · subst h; rw [zpow_one]
          · rw [zpow_zero]
        simp only [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    have h1 : φ (chartMono y (fun k => c (some k)) e) ≠ 0 := (map_ne_zero φ).2 (chartMono_ne hcy e)
    have h2 : φ (y ⟨k₀, c (some k₀)⟩) ≠ 0 := (map_ne_zero φ).2 (hcy k₀)
    rw [e1]
    simp only [map_mul, map_div₀, map_inv₀, map_zero]
    change RatFunc.X * φ cf / _ = _
    field_simp
    ring

theorem isPt_diag {z : (Σ k, ι k) → L} (hz : IsPt y z) :
    IsPt (ext2 y k₀ fun m => y ⟨k₀, m⟩) (ext2 z k₀ fun m => z ⟨k₀, m⟩) := by
  let fold : (Σ o : Option K, ι (o.getD k₀)) → Σ k, ι k := fun q => ⟨q.1.getD k₀, q.2⟩
  have e1 : (ext2 y k₀ fun m => y ⟨k₀, m⟩) = y ∘ fold := by
    funext q
    rcases q with ⟨_ | k, m⟩ <;> rfl
  have e2 : (ext2 z k₀ fun m => z ⟨k₀, m⟩) = z ∘ fold := by
    funext q
    rcases q with ⟨_ | k, m⟩ <;> rfl
  rw [e1, e2]
  refine ⟨fun o => hz.1 (o.getD k₀), fun f hf => ?_⟩
  rw [← aeval_rename]
  refine hz.2 _ ?_
  have hf' : mConeMap (y ∘ fold) f = 0 := hf
  have e : (mConeMap y).comp (rename fold) = ((rename fun o : Option K => o.getD k₀).restrictScalars ℤ).comp
      (mConeMap (y ∘ fold)) := MvPolynomial.algHom_ext fun q => by simp [mConeMap, fold]
  have := DFunLike.congr_fun e f
  simp only [AlgHom.comp_apply, hf', map_zero] at this
  exact this

theorem sec_pen (h0 : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hFr : ∀ (E : Type) [Field E] (z : (Σ k, ι k) → E), IsPt y z → ∀ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) →
      Nonempty (PenFrame y k₀ B cf e z c)) :
    ∃ (g h : MRing (iW ι k₀)) (dg dh : Option K → ℕ), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      g ∉ mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) ∧
      h ∉ mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) ∧
      (∀ o, (dg o : ℤ) - dh o = totDeg k₀ e o) ∧
      aeval (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) g =
        RatFunc.X * algebraMap Φ (RatFunc Φ) cf * aeval (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X) h ∧
      divCycle (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X)) g =
        divCycle (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X)) h +
          Finsupp.single (mCoordIdeal (ext2 y k₀ fun m => y ⟨k₀, m⟩)) 1 := by
  set w := penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X with hw
  set δ := ext2 y k₀ fun m => y ⟨k₀, m⟩ with hδ
  let φ := algebraMap Φ (RatFunc Φ)
  choose c₀ hc₀ using h0
  let c : ∀ o, iW ι k₀ o := fun o => c₀ (o.getD k₀)
  have hc : ∀ o, δ ⟨o, c o⟩ ≠ 0 := by
    rintro (_ | k)
    · exact hc₀ k₀
    · exact hc₀ k
  have hle : mCoordIdeal w ≤ mCoordIdeal δ := pen_le_zero _ _ _ _
  have hpt : IsPt w δ := ⟨fun o => ⟨c o, hc o⟩, fun f hf => aeval_eq_zero_of_mem (hle hf)⟩
  have hcw : ∀ o, w ⟨o, c o⟩ ≠ 0 := fun o => hpt.coord_ne (hc o)
  obtain ⟨Fr⟩ := hFr Φ y (isPt_self fun k => ⟨c₀ k, hc₀ k⟩) c₀ hc₀
  obtain ⟨η, U, V, Uv, hη, hp, hU, hV, hrel, hσ⟩ := local_data (cf := cf) (e := e) hpt hc Fr
  rw [← hw] at hη hU hV hrel hσ
  have hηv : (Fr.sv * ∑ m, Fr.αv m * (δ ⟨some k₀, m⟩ / δ ⟨some k₀, c (some k₀)⟩)) ≠ 0 := by
    refine mul_ne_zero Fr.sv_ne fun h => ?_
    have := hp (c (some k₀))
    rw [h, mul_zero, div_self (hc _)] at this
    exact one_ne_zero this
  have hV0 : (∑ m, Fr.βv m * (δ ⟨none, m⟩ / δ ⟨none, c none⟩)) = 0 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, hasVal_self_eq (Fr.hβ _)]
    rw [show (∑ m, Fr.β m * δ ⟨none, m⟩) = 0 from Fr.βA, zero_div]
  rw [hV0] at hV
  have hcf : cf ≠ 0 := by
    rintro rfl
    exact Fr.hs.ne_zero (isPt_self fun k => ⟨c₀ k, hc₀ k⟩) Fr.sv_ne (by simp)
  have hσ0 : RatFunc.X * φ cf ≠ 0 := mul_ne_zero RatFunc.X_ne_zero ((map_ne_zero φ).2 hcf)
  obtain ⟨d, n, m, hn, hm, hm0, e1, e2⟩ := hη.mul hV
  let dp : Option K → ℕ := fun o => (totDeg k₀ e o).toNat
  let dm : Option K → ℕ := fun o => (-totDeg k₀ e o).toNat
  have hpm : ∀ o, (dp o : ℤ) - dm o = totDeg k₀ e o := fun o => Int.toNat_sub_toNat_neg _
  have hg := isMultiHomog_mul hn (isMultiHomog_monoX c dp)
  have hh := isMultiHomog_mul hm (isMultiHomog_monoX c dm)
  have hdeg : ∀ o, ((d + dp) o : ℤ) - (d + dm) o = totDeg k₀ e o := fun o => by
    rw [← hpm]; simp
  have hhδ : aeval δ (m * monoX c dm) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hm0 (aeval_monoX_ne hc _)
  have hhw : aeval w (m * monoX c dm) ≠ 0 := hpt.aeval_ne hh hhδ
  have hmono := chartMono_ne hcw (totDeg k₀ e)
  have hq : aeval w (n * monoX c dp) = RatFunc.X * φ cf * aeval w (m * monoX c dm) := by
    rw [map_mul, map_mul, e1, ← hσ, ← chartMono_mul hcw hpm]
    change RatFunc.X * φ cf / _ * _ * _ = _
    field_simp
  set g := n * monoX c dp
  set h := m * monoX c dm
  have hgw : g ∉ mCoordIdeal w := fun hh' => mul_ne_zero hσ0 hhw (hq ▸ aeval_eq_zero_of_mem hh')
  have hΔp : (mCoordIdeal δ).IsPrime := RingHom.ker_isPrime _
  refine ⟨g, h, d + dp, d + dm, hg, hh, hgw, fun hh' => hhw (aeval_eq_zero_of_mem hh'), hdeg, hq, ?_⟩
  refine div_eq_of_local (RingHom.ker_isPrime _) hΔp (CoordinateConeArithVar.relevant δ c hc) hle hgw
    (fun hh' => hhδ (aeval_eq_zero_of_mem hh')) ((mem_iff_of_homog hg).2 (by
      rw [map_mul, e2, mul_zero, zero_mul, zero_mul])) ?_ ?_
  · let J : Ideal (MRing (iW ι k₀)) :=
      { carrier := {f | ∃ u ∉ mCoordIdeal δ, u * f ∈ mCoordIdeal w ⊔ Ideal.span {g}}
        add_mem' := by
          rintro a b ⟨u, hu, hua⟩ ⟨v, hv, hvb⟩
          refine ⟨u * v, fun hm => (hΔp.mem_or_mem hm).elim hu hv, ?_⟩
          have e' : u * v * (a + b) = v * (u * a) + u * (v * b) := by ring
          rw [e']
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hua) (Ideal.mul_mem_left _ _ hvb)
        zero_mem' := ⟨1, fun h1 => hΔp.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simp⟩
        smul_mem' := by
          rintro a b ⟨u, hu, hub⟩
          refine ⟨u, hu, ?_⟩
          rw [smul_eq_mul, mul_left_comm]
          exact Ideal.mul_mem_left _ _ hub }
    refine mCoordIdeal_le_of_homog (J := J) fun f a hf hf0 => ?_
    have pull : ∀ {s v}, HasVal y y s v → φ s ∈ regO w δ := fun h =>
      ⟨_, HasVal.pull (isBlockMap_initial_vertex k₀) φ (y' := w) (z' := δ) rfl h⟩
    let sc : Option K → RatFunc Φ := fun o => o.elim (φ Fr.ε * U) fun k => (φ (y ⟨k, c₀ k⟩))⁻¹
    have hrat : ∀ q, CoordinateConeArithVar.ratioPt w c q ∈ regO w δ := fun q =>
      ⟨_, hasVal_ratio hpt q.2 (c q.1) (hc q.1)⟩
    have hb1 : ∀ m, sc none * (φ ∘ δ) ⟨none, m⟩ = φ (Fr.p m) * U := fun m => by
      rw [Fr.p_eq, map_mul]
      show φ Fr.ε * U * φ (y ⟨k₀, m⟩) = _
      ring
    have hb2 : ∀ k m, sc (some k) * (φ ∘ δ) ⟨some k, m⟩ = CoordinateConeArithVar.ratioPt w c ⟨some k, m⟩ := fun k m => by
      show (φ (y ⟨k, c₀ k⟩))⁻¹ * φ (y ⟨k, m⟩) = φ (y ⟨k, m⟩) / φ (y ⟨k, c₀ k⟩)
      rw [div_eq_mul_inv, mul_comm]
    obtain ⟨-, ρ, hρ, hρe⟩ := congr_aeval (regO w δ) (CoordinateConeArithVar.ratioPt w c)
      (fun q => sc q.1 * (φ ∘ δ) q) V hrat (by
        rintro ⟨_ | k, m⟩
        · exact hb1 m ▸ mul_mem (pull (Fr.hp m)) ⟨_, hU⟩
        · exact hb2 k m ▸ hrat _) (by
        rintro ⟨_ | k, m⟩
        · refine ⟨φ (Fr.r m), pull (Fr.hr m), ?_⟩
          rw [hb1 m, show CoordinateConeArithVar.ratioPt w c ⟨none, m⟩ = _ from hrel m]
          exact add_sub_cancel_left _ _
        · exact ⟨0, zero_mem _, by rw [hb2 k m, sub_self, zero_mul]⟩) f
    rw [aeval_scale' sc _ hf, CPts.aeval_comp_ringHom, hf0, map_zero, mul_zero, sub_zero, aeval_ratioPt hf] at hρe
    obtain ⟨ρv, hρ⟩ := hρ
    obtain ⟨d', n', m', hn', hm', hm0', e1', -⟩ := hρ.mul (hη.inv hpt hηv)
    have hη0 : η ≠ 0 := hη.ne_zero hpt hηv
    refine ⟨m' * monoX c (d + dp) * h, fun hh' => ?_, ?_⟩
    · have := aeval_eq_zero_of_mem hh'
      rw [map_mul, map_mul] at this
      exact mul_ne_zero (mul_ne_zero hm0' (aeval_monoX_ne hc _)) hhδ this
    · have hd : IsMultiHomog (m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g)
          (d' + (d + dp) + (d + dm) + a) := by
        refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul
          (isMultiHomog_mul hm' (isMultiHomog_monoX _ _)) hh) hf) ?_
        rw [show d' + (d + dp) + (d + dm) + a = d' + a + (d + dm) + (d + dp) by ring]
        exact isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_mul hn' (isMultiHomog_monoX _ _))
          (isMultiHomog_monoX _ _)) hg
      have hP : m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g ∈ mCoordIdeal w := by
        rw [mem_iff_of_homog hd]
        have h1 : aeval w f = aeval w (monoX c a) * (ρ * V) := by
          rw [← hρe, aeval_monoX, ← mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one fun k _ => by
            rw [← mul_pow, mul_inv_cancel₀ (hcw k), one_pow], one_mul]
        have h2 : RatFunc.X * φ cf = η * V * chartMono w c (totDeg k₀ e) := by
          rw [← hσ]; exact (div_mul_cancel₀ _ hmono).symm
        rw [map_sub, map_mul _ _ f, map_mul _ _ g, map_mul _ _ h, map_mul _ m', map_mul _ (n' * _), map_mul _ n', h1, hq, h2, e1',
          ← chartMono_mul hcw hdeg]
        field_simp
        ring
      have e' : m' * monoX c (d + dp) * h * f = (m' * monoX c (d + dp) * h * f - n' * monoX c a * monoX c (d + dm) * g)
          + n' * monoX c a * monoX c (d + dm) * g := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mem_sup_left hP)
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))
  · intro W hW hWr hPW hΔW
    obtain ⟨E, _, z, hz⟩ := exists_point W hW
    choose c' hc' using hWr
    have hc'' : ∀ o, z ⟨o, c' o⟩ ≠ 0 := fun o h => hc' o ((hz _).1 (by rwa [aeval_X]))
    have hzp : IsPt w z := ⟨fun o => ⟨c' o, hc'' o⟩, fun f hf => (hz f).2 (hPW hf)⟩
    have hz0 : IsPt y (z ∘ v₀ k₀) := hzp.comp (isBlockMap_initial_vertex k₀) φ rfl
    obtain ⟨Fr'⟩ := hFr E (z ∘ v₀ k₀) hz0 (fun k => c' (some k)) fun k => hc'' (some k)
    obtain ⟨η', U', V', Uv', hη', hp', hU', hV', hrel', hσ'⟩ := local_data (cf := cf) (e := e) hzp hc'' Fr'
    rw [← hw] at hη' hU' hV' hrel' hσ'
    set U₀ := ∑ m, Fr'.αv m * (z ⟨some k₀, m⟩ / z ⟨some k₀, c' (some k₀)⟩)
    set Vv := ∑ m, Fr'.βv m * (z ⟨none, m⟩ / z ⟨none, c' none⟩)
    have hU₀ : U₀ ≠ 0 := fun h => by
      have := hp' (c' (some k₀))
      rw [h, mul_zero, div_self (hc'' _)] at this
      exact one_ne_zero this
    have hVv : Vv ≠ 0 := fun h => hΔW <| by
      rw [h] at hV'
      have h1 : ∀ m, z ⟨none, m⟩ / z ⟨none, c' none⟩ = Fr'.pv m * Uv' := fun m => by
        refine (hasVal_ratio hzp (k := none) m (c' none) (hc'' none)).unique hzp ?_
        rw [hrel' m]
        simpa only [mul_zero, add_zero] using (((Fr'.hp m).pull (isBlockMap_initial_vertex k₀) φ (y' := w) rfl).mul hU').add
          (((Fr'.hr m).pull (isBlockMap_initial_vertex k₀) φ (y' := w) rfl).mul hV')
      let sc : Option K → E := fun o => o.elim (z ⟨none, c' none⟩ * Uv' / (U₀ * z ⟨some k₀, c' (some k₀)⟩)) fun _ => 1
      have h2 : z = fun q => sc q.1 * ext2 (z ∘ v₀ k₀) k₀ (fun m => (z ∘ v₀ k₀) ⟨k₀, m⟩) q := by
        funext q
        rcases q with ⟨_ | k, m⟩
        · show z ⟨none, m⟩ = z ⟨none, c' none⟩ * Uv' / (U₀ * z ⟨some k₀, c' (some k₀)⟩) * z ⟨some k₀, m⟩
          have a1 := (div_eq_iff (hc'' none)).1 (h1 m)
          have a2 := (div_eq_iff (hc'' (some k₀))).1 (hp' m)
          have a3 := hc'' (some k₀)
          rw [a1, a2]
          field_simp
        · exact (one_mul _).symm
      refine mCoordIdeal_le_of_homog fun f a hf hf0 => (hz f).1 ?_
      rw [h2, aeval_scale' sc _ hf, (isPt_diag hz0).2 f ((mem_iff_of_homog hf).2 hf0), mul_zero]
    obtain ⟨u, u', hu, hu', hm⟩ := exists_rel hzp hc'' (hσ' ▸ hη'.mul hV') hg hh hdeg hq
    refine ⟨u, u', fun h => hu ((hz _).2 h), fun h => ?_, hm⟩
    rw [(hz _).2 h] at hu'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero Fr'.sv_ne hU₀) hVv) (chartMono_ne hc'' _)) hu hu'.symm

end PositivityTheory.Xgp.W
