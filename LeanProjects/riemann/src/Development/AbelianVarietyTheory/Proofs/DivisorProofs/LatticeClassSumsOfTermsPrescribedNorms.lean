import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section
open Filter Topology

namespace GlobalTheory.UPoinc.USum.ClassTerms

theorem summable_of_mem_fd {p : ℕ} [Fact p.Prime] {I : Type} (M : Submodule ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] M] (f : I → PadicAlgCl p) (hf : ∀ i, f i ∈ M)
    (h0 : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0)) : Summable f := by
  haveI : CompleteSpace M := FiniteDimensional.complete ℚ_[p] M
  let g : I → M := fun i => ⟨f i, hf i⟩
  have hg : Tendsto g cofinite (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [g] using h0
  have hs : Summable g := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hg
  have := hs.hasSum.map M.subtype continuous_subtype_val
  exact this.summable

theorem exists_unit_sub_one_unit (p : ℕ) [Fact p.Prime] :
    ∃ u : PadicAlgCl p, ‖u‖ = 1 ∧ ‖u - 1‖ = 1 := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial (PadicAlgCl p))
    (by
      have hd : (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial (PadicAlgCl p)).degree = 2 := by compute_degree!
      rw [hd]; decide)
  have h2 : u ^ 2 = u + 1 := by
    simp [Polynomial.IsRoot] at hu
    linear_combination hu
  have hle : ‖u‖ ≤ 1 := by
    by_contra h
    push_neg at h
    have h3 : ‖u‖ ^ 2 ≤ max ‖u‖ ‖(1 : PadicAlgCl p)‖ := by
      rw [← norm_pow, h2]; exact IsUltrametricDist.norm_add_le_max _ _
    rw [norm_one, max_eq_left h.le] at h3
    nlinarith
  have hle' : ‖u - 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max u (-1)
    rw [← sub_eq_add_neg, norm_neg, norm_one] at this
    exact this.trans (max_le hle le_rfl)
  have hprod : ‖u‖ * ‖u - 1‖ = 1 := by
    rw [← norm_mul, show u * (u - 1) = 1 by linear_combination h2, norm_one]
  have a1 := mul_le_mul_of_nonneg_left hle' (norm_nonneg u)
  have a2 := mul_le_mul_of_nonneg_right hle (norm_nonneg (u - 1))
  exact ⟨u, le_antisymm hle (by nlinarith), le_antisymm hle' (by nlinarith)⟩

theorem one_class {p : ℕ} [Fact p.Prime] {Y K : Type} [Nonempty Y] [Nonempty K] (q : Y → ℝ) (s : PadicAlgCl p)
    (n : Y → ℕ) (hq : Tendsto q cofinite atTop) (hs : ∀ χ, ‖s‖ ^ n χ = Real.exp (-q χ))
    (C : Set Y) (χ₀ : Y) (h0 : χ₀ ∈ C) (hmin : ∀ χ ∈ C, q χ₀ ≤ q χ) (G : K → PadicAlgCl p)
    (hG : ∀ κ, ‖G κ‖ ≤ Real.exp (-q χ₀))
    (hG' : (∀ χ ∈ C, χ ≠ χ₀ → q χ₀ < q χ) → ∃ κ, ‖G κ‖ = Real.exp (-q χ₀)) :
    ∃ t : Y → K → PadicAlgCl p, (∀ χ ∈ C, ∀ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧
      (∀ χ ∈ C, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧ ∀ κ, HasSum (fun χ : C => t χ κ) (G κ) := by
  classical
  obtain ⟨u₀, hu1, hu2⟩ := exists_unit_sub_one_unit p
  set D : Set Y := C \ {χ₀} with hD
  set A : Subalgebra ℚ_[p] (PadicAlgCl p) := Algebra.adjoin ℚ_[p] ({s, u₀} : Set (PadicAlgCl p)) with hA
  let M : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule A
  haveI : FiniteDimensional ℚ_[p] M :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (by simp) (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hsA : s ∈ A := Algebra.subset_adjoin (by simp)
  have huA : u₀ ∈ A := Algebra.subset_adjoin (by simp)
  have hexp : Tendsto (fun χ => Real.exp (-q χ)) cofinite (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq)
  have hsumm : ∀ w : Y → PadicAlgCl p, (∀ χ, w χ ∈ A) → (∀ χ, ‖w χ‖ = Real.exp (-q χ)) →
      Summable (D.indicator w) := by
    intro w hwA hw
    refine summable_of_mem_fd M _ (fun χ => ?_) ?_
    · by_cases h : χ ∈ D
      · rw [Set.indicator_of_mem h]; exact hwA χ
      · rw [Set.indicator_of_notMem h]; exact M.zero_mem
    · refine squeeze_zero (fun _ => norm_nonneg _) (fun χ => ?_) hexp
      by_cases h : χ ∈ D
      · rw [Set.indicator_of_mem h, hw]
      · rw [Set.indicator_of_notMem h, norm_zero]; positivity
  have hSle : ∀ w : Y → PadicAlgCl p, (∀ χ, ‖w χ‖ = Real.exp (-q χ)) →
      ‖∑' χ, D.indicator w χ‖ ≤ Real.exp (-q χ₀) := by
    intro w hw
    refine IsUltrametricDist.norm_tsum_le_of_forall_le (fun χ => ?_)
    by_cases h : χ ∈ D
    · rw [Set.indicator_of_mem h, hw]
      exact Real.exp_le_exp.mpr (neg_le_neg (hmin χ h.1))
    · rw [Set.indicator_of_notMem h, norm_zero]; positivity
  have key : ∀ w : Y → PadicAlgCl p, (∀ χ, w χ ∈ A) → (∀ χ, ‖w χ‖ = Real.exp (-q χ)) →
      (∃ κ, ‖G κ - ∑' χ, D.indicator w χ‖ = Real.exp (-q χ₀)) →
      ∃ t : Y → K → PadicAlgCl p, (∀ χ ∈ C, ∀ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧
      (∀ χ ∈ C, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧ ∀ κ, HasSum (fun χ : C => t χ κ) (G κ) := by
    intro w hwA hw hex
    set S := ∑' χ, D.indicator w χ with hSdef
    have hsum := hsumm w hwA hw
    have hS := hSle w hw
    refine ⟨fun χ κ => if χ = χ₀ then G κ - S else w χ, ?_, ?_, ?_⟩
    · intro χ hχ κ
      by_cases h : χ = χ₀
      · subst h
        simp only [if_true]
        rw [sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hG κ) (by rw [norm_neg]; exact hS))
      · simp only [h, if_false, hw, le_refl]
    · intro χ hχ
      by_cases h : χ = χ₀
      · subst h
        obtain ⟨κ, hκ⟩ := hex
        exact ⟨κ, by simpa using hκ⟩
      · exact ⟨Classical.arbitrary K, by simp only [h, if_false, hw]⟩
    · intro κ
      have h1 : HasSum (fun χ => if χ = χ₀ then G κ - S else 0) (G κ - S) := hasSum_ite_eq _ _
      have h2 := h1.add hsum.hasSum
      rw [sub_add_cancel] at h2
      refine (hasSum_subtype_iff_indicator (f := fun χ => if χ = χ₀ then G κ - S else w χ)).mpr ?_
      convert h2 using 1
      funext χ
      by_cases h : χ = χ₀
      · subst h
        have : χ ∉ D := fun hh => hh.2 rfl
        simp [Set.indicator_of_mem h0, Set.indicator_of_notMem this]
      · by_cases hc : χ ∈ C
        · have : χ ∈ D := ⟨hc, h⟩
          simp [Set.indicator_of_mem hc, Set.indicator_of_mem this, h]
        · have : χ ∉ D := fun hh => hc hh.1
          simp [Set.indicator_of_notMem hc, Set.indicator_of_notMem this, h]
  set rr : Y → PadicAlgCl p := fun χ => s ^ n χ with hrr
  have hrA : ∀ χ, rr χ ∈ A := fun χ => A.pow_mem hsA _
  have hrn : ∀ χ, ‖rr χ‖ = Real.exp (-q χ) := fun χ => by simp [rr, norm_pow, hs]
  by_cases hstrict : ∀ χ ∈ C, χ ≠ χ₀ → q χ₀ < q χ
  · obtain ⟨κ, hκ⟩ := hG' hstrict
    refine key rr hrA hrn ⟨κ, ?_⟩
    have hlt : ‖∑' χ, D.indicator rr χ‖ < Real.exp (-q χ₀) := by
      by_cases hDe : D.Nonempty
      · haveI : Nonempty D := hDe.to_subtype
        have hqD : Tendsto (fun x : D => q x) cofinite atTop :=
          hq.comp Subtype.val_injective.tendsto_cofinite
        obtain ⟨a₁, ha₁⟩ := hqD.exists_forall_le
        have hlt₁ : q χ₀ < q a₁ := hstrict a₁ a₁.2.1 (fun h => a₁.2.2 h)
        refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le (C := Real.exp (-q a₁)) (fun χ => ?_))
          (Real.exp_lt_exp.mpr (neg_lt_neg hlt₁))
        by_cases h : χ ∈ D
        · rw [Set.indicator_of_mem h, hrn]
          exact Real.exp_le_exp.mpr (neg_le_neg (ha₁ ⟨χ, h⟩))
        · rw [Set.indicator_of_notMem h, norm_zero]; positivity
      · have hz : D.indicator rr = 0 := funext fun χ => Set.indicator_of_notMem (fun h => hDe ⟨χ, h⟩) _
        simp only [hz, Pi.zero_apply, tsum_zero, norm_zero]; positivity
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, hκ]; exact hlt.ne'), norm_neg, hκ, max_eq_left hlt.le]
  · push_neg at hstrict
    obtain ⟨χ₁, hχ₁C, hχ₁ne, hχ₁le⟩ := hstrict
    have hq₁ : q χ₁ = q χ₀ := le_antisymm hχ₁le (hmin χ₁ hχ₁C)
    have hχ₁D : χ₁ ∈ D := ⟨hχ₁C, hχ₁ne⟩
    set κ₀ : K := Classical.arbitrary K
    by_cases hc : ‖G κ₀ - ∑' χ, D.indicator rr χ‖ = Real.exp (-q χ₀)
    · exact key rr hrA hrn ⟨κ₀, hc⟩
    · set w : Y → PadicAlgCl p := Function.update rr χ₁ (u₀ * rr χ₁) with hwdef
      have hwA : ∀ χ, w χ ∈ A := by
        intro χ
        by_cases h : χ = χ₁
        · subst h; simp only [w, Function.update_self]; exact A.mul_mem huA (hrA _)
        · simp only [w, Function.update_of_ne h]; exact hrA χ
      have hwn : ∀ χ, ‖w χ‖ = Real.exp (-q χ) := by
        intro χ
        by_cases h : χ = χ₁
        · subst h; simp only [w, Function.update_self, norm_mul, hu1, _root_.one_mul, hrn]
        · simp only [w, Function.update_of_ne h, hrn]
      refine key w hwA hwn ⟨κ₀, ?_⟩
      have hind : D.indicator w = Function.update (D.indicator rr) χ₁ (u₀ * rr χ₁) := by
        funext χ
        by_cases h : χ = χ₁
        · subst h; simp [w, Set.indicator_of_mem hχ₁D]
        · by_cases hd : χ ∈ D
          · simp [w, Set.indicator_of_mem hd, Function.update_of_ne h]
          · simp [w, Set.indicator_of_notMem hd, Function.update_of_ne h]
      have hS' : ∑' χ, D.indicator w χ = u₀ * rr χ₁ - rr χ₁ + ∑' χ, D.indicator rr χ := by
        rw [hind]
        have := ((hsumm rr hrA hrn).hasSum.update χ₁ (u₀ * rr χ₁))
        rw [Set.indicator_of_mem hχ₁D] at this
        exact this.tsum_eq
      have hle : ‖G κ₀ - ∑' χ, D.indicator rr χ‖ < Real.exp (-q χ₀) := by
        refine lt_of_le_of_ne ?_ hc
        rw [sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (hG κ₀) (by rw [norm_neg]; exact hSle rr hrn))
      have hn1 : ‖-((u₀ - 1) * rr χ₁)‖ = Real.exp (-q χ₀) := by
        rw [norm_neg, norm_mul, hu2, _root_.one_mul, hrn, hq₁]
      have : G κ₀ - ∑' χ, D.indicator w χ = (G κ₀ - ∑' χ, D.indicator rr χ) + -((u₀ - 1) * rr χ₁) := by
        rw [hS']; ring
      rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hn1]; exact hle.ne), hn1,
        max_eq_right hle.le]

end GlobalTheory.UPoinc.USum.ClassTerms

namespace GlobalTheory.UPoinc.USum

open GlobalTheory.UPoinc.USum.ClassTerms in

theorem classSum_of_terms : ∀ (p : ℕ) [Fact p.Prime] (Y K : Type) [AddCommGroup Y] [Nonempty K] (m : ℕ) (q : Y → ℝ) (s : PadicAlgCl p) (n : Y → ℕ), Filter.Tendsto q Filter.cofinite Filter.atTop → (∀ χ, ‖s‖ ^ n χ = Real.exp (-q χ)) → ∀ F : Y → K → PadicAlgCl p, (∀ ν ν' κ, CongMod m ν ν' → F ν κ = F ν' κ) → (∀ ν κ, (∀ χ, CongMod m χ ν → q ν ≤ q χ) → ‖F ν κ‖ ≤ Real.exp (-q ν)) → (∀ ν, (∀ χ, CongMod m χ ν → χ ≠ ν → q ν < q χ) → ∃ κ, ‖F ν κ‖ = Real.exp (-q ν)) → ∃ t : Y → K → PadicAlgCl p, (∀ χ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧ (∀ χ, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧ ∀ ν κ (δ : ℝ), 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ χ ∈ S, CongMod m χ ν) → (∀ χ ∈ S₀, CongMod m χ ν → χ ∈ S) → ‖F ν κ - ∑ χ ∈ S, t χ κ‖ ≤ δ := by
  intro p _ Y K _ _ m q s n hq hs F hF hle heq
  classical
  have hrefl : ∀ x : Y, CongMod m x x := fun x => ⟨0, by simp⟩
  have hsymm : ∀ x y : Y, CongMod m x y → CongMod m y x := by
    rintro x y ⟨w, hw⟩
    exact ⟨-w, by rw [hw]; simp⟩
  have htrans : ∀ x y z : Y, CongMod m x y → CongMod m y z → CongMod m x z := by
    rintro x y z ⟨w, hw⟩ ⟨w', hw'⟩
    exact ⟨w' + w, by rw [hw, hw', smul_add]; abel⟩
  let R : Setoid Y := ⟨CongMod m, ⟨hrefl, fun h => hsymm _ _ h, fun h h' => htrans _ _ _ h h'⟩⟩
  have hR : ∀ x y : Y, Quotient.mk R x = Quotient.mk R y ↔ CongMod m x y :=
    fun x y => ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  have hmin : ∀ c : Quotient R, ∃ χ₀, Quotient.mk R χ₀ = c ∧ ∀ χ, Quotient.mk R χ = c → q χ₀ ≤ q χ := by
    intro c
    obtain ⟨x, rfl⟩ := Quotient.exists_rep c
    let Cs : Set Y := {χ | Quotient.mk R χ = Quotient.mk R x}
    haveI : Nonempty Cs := ⟨⟨x, rfl⟩⟩
    have hqC : Tendsto (fun a : Cs => q a) cofinite atTop := hq.comp Subtype.val_injective.tendsto_cofinite
    obtain ⟨a, ha⟩ := hqC.exists_forall_le
    exact ⟨a, a.2, fun χ hχ => ha ⟨χ, hχ⟩⟩
  choose z hzc hzmin using hmin
  have hone : ∀ c : Quotient R, ∃ t : Y → K → PadicAlgCl p,
      (∀ χ ∈ {χ | Quotient.mk R χ = c}, ∀ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧
      (∀ χ ∈ {χ | Quotient.mk R χ = c}, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧
      ∀ κ, HasSum (fun χ : {χ | Quotient.mk R χ = c} => t χ κ) (F (z c) κ) := by
    intro c
    refine one_class q s n hq hs {χ | Quotient.mk R χ = c} (z c) (hzc c) (hzmin c) (F (z c))
      (fun κ => hle _ κ (fun χ hχ => hzmin c χ (((hR _ _).2 hχ).trans (hzc c)))) ?_
    intro H
    exact heq (z c) (fun χ hχ hne => H χ (((hR _ _).2 hχ).trans (hzc c)) hne)
  choose tc htc1 htc2 htc3 using hone
  refine ⟨fun χ κ => tc (Quotient.mk R χ) χ κ, fun χ κ => htc1 _ χ rfl κ, fun χ => htc2 _ χ rfl, ?_⟩
  intro ν κ δ hδ
  set c := Quotient.mk R ν with hc
  have hFz : F (z c) κ = F ν κ := hF _ _ κ ((hR _ _).1 (hzc c))
  have ht : Tendsto (fun T : Finset {χ | Quotient.mk R χ = c} => ∑ χ ∈ T, tc c χ κ) atTop (𝓝 (F ν κ)) := by
    rw [← hFz]; exact htc3 c κ
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.1 ht δ hδ
  refine ⟨T₀.map (Function.Embedding.subtype _), fun S hSc hS₀ => ?_⟩
  have hTT : T₀ ≤ S.subtype (fun χ => Quotient.mk R χ = c) := by
    intro x hx
    rw [Finset.mem_subtype]
    exact hS₀ x (Finset.mem_map_of_mem _ hx) ((hR _ _).1 x.2)
  have h1 := hT₀ _ hTT
  change dist (∑ χ ∈ S.subtype (fun χ => Quotient.mk R χ = c), tc c χ κ) (F ν κ) < δ at h1
  rw [Finset.sum_subtype_eq_sum_filter (fun χ => tc c χ κ),
    Finset.filter_true_of_mem (fun χ hχ => (hR _ _).2 (hSc χ hχ))] at h1
  have hsum : ∑ χ ∈ S, tc (Quotient.mk R χ) χ κ = ∑ χ ∈ S, tc c χ κ :=
    Finset.sum_congr rfl (fun χ hχ => by rw [(hR _ _).2 (hSc χ hχ)])
  show ‖F ν κ - ∑ χ ∈ S, tc (Quotient.mk R χ) χ κ‖ ≤ δ
  rw [hsum, ← dist_eq_norm, dist_comm]
  exact h1.le

end GlobalTheory.UPoinc.USum
