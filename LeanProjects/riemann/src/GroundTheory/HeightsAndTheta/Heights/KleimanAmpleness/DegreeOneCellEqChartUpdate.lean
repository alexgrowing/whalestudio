import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.ModelSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsHomogOfMemQuotPartBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc mIdealOver
  chartRingOver quotPart secOver GlobalSectionsComparisonStatement)

noncomputable section

namespace HZeroRowPlaceData

set_option linter.unusedSectionVars false

section Cells

variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def cell0 (c : ∀ k, ι k) : Cell K ι 0 :=
  ⟨chart c, fun _ => Finset.singleton_nonempty _, by simp [chart]⟩

theorem degree_zero_cell_eq_chart (I : Cell K ι 0) : ∃ c, I = cell0 c := by
  refine ⟨fun k => (I.1 k).min' (I.2.1 k), Subtype.ext (funext fun k => ?_)⟩
  have h0 : (I.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp I.2.2) k (Finset.mem_univ _)
  have h1 : (I.1 k).card = 1 := by have := (I.2.1 k).card_pos; omega
  show I.1 k = {(I.1 k).min' (I.2.1 k)}
  rw [Finset.eq_singleton_iff_unique_mem]
  exact ⟨Finset.min'_mem _ _, fun x hx => Finset.card_le_one.mp h1.le x hx _ (Finset.min'_mem _ _)⟩

theorem degree_one_cell_eq_chart_update (J : Cell K ι 1) : ∃ (c : ∀ k, ι k) (k : K) (b : ι k), c k < b ∧
    J.1 = Function.update (chart c) k {c k, b} := by
  have hpos : ∀ l, 1 ≤ (J.1 l).card := fun l => (J.2.1 l).card_pos
  obtain ⟨k, hk⟩ : ∃ k, (J.1 k).card - 1 ≠ 0 := by
    by_contra h
    push Not at h
    have := J.2.2
    rw [Finset.sum_eq_zero fun l _ => h l] at this
    exact absurd this (by norm_num)
  have hle : ∀ l, (J.1 l).card - 1 ≤ 1 := fun l =>
    le_of_le_of_eq (Finset.single_le_sum (f := fun l => (J.1 l).card - 1) (fun l _ => Nat.zero_le _)
      (Finset.mem_univ l)) J.2.2
  have hk2 : (J.1 k).card = 2 := by have := hle k; have := hpos k; omega
  have hl1 : ∀ l, l ≠ k → (J.1 l).card = 1 := by
    intro l hl
    have hsum : (J.1 l).card - 1 + ((J.1 k).card - 1) ≤ 1 :=
      calc (J.1 l).card - 1 + ((J.1 k).card - 1) = ∑ x ∈ {l, k}, ((J.1 x).card - 1) :=
          (Finset.sum_pair (f := fun x => (J.1 x).card - 1) hl).symm
        _ ≤ ∑ x, ((J.1 x).card - 1) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = 1 := J.2.2
    have := hpos l
    omega
  have hlt : (J.1 k).min' (J.2.1 k) < (J.1 k).max' (J.2.1 k) := Finset.min'_lt_max'_of_card _ (by omega)
  refine ⟨fun l => (J.1 l).min' (J.2.1 l), k, (J.1 k).max' (J.2.1 k), hlt, funext fun l => ?_⟩
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.min'_mem _ _
      · exact Finset.max'_mem _ _
    · simp only [hk2, Finset.card_pair hlt.ne, le_refl]
  · rw [Function.update_of_ne hl]
    show J.1 l = {(J.1 l).min' (J.2.1 l)}
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.min'_mem _ _, fun x hx => Finset.card_le_one.mp (hl1 l hl).le x hx _ (Finset.min'_mem _ _)⟩

theorem pair_isCell (c : ∀ k, ι k) (k : K) (b : ι k) (hb : c k ≠ b) :
    (∀ l, (Function.update (chart c) k {c k, b} l).Nonempty) ∧
      ∑ l, ((Function.update (chart c) k {c k, b} l).card - 1) = 1 := by
  refine ⟨fun l => ?_, ?_⟩
  · by_cases hl : l = k
    · subst hl; rw [Function.update_self]; exact Finset.insert_nonempty _ _
    · rw [Function.update_of_ne hl]; exact Finset.singleton_nonempty _
  · rw [Finset.sum_eq_single k]
    · rw [Function.update_self, Finset.card_pair hb]
    · intro l _ hl
      rw [Function.update_of_ne hl]
      simp [chart]
    · intro h; exact absurd (Finset.mem_univ k) h

theorem constD_pair {V : Type} [AddCommGroup V] (f : Cell K ι 0 → V) (J : Cell K ι 1) (c : ∀ k, ι k) (k : K)
    (b : ι k) (hb : c k < b) (hJ : J.1 = Function.update (chart c) k {c k, b}) :
    constD K ι V 0 f J = f (cell0 (Function.update c k b)) - f (cell0 c) := by
  have hne : c k ≠ b := hb.ne
  have hJk : J.1 k = {c k, b} := by rw [hJ, Function.update_self]
  have hJl : ∀ l, l ≠ k → J.1 l = {c l} := fun l hl => by rw [hJ, Function.update_of_ne hl]; rfl
  have hsgn : ∑ l ∈ Finset.univ.filter (· < k), ((J.1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      rw [hJl l (Finset.mem_filter.mp hl).2.ne]
      simp
  have sgn1 : faceSign J.1 k (c k) = 1 := by
    unfold faceSign
    rw [hsgn, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, hb.not_gt]
  have sgn2 : faceSign J.1 k b = -1 := by
    unfold faceSign
    rw [hsgn, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, hb]
  have e1 : Function.update J.1 k (({c k, b} : Finset (ι k)).erase (c k)) = chart (Function.update c k b) := by
    funext l
    by_cases hl : l = k
    · subst hl; simp [chart, hne]
    · rw [Function.update_of_ne hl, hJl l hl]; simp [chart, Function.update_of_ne hl]
  have e2 : Function.update J.1 k (({c k, b} : Finset (ι k)).erase b) = chart c := by
    funext l
    by_cases hl : l = k
    · subst hl; rw [Function.update_self, Finset.erase_insert_of_ne hne]; simp [chart]
    · rw [Function.update_of_ne hl, hJl l hl]; rfl
  unfold constD
  rw [Finset.sum_eq_single k]
  · rw [hJk, Finset.sum_pair hne]
    split_ifs with h1 h2 h2
    · rw [show (⟨_, h1⟩ : Cell K ι 0) = cell0 (Function.update c k b) from Subtype.ext e1,
        show (⟨_, h2⟩ : Cell K ι 0) = cell0 c from Subtype.ext e2, sgn1, sgn2, one_zsmul, neg_one_zsmul,
        sub_eq_add_neg]
    · exact (h2 (by rw [e2]; exact (cell0 c).2)).elim
    · exact (h1 (by rw [e1]; exact (cell0 _).2)).elim
    · exact (h1 (by rw [e1]; exact (cell0 _).2)).elim
  · intro l _ hl
    refine Finset.sum_eq_zero fun i hi => dif_neg ?_
    rintro ⟨h, -⟩
    have := h l
    rw [Function.update_self, hJl l hl] at this
    rw [hJl l hl, Finset.mem_singleton] at hi
    subst hi
    simp at this
  · intro h; exact absurd (Finset.mem_univ k) h

theorem constD_const {V : Type} [AddCommGroup V] (v : V) (J : Cell K ι 1) :
    constD K ι V 0 (fun _ => v) J = 0 := by
  obtain ⟨c, k, b, hb, hJ⟩ := degree_one_cell_eq_chart_update J
  rw [constD_pair _ J c k b hb hJ, sub_self]

end Cells

section Main

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}

theorem good_chart {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Good y (chart c) := by
  intro k i hi
  rw [show i = c k from Finset.mem_singleton.mp hi]
  exact hc k

theorem evMap_cellRes {J I : ∀ k, Finset (ι k)} (hJI : ∀ k, J k ⊆ I k) (hI : Good y I)
    (x : LocalizedModule (cellMon S J) (MRingOver S ι ⧸ mIdealOver S y)) :
    evMap y I (cellRes S _ J I x) = evMap y J x := by
  have hJ : Good y J := fun k i hi => hI k i (hJI k hi)
  induction x using LocalizedModule.induction_on with
  | h m t =>
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [CechPointVanish.cellRes_mk (CechPointVanish.cellMon_mono hJI), evMap_mk y hI, evMap_mk y hJ]

theorem evMap_cechD (x : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0) (J : Cell K ι 1) (hJ : Good y J.1) :
    evMap y J.1 (cechD S ι _ 0 x J) = constD K ι Ω 0 (fun I => evMap y I.1 (x I)) J := by
  rw [CechPointVanish.cechD_apply]
  simp only [constD, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · rw [map_zsmul, evMap_cellRes (CechPointVanish.face_subset J.1 k i) hJ]
  · simp

theorem ev_step_lt {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0} (hz : cechD S ι _ 0 z = 0)
    {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (b : ι k) (hb : c k < b) (hyb : y ⟨k, b⟩ ≠ 0) :
    evMap y (chart c) (z (cell0 c)) =
      evMap y (chart (Function.update c k b)) (z (cell0 (Function.update c k b))) := by
  have hJ : Good y (Function.update (chart c) k {c k, b}) := by
    intro l i hi
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hc _
      · exact hyb
    · rw [Function.update_of_ne hl] at hi
      rw [show i = c l from Finset.mem_singleton.mp hi]
      exact hc l
  set J : Cell K ι 1 := ⟨Function.update (chart c) k {c k, b}, pair_isCell c k b hb.ne⟩ with hJdef
  have h := evMap_cechD z J hJ
  have h0 : cechD S ι _ 0 z J = 0 := congrFun hz J
  rw [h0, map_zero, constD_pair _ J c k b hb rfl] at h
  exact (sub_eq_zero.mp h.symm).symm

theorem ev_step {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0} (hz : cechD S ι _ 0 z = 0)
    {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (b : ι k) (hyb : y ⟨k, b⟩ ≠ 0) :
    evMap y (chart c) (z (cell0 c)) =
      evMap y (chart (Function.update c k b)) (z (cell0 (Function.update c k b))) := by
  rcases lt_trichotomy (c k) b with hb | hb | hb
  · exact ev_step_lt hz hc k b hb hyb
  · subst hb; rw [Function.update_eq_self]
  · have hc' : ∀ l, y ⟨l, Function.update c k b l⟩ ≠ 0 := by
      intro l
      by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact hyb
      · rw [Function.update_of_ne hl]; exact hc l
    have h := ev_step_lt hz hc' k (c k) (by rw [Function.update_self]; exact hb) (hc k)
    rw [Function.update_idem, Function.update_eq_self] at h
    exact h.symm

theorem ev_agree {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0} (hz : cechD S ι _ 0 z = 0)
    {c c' : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0) :
    evMap y (chart c) (z (cell0 c)) = evMap y (chart c') (z (cell0 c')) := by
  have key : ∀ s : Finset K, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k ∉ s, c k = c' k) →
      evMap y (chart c) (z (cell0 c)) = evMap y (chart c') (z (cell0 c')) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro c _ h
      rw [show c = c' from funext fun k => h k (Finset.notMem_empty k)]
    | @insert k s hk ih =>
      intro c hc hcs
      rw [ev_step hz hc k (c' k) (hc' k)]
      refine ih _ (fun l => ?_) (fun l hl => ?_)
      · by_cases hl : l = k
        · subst hl; rw [Function.update_self]; exact hc' _
        · rw [Function.update_of_ne hl]; exact hc l
      · by_cases hlk : l = k
        · subst hlk; rw [Function.update_self]
        · rw [Function.update_of_ne hlk]; exact hcs l (by simp [hlk, hl])
  exact key Finset.univ c hc (fun k hk => absurd (Finset.mem_univ k) hk)

def ratio (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩

theorem aeval_ratio_cellMon {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {t : MRingOver S ι}
    (ht : t ∈ cellMon S (chart c)) : aeval (ratio y c) t = 1 := by
  unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    rw [show i = c k from Finset.mem_singleton.mp hi, aeval_X]
    exact div_self (hc k)
  | one => simp
  | mul x w _ _ hx hw => rw [map_mul, hx, hw, one_mul]

theorem aeval_homog_eq {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {p : MRingOver S ι} {d : K → ℕ}
    (hp : IsMultiHomog p d) : aeval y p = (∏ k, y ⟨k, c k⟩ ^ d k) * aeval (ratio y c) p := by
  have hP : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hdeg := hp μ hμ
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have key : ∏ q : Σ k, ι k, ratio y c q ^ μ q = (∏ q : Σ k, ι k, y q ^ μ q) / ∏ k, y ⟨k, c k⟩ ^ d k := by
    simp only [ratio]
    rw [Finset.prod_congr rfl fun q _ => div_pow (y q) _ (μ q), Finset.prod_div_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [key]
  field_simp

theorem exists_lift {I : ∀ k, Finset (ι k)} (hI : Good y I) {c : ∀ k, ι k} (hcI : ∀ k, c k ∈ I k) (n : K → ℤ)
    {s : Ω} (hs : s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver S y c) :
    ∃ w ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I) n, evMap y I w = s := by
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hI k (c k) (hcI k)
  obtain ⟨b, h, hh, he⟩ := exists_of_mem_chartRing y c hc hs
  let e : K → ℕ := fun k => (n k).toNat
  let a : K → ℕ := fun k => b k + (-n k).toNat
  have hmem : ∀ f : K → ℕ, ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ f k ∈ cellMon S I := fun f =>
    Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (Submonoid.subset_closure
      (show (X ⟨k, c k⟩ : MRingOver S ι) ∈ {f | ∃ k, ∃ i ∈ I k, f = X ⟨k, i⟩} from ⟨k, c k, hcI k, rfl⟩)) _
  refine ⟨LocalizedModule.mk (Ideal.Quotient.mk _ (h * ∏ k, X ⟨k, c k⟩ ^ e k)) ⟨_, hmem a⟩,
    Submodule.subset_span ⟨_, ⟨_, hmem a⟩, a, isMultiHomog_prod_X c a, ?_, rfl⟩, ?_⟩
  · apply Submodule.subset_span
    refine ⟨_, ⟨fun k => ?_, ?_⟩, rfl⟩
    · show 0 ≤ n k + ((b k + (-n k).toNat : ℕ) : ℤ)
      omega
    · convert isMultiHomog_mul hh (isMultiHomog_prod_X (S := S) c e) using 1
      funext k
      simp only [Pi.add_apply, e, a]
      push_cast
      omega
  · have hPb : ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have hPe : ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have hPn : ∏ k, y ⟨k, c k⟩ ^ (-n k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hA : ∏ k, y ⟨k, c k⟩ ^ a k =
        (∏ k, y ⟨k, c k⟩ ^ b k) * (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ (-n k) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]
      congr 1
      simp only [a, e]
      push_cast
      omega
    have hh' : s * (∏ k, y ⟨k, c k⟩ ^ (-n k)) * ∏ k, y ⟨k, c k⟩ ^ b k = aeval y h := (eq_div_iff hPb).mp he
    rw [evMap_mk y hI, map_mul, aeval_prod_X, aeval_prod_X, hA, ← hh']
    field_simp

end Main

end HZeroRowPlaceData

open HZeroRowPlaceData in

theorem HZeroRowPlaceData.full : GlobalSectionsComparisonStatement := by
  intro S _ K _ _ ι _ _ Ω _ _ y n hy
  choose c₀ hc₀ using hy
  have hg₀ : Good y (cell0 c₀).1 := good_chart hc₀
  let Z := cechZc ι (quotPart S (mIdealOver S y)) n 0
  let φ : ↥Z →ₗ[S] Ω := (evMap y (cell0 c₀).1).comp ((LinearMap.proj (R := S)
    (φ := fun I : Cell K ι 0 => LocalizedModule (cellMon S I.1) (MRingOver S ι ⧸ mIdealOver S y)) (cell0 c₀)).comp
      Z.subtype)
  have hφ : ∀ z : ↥Z, φ z = evMap y (cell0 c₀).1 (z.1 (cell0 c₀)) := fun z => rfl
  have hZ : ∀ z : ↥Z, (∀ I : Cell K ι 0, z.1 I ∈
      locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n) ∧ cechD S ι _ 0 z.1 = 0 := by
    intro z
    obtain ⟨hC, hK⟩ := Submodule.mem_inf.mp z.2
    exact ⟨fun I => Submodule.mem_pi.mp hC I (Set.mem_univ _), hK⟩
  have hagree : ∀ (z : ↥Z) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
      φ z = evMap y (cell0 c).1 (z.1 (cell0 c)) :=
    fun z c hc => ev_agree (hZ z).2 hc₀ hc
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz0
    apply Subtype.ext
    funext I
    obtain ⟨c, rfl⟩ := degree_zero_cell_eq_chart I
    show z.1 (cell0 c) = 0
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · refine evMap_injOn y (I := (cell0 c).1) (good_chart hc) n ((hZ z).1 (cell0 c)) (Submodule.zero_mem _) ?_
      rw [map_zero, ← hagree z c hc, hz0]
    · push Not at hc
      obtain ⟨k, hk⟩ := hc
      have := subsingleton_of_bad (S := S) (I := chart c) (Finset.mem_singleton_self (c k)) hk
      exact @Subsingleton.elim _ this _ _
  · apply le_antisymm
    · rintro x ⟨z, rfl⟩
      simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
        Subalgebra.mem_toSubmodule]
      intro c hc
      rw [hagree z c hc]
      obtain ⟨g, t, a, ht, hg, hd, he⟩ := exists_rep ((hZ z).1 (cell0 c))
      rw [he, evMap_mk y (I := (cell0 c).1) (good_chart hc)]
      rcases hd with hd | rfl
      · have ht1 : aeval y (t : MRingOver S ι) = ∏ k, y ⟨k, c k⟩ ^ a k := by
          rw [aeval_homog_eq hc ht, aeval_ratio_cellMon hc t.2, mul_one]
        have hP : ∀ k, y ⟨k, c k⟩ ^ ((n k + (a k : ℤ)).toNat) = y ⟨k, c k⟩ ^ a k * y ⟨k, c k⟩ ^ n k := by
          intro k
          rw [← zpow_natCast, Int.toNat_of_nonneg (hd k), zpow_add₀ (hc k), ← zpow_natCast]
          ring
        have hPa : ∏ k, y ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
        have hPn : ∏ k, y ⟨k, c k⟩ ^ n k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
        have hmem := aeval_div_mem_chartRing y c hg
        convert hmem using 1
        rw [Finset.prod_congr rfl fun k _ => hP k, Finset.prod_mul_distrib, ht1]
        simp only [zpow_neg, Finset.prod_inv_distrib]
        field_simp
      · simp
    · intro s hs
      have hs' : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
          s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver S y c := by
        intro c hc
        exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hs c) hc
      have hlift : ∀ I : Cell K ι 0, Good y I.1 → ∃ w ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n,
          evMap y I.1 w = s := fun I hI =>
        exists_lift hI (fun k => Finset.min'_mem _ (I.2.1 k)) n
          (hs' _ fun k => hI k _ (Finset.min'_mem _ (I.2.1 k)))
      classical
      let z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0 := fun I =>
        if hI : Good y I.1 then (hlift I hI).choose else 0
      have hzC : ∀ I : Cell K ι 0, z I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) n := by
        intro I
        by_cases hI : Good y I.1
        · simp only [z, dif_pos hI]; exact (hlift I hI).choose_spec.1
        · simp only [z, dif_neg hI]; exact Submodule.zero_mem _
      have hzv : ∀ I : Cell K ι 0, Good y I.1 → evMap y I.1 (z I) = s := by
        intro I hI
        simp only [z, dif_pos hI]
        exact (hlift I hI).choose_spec.2
      have hzCc : z ∈ cechCc ι (quotPart S (mIdealOver S y)) n 0 :=
        Submodule.mem_pi.mpr fun I _ => hzC I
      have hzD : cechD S ι _ 0 z = 0 := by
        funext J
        by_cases hJ : Good y J.1
        · refine evMap_injOn y hJ n (cechD_mem_locPart n 0 hzCc J) (Submodule.zero_mem _) ?_
          have hconst : constD K ι Ω 0 (fun I => evMap y I.1 (z I)) J = constD K ι Ω 0 (fun _ => s) J :=
            CechPointVanish.constD_congr J.1 0 (fun I hIJ => hzv I fun k i hi => hJ k i (hIJ k hi)) J
              fun k => subset_refl _
          rw [evMap_cechD z J hJ, hconst, constD_const, Pi.zero_apply, map_zero]
        · unfold Good at hJ
          push Not at hJ
          obtain ⟨k, i, hi, hy0⟩ := hJ
          have := subsingleton_of_bad (S := S) hi hy0
          exact @Subsingleton.elim _ this _ _
      refine ⟨⟨z, Submodule.mem_inf.mpr ⟨hzCc, hzD⟩⟩, ?_⟩
      rw [hφ]
      exact hzv (cell0 c₀) hg₀
  · intro z d g _ _ hz1
    rw [hφ, hz1 (cell0 c₀), evMap_mk y hg₀]
    simp

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
