import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZeroCocycleSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ZeroCocycleSection

set_option linter.unusedSectionVars false

open GenOnFibres

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Graded

variable {S : Type} [CommRing S] {V : Ideal (MRingOver S ι)}

theorem homog_smul {p : MRingOver S ι} {a : K → ℕ} (r : S) (hp : IsMultiHomog p a) :
    IsMultiHomog (r • p) a :=
  fun m hm k => hp m (MvPolynomial.support_smul hm) k

theorem quotPart_eq_mk {c : K → ℤ} {m : MRingOver S ι ⧸ V} (hm : m ∈ KH.quotPart S V c) (h0 : m ≠ 0) :
    (∀ k, 0 ≤ c k) ∧ ∃ p, IsMultiHomog p (fun k => (c k).toNat) ∧ Ideal.Quotient.mk V p = m := by
  by_cases hc : ∀ k, 0 ≤ c k
  · refine ⟨hc, ?_⟩
    have hm' : m ∈ Submodule.map (Ideal.Quotient.mkₐ S V).toLinearMap
        (Submodule.span S {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)}) := by
      rw [← Submodule.span_image]
      exact hm
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm'
    refine ⟨p, ?_, rfl⟩
    clear hm h0 hm'
    induction hp using Submodule.span_induction with
    | mem x hx => exact hx.2
    | zero => exact homog_zero _
    | add x y _ _ hx hy => exact homog_add hx hy
    | smul r x _ hx => exact homog_smul r hx
  · exfalso
    apply h0
    have e : {p : MRingOver S ι | (∀ k, 0 ≤ c k) ∧ IsMultiHomog p (fun k => (c k).toNat)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp => hc hp.1
    unfold KH.quotPart at hm
    rw [e, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hm
    exact hm

theorem quotPart_mul {c d : K → ℤ} {x y : MRingOver S ι ⧸ V} (hx : x ∈ KH.quotPart S V c)
    (hy : y ∈ KH.quotPart S V d) : x * y ∈ KH.quotPart S V (c + d) := by
  have h := Submodule.mul_mem_mul hx hy
  unfold KH.quotPart at h ⊢
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨_, ⟨p, ⟨hc, hp⟩, rfl⟩, _, ⟨q, ⟨hd, hq⟩, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨p * q, ⟨fun k => add_nonneg (hc k) (hd k), ?_⟩, map_mul _ _ _⟩
  have e : (fun k => ((c + d) k).toNat) = (fun k => (c k).toNat) + fun k => (d k).toNat := by
    funext k
    simp [Int.toNat_add (hc k) (hd k)]
  rw [e]
  exact homog_mul hp hq

theorem smul_quot (r : MRingOver S ι) (a : MRingOver S ι ⧸ V) : r • a = Ideal.Quotient.mk V r * a :=
  Algebra.smul_def r a

theorem locPart_eq_mk {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T (MRingOver S ι ⧸ V)} (hx : x ∈ KH.locPart ι (KH.quotPart S V) T c) :
    ∃ (m : MRingOver S ι ⧸ V) (t : T) (β : K → ℕ), IsMultiHomog (t : MRingOver S ι) β ∧
      m ∈ KH.quotPart S V (c + fun k => (β k : ℤ)) ∧ x = LocalizedModule.mk m t := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 1, 0, homog_one, Submodule.zero_mem _, (LocalizedModule.zero_mk 1).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, t, β, ht, hm, rfl⟩ := hx
    obtain ⟨m', t', β', ht', hm', rfl⟩ := hy
    refine ⟨t' • m + t • m', t * t', β + β', homog_mul ht ht', ?_, LocalizedModule.mk_add_mk⟩
    have deg : ∀ (s : T) (γ : K → ℕ), IsMultiHomog (s : MRingOver S ι) γ →
        Ideal.Quotient.mk V (s : MRingOver S ι) ∈ KH.quotPart S V (fun k => (γ k : ℤ)) := by
      intro s γ hs
      exact Submodule.subset_span ⟨s, ⟨fun k => Int.natCast_nonneg _, by simpa using hs⟩, rfl⟩
    have h1 := quotPart_mul hm (deg t' β' ht')
    have h2 := quotPart_mul hm' (deg t β ht)
    have e1 : ((c + fun k => (β k : ℤ)) + fun k => (β' k : ℤ)) = c + fun k => ((β + β') k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    have e2 : ((c + fun k => (β' k : ℤ)) + fun k => (β k : ℤ)) = c + fun k => ((β + β') k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    rw [e1] at h1
    rw [e2] at h2
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_quot, smul_quot, mul_comm _ m, mul_comm _ m']
    exact add_mem h1 h2
  | smul r x _ hx =>
    obtain ⟨m, t, β, ht, hm, rfl⟩ := hx
    exact ⟨r • m, t, β, ht, Submodule.smul_mem _ r hm, LocalizedModule.smul'_mk r m t⟩

end Graded

variable {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω}

theorem map_int (f : MRing ι) : MvPolynomial.map (Int.castRingHom ℤ) f = f := by
  rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, MvPolynomial.map_id]

variable (y) in

theorem aeval_eq_eval_mConeMap (f : MRing ι) :
    aeval y f = MvPolynomial.eval (fun _ : K => (1 : Ω)) (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, map_mul, hp]; simp [mConeMap]

theorem aeval_eq_zero_of_mem {f : MRing ι} (hf : f ∈ idealOver y ℤ) : aeval y f = 0 := by
  have h : idealOver y ℤ ≤ RingHom.ker (aeval y : MRing ι →ₐ[ℤ] Ω) := by
    refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, map_int, aeval_eq_eval_mConeMap, RingHom.mem_ker.mp hg, map_zero]
  exact RingHom.mem_ker.mp (h hf)

theorem cellMon_aeval_ne {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0) {t : MRing ι}
    (ht : t ∈ KH.cellMon ℤ I) : aeval y t ≠ 0 := by
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    rw [aeval_X]
    exact hI k i hi
  | one => simp
  | mul x x' _ _ hx hx' => rw [map_mul]; exact mul_ne_zero hx hx'

variable (y) in

theorem aeval_div_mem (c : ∀ k, ι k) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k ∈ chartRingZ y c := by
  classical
  rw [g.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, mul_div_assoc]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  have key : m.prod (fun p e => y p ^ e) / ∏ k, y ⟨k, c k⟩ ^ d k = ∏ p, (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [div_pow]
    rw [Finset.prod_div_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [key]
  exact Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _
    (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) p)) _

theorem mem_chartRingZ_of_isRep {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {T : Submonoid (MRing ι)}
    {x : LocalizedModule T (MRing ι ⧸ idealOver y ℤ)} {t : Ω} {a : K → ℤ}
    (ht : IsRep y ℤ T x c t a) : t * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := by
  obtain ⟨e, F, ⟨d, hF, hd, hv⟩, -, -⟩ := ht
  have hpe : ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hpa : ∏ k, y ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hd' : ∏ k, y ⟨k, c k⟩ ^ d k = (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ a k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), hd k]
  have e1 : t * ∏ k, y ⟨k, c k⟩ ^ (-a k) = aeval y F / ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [hv, hd']
    simp only [zpow_neg, Finset.prod_inv_distrib]
    field_simp
  rw [e1]
  exact aeval_div_mem y c hF

def chartCell (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

theorem chartCell_good {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∀ k, ∀ i ∈ (chartCell c).1 k, y ⟨k, i⟩ ≠ 0 :=
  fun k i hi => by rw [Finset.mem_singleton.mp hi]; exact hc k

theorem eq_chartCell {J : KH.Cell K ι 0} {c : ∀ k, ι k} (hc : ∀ k, c k ∈ J.1 k) : J = chartCell c := by
  have hcard : ∀ k, (J.1 k).card = 1 := by
    intro k
    have h0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
    have h1 := Finset.card_pos.mpr (J.2.1 k)
    omega
  refine Subtype.ext (funext fun k => ?_)
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (hcard k)
  show J.1 k = {c k}
  have h := hc k
  rw [hi] at h ⊢
  rw [Finset.mem_singleton.mp h]

theorem mem_cellMon_chart {c : ∀ k, ι k} {t : MRing ι} (ht : t ∈ KH.cellMon ℤ (chartCell c).1) :
    ∃ e : K → ℕ, t = cmon c e := by
  classical
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    have hi' : i = c k := Finset.mem_singleton.mp hi
    subst hi'
    refine ⟨Pi.single k 1, ?_⟩
    unfold cmon
    rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (fun h => absurd (Finset.mem_univ k) h)]
    simp
  | one => exact ⟨0, by simp [cmon]⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨f', rfl⟩ := hx'
    exact ⟨f + f', (cmon_add c f f').symm⟩

theorem exists_isRep {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : K → ℤ}
    {x : LocalizedModule (KH.cellMon ℤ (chartCell c).1) (MRing ι ⧸ idealOver y ℤ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℤ (idealOver y ℤ)) (KH.cellMon ℤ (chartCell c).1) a) :
    ∃ s, IsRep y ℤ (KH.cellMon ℤ (chartCell c).1) x c s a := by
  obtain ⟨m, t, β, ht, hm, rfl⟩ := locPart_eq_mk hx
  obtain ⟨e, he⟩ := mem_cellMon_chart t.2
  have hβ : β = e := by
    have hne : cmon c e ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero _)
    obtain ⟨μ, hμ⟩ : (cmon c e).support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hne)
    rw [he] at ht
    exact funext fun k => (ht μ hμ k).symm.trans (homog_cmon c e μ hμ k)
  rw [hβ] at hm
  have hmem : ∀ f : K → ℕ, MvPolynomial.map (Int.castRingHom ℤ) (cmon c f) ∈ KH.cellMon ℤ (chartCell c).1 :=
    fun f => cmon_mem ℤ (I := (chartCell c).1) (fun k => Finset.mem_singleton_self (c k)) f
  by_cases h0 : m = 0
  · subst h0
    refine ⟨0, fun k => (-a k).toNat, 0, ⟨fun k => (a k).toNat, homog_zero _, fun k => by dsimp only; omega,
      by simp⟩, hmem _, ?_⟩
    rw [map_zero, map_zero, LocalizedModule.zero_mk, LocalizedModule.zero_mk]
  · obtain ⟨hnn, p, hp, rfl⟩ := quotPart_eq_mk hm h0
    have hpe : ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    refine ⟨aeval y p / ∏ k, y ⟨k, c k⟩ ^ e k, e, p, ⟨_, hp, fun k => ?_, (div_mul_cancel₀ _ hpe).symm⟩,
      hmem e, ?_⟩
    · have := hnn k
      simp only [Pi.add_apply] at this ⊢
      omega
    · congr 1
      · rw [map_int]
      · exact Subtype.ext (he.trans (map_int _).symm)

theorem val_eq_of_isRep {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0)
    {x : LocalizedModule (KH.cellMon ℤ I) (MRing ι ⧸ idealOver y ℤ)} {c c' : ∀ k, ι k} {s s' : Ω} {a : K → ℤ}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0)
    (hx : IsRep y ℤ (KH.cellMon ℤ I) x c s a) (hx' : IsRep y ℤ (KH.cellMon ℤ I) x c' s' a) : s = s' := by
  obtain ⟨e1, F1, ⟨d1, -, -, hv1⟩, h1, rfl⟩ := hx
  obtain ⟨e2, F2, ⟨d2, -, -, hv2⟩, h2, hx'⟩ := hx'
  rw [LocalizedModule.mk_eq] at hx'
  obtain ⟨u, hu⟩ := hx'
  simp only [Submonoid.smul_def, smul_mk, map_int] at hu
  rw [Ideal.Quotient.eq] at hu
  have h0 := aeval_eq_zero_of_mem hu
  have hu0 := cellMon_aeval_ne hI u.2
  rw [map_sub, map_mul, map_mul, map_mul, map_mul, aeval_cmon, aeval_cmon, hv1, hv2] at h0
  have p1 : ∏ k, y ⟨k, c k⟩ ^ e1 k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have p2 : ∏ k, y ⟨k, c' k⟩ ^ e2 k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc' k)
  have key : (aeval y (u : MRing ι) * (∏ k, y ⟨k, c' k⟩ ^ e2 k) * ∏ k, y ⟨k, c k⟩ ^ e1 k) * (s - s') = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero hu0 p2) p1)
  · exact sub_eq_zero.mp h

section Cocycle

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem res_faces {M : Type} [AddCommGroup M] [Module (MRing ι) M] (z : KH.CechC ℤ ι M 0)
    (hz : KH.cechD ℤ ι M 0 z = 0) (I : KH.Cell K ι 1) (k0 : K) (i1 i2 : ι k0) (hlt : i1 < i2)
    (hI : I.1 k0 = {i1, i2}) (hrest : ∀ k ≠ k0, (I.1 k).card = 1) (J1 J2 : KH.Cell K ι 0)
    (hJ1 : J1.1 = Function.update I.1 k0 ((I.1 k0).erase i1))
    (hJ2 : J2.1 = Function.update I.1 k0 ((I.1 k0).erase i2)) :
    KH.cellRes ℤ M J1.1 I.1 (z J1) = KH.cellRes ℤ M J2.1 I.1 (z J2) := by
  have hne : ∀ k, (I.1 k).Nonempty := I.2.1
  have h2 : (I.1 k0).card = 2 := by rw [hI]; exact Finset.card_pair (ne_of_lt hlt)
  have hface : ∀ i ∈ I.1 k0, (∀ l, (Function.update I.1 k0 ((I.1 k0).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k0 ((I.1 k0).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k0).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, h2]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k0
      · subst hl
        rw [Function.update_self]
        exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]
        exact hne l
    · by_cases hl : l = k0
      · subst hl
        rw [Function.update_self, hc]
        rfl
      · rw [Function.update_of_ne hl, hrest l hl]
        rfl
  have hsumsign : ∑ l ∈ Finset.univ.filter (· < k0), ((I.1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hrest l (ne_of_lt (Finset.mem_filter.mp hl).2)]; rfl
  have hs1 : KH.faceSign I.1 k0 i1 = 1 := by
    have f1 : (({i1, i2} : Finset (ι k0)).filter (· < i1)).card = 0 := by
      simp [Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hlt.le]
    simp only [KH.faceSign, hsumsign, hI, add_zero, f1]
    norm_num
  have hs2 : KH.faceSign I.1 k0 i2 = -1 := by
    have f2 : (({i1, i2} : Finset (ι k0)).filter (· < i2)).card = 1 := by
      simp [Finset.filter_insert, Finset.filter_singleton, hlt]
    simp only [KH.faceSign, hsumsign, hI, add_zero, f2]
    norm_num
  have hi1 : i1 ∈ I.1 k0 := by rw [hI]; simp
  have hi2 : i2 ∈ I.1 k0 := by rw [hI]; simp
  have key : KH.cechD ℤ ι M 0 z I =
      KH.faceSign I.1 k0 i1 • KH.cellRes ℤ M (Function.update I.1 k0 ((I.1 k0).erase i1)) I.1
        (z ⟨_, hface i1 hi1⟩) + KH.faceSign I.1 k0 i2 • KH.cellRes ℤ M
        (Function.update I.1 k0 ((I.1 k0).erase i2)) I.1 (z ⟨_, hface i2 hi2⟩) := by
    rw [KH.cechD]
    erw [LinearMap.pi_apply]
    simp only [LinearMap.sum_apply]
    rw [Finset.sum_eq_single k0]
    · rw [Finset.sum_eq_add_of_mem i1 i2 hi1 hi2 (ne_of_lt hlt)]
      · rw [dif_pos (hface i1 hi1), dif_pos (hface i2 hi2)]
        rfl
      · intro i hi hne'
        rw [hI] at hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact absurd rfl hne'.1
        · exact absurd rfl hne'.2
    · intro k _ hk
      refine Finset.sum_eq_zero fun i hi => ?_
      split_ifs with hc
      · exfalso
        obtain ⟨hn, -⟩ := hc
        have h3 := hn k
        rw [Function.update_self] at h3
        have h4 := Finset.card_erase_of_mem hi
        rw [hrest k hk] at h4
        have h5 := Finset.card_pos.mpr h3
        omega
      · rfl
    · intro h
      exact absurd (Finset.mem_univ k0) h
  have e0 : KH.cechD ℤ ι M 0 z I = 0 := by rw [hz]; rfl
  rw [key, hs1, hs2, one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at e0
  obtain ⟨A1, hA1⟩ := J1
  obtain ⟨A2, hA2⟩ := J2
  simp only at hJ1 hJ2
  subst hJ1 hJ2
  exact e0

variable {a : K → ℤ} {v : KH.CechC ℤ ι (MRing ι ⧸ idealOver y ℤ) 0}

theorem val_step_lt (hz : KH.cechD ℤ ι _ 0 v = 0) {c d : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) (k0 : K) (hcd : ∀ k ≠ k0, c k = d k)
    (hlt : c k0 < d k0) {s t : Ω}
    (hs : IsRep y ℤ (KH.cellMon ℤ (chartCell c).1) (v (chartCell c)) c s a)
    (ht : IsRep y ℤ (KH.cellMon ℤ (chartCell d).1) (v (chartCell d)) d t a) : s = t := by
  classical
  have hne : c k0 ≠ d k0 := ne_of_lt hlt
  set A : ∀ k, Finset (ι k) := Function.update (fun k => ({c k} : Finset (ι k))) k0 {c k0, d k0} with hAdef
  have hA0 : A k0 = {c k0, d k0} := Function.update_self _ _ _
  have hAk : ∀ k ≠ k0, A k = {c k} := fun k hk => Function.update_of_ne hk _ _
  have hAne : ∀ k, (A k).Nonempty := by
    intro k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      exact Finset.insert_nonempty _ _
    · rw [hAk k hk]
      exact Finset.singleton_nonempty _
  have hAsum : ∑ k, ((A k).card - 1) = 1 := by
    rw [Finset.sum_eq_single k0 (fun k _ hk => by rw [hAk k hk]; rfl)
      (fun h => absurd (Finset.mem_univ k0) h), hA0, Finset.card_pair hne]
  have hIy : ∀ k, ∀ i ∈ A k, y ⟨k, i⟩ ≠ 0 := by
    intro k i hi
    by_cases hk : k = k0
    · subst hk
      rw [hA0] at hi
      rcases Finset.mem_insert.mp hi with h | h
      · rw [h]; exact hc _
      · rw [Finset.mem_singleton.mp h]; exact hd _
    · rw [hAk k hk, Finset.mem_singleton] at hi
      rw [hi]
      exact hc k
  have hrest : ∀ k ≠ k0, (A k).card = 1 := fun k hk => by rw [hAk k hk]; rfl
  have hsc : ∀ k, (chartCell c).1 k ⊆ A k := by
    intro k
    show {c k} ⊆ A k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      simp
    · rw [hAk k hk]
  have hsd : ∀ k, (chartCell d).1 k ⊆ A k := by
    intro k
    show {d k} ⊆ A k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      simp
    · rw [hAk k hk, hcd k hk]
  have e := res_faces v hz ⟨A, hAne, hAsum⟩ k0 (c k0) (d k0) hlt hA0 hrest (chartCell d) (chartCell c) ?_ ?_
  · rw [cellRes_of_le (cellMon_mono hsd), cellRes_of_le (cellMon_mono hsc)] at e
    have h1 := hs.lift (cellMon_mono hsc)
    have h2 := ht.lift (cellMon_mono hsd)
    rw [← e] at h1
    exact val_eq_of_isRep hIy hc hd h1 h2
  · funext k
    by_cases hk : k = k0
    · subst hk
      show ({d k} : Finset (ι k)) = Function.update A k ((A k).erase (c k)) k
      rw [Function.update_self, hA0, Finset.erase_insert (by simpa using hne)]
    · show ({d k} : Finset (ι k)) = Function.update A k0 ((A k0).erase (c k0)) k
      rw [Function.update_of_ne hk, hAk k hk, hcd k hk]
  · funext k
    by_cases hk : k = k0
    · subst hk
      show ({c k} : Finset (ι k)) = Function.update A k ((A k).erase (d k)) k
      rw [Function.update_self, hA0, Finset.pair_comm, Finset.erase_insert (by simpa using hne.symm)]
    · show ({c k} : Finset (ι k)) = Function.update A k0 ((A k0).erase (d k0)) k
      rw [Function.update_of_ne hk, hAk k hk]

theorem val_step (hz : KH.cechD ℤ ι _ 0 v = 0) {c d : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) (k0 : K) (hcd : ∀ k ≠ k0, c k = d k) {s t : Ω}
    (hs : IsRep y ℤ (KH.cellMon ℤ (chartCell c).1) (v (chartCell c)) c s a)
    (ht : IsRep y ℤ (KH.cellMon ℤ (chartCell d).1) (v (chartCell d)) d t a) : s = t := by
  rcases lt_trichotomy (c k0) (d k0) with h | h | h
  · exact val_step_lt hz hc hd k0 hcd h hs ht
  · have e : c = d := funext fun k => by
      by_cases hk : k = k0
      · subst hk; exact h
      · exact hcd k hk
    subst e
    exact val_eq_of_isRep (chartCell_good hc) hc hc hs ht
  · exact (val_step_lt hz hd hc k0 (fun k hk => (hcd k hk).symm) h ht hs).symm

theorem val_chart_eq (hz : KH.cechD ℤ ι _ 0 v = 0)
    (hloc : ∀ J : KH.Cell K ι 0, v J ∈ KH.locPart ι (KH.quotPart ℤ (idealOver y ℤ)) (KH.cellMon ℤ J.1) a)
    {c d : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) {s t : Ω}
    (hs : IsRep y ℤ (KH.cellMon ℤ (chartCell c).1) (v (chartCell c)) c s a)
    (ht : IsRep y ℤ (KH.cellMon ℤ (chartCell d).1) (v (chartCell d)) d t a) : s = t := by
  classical
  have hmix : ∀ (U : Finset K) k, y ⟨k, (fun k => if k ∈ U then d k else c k) k⟩ ≠ 0 := by
    intro U k
    dsimp only
    split_ifs
    exacts [hd k, hc k]
  have key : ∀ U : Finset K, ∀ t,
      IsRep y ℤ (KH.cellMon ℤ (chartCell fun k => if k ∈ U then d k else c k).1)
        (v (chartCell fun k => if k ∈ U then d k else c k)) (fun k => if k ∈ U then d k else c k) t a → s = t := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro t ht
      have e0 : (fun k => if k ∈ (∅ : Finset K) then d k else c k) = c := funext fun k => by simp
      rw [e0] at ht
      exact val_eq_of_isRep (chartCell_good hc) hc hc hs ht
    | insert k0 U hk0 ih =>
      intro t ht
      obtain ⟨t', ht'⟩ := exists_isRep (hmix U) (hloc _)
      rw [ih t' ht']
      exact val_step hz (hmix U) (hmix (insert k0 U)) k0 (fun k hk => by simp [Finset.mem_insert, hk]) ht' ht
  have e1 : (fun k => if k ∈ (Finset.univ : Finset K) then d k else c k) = d := funext fun k => by simp
  have h := key Finset.univ t
  rw [e1] at h
  exact h ht

end Cocycle

end ZeroCocycleSection

open ZeroCocycleSection GenOnFibres in

theorem ZeroCocycleSection.proof : ZeroCocycleSection.Statement := by
  intro K _ _ ι _ _ Ω _ y a v hv
  classical
  obtain ⟨hv1, hv2⟩ := hv
  have hloc : ∀ J : KH.Cell K ι 0,
      v J ∈ KH.locPart ι (KH.quotPart ℤ (idealOver y ℤ)) (KH.cellMon ℤ J.1) a :=
    fun J => hv1 J (Set.mem_univ _)
  have hz : KH.cechD ℤ ι _ 0 v = 0 := hv2
  by_cases hex : ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0
  · obtain ⟨c0, hc0⟩ := hex
    obtain ⟨s, hs⟩ := exists_isRep hc0 (hloc (chartCell c0))
    have hmem : s ∈ chartLat y a 1 := by
      intro c hc
      obtain ⟨t, ht⟩ := exists_isRep hc (hloc (chartCell c))
      rw [val_chart_eq hz hloc hc0 hc hs ht]
      simp only [Nat.cast_one, one_mul]
      exact mem_chartRingZ_of_isRep hc ht
    refine ⟨s, hmem, funext fun J => ?_⟩
    by_cases hJ : ∀ k, y ⟨k, cellChart J k⟩ ≠ 0
    · have eJ := eq_chartCell (cellChart_mem J)
      have h1 := secCoch_spec (S := ℤ) hmem J hJ
      obtain ⟨t, ht⟩ := exists_isRep hJ (hloc (chartCell (cellChart J)))
      have hst := val_chart_eq hz hloc hc0 hJ hs ht
      rw [← hst, ← eJ] at ht
      exact h1.unique ht
    · push Not at hJ
      obtain ⟨k, h0⟩ := hJ
      have := subsingleton_loc (S := ℤ) (y := y) (cellChart_mem J k) h0
      exact Subsingleton.elim _ _
  · refine ⟨0, zero_mem _, funext fun J => ?_⟩
    push Not at hex
    obtain ⟨k, h0⟩ := hex (cellChart J)
    have := subsingleton_loc (S := ℤ) (y := y) (cellChart_mem J k) h0
    exact Subsingleton.elim _ _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
