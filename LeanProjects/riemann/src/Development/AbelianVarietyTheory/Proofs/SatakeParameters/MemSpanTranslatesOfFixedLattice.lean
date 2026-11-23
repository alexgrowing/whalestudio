import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave

noncomputable section

namespace GlobalTheory.FourierSpan

variable {G : Type} [AddCommGroup G]

def annihIn (χ : G → G → ℂ) (hχ : GlobalTheory.PlaceModel.IsBichar χ) (Yh L : AddSubgroup G) : AddSubgroup G where
  carrier := {y | y ∈ Yh ∧ ∀ x ∈ L, χ x y = 1}
  add_mem' := fun {a b} ha hb => ⟨Yh.add_mem ha.1 hb.1, fun x hx => by rw [hχ.right, ha.2 x hx, hb.2 x hx, one_mul]⟩
  zero_mem' := ⟨Yh.zero_mem, fun x _ => hχ.zero_right x⟩
  neg_mem' := fun {a} ha => ⟨Yh.neg_mem ha.1, fun x hx => by
    have e : χ x (-a) * χ x a = 1 := by rw [← hχ.right, neg_add_cancel, hχ.zero_right]
    rwa [ha.2 x hx, mul_one] at e⟩

theorem bichar_pow_left {χ : G → G → ℂ} (hχ : GlobalTheory.PlaceModel.IsBichar χ) (k : ℕ) (x y : G) :
    χ (k • x) y = χ x y ^ k := by
  induction k with
  | zero => simp [hχ.zero_left]
  | succ k ih => rw [succ_nsmul, hχ.left, ih, pow_succ]

theorem mem_span_translates_of_fixed {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V]
    (χ : G → G → ℂ) (hχ : GlobalTheory.PlaceModel.IsBichar χ) (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G)
    (hLL' : L ≤ L') (hL'X : L' ≤ X) (hKY : K ≤ Yh) (ρ0 : ∀ v, ρ 0 v = v)
    (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v)
    (ρY : ∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v))
    (hR : ∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L)
    (hLK : ∀ x ∈ L', ∀ y ∈ K, χ x y = 1)
    (hsep : ∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K)
    (W : Submodule ℂ V) (hWX : ∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) (hWY : ∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W)
    (f : V) (hfW : f ∈ W) (hfL : ∀ x ∈ L, ρ x f = f) (hfK : ∀ y ∈ K, ρ y f = f) :
    f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧
      (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  classical
  obtain ⟨R, hR⟩ := hR
  have negR : ∀ x y, χ x (-y) * χ x y = 1 := fun x y => by rw [← hχ.right, neg_add_cancel, hχ.zero_right]
  set P := annihIn χ hχ Yh L with hPdef
  have memP : ∀ y, y ∈ P ↔ y ∈ Yh ∧ ∀ x ∈ L, χ x y = 1 := fun y => Iff.rfl
  have hPY : ∀ y ∈ P, y ∈ Yh := fun y hy => ((memP y).1 hy).1
  have hKP : K ≤ P := fun y hy => (memP y).2 ⟨hKY hy, fun x hx => hLK x (hLL' hx) y hy⟩

  have wdQ : ∀ y ∈ P, ∀ u v : L', (QuotientAddGroup.mk u : L' ⧸ L.addSubgroupOf L') = QuotientAddGroup.mk v →
      χ u y = χ v y := by
    intro y hy u v huv
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at huv
    have e : (v : G) = u + ((-u + v : L') : G) := by simp
    rw [e, hχ.left, ((memP y).1 hy).2 _ huv, mul_one]
  have wdQ' : ∀ h : V, (∀ k ∈ K, ρ k h = h) → ∀ u v : P,
      (QuotientAddGroup.mk u : P ⧸ K.addSubgroupOf P) = QuotientAddGroup.mk v → ρ u h = ρ v h := by
    intro h hh u v huv
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at huv
    have e : (v : G) = u + ((-u + v : P) : G) := by simp
    rw [e, ← ρY _ (hPY _ u.2) _ (hKY huv), hh _ huv]

  have finQ : Finite (L' ⧸ L.addSubgroupOf L') := by
    let φ : R → L' ⧸ L.addSubgroupOf L' := fun r =>
      if h : (r : G) ∈ L' then QuotientAddGroup.mk ⟨r, h⟩ else 0
    refine Finite.of_surjective φ ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, htr⟩ := hR t t.2
    have hrL' : r ∈ L' := by
      have := L'.sub_mem t.2 (hLL' htr)
      simpa using this
    refine ⟨⟨r, hr⟩, ?_⟩
    simp only [φ, dif_pos hrL']
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
    convert htr using 1
    simp only
    abel
  letI : Fintype (L' ⧸ L.addSubgroupOf L') := Fintype.ofFinite _
  set n := Fintype.card (L' ⧸ L.addSubgroupOf L') with hn_def
  have hn : 0 < n := Fintype.card_pos
  have powQ : ∀ y ∈ P, ∀ u : L', χ u y ^ n = 1 := by
    intro y hy u
    have hnu : ((n • u : L') : G) ∈ L := by
      have h0 : n • (QuotientAddGroup.mk u : L' ⧸ L.addSubgroupOf L') = 0 := card_nsmul_eq_zero
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
      exact h0
    rw [← bichar_pow_left hχ, ← AddSubgroup.coe_nsmul]
    exact ((memP y).1 hy).2 _ hnu

  have finS : ({z : ℂ | z ^ n = 1} : Set ℂ).Finite :=
    (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots hn).2 hz
  haveI := finS.to_subtype
  have finQ' : Finite (P ⧸ K.addSubgroupOf P) := by
    let Φ : (P ⧸ K.addSubgroupOf P) → ((L' ⧸ L.addSubgroupOf L') → ({z : ℂ | z ^ n = 1} : Set ℂ)) :=
      fun q' q => ⟨χ (q.out : L') (q'.out : P), powQ _ (q'.out).2 _⟩
    refine Finite.of_injective Φ ?_
    intro a b hab
    rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    refine hsep _ (hPY _ (-a.out + b.out : P).2) fun x hx => ?_
    have e := congrArg Subtype.val (congrFun hab (QuotientAddGroup.mk ⟨x, hx⟩))
    simp only [Φ] at e
    have ea := wdQ _ (a.out).2 ((QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L').out) ⟨x, hx⟩
      (QuotientAddGroup.out_eq' _)
    have eb := wdQ _ (b.out).2 ((QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L').out) ⟨x, hx⟩
      (QuotientAddGroup.out_eq' _)
    rw [ea, eb] at e
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, hχ.right, ← e]
    exact negR _ _
  letI : Fintype (P ⧸ K.addSubgroupOf P) := Fintype.ofFinite _

  have hKh : ∀ r ∈ L', ∀ k ∈ K, ρ k (ρ (-r) f) = ρ (-r) f := by
    intro r hr k hk
    have := ρXY (-r) (X.neg_mem (hL'X hr)) k (hKY hk) f
    rw [hfK k hk, hLK _ (L'.neg_mem hr) k hk, one_smul] at this
    exact this.symm
  let g : (L' ⧸ L.addSubgroupOf L') → V := fun q =>
    ∑ q' : P ⧸ K.addSubgroupOf P, ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)
  have gW : ∀ q, g q ∈ W := fun q => Submodule.sum_mem _ fun q' _ =>
    hWY _ (hWX f hfW _ (X.neg_mem (hL'X (q.out).2))) _ (hPY _ (q'.out).2)
  have gL : ∀ q, ∀ x ∈ L, ρ x (g q) = g q := by
    intro q x hx
    simp only [g, map_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    have hxX : x ∈ X := hL'X (hLL' hx)
    have hrX : -((q.out : L') : G) ∈ X := X.neg_mem (hL'X (q.out).2)
    rw [ρXY x hxX _ (hPY _ (q'.out).2), ((memP _).1 (q'.out).2).2 x hx, one_smul, ρX x hxX _ hrX, add_comm,
      ← ρX _ hrX _ hxX, hfL x hx]
  have gP : ∀ q, ∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y (g q) = g q := by
    intro q y hy hyL
    have hyP : y ∈ P := (memP y).2 ⟨hy, hyL⟩
    simp only [g, map_sum]
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ⟨y, hyP⟩ : P ⧸ K.addSubgroupOf P))
      (fun q' : P ⧸ K.addSubgroupOf P => ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)))
    refine Finset.sum_congr rfl fun q' _ => ?_
    simp only [Equiv.coe_addRight]
    rw [ρY y hy _ (hPY _ (q'.out).2), ← wdQ' _ (hKh _ (q.out).2) (q'.out + ⟨y, hyP⟩) _ ?_]
    · rw [AddSubgroup.coe_add, add_comm]
    · rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
  have key : ∑ q : L' ⧸ L.addSubgroupOf L', ρ ((q.out : L') : G) (g q) = (n : ℂ) • f := by
    have step : ∀ q : L' ⧸ L.addSubgroupOf L', ∀ q' : P ⧸ K.addSubgroupOf P,
        ρ ((q.out : L') : G) (ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)) =
          χ ((q.out : L') : G) ((q'.out : P) : G) • ρ ((q'.out : P) : G) f := by
      intro q q'
      have hrX := hL'X (q.out).2
      rw [ρXY _ hrX _ (hPY _ (q'.out).2), ρX _ hrX _ (X.neg_mem hrX), add_neg_cancel, ρ0]
    simp only [g, map_sum, step]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (0 : P ⧸ K.addSubgroupOf P)]
    · have h0K : (((0 : P ⧸ K.addSubgroupOf P).out : P) : G) ∈ K := by
        have := QuotientAddGroup.out_eq' (0 : P ⧸ K.addSubgroupOf P)
        rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at this
        exact this
      have h1 : ∀ q : L' ⧸ L.addSubgroupOf L',
          χ ((q.out : L') : G) (((0 : P ⧸ K.addSubgroupOf P).out : P) : G) = 1 :=
        fun q => hLK _ (q.out).2 _ h0K
      rw [hfK _ h0K]
      simp only [h1, Finset.sum_const, Finset.card_univ, ← hn_def, nsmul_eq_mul, mul_one]
    · intro q' _ hq'
      have hnK : ((q'.out : P) : G) ∉ K := by
        intro hK
        apply hq'
        rw [← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        exact hK
      obtain ⟨x, hx, hxy⟩ : ∃ x ∈ L', χ x ((q'.out : P) : G) ≠ 1 := by
        by_contra hc
        push_neg at hc
        exact hnK (hsep _ (hPY _ (q'.out).2) hc)
      have hyP := (q'.out).2
      have shift : ∀ q : L' ⧸ L.addSubgroupOf L',
          χ (((q + (QuotientAddGroup.mk (⟨x, hx⟩ : L') : L' ⧸ L.addSubgroupOf L')).out : L') : G) ((q'.out : P) : G) =
            χ ((q.out : L') : G) ((q'.out : P) : G) * χ x ((q'.out : P) : G) := by
        intro q
        rw [← wdQ _ hyP (q.out + (⟨x, hx⟩ : L')) _ ?_, AddSubgroup.coe_add, hχ.left]
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
      have hS2 := Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L'))
        (fun q : L' ⧸ L.addSubgroupOf L' => χ ((q.out : L') : G) ((q'.out : P) : G))
      simp only [Equiv.coe_addRight, shift, ← Finset.sum_mul] at hS2
      have hsum : ∑ q : L' ⧸ L.addSubgroupOf L', χ ((q.out : L') : G) ((q'.out : P) : G) = 0 := by
        have h3 : (∑ q : L' ⧸ L.addSubgroupOf L', χ ((q.out : L') : G) ((q'.out : P) : G)) *
            (χ x ((q'.out : P) : G) - 1) = 0 := by
          rw [mul_sub, hS2, mul_one, sub_self]
        exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hxy)
      rw [hsum, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hf : f = (n : ℂ)⁻¹ • ∑ q : L' ⧸ L.addSubgroupOf L', ρ ((q.out : L') : G) (g q) := by
    rw [key, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  rw [hf]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_)
  exact ⟨_, hL'X (q.out).2, g q, gW q, gL q, gP q, rfl⟩
end GlobalTheory.FourierSpan
