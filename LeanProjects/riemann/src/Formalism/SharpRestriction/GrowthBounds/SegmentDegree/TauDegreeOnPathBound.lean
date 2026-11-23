import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumSingleApplyZero
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.OldestLetterInSegment

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def BetaRatioBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → 4 * X.Y * (X.beS p K j (X.restr j b) : ℝ) ≤ (X.Qc p K j : ℝ)

def TauDegreeOnPathBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K →
    ∀ (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) (dd : Fin (segN X.F j) → ℕ),
      X.IsPATH p K j b μ dd → ∀ i, X.F.fr j 0 ≤ segE X.F j i → dd i ≤ 2 * X.beS p K j b

def ResidueClassCount : Prop :=
  ∀ (r Q be c ρ : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card : ℝ)

section Congr

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K]

theorem Bdeg_congr (j : ℤ) {b b' : ℤ → ℕ} (x : ℤ) (h : b x = b' x) : X.Bdeg p K j b x = X.Bdeg p K j b' x := by
  unfold Dat.Bdeg
  rw [h]

theorem beS_congr (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x) :
    X.beS p K j b = X.beS p K j b' := by
  unfold Dat.beS
  refine Finset.sum_congr rfl fun x hx => ?_
  exact Bdeg_congr X p K j x (h x (Finset.mem_filter.mp hx).2)

theorem IsPATH_congr (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x)
    {μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ} {dd : Fin (segN X.F j) → ℕ} (hP : X.IsPATH p K j b μ dd) :
    X.IsPATH p K j b' μ dd :=
  ⟨hP.path, fun i hi => by rw [hP.degs i hi]; exact Bdeg_congr X p K j _ (h _ hi),
    fun i i' hi m hm => by rw [hP.head i i' hi m hm, beS_congr X p K j h]⟩

theorem IsGood_congr (hX : X.Hyp p K) (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x)
    {μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ} (hG : X.IsGood p K j b μ) : X.IsGood p K j b' μ := by
  classical
  intro i hi
  have hlate : segE X.F j i ∈ X.toLate j := Finset.mem_filter.mpr ⟨segE_mem X.F j i, hi⟩
  have hold := (oldest_letter_in_segment p n' r K X hX j _ hlate).2
  have hth : X.thc p K j b' (segE X.F j i) = X.thc p K j b (segE X.F j i) := by
    unfold Dat.thc
    split_ifs with hW
    · rfl
    · have hLL := hold hW
      unfold Frames.LLset at hLL
      have hlt := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hLL).1).2
      rw [h _ hlt]
  rw [hth]
  exact hG i hi

theorem restr_setTau_low (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) (x : ℤ) (hx : x < X.F.fr j 0) :
    X.restr j b x = X.restr j (X.setTau j b e) x := by
  unfold Dat.restr Dat.setTau
  have : ¬ (X.F.fr j 0 ≤ x ∧ x ≤ X.F.fr j (r - 1)) := fun h => by omega
  simp only [this, if_false]

theorem restr_setTau_tau (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) (i' : Fin r) :
    X.restr j (X.setTau j b e) (X.F.fr j i'.val) = e i' := by
  classical
  have hV := hX.valid
  have hmem := k_fr_mem_letters X.F hV j i'.isLt
  have h4 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h4
  have a2 := kfr_le X.F hV j (Nat.zero_le i'.val) i'.isLt
  have a3 := kfr_le X.F hV j (by have := i'.isLt; omega : i'.val ≤ r - 1) (by have := i'.isLt; omega)
  have hlate : X.F.fr j i'.val ∈ X.toLate j := by
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    unfold Frames.IsW
    omega
  unfold Dat.restr Dat.setTau
  rw [if_pos hlate, if_pos ⟨a2, a3⟩, Finset.sum_eq_single i']
  · simp
  · intro i _ hne
    rw [if_neg]
    intro h
    exact hne (fr_injective X.F hV j h).symm
  · intro h; exact absurd (Finset.mem_univ _) h

end Congr

theorem restMon_of (C₀ : ℝ) (h61 : BetaRatioBound C₀) (h21 : TauDegreeOnPathBound) (h63 : ResidueClassCount) : RestMon C₀ := by
  intro p n' r K _ _ _ X hX hLa hk j b hA hfin ρ
  classical
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hY : (1 : ℝ) ≤ X.Y := hX.Y1
  have hrhs : (0 : ℝ) ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
      (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
        (Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rcases le_or_gt (1 - (r : ℝ) / (2 * X.Y)) 0 with hneg | hpos
  · rw [max_eq_left hneg, mul_zero, zero_pow hr.ne', mul_zero]
    exact hrhs
  rw [max_eq_right hpos.le]
  set be := X.beS p K j (X.restr j b) with hbe
  set Q := X.Qc p K j with hQ
  have hQpos : 0 < Q := by
    rw [hQ]; unfold Dat.Qc
    exact pow_pos hX.prime.pos _
  have hbeQ : 4 * X.Y * (be : ℝ) ≤ (Q : ℝ) := h61 p n' r K X hX hLa hk j b hA
  have hbeQ' : 4 * be ≤ Q := by
    have : (4 : ℝ) * (be : ℝ) ≤ (Q : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) be]
    exact_mod_cast this
  obtain ⟨T, hT⟩ : ∃ T, Q = T + 2 * be := ⟨Q - 2 * be, by omega⟩
  have hTpos : 0 < T := by omega
  have hrN := k_r_le_segN X.F hV hr j
  let idxT : Fin r → Fin (segN X.F j) := fun i' => ⟨segN X.F j - r + i'.val, by have := i'.isLt; omega⟩
  have hidx : ∀ i', segE X.F j (idxT i') = X.F.fr j i'.val := fun i' =>
    (segE_eq_fr_iff X.F hV j _ i'.isLt).mpr rfl
  have := Fintype.ofFinite (X.Tset p K j (X.restr j b))
  let ddOf : X.Tset p K j (X.restr j b) → Fin (segN X.F j) → ℕ := fun τ => Classical.choose τ.2
  have hdd : ∀ τ : X.Tset p K j (X.restr j b), X.IsPATH p K j (X.restr j b) τ.1.1 (ddOf τ) ∧
      X.IsGood p K j (X.restr j b) τ.1.1 ∧ IsSt (tanPart τ.1.1) τ.1.2 := fun τ => Classical.choose_spec τ.2
  let dtau : X.Tset p K j (X.restr j b) → Fin r → ℕ := fun τ i' => ddOf τ (idxT i')
  have hdtau : ∀ τ i', dtau τ i' ≤ 2 * be := by
    intro τ i'
    refine h21 p n' r K X hX j _ _ _ (hdd τ).1 (idxT i') ?_
    rw [hidx]
    exact kfr_le X.F hV j (Nat.zero_le _) i'.isLt
  let Wfin : Finset (Fin r → ℕ) := Fintype.piFinset fun _ : Fin r => Finset.range T
  let Ufin : Finset (Fin r × Fin r → ℕ) := Fintype.piFinset fun _ : Fin r × Fin r => Finset.range T
  let φ : X.Tset p K j (X.restr j b) × (Fin r × Fin r → ℕ) → Fin r → ℕ := fun x i' =>
    dtau x.1 i' + ∑ c, x.2 (i', c)
  let A : Finset (X.Tset p K j (X.restr j b) × (Fin r × Fin r → ℕ)) :=
    ((Finset.univ : Finset (X.Tset p K j (X.restr j b))) ×ˢ Ufin).filter fun x => ∀ i', φ x i' % Q = ρ i' % Q
  set E := Fintype.piFinset fun i : Fin r => (Finset.range (r * Q)).filter fun e => e % Q = ρ i % Q with hE
  set cst : ℝ := (Q : ℝ) ^ (r - 1) * (1 - (r : ℝ) / (2 * X.Y)) with hcst
  have hcst0 : 0 ≤ cst := by positivity

  have hφE : ∀ x ∈ A, φ x ∈ E := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    have hu := (Finset.mem_product.mp hx1).2
    rw [Fintype.mem_piFinset] at hu
    rw [hE, Fintype.mem_piFinset]
    intro i'
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hx2 i'⟩
    have h1 : ∑ c, x.2 (i', c) ≤ r * (T - 1) := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin r)) (fun c => x.2 (i', c)) (T - 1) (by
        intro c _
        have := Finset.mem_range.mp (hu (i', c))
        omega)
      simpa using this
    have h2 := hdtau x.1 i'
    have h3 : r * (T - 1) + r = r * T := by
      obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have h4 : 2 * be ≤ r * (2 * be) := Nat.le_mul_of_pos_left _ hr
    have h5 : r * Q = r * T + r * (2 * be) := by rw [hT]; ring
    show dtau x.1 i' + ∑ c, x.2 (i', c) < r * Q
    omega

  have hfib : ∀ e ∈ E, (A.filter fun x => φ x = e).card ≤ Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) := by
    intro e _
    have hlow := restr_setTau_low X j b e
    have hbe' : X.beS p K j (X.restr j (X.setTau j b e)) = be := (beS_congr X p K j hlow).symm
    have hfinI : Finite (X.Idx p K j (X.restr j (X.setTau j b e))) := by
      let g : X.Idx p K j (X.restr j (X.setTau j b e)) →
          X.Tset p K j (X.restr j b) × (Fin r × Fin r → Fin Q) := fun q =>
        (⟨(q.1.1, q.1.2.1), by
          obtain ⟨dd, h1, h2, h3, -⟩ := q.2
          exact ⟨dd, IsPATH_congr X p K j (fun x hx => (hlow x hx).symm) h1,
            IsGood_congr X p K hX j (fun x hx => (hlow x hx).symm) h2, h3⟩⟩,
          fun v => ⟨q.1.2.2 v, by
            obtain ⟨dd, -, -, -, h4, -⟩ := q.2
            have := h4 v
            omega⟩)
      refine Finite.of_injective g ?_
      intro q q' hqq
      have h1 : q.1.1 = q'.1.1 := congrArg (fun z => z.1.1.1) hqq
      have h2 : q.1.2.1 = q'.1.2.1 := congrArg (fun z => z.1.1.2) hqq
      refine Subtype.ext (Prod.ext h1 (Prod.ext h2 ?_))
      funext v
      exact congrArg (fun z => (z.2 v).val) hqq
    let g : {x // x ∈ A.filter fun x => φ x = e} → X.Idx p K j (X.restr j (X.setTau j b e)) := fun x =>
      ⟨(x.1.1.1.1, x.1.1.1.2, x.1.2), by
        obtain ⟨hxA, hxe⟩ := Finset.mem_filter.mp x.2
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hxA
        have hu := (Finset.mem_product.mp hx1).2
        rw [Fintype.mem_piFinset] at hu
        refine ⟨ddOf x.1.1, IsPATH_congr X p K j hlow (hdd x.1.1).1, IsGood_congr X p K hX j hlow (hdd x.1.1).2.1,
          (hdd x.1.1).2.2, ?_, ?_⟩
        · intro v
          rw [hbe']
          have := Finset.mem_range.mp (hu v)
          show x.1.2 v + 2 * be < Q
          omega
        · intro i i' hi
          have hii : i = idxT i' := (segE_strictMono X.F j).injective (hi.trans (hidx i').symm)
          rw [restr_setTau_tau X p K hX j b e i', hii]
          exact congrFun hxe i'⟩
    have hg : Function.Injective g := by
      intro x x' hxx
      have h1 : x.1.1.1.1 = x'.1.1.1.1 := congrArg (fun z => z.1.1) hxx
      have h2 : x.1.1.1.2 = x'.1.1.1.2 := congrArg (fun z => z.1.2.1) hxx
      have h3 : x.1.2 = x'.1.2 := congrArg (fun z => z.1.2.2) hxx
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h1 h2)) h3)
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

  have hcount : ∀ τ : X.Tset p K j (X.restr j b), cst ^ r ≤ ((A.filter fun x => x.1 = τ).card : ℝ) := by
    intro τ
    have h1 : ∀ i' : Fin r, cst ≤ ((Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card : ℝ) := by
      intro i'
      have h63' := h63 r Q be (dtau τ i') (ρ i') hX.r2 (by omega)
      rw [show Q - 2 * be = T by omega] at h63'
      refine le_trans ?_ h63'
      rw [hcst]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
      have hYp : (0 : ℝ) < X.Y := by linarith
      have : 2 * (r : ℝ) * (be : ℝ) / Q ≤ (r : ℝ) / (2 * X.Y) := by
        rw [div_le_div_iff₀ hQr (by positivity)]
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
        nlinarith
      linarith
    have h2 : (Fintype.piFinset fun i' : Fin r =>
        Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card ≤ (A.filter fun x => x.1 = τ).card := by
      refine Finset.card_le_card_of_injOn (fun w => (τ, fun v : Fin r × Fin r => w v.1 v.2)) ?_ ?_
      · intro w hw
        have hw' := Fintype.mem_piFinset.mp (Finset.mem_coe.mp hw)
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun v => ?_⟩, fun i' => ?_⟩, rfl⟩)
        · exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (hw' v.1)).1 v.2
        · exact (Finset.mem_filter.mp (hw' i')).2
      · intro w _ w' _ hww
        simp only [Prod.mk.injEq, true_and] at hww
        funext a c
        exact congrFun hww (a, c)
    rw [Fintype.card_piFinset] at h2
    have h3 : cst ^ r ≤ ∏ i' : Fin r, ((Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card : ℝ) := by
      have : cst ^ r = ∏ _i' : Fin r, cst := by simp
      rw [this]
      exact Finset.prod_le_prod (fun _ _ => hcst0) fun i' _ => h1 i'
    refine le_trans h3 ?_
    exact_mod_cast h2
  have hA1 : A.card = ∑ τ : X.Tset p K j (X.restr j b), (A.filter fun x => x.1 = τ).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hA2 : A.card = ∑ e ∈ E, (A.filter fun x => φ x = e).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx => Finset.mem_coe.mpr (hφE x (Finset.mem_coe.mp hx))
  have hstep1 : (Nat.card (X.Tset p K j (X.restr j b)) : ℝ) * cst ^ r ≤ (A.card : ℝ) := by
    rw [hA1, Nat.card_eq_fintype_card]
    push_cast
    have : (Fintype.card (X.Tset p K j (X.restr j b)) : ℝ) * cst ^ r =
        ∑ _τ : X.Tset p K j (X.restr j b), cst ^ r := by
      simp
    rw [this]
    exact Finset.sum_le_sum fun τ _ => hcount τ
  refine le_trans hstep1 ?_
  rw [hA2]
  push_cast
  exact Finset.sum_le_sum fun e he => by exact_mod_cast hfib e he

end Formalism.MainNotions.SelectionLemmas.Pf
