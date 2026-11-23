import Formalism.LocalToGlobal.ProjectiveLattices.GenSectA

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial Cardinal

open MvPolynomial in
theorem exists_pderiv_ne_zero_lt' {K : Type*} [Field K] [CharZero K] {ι : Type*}
    (P : MvPolynomial ι K) (hP : 0 < P.totalDegree) :
    ∃ i, pderiv i P ≠ 0 ∧ (pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨s, hs, hsd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.2 hP0)
    (fun s : ι →₀ ℕ => s.sum fun _ e => e)
  have htd : P.totalDegree = s.sum fun _ e => e := hsd
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [htd] at hP
    simp at hP
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hs0 (Finsupp.ext h)
  have hdeg : ∀ t : ι →₀ ℕ, t i ≠ 0 →
      (t.sum fun _ e => e) = ((t - Finsupp.single i 1).sum fun _ e => e) + 1 := by
    intro t ht
    have hle : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 ht)
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hder : pderiv i P =
      ∑ t ∈ P.support, monomial (t - Finsupp.single i 1) (coeff t P * (t i : K)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pderiv_monomial]
  refine ⟨i, ?_, ?_⟩
  · intro h0
    have hc := congrArg (coeff (s - Finsupp.single i 1)) h0
    rw [hder, coeff_sum, coeff_zero, Finset.sum_eq_single s] at hc
    · rw [coeff_monomial, if_pos rfl] at hc
      exact mul_ne_zero (mem_support_iff.1 hs) (by exact_mod_cast hi) hc
    · intro t _ hts
      rw [coeff_monomial]
      split_ifs with heq
      · by_cases hti : t i = 0
        · simp [hti]
        · exfalso
          apply hts
          have h1 : Finsupp.single i 1 ≤ t := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hti)
          have h2 : Finsupp.single i 1 ≤ s := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
          rw [← tsub_add_cancel_of_le h1, ← tsub_add_cancel_of_le h2, heq]
      · rfl
    · intro hns
      exact absurd hs hns
  · have hpos : (⊥ : ℕ) < s.sum fun _ e => e := by
      rw [← htd]
      exact hP
    rw [htd, hder]
    refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ((Finset.sup_lt_iff hpos).2 fun t ht => ?_)
    by_cases hti : t i = 0
    · simpa [hti, htd] using hP
    · refine lt_of_le_of_lt (totalDegree_monomial_le _ _) ?_
      have h1 := hdeg t hti
      have h2 : (t.sum fun _ e => e) ≤ s.sum fun _ e => e := by
        rw [← htd]
        exact le_totalDegree ht
      rw [h1] at h2
      exact h2

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem card_Z (j₀ : Fin m) : Fintype.card {p : Fin (D + 1) × Fin m // Zs j₀ p} = D := by
  let e : {p : Fin (D + 1) × Fin m // Zs j₀ p} ≃ {i : Fin (D + 1) // i ≠ 0} :=
    { toFun := fun q => ⟨q.1.1, (q.2 : q.1.1 ≠ 0 ∧ q.1.2 = j₀).1⟩
      invFun := fun i => ⟨(i.1, j₀), (⟨i.2, rfl⟩ : i.1 ≠ 0 ∧ j₀ = j₀)⟩
      left_inv := fun q => by
        obtain ⟨⟨a, b⟩, h⟩ := q
        have hb : b = j₀ := (h : a ≠ 0 ∧ b = j₀).2
        subst hb
        rfl
      right_inv := fun i => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  simp

theorem trdeg_CT (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D) :
    Algebra.trdeg K (CT Ω D j₀) = (Fintype.card (Fin (D + 1) × Fin m) : Cardinal) := by
  classical
  have hle : D ≤ Fintype.card (Fin (D + 1) × Fin m) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have := j₀.pos
    nlinarith
  rw [← trdeg_add_eq (R := K) (S := Ω) (A := CT Ω D j₀), htr,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype,
    Fintype.card_subtype_compl, card_Z, ← Nat.cast_add, Nat.add_sub_of_le hle]

theorem isAlgebraic_map_adjoin {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (hφ : Function.Injective φ) (s : Set A) {a : A}
    (h : IsAlgebraic (Algebra.adjoin R s) a) : IsAlgebraic (Algebra.adjoin R (φ '' s)) (φ a) := by
  have hmem : ∀ y : Algebra.adjoin R s, φ y ∈ Algebra.adjoin R (φ '' s) := by
    intro y
    rw [← AlgHom.map_adjoin]
    exact Subalgebra.mem_map.2 ⟨y, y.2, rfl⟩
  let f : Algebra.adjoin R s →+* Algebra.adjoin R (φ '' s) :=
    { toFun := fun y => ⟨φ y, hmem y⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hf : Function.Injective f := fun y z hyz => Subtype.ext (hφ (congrArg Subtype.val hyz))
  exact h.ringHom_of_comp_eq (f := f) (g := φ.toRingHom) hf (RingHom.ext fun y => rfl)

theorem alg_CT (x : Fin m → Ω) (j₀ : Fin m)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω)
    (hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT Ω D j₀)) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀) := by
  have hC : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C ω : CT Ω D j₀) := by
    intro ω
    have h1 := isAlgebraic_map_adjoin (IsScalarTower.toAlgHom K Ω (CT Ω D j₀)) (C_injective _ _) _
      (halg ω)
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h1
    rintro _ ⟨⟨_, ⟨k, rfl⟩, rfl⟩, -⟩
    exact hr k
  constructor
  intro c
  have hc : c ∈ Algebra.adjoin K (Set.range (X : _ → CT Ω D j₀) ∪ Set.range (C : Ω → CT Ω D j₀)) := by
    induction c using MvPolynomial.induction_on with
    | C a => exact Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
    | add p r hp hr => exact add_mem hp hr
    | mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨n, rfl⟩))
  have h0 : IsAlgebraic (Algebra.adjoin K (Set.range (X : _ → CT Ω D j₀) ∪
      Set.range (C : Ω → CT Ω D j₀))) c :=
    isAlgebraic_algebraMap (⟨c, hc⟩ : Algebra.adjoin K _)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic ?_ h0
  rintro y ⟨hy | ⟨ω, rfl⟩, -⟩
  · obtain ⟨q, rfl⟩ := hy
    have hq : (X q : CT Ω D j₀) ∈ Algebra.adjoin K (Set.range (gs (D := D) x j₀)) :=
      Algebra.subset_adjoin ⟨q.1, by rw [gs, if_neg q.2, xv_of_not q.2]⟩
    exact isAlgebraic_algebraMap (⟨X q, hq⟩ : Algebra.adjoin K _)
  · exact hC ω

theorem gs_indep [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    AlgebraicIndependent K (gs (D := D) x j₀) := by
  classical
  by_contra hdep
  have hex : ∃ n, ∃ G : MvPolynomial (Fin (D + 1) × Fin m) K, aeval (gs x j₀) G = 0 ∧ G ≠ 0 ∧
      G.totalDegree = n := by
    rw [algebraicIndependent_iff] at hdep
    push Not at hdep
    obtain ⟨G, h1, h2⟩ := hdep
    exact ⟨_, G, h1, h2, rfl⟩
  obtain ⟨G, hG0, hGne, hGdeg⟩ := Nat.find_spec hex
  have hmin : ∀ H : MvPolynomial (Fin (D + 1) × Fin m) K, H.totalDegree < G.totalDegree →
      aeval (gs x j₀) H = 0 → H = 0 := by
    intro H hH h0
    by_contra hne
    rw [hGdeg] at hH
    exact Nat.find_min hex hH ⟨H, h0, hne, rfl⟩
  have hd : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) = 0 := by
    intro q; rw [← pderiv_aeval, hG0, map_zero]
  have hsum : ∀ q : {p : Fin (D + 1) × Fin m // ¬ Zs j₀ p},
      ∑ p, aeval (gs x j₀) (pderiv p G) * pderiv q (gs x j₀ p) =
        aeval (gs x j₀) (pderiv q.1 G) -
          if q.1.1 = 0 then 0 else aeval (gs x j₀) (pderiv (q.1.1, j₀) G) * C (rr x j₀ q.1.2) := by
    intro q
    simp_rw [pderiv_gs, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    split_ifs with h0
    · exact Finset.sum_eq_zero fun p _ =>
        if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => e.1.1 (e.2.trans h0))
    · rw [Finset.sum_eq_single (q.1.1, j₀)]
      · exact if_pos (show Zs j₀ (q.1.1, j₀) ∧ (q.1.1, j₀).1 = q.1.1 from ⟨⟨h0, rfl⟩, rfl⟩)
      · intro p _ hp
        exact if_neg (show ¬ (Zs j₀ p ∧ p.1 = q.1.1) from fun e => hp (Prod.ext_iff.mpr ⟨e.2, e.1.2⟩))
      · intro h; exact absurd (Finset.mem_univ _) h
  have hpos : 0 < G.totalDegree := by
    by_contra h
    have h0 : G.totalDegree = 0 := by omega
    rw [totalDegree_eq_zero_iff_eq_C] at h0
    rw [h0, aeval_C] at hG0
    have hc : coeff 0 G = 0 :=
      (algebraMap K (CT Ω D j₀)).injective (by rw [hG0, map_zero])
    exact hGne (by rw [h0, hc, C_0])
  obtain ⟨p₁, hp₁ne, hp₁lt⟩ := exists_pderiv_ne_zero_lt' G hpos
  have hp₁ : aeval (gs x j₀) (pderiv p₁ G) ≠ 0 := fun h => hp₁ne (hmin _ hp₁lt h)
  have hexi : ∃ i : Fin D, aeval (gs x j₀) (pderiv (i.succ, j₀) G) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hp₁
    by_cases hZ : Zs j₀ p₁
    · obtain ⟨h1, h2⟩ := hZ
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h1
      have e : p₁ = (i.succ, j₀) := Prod.ext_iff.mpr ⟨hi.symm, h2⟩
      rw [e]; exact hall i
    · have h := hd ⟨p₁, hZ⟩
      rw [hsum] at h
      split_ifs at h with h0
      · rwa [sub_zero] at h
      · obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr h0
        simp only at h hi
        rw [← hi, hall i, zero_mul, sub_zero] at h
        exact h
  obtain ⟨i, hi⟩ := hexi
  have hr : ∀ k, IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀)))
      (C (rr x j₀ k) : CT Ω D j₀) := by
    intro k
    by_cases hk : k = j₀
    · subst hk
      rw [rr, div_self hx₀, C_1]
      exact isAlgebraic_one
    · have hq : ¬ Zs j₀ (i.succ, k) := fun h => hk h.2
      have h := hd ⟨(i.succ, k), hq⟩
      rw [hsum, if_neg (Fin.succ_ne_zero i), sub_eq_zero] at h
      have m1 : aeval (gs x j₀) (pderiv (i.succ, j₀) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      have m2 : aeval (gs x j₀) (pderiv (i.succ, k) G) ∈ Algebra.adjoin K (Set.range (gs x j₀)) := by
        rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨_, rfl⟩
      refine ⟨Polynomial.C ⟨_, m1⟩ * Polynomial.X - Polynomial.C ⟨_, m2⟩, ?_, ?_⟩
      · intro h0
        have h1 := congrArg (fun f => Polynomial.coeff f 1) h0
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
          Polynomial.coeff_zero, if_pos, one_ne_zero, if_false, sub_zero] at h1
        exact hi (congrArg Subtype.val h1)
      · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
        exact sub_eq_zero.mpr h.symm
  have := alg_CT x j₀ halg hr
  have htb : IsTranscendenceBasis K (gs (D := D) x j₀) :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K (gs x j₀)
      (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])
  exact hdep htb.1

theorem gs_alg [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀) :=
  ((gs_indep x j₀ hx₀ htr halg).isTranscendenceBasis_of_trdeg_le_of_finite
    (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])).isAlgebraic

theorem halg_of (x : Fin m → Ω) (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω := by
  intro ω
  have hadd := trdeg_add_eq (R := K)
    (S := IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) (A := Ω)
  rw [hbig, htr] at hadd
  have h0 : Algebra.trdeg (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω = 0 := by
    rcases (Cardinal.add_eq_left_iff).mp hadd with h | h
    · exact absurd ((le_max_left _ _).trans h) (not_le.mpr ((Cardinal.natCast_lt_aleph0 (n := D))))
    · exact h
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) Ω := by
    first
    | exact Algebra.trdeg_eq_zero_iff.mp h0
    | exact trdeg_eq_zero_iff.mp h0
  exact IntermediateField.isAlgebraic_adjoin_iff.mp (halg.isAlgebraic ω)

end Formalism.L2.Pj.GenSect
