import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.FormalDegreeBessel.FinalG

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

namespace C2x2

variable {m : ℕ}

lemma ut_bt {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.BlockTriangular id :=
  fun i j h => hu.1 i j h

lemma lt_bt {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.BlockTriangular OrderDual.toDual :=
  fun i j h => hl.1 i j (OrderDual.toDual_lt_toDual.mp h)

lemma bt_mul_diag {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M N : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (i : Fin m) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne (hb.ne hk) with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp

lemma bt_inv_facts {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hd : ∀ i, M i i = 1) (hu : IsUnit M.det) :
    M⁻¹.BlockTriangular b ∧ ∀ i, M⁻¹ i i = 1 := by
  haveI := M.invertibleOfIsUnitDet hu
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨hi, fun i => ?_⟩
  have := congrFun (congrFun (Matrix.mul_nonsing_inv M hu) i) i
  rw [bt_mul_diag hb hM hi, hd, one_mul, Matrix.one_apply_eq] at this
  exact this

lemma ut_det {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (ut_bt hu)]
  simp [hu.2]

lemma lt_det {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (lt_bt hl)]
  simp [hl.2]

lemma ut_unit {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : IsUnit u.det := by
  rw [ut_det hu]; exact isUnit_one

lemma lt_unit {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : IsUnit l.det := by
  rw [lt_det hl]; exact isUnit_one

lemma ut_inv {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : u⁻¹ ∈ C2.UTset m := by
  obtain ⟨h1, h2⟩ := bt_inv_facts Function.injective_id (ut_bt hu) hu.2 (ut_unit hu)
  exact ⟨fun i j h => h1 h, h2⟩

lemma lt_inv {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : l⁻¹ ∈ C2.LTset m := by
  obtain ⟨h1, h2⟩ := bt_inv_facts OrderDual.toDual.injective (lt_bt hl) hl.2 (lt_unit hl)
  exact ⟨fun i j h => h1 (OrderDual.toDual_lt_toDual.mpr h), h2⟩

lemma ut_mul {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (hv : v ∈ C2.UTset m) :
    u * v ∈ C2.UTset m :=
  ⟨fun i j h => ((ut_bt hu).mul (ut_bt hv)) h,
   fun i => by rw [bt_mul_diag Function.injective_id (ut_bt hu) (ut_bt hv), hu.2, hv.2, one_mul]⟩

lemma lt_mul {u v : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.LTset m) (hv : v ∈ C2.LTset m) :
    u * v ∈ C2.LTset m :=
  ⟨fun i j h => ((lt_bt hu).mul (lt_bt hv)) (OrderDual.toDual_lt_toDual.mpr h),
   fun i => by rw [bt_mul_diag OrderDual.toDual.injective (lt_bt hu) (lt_bt hv), hu.2, hv.2, one_mul]⟩

lemma ut_conjT {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : uᴴ ∈ C2.LTset m :=
  ⟨fun i j h => by rw [Matrix.conjTranspose_apply, hu.1 j i h, star_zero],
   fun i => by rw [Matrix.conjTranspose_apply, hu.2, star_one]⟩

lemma lt_conjT {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ C2.LTset m) : lᴴ ∈ C2.UTset m :=
  ⟨fun i j h => by rw [Matrix.conjTranspose_apply, hl.1 j i h, star_zero],
   fun i => by rw [Matrix.conjTranspose_apply, hl.2, star_one]⟩

lemma ut_inv_super {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) (a : Fin m) (h : a.val + 1 < m) :
    u⁻¹ a ⟨a.val + 1, h⟩ = -u a ⟨a.val + 1, h⟩ := by
  have hi := ut_inv hu
  have hne : a ≠ ⟨a.val + 1, h⟩ := fun e => by have := congrArg Fin.val e; simp at this
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv u (ut_unit hu)) a) ⟨a.val + 1, h⟩
  rw [Matrix.mul_apply, Matrix.one_apply_ne hne, Fintype.sum_eq_add a ⟨a.val + 1, h⟩ hne] at e
  · rw [hu.2, hi.2, one_mul, mul_one] at e
    linear_combination e
  · intro k ⟨hk1, hk2⟩
    rcases lt_or_gt_of_ne hk1 with hl | hl
    · rw [hu.1 a k hl, zero_mul]
    · have : (⟨a.val + 1, h⟩ : Fin m) < k := by
        rw [Fin.lt_def] at hl ⊢
        have : k.val ≠ a.val + 1 := fun e => hk2 (Fin.ext e)
        simp only; omega
      rw [hi.1 k _ this, mul_zero]

lemma monomialMatrix_inv_left (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) * C2.monoP w d = 1 := by
  ext i j
  simp only [C2.monoP, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (w j)]
  · by_cases hij : i = j
    · subst hij; simp [hd i]
    · rw [if_neg (by simpa using hij), zero_mul, Matrix.one_apply_ne hij]
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp

lemma isUnit_det_monomialMatrix (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) : IsUnit (C2.monoP w d).det :=
  Matrix.isUnit_det_of_left_inverse (monomialMatrix_inv_left w d hd)

lemma monomialMatrix_inv (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    (C2.monoP w d)⁻¹ = C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) :=
  Matrix.inv_eq_left_inv (monomialMatrix_inv_left w d hd)

lemma monomialMatrix_conj_apply (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    ((C2.monoP w d)⁻¹ * l * C2.monoP w d) a b = (d a)⁻¹ * l (w a) (w b) * d b := by
  rw [monomialMatrix_inv w d hd]
  simp only [Matrix.mul_apply, C2.monoP, Matrix.of_apply]
  rw [Finset.sum_eq_single (w b)]
  · rw [if_pos rfl, Finset.sum_eq_single (w a)]
    · simp
    · intro k _ hk
      rw [if_neg (fun e => hk (by rw [e]; simp)), zero_mul]
    · simp
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp

lemma isMonomial_unit {P : Matrix (Fin m) (Fin m) ℂ} (hP : C2.IsMonomial P) : IsUnit P.det := by
  obtain ⟨w, d, hd, rfl⟩ := hP
  exact isUnit_det_monomialMatrix w d hd

end C2x2

open C2x2

theorem inverse_star_substitution : C2.InvStarSub := by
  intro m u hu a h
  rw [Matrix.conjTranspose_apply, ut_inv_super hu a h]
  simp

lemma c2x2_antiW_mul {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    (C2.antiW s * M) i j = M i.rev j := by
  simp only [C2.antiW, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single i.rev]
  · simp
  · intro k _ hk; rw [if_neg hk, zero_mul]
  · simp

lemma c2x2_mul_antiW {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (i j : Fin s) :
    (M * C2.antiW s) i j = M i j.rev := by
  simp only [C2.antiW, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro e; apply hk; rw [e, Fin.rev_rev]
  · simp

lemma c2x2_antiW_sq (s : ℕ) : C2.antiW s * C2.antiW s = 1 := by
  ext i j
  rw [c2x2_antiW_mul]
  simp only [C2.antiW, Matrix.of_apply, Fin.rev_rev, Matrix.one_apply]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg (fun e => h e.symm), if_neg h]

lemma c2x2_simpleLow_succ {n : ℕ} (l : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    C2.simpleLow l = ∑ a : Fin n, l a.succ a.castSucc := by
  unfold C2.simpleLow
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [dif_pos (by have := a.isLt; simp only [Fin.coe_castSucc]; omega)]
  rfl

lemma c2x2_simpleUp_succ {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    C2.simpleUp u = ∑ a : Fin n, u a.castSucc a.succ := by
  unfold C2.simpleUp
  rw [Fin.sum_univ_castSucc, dif_neg (by simp), add_zero]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [dif_pos (by have := a.isLt; simp only [Fin.coe_castSucc]; omega)]
  rfl

theorem stabilizer_antidiagonal : C2.StabAntidiag := by
  intro s u t hu ht
  have hi := ut_inv hu
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, ?_⟩
  · rw [c2x2_mul_antiW, c2x2_antiW_mul]
    exact hi.1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [c2x2_mul_antiW, c2x2_antiW_mul]
    exact hi.2 _
  · calc C2.antiW s * u⁻¹ * C2.antiW s * (t • C2.antiW s) * u
        = t • (C2.antiW s * u⁻¹ * (C2.antiW s * C2.antiW s) * u) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = t • C2.antiW s := by
          rw [c2x2_antiW_sq, Matrix.mul_one, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (ut_unit hu),
            Matrix.mul_one]
  · rcases s with _ | n
    · simp [C2.simpleLow, C2.simpleUp]
    · rw [c2x2_simpleLow_succ, c2x2_simpleUp_succ]
      have e1 : ∀ a : Fin n, (C2.antiW (n + 1) * u⁻¹ * C2.antiW (n + 1)) a.succ a.castSucc =
          -u a.rev.castSucc a.rev.succ := by
        intro a
        rw [c2x2_mul_antiW, c2x2_antiW_mul, Fin.rev_succ, Fin.rev_castSucc]
        have := ut_inv_super hu a.rev.castSucc (by simp only [Fin.coe_castSucc]; exact Nat.succ_lt_succ a.rev.isLt)
        exact this
      simp only [e1]
      rw [Finset.sum_neg_distrib]
      have e2 : ∑ a : Fin n, u a.rev.castSucc a.rev.succ = ∑ a : Fin n, u a.castSucc a.succ :=
        Equiv.sum_comp Fin.revPerm (fun a => u a.castSucc a.succ)
      rw [e2]; ring

theorem unipotent_radical_image : C2.URImage := by
  intro m P hP
  have hPu := isMonomial_unit hP
  ext u
  simp only [Set.mem_setOf_eq, C2.Lstg]
  constructor
  · rintro ⟨hu, u', hu', he⟩
    refine ⟨hu, ut_conjT hu, ?_⟩
    have : P⁻¹ * uᴴ * P = u'⁻¹ := by
      calc P⁻¹ * uᴴ * P = P⁻¹ * uᴴ * P * (u' * u'⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ (ut_unit hu'), Matrix.mul_one]
        _ = P⁻¹ * (uᴴ * P * u') * u'⁻¹ := by simp only [Matrix.mul_assoc]
        _ = u'⁻¹ := by rw [he, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mul]
    rw [this]; exact ut_inv hu'
  · rintro ⟨hu, _, hX⟩
    refine ⟨hu, (P⁻¹ * uᴴ * P)⁻¹, ut_inv hX, ?_⟩
    have e : uᴴ * P = P * (P⁻¹ * uᴴ * P) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [e, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (ut_unit hX), Matrix.mul_one]

theorem upper_splitting_of_lower : C2.UpSplitOfLowSplit := by
  intro hLow m P hP u hu
  obtain ⟨p, ⟨hp1, hp2, hpe⟩, huniq⟩ := hLow m P hP uᴴ (ut_conjT hu)
  refine ⟨(p.2ᴴ, p.1ᴴ), ⟨lt_conjT hp2.1, lt_conjT hp1.1, ?_, ?_, ?_⟩, ?_⟩
  · simpa using hp2
  · simpa using hp1
  · simp only
    rw [← Matrix.conjTranspose_mul, ← hpe, Matrix.conjTranspose_conjTranspose]
  · rintro q ⟨_, _, hq1, hq2, hqe⟩
    have := huniq (q.2ᴴ, q.1ᴴ) ⟨hq2, hq1, by
      simp only
      rw [← Matrix.conjTranspose_mul, ← hqe]⟩
    rw [Prod.ext_iff] at this
    simp only at this
    obtain ⟨e1, e2⟩ := this
    apply Prod.ext
    · simp only; rw [← e2, Matrix.conjTranspose_conjTranspose]
    · simp only; rw [← e1, Matrix.conjTranspose_conjTranspose]

lemma c2x2_lowOf_sub {m : ℕ} (p : Fin m × Fin m → Prop) [DecidablePred p] (v : {q : Fin m × Fin m // p q} → ℂ)
    (i j : Fin m) :
    C2.lowOf (fun q : {q : Fin m × Fin m // p q} => q.1) v i j =
      (1 : Matrix (Fin m) (Fin m) ℂ) i j + if h : p (i, j) then v ⟨(i, j), h⟩ else 0 := by
  simp only [C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro e; apply hq; exact Subtype.ext e
    · simp
  · apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro e; apply h; rw [← e]; exact q.2

theorem lower_parabolic_coordinates : C2.LPCoords := by
  intro m w d hd
  have hPu := isUnit_det_monomialMatrix w d hd
  constructor
  · ext l
    simp only [Set.mem_range, C2.LPg, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩
      · rw [c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]
      · rw [c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub,
          Matrix.one_apply_ne (fun e => (ne_of_lt hab) (w.injective e)), dif_neg]
        · simp
        · intro h; simp at h; exact absurd h.2 (not_lt.mpr (le_of_lt hab))
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1)]
        simp [hd a]
    · rintro ⟨hl, hc⟩
      refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
      ext i j
      rw [c2x2_lowOf_sub]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))),
          hl.1 i j hij, add_zero]
      · rw [Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), hl.2, add_zero]
      · rw [Matrix.one_apply_ne (ne_of_gt hij), zero_add]
        split_ifs with h
        · rfl
        · have hlt : w.symm i < w.symm j := by
            have hne : w.symm i ≠ w.symm j := fun e => (ne_of_gt hij) (w.symm.injective e)
            rcases lt_or_gt_of_ne hne with h' | h'
            · exact h'
            · exact absurd ⟨hij, h'⟩ h
          have := hc.1 _ _ hlt
          rw [monomialMatrix_conj_apply w d hd] at this
          simp only [Equiv.apply_symm_apply] at this
          have hdi := hd (w.symm i)
          have hdj := hd (w.symm j)
          rcases mul_eq_zero.mp this with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero hdi)
            · exact h2.symm
          · exact absurd h1 hdj
  · ext l
    simp only [Set.mem_range, C2.Lstg, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩
      · rw [c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]
      · rw [c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub,
          Matrix.one_apply_ne (fun e => (ne_of_gt hab) (w.injective e)), dif_neg]
        · simp
        · intro h; simp at h; exact absurd h.2 (not_lt.mpr (le_of_lt hab))
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1)]
        simp [hd a]
    · rintro ⟨hl, hc⟩
      refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
      ext i j
      rw [c2x2_lowOf_sub]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))),
          hl.1 i j hij, add_zero]
      · rw [Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), hl.2, add_zero]
      · rw [Matrix.one_apply_ne (ne_of_gt hij), zero_add]
        split_ifs with h
        · rfl
        · have hlt : w.symm j < w.symm i := by
            have hne : w.symm i ≠ w.symm j := fun e => (ne_of_gt hij) (w.symm.injective e)
            rcases lt_or_gt_of_ne hne with h' | h'
            · exact absurd ⟨hij, h'⟩ h
            · exact h'
          have := hc.1 _ _ hlt
          rw [monomialMatrix_conj_apply w d hd] at this
          simp only [Equiv.apply_symm_apply] at this
          have hdi := hd (w.symm i)
          have hdj := hd (w.symm j)
          rcases mul_eq_zero.mp this with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero hdi)
            · exact h2.symm
          · exact absurd h1 hdj

end Formalism.FourierDecayAlt.P
