import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IwahoriEntryBound
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow.Triang

section Basic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_eq_ord {x : L} (hx : x ≠ 0) : Valued.v x =
    ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dif_neg h]
  simp

theorem ord_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have h := v_eq_ord (mul_ne_zero hx hy)
  rw [map_mul, v_eq_ord hx, v_eq_ord hy, ← WithZero.coe_mul, ← ofAdd_add] at h
  have := Multiplicative.ofAdd.injective (WithZero.coe_injective h)
  omega

theorem ord_prod {ι : Type} (s : Finset ι) (c : ι → L) (h : ∀ x ∈ s, c x ≠ 0) :
    ordL (∏ x ∈ s, c x) = ∑ x ∈ s, ordL (c x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    have := v_eq_ord (one_ne_zero : (1 : L) ≠ 0)
    rw [map_one] at this
    have h2 : (1 : Multiplicative ℤ) = Multiplicative.ofAdd (-ordL (1 : L)) := WithZero.coe_injective this
    have h3 : (0 : ℤ) = -ordL (1 : L) := Multiplicative.ofAdd.injective h2
    omega
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ord_mul (h a (by simp))
      (Finset.prod_ne_zero_iff.2 fun x hx => h x (by simp [hx])), ih fun x hx => h x (by simp [hx])]

theorem ord_nonneg {x : L} (hx : x ≠ 0) (h : Valued.v x ≤ 1) : 0 ≤ ordL x := by
  rw [v_eq_ord hx, ← WithZero.coe_one, WithZero.coe_le_coe] at h
  have : Multiplicative.ofAdd (-ordL x) ≤ Multiplicative.ofAdd (0 : ℤ) := h
  have := Multiplicative.ofAdd_le.1 this
  omega

theorem ord_eq_zero {x : L} (hx : x ≠ 0) (h : Valued.v x = 1) : ordL x = 0 := by
  rw [v_eq_ord hx, ← WithZero.coe_one] at h
  have h2 : Multiplicative.ofAdd (-ordL x) = Multiplicative.ofAdd (0 : ℤ) := WithZero.coe_injective h
  have := Multiplicative.ofAdd.injective h2
  omega

theorem v_eq_one_of_ord {x : L} (hx : x ≠ 0) (h : ordL x = 0) : Valued.v x = 1 := by
  rw [v_eq_ord hx, h]; simp

theorem prod_lt_one {ι : Type} (s : Finset ι) (c : ι → WithZero (Multiplicative ℤ)) (h : ∀ x ∈ s, c x ≤ 1)
    {x : ι} (hx : x ∈ s) (hlt : c x < 1) : ∏ y ∈ s, c y < 1 := by
  classical
  rw [← Finset.mul_prod_erase s c hx]
  exact (mul_le_of_le_one_right' (Finset.prod_le_one' fun y hy => h y (Finset.mem_of_mem_erase hy))).trans_lt hlt

theorem v_sign_smul {ι : Type} [DecidableEq ι] [Fintype ι] (s : Equiv.Perm ι) (x : L) :
    Valued.v (Equiv.Perm.sign s • x) = Valued.v x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> simp [h, Units.smul_def]

theorem perm_sum_eq {ι : Type} [Fintype ι] (s : Equiv.Perm ι) (u : ι → ℤ) (h : ∀ x, u (s x) ≤ u x) (x : ι) :
    u (s x) = u x := by
  have e : ∑ x, u (s x) = ∑ x, u x := Equiv.sum_comp s u
  exact (Finset.sum_eq_sum_iff_of_le fun i _ => h i).1 e x (Finset.mem_univ x)

end Basic

section Minor

open scoped Pointwise

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def IwEnt (M : Matrix (Fin n) (Fin n) L) : Prop :=
  (∀ i j, Valued.v (M i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (M i j) < 1

theorem iwEnt_of_mem {g : GL (Fin n) L} (hg : g ∈ IwGL L n) : IwEnt (g : Matrix (Fin n) (Fin n) L) := by
  refine ⟨fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries hg i j, fun i j hji => ?_⟩
  have h := (Subgroup.mem_iInf.1 hg) ⟨i.val, by omega⟩
  have hs : (Matrix.GeneralLinearGroup.toLin g) • latK L n i.val = latK L n i.val := h
  have he : (Pi.single j (1 : L) : Fin n → L) ∈ latK L n i.val := by
    intro k
    by_cases hk : k = j
    · subst hk
      have : k.val < i.val := hji
      simp [this]
    · have : (Pi.single j (1 : L) : Fin n → L) k = 0 := Pi.single_eq_of_ne hk _
      rw [this]
      split_ifs <;> simp
  have hm := Set.smul_mem_smul_set (a := Matrix.GeneralLinearGroup.toLin g) he
  rw [hs] at hm
  have hi := hm i
  rw [if_neg (lt_irrefl _)] at hi
  have e : ((Matrix.GeneralLinearGroup.toLin g) • (Pi.single j (1 : L) : Fin n → L)) i =
      (g : Matrix (Fin n) (Fin n) L) i j := by
    show (Matrix.mulVec (g : Matrix (Fin n) (Fin n) L) (Pi.single j (1 : L) : Fin n → L)) i = _
    simp
  rwa [e] at hi

theorem diag_of_mem {g : GL (Fin n) L} (hg : g ∈ IwGL L n) (i : Fin n) :
    Valued.v ((g : Matrix (Fin n) (Fin n) L) i i) = 1 :=
  _root_.UpperTheory.Reformulated.B.IwahoriEntryBound.main hg i

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem term_le {M : Matrix (Fin n) (Fin n) L} (hM : IwEnt M) (f h : ι → Fin n) (s : Equiv.Perm ι) :
    Valued.v (Equiv.Perm.sign s • ∏ x, M (f (s x)) (h x)) ≤ 1 := by
  rw [v_sign_smul, map_prod]
  exact Finset.prod_le_one' fun x _ => hM.1 _ _

theorem term_lt {M : Matrix (Fin n) (Fin n) L} (hM : IwEnt M) (f h : ι → Fin n) (s : Equiv.Perm ι)
    {x : ι} (hx : h x < f (s x)) : Valued.v (Equiv.Perm.sign s • ∏ x, M (f (s x)) (h x)) < 1 := by
  rw [v_sign_smul, map_prod]
  exact prod_lt_one _ _ (fun x _ => hM.1 _ _) (Finset.mem_univ x) (hM.2 _ _ hx)

theorem minor_le {M : Matrix (Fin n) (Fin n) L} (hM : IwEnt M) (f h : ι → Fin n) :
    Valued.v (M.submatrix f h).det ≤ 1 := by
  rw [Matrix.det_apply]
  exact Valuation.map_sum_le _ fun s _ => term_le hM f h s

theorem minor_diag {M : Matrix (Fin n) (Fin n) L} (hM : IwEnt M) (hd : ∀ i, Valued.v (M i i) = 1)
    {f : ι → Fin n} (hf : Function.Injective f) : Valued.v (M.submatrix f f).det = 1 := by
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm ι))]
  have h1 : Valued.v (Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ x, (M.submatrix f f) ((1 : Equiv.Perm ι) x) x) = 1 := by
    rw [v_sign_smul, map_prod]
    exact Finset.prod_eq_one fun x _ => hd _
  have h2 : Valued.v (∑ s ∈ Finset.univ.erase (1 : Equiv.Perm ι),
      Equiv.Perm.sign s • ∏ x, (M.submatrix f f) (s x) x) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero fun s hs => ?_
    have hs1 : s ≠ 1 := Finset.ne_of_mem_erase hs
    by_cases hex : ∃ x, f x < f (s x)
    · obtain ⟨x, hx⟩ := hex
      exact term_lt hM f f s hx
    · exfalso
      push_neg at hex
      apply hs1
      ext x
      have := perm_sum_eq s (fun x => ((f x).val : ℤ)) (fun x => by exact_mod_cast hex x) x
      have e : f (s x) = f x := Fin.ext (by exact_mod_cast this)
      rw [hf e]; rfl
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [h1]; exact h2), h1]

theorem minor_perm {M : Matrix (Fin n) (Fin n) L} (hM : IwEnt M) (f h : ι → Fin n)
    (h1 : Valued.v (M.submatrix f h).det = 1) : ∃ s : Equiv.Perm ι, ∀ x, f (s x) ≤ h x := by
  by_contra hcon
  push_neg at hcon
  have : Valued.v (M.submatrix f h).det < 1 := by
    rw [Matrix.det_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    obtain ⟨x, hx⟩ := hcon s
    exact term_lt hM f h s hx
  exact absurd h1 this.ne

end Minor

section Block

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

abbrev Up (n m : ℕ) : Type := {a : Fin n // m ≤ a.val}

theorem up_det {R I B T : Matrix (Fin n) (Fin n) L} {π π' : Equiv.Perm (Fin n)}
    (hB : ∀ i j, j < i → B i j = 0)
    (hg : ∀ a c, R (π a) c * T c c = ∑ x, B a x * I (π' x) c) (m : ℕ) (h : Up n m → Fin n) :
    (R.submatrix (fun a : Up n m => π a.1) h).det * ∏ x, T (h x) (h x) =
      (∏ a : Up n m, B a.1 a.1) * (I.submatrix (fun a : Up n m => π' a.1) h).det := by
  have hm : R.submatrix (fun a : Up n m => π a.1) h * Matrix.diagonal (fun x => T (h x) (h x)) =
      B.submatrix (fun a : Up n m => a.1) (fun a : Up n m => a.1) *
        I.submatrix (fun a : Up n m => π' a.1) h := by
    ext a c
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.submatrix_apply]
    rw [hg a.1 (h c), ← Finset.sum_filter_of_ne (p := fun x : Fin n => m ≤ x.val)]
    · exact Finset.sum_subtype _ (by simp) (fun x => B a.1 x * I (π' x) (h c))
    · intro x _ hx
      by_contra hlt
      apply hx
      have hxa : x < a.1 := by
        have := a.2
        rw [Fin.lt_def]; omega
      rw [hB a.1 x hxa, zero_mul]
  have hdet := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_of_upperTriangular (M := B.submatrix (fun a : Up n m => a.1) (fun a : Up n m => a.1))
      (fun i j hij => hB _ _ hij)] at hdet
  simpa using hdet

theorem key {R I B T : Matrix (Fin n) (Fin n) L} {π π' : Equiv.Perm (Fin n)}
    (hR : IwEnt R) (hRd : ∀ i, Valued.v (R i i) = 1) (hI : IwEnt I) (hId : ∀ i, Valued.v (I i i) = 1)
    (hBz : ∀ a, B a a ≠ 0) (hTz : ∀ a, T a a ≠ 0)
    (hdom : ∀ i j, i < j → ordL (T j j) < ordL (T i i))
    (hB : ∀ i j, j < i → B i j = 0)
    (hg : ∀ a c, R (π a) c * T c c = ∑ x, B a x * I (π' x) c) (m : ℕ) :
    ∑ a : Up n m, ordL (T (π' a.1) (π' a.1)) ≤ ∑ a : Up n m, ordL (T (π a.1) (π a.1)) ∧
    (∑ a : Up n m, ordL (T (π' a.1) (π' a.1)) = ∑ a : Up n m, ordL (T (π a.1) (π a.1)) →
      (∀ x : Up n m, ∃ y : Up n m, π y.1 = π' x.1) ∧
        ∑ a : Up n m, ordL (B a.1 a.1) = ∑ a : Up n m, ordL (T (π a.1) (π a.1))) := by
  have hf : Function.Injective (fun a : Up n m => π a.1) := fun a b e =>
    Subtype.ext (π.injective e)
  have hf' : Function.Injective (fun a : Up n m => π' a.1) := fun a b e =>
    Subtype.ext (π'.injective e)
  have h1 := up_det hB hg m (fun a : Up n m => π' a.1)
  have h2 := up_det hB hg m (fun a : Up n m => π a.1)
  have d1 := minor_diag hI hId hf'
  have d2 := minor_diag hR hRd hf
  have l1 := minor_le hR (fun a : Up n m => π a.1) (fun a : Up n m => π' a.1)
  have l2 := minor_le hI (fun a : Up n m => π' a.1) (fun a : Up n m => π a.1)
  set mm := (R.submatrix (fun a : Up n m => π a.1) (fun a : Up n m => π' a.1)).det with hmm
  set e := (I.submatrix (fun a : Up n m => π' a.1) (fun a : Up n m => π a.1)).det with he
  set D1 := (I.submatrix (fun a : Up n m => π' a.1) (fun a : Up n m => π' a.1)).det with hD1
  set D2 := (R.submatrix (fun a : Up n m => π a.1) (fun a : Up n m => π a.1)).det with hD2
  have nD1 : D1 ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [d1]; exact one_ne_zero)
  have nD2 : D2 ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [d2]; exact one_ne_zero)
  have nB : (∏ a : Up n m, B a.1 a.1) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hBz _
  have nP' : (∏ a : Up n m, T (π' a.1) (π' a.1)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hTz _
  have nP : (∏ a : Up n m, T (π a.1) (π a.1)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hTz _
  have nm : mm ≠ 0 := left_ne_zero_of_mul (h1 ▸ mul_ne_zero nB nD1)
  have ne : e ≠ 0 := right_ne_zero_of_mul (h2 ▸ mul_ne_zero nD2 nP)
  have o1 := congrArg ordL h1
  have o2 := congrArg ordL h2
  rw [ord_mul nm nP', ord_mul nB nD1, ord_eq_zero nD1 d1, ord_prod _ _ fun a _ => hTz _,
    ord_prod _ _ fun a _ => hBz _] at o1
  rw [ord_mul nD2 nP, ord_mul nB ne, ord_eq_zero nD2 d2, ord_prod _ _ fun a _ => hTz _,
    ord_prod _ _ fun a _ => hBz _] at o2
  have pm := ord_nonneg nm l1
  have pe := ord_nonneg ne l2
  refine ⟨by omega, fun heq => ?_⟩
  have zm : ordL mm = 0 := by omega
  have ze : ordL e = 0 := by omega
  refine ⟨?_, by omega⟩
  obtain ⟨s, hs⟩ := minor_perm hR (fun a : Up n m => π a.1) (fun a : Up n m => π' a.1)
    (v_eq_one_of_ord nm zm)
  have hle : ∀ x : Up n m, ordL (T (π' x.1) (π' x.1)) ≤ ordL (T (π (s x).1) (π (s x).1)) := fun x => by
    rcases (hs x).lt_or_eq with h | h
    · exact (hdom _ _ h).le
    · have h' : π (s x).1 = π' x.1 := h
      rw [h']
  have hsum : ∑ x : Up n m, ordL (T (π' x.1) (π' x.1)) =
      ∑ x : Up n m, ordL (T (π (s x).1) (π (s x).1)) := by
    rw [heq]
    exact (Equiv.sum_comp s (fun a : Up n m => ordL (T (π a.1) (π a.1)))).symm
  have hall := (Finset.sum_eq_sum_iff_of_le fun x _ => hle x).1 hsum
  intro x
  refine ⟨s x, ?_⟩
  rcases (hs x).lt_or_eq with h | h
  · exact absurd (hall x (Finset.mem_univ x)) (hdom _ _ h).ne
  · exact h

theorem sum_up (F : Fin n → ℤ) (m : ℕ) :
    ∑ a : Up n m, F a.1 = ∑ a ∈ Finset.univ.filter (fun a : Fin n => m ≤ a.val), F a :=
  (Finset.sum_subtype _ (by simp) F).symm

theorem sum_sum_up (F : Fin n → ℤ) :
    ∑ m ∈ Finset.range n, ∑ a : Up n m, F a.1 = ∑ a : Fin n, ((a.val : ℤ) + 1) * F a := by
  simp_rw [sum_up, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const]
  have e : (Finset.range n).filter (fun m => m ≤ a.val) = Finset.range (a.val + 1) := by
    ext x
    have := a.2
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [e]
  simp

theorem up_diff (f h : Fin n → ℤ) (H : ∀ m, m < n → ∑ a : Up n m, f a.1 = ∑ a : Up n m, h a.1) (a : Fin n) :
    f a = h a := by
  have split : ∀ F : Fin n → ℤ, ∑ x : Up n a.val, F x.1 = F a + ∑ x : Up n (a.val + 1), F x.1 := by
    intro F
    rw [sum_up, sum_up, ← Finset.sum_insert (by simp)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have top : ∀ (F : Fin n → ℤ) (m : ℕ), ¬ m < n → ∑ x : Up n m, F x.1 = 0 := by
    intro F m hm
    rw [sum_up]
    refine Finset.sum_eq_zero fun x hx => ?_
    have := x.2
    have h2 := (Finset.mem_filter.1 hx).2
    omega
  have H' : ∀ m, ∑ x : Up n m, f x.1 = ∑ x : Up n m, h x.1 := fun m => by
    by_cases hm : m < n
    · exact H m hm
    · rw [top f m hm, top h m hm]
  have a1 := split f
  have a2 := split h
  have a3 := H' a.val
  have a4 := H' (a.val + 1)
  omega

theorem perm_one_of_le (ξ : Equiv.Perm (Fin n)) (h : ∀ a, a ≤ ξ a) : ξ = 1 := by
  refine Equiv.ext fun a => Fin.ext ?_
  have h2 : -(((ξ a).val : ℕ) : ℤ) = -((a.val : ℕ) : ℤ) :=
    perm_sum_eq ξ (fun x : Fin n => -((x.val : ℕ) : ℤ)) (fun x => by
      have : x.val ≤ (ξ x).val := h x
      show -(((ξ x).val : ℕ) : ℤ) ≤ -((x.val : ℕ) : ℤ)
      omega) a
  show (ξ a).val = a.val
  omega

theorem upper_diag_ne {g : GL (Fin n) L} (h : ∀ i j, j < i → (g : Matrix (Fin n) (Fin n) L) i j = 0) (a : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) a a ≠ 0 := by
  have hdet : (g : Matrix (Fin n) (Fin n) L).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [Matrix.det_of_upperTriangular (fun i j hij => h i j hij)] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet a (Finset.mem_univ a)

theorem mat_triang {R I B T : Matrix (Fin n) (Fin n) L} {π π' : Equiv.Perm (Fin n)}
    (hR : IwEnt R) (hRd : ∀ i, Valued.v (R i i) = 1) (hI : IwEnt I) (hId : ∀ i, Valued.v (I i i) = 1)
    (hBz : ∀ a, B a a ≠ 0) (hTz : ∀ a, T a a ≠ 0)
    (hdom : ∀ i j, i < j → ordL (T j j) < ordL (T i i))
    (hB : ∀ i j, j < i → B i j = 0)
    (hg : ∀ a c, R (π a) c * T c c = ∑ x, B a x * I (π' x) c) :
    ∑ a : Fin n, ((a.val : ℤ) + 1) * ordL (T (π' a) (π' a)) <
        ∑ a : Fin n, ((a.val : ℤ) + 1) * ordL (T (π a) (π a)) ∨
      (π' = π ∧ ∀ a, ordL (B a a) = ordL (T (π a) (π a))) := by
  have hk := key hR hRd hI hId hBz hTz hdom hB hg
  rw [← sum_sum_up (fun a => ordL (T (π' a) (π' a))), ← sum_sum_up (fun a => ordL (T (π a) (π a)))]
  by_cases hlt : ∑ m ∈ Finset.range n, ∑ a : Up n m, ordL (T (π' a.1) (π' a.1)) <
      ∑ m ∈ Finset.range n, ∑ a : Up n m, ordL (T (π a.1) (π a.1))
  · exact Or.inl hlt
  right
  have hle := Finset.sum_le_sum fun m (_ : m ∈ Finset.range n) => (hk m).1
  have heq := (Finset.sum_eq_sum_iff_of_le fun m _ => (hk m).1).1 (le_antisymm hle (not_lt.1 hlt))
  have hpp : π' = π := by
    have h1 : π⁻¹ * π' = 1 := by
      refine perm_one_of_le _ fun a => ?_
      obtain ⟨y, hy⟩ := ((hk a.val).2 (heq a.val (Finset.mem_range.2 a.2))).1 ⟨a, le_rfl⟩
      have e : (π⁻¹ * π') a = y.1 := by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        rw [← hy]
        simp
      rw [e]
      exact y.2
    calc π' = π * (π⁻¹ * π') := by group
      _ = π := by rw [h1, mul_one]
  refine ⟨hpp, up_diff (fun a => ordL (B a a)) (fun a => ordL (T (π a) (π a))) fun m hm => ?_⟩
  exact ((hk m).2 (heq m (Finset.mem_range.2 hm))).2

end Block

theorem perm_mul {L : Type} [Field L] {n : ℕ} {W : Matrix (Fin n) (Fin n) L} {π : Equiv.Perm (Fin n)}
    (hW : ∀ a c, W a c = if c = π a then 1 else 0) (M : Matrix (Fin n) (Fin n) L) (a c : Fin n) :
    (W * M) a c = M (π a) c := by
  simp [Matrix.mul_apply, hW]

end GlobalTheory.CompanionTheory.SatPow.Triang

namespace GlobalTheory.CompanionTheory.SatPow

open Triang in

theorem cell_triang : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (t w w' b r i : GU σ n) (π π' : Equiv.Perm (Fin n)), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → IsPermW w π → IsPermW w' π' → IsBorelU b → r ∈ IwU σ n → i ∈ IwU σ n → w * r * t = b * w' * i → permWt t π' < permWt t π ∨ (π' = π ∧ ∀ a : Fin n, ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) = ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a))) := by
  intro L _ _ σ n t w w' b r i π π' hD hS hW hW' hb hr hi h
  have hr' : (r : GL (Fin n) L) ∈ IwGL L n := hr
  have hi' : (i : GL (Fin n) L) ∈ IwGL L n := hi
  have hmat : ((w : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((r : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) =
      ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (((w' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((i : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
    have := congrArg (fun g : GU σ n => ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) h
    simpa [mul_assoc] using this
  have hg : ∀ a c, ((r : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) c *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) c c =
      ∑ x, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a x *
        ((i : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π' x) c := by
    intro a c
    have e := congrFun (congrFun hmat a) c
    rw [perm_mul hW, Matrix.mul_apply, Matrix.mul_apply] at e
    simp only [perm_mul hW'] at e
    rw [← e]
    rw [Finset.sum_eq_single c]
    · intro y _ hy
      rw [hD y c hy, mul_zero]
    · simp
  exact mat_triang (iwEnt_of_mem hr') (diag_of_mem hr') (iwEnt_of_mem hi') (diag_of_mem hi')
    (upper_diag_ne hb) (upper_diag_ne fun i j hij => hD i j hij.ne') hS hb hg

end GlobalTheory.CompanionTheory.SatPow

end
