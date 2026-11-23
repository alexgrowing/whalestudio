import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.DDMulApply

open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace WlocSk.NB

variable {k r : ℕ}

def blk (A : Matrix (Fin r) (Fin r) ℂ) (B : Matrix (Fin r) (Fin (k + 1)) ℂ) (C : Matrix (Fin r) (Fin r) ℂ)
    (E : Matrix (Fin (k + 1)) (Fin r) ℂ) (F : Matrix (Fin r) (Fin r) ℂ) : Ix k r → Ix k r → ℂ
  | Sum.inl a, Sum.inl b => A a b
  | Sum.inl a, Sum.inr (Sum.inl j) => B a j
  | Sum.inl a, Sum.inr (Sum.inr b) => C a b
  | Sum.inr (Sum.inl _), Sum.inl _ => 0
  | Sum.inr (Sum.inl j), Sum.inr (Sum.inl c) => if j = c then 1 else 0
  | Sum.inr (Sum.inl j), Sum.inr (Sum.inr b) => E j b
  | Sum.inr (Sum.inr _), Sum.inl _ => 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr a), Sum.inr (Sum.inr b) => F a b

def mkM (A : Matrix (Fin r) (Fin r) ℂ) (B : Matrix (Fin r) (Fin (k + 1)) ℂ) (C : Matrix (Fin r) (Fin r) ℂ)
    (E : Matrix (Fin (k + 1)) (Fin r) ℂ) (F : Matrix (Fin r) (Fin r) ℂ) : Mx k r :=
  fun i j => blk A B C E F ((posE k r).symm i) ((posE k r).symm j)

theorem symm_eI (a : Fin r) : (posE k r).symm (eI k r a) = Sum.inl a := by
  exact (posE k r).symm_apply_eq.mpr rfl
theorem symm_wI (j : Fin (k + 1)) : (posE k r).symm (wI k r j) = Sum.inr (Sum.inl j) := by
  exact (posE k r).symm_apply_eq.mpr rfl
theorem symm_esI (a : Fin r) : (posE k r).symm (esI k r a) = Sum.inr (Sum.inr a) := by
  exact (posE k r).symm_apply_eq.mpr rfl

section mk
variable (A : Matrix (Fin r) (Fin r) ℂ) (B : Matrix (Fin r) (Fin (k + 1)) ℂ) (C : Matrix (Fin r) (Fin r) ℂ)
    (E : Matrix (Fin (k + 1)) (Fin r) ℂ) (F : Matrix (Fin r) (Fin r) ℂ)

@[simp] theorem mk_ee (a b : Fin r) : mkM A B C E F (eI k r a) (eI k r b) = A a b := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]
@[simp] theorem mk_ew (a : Fin r) (j : Fin (k + 1)) : mkM A B C E F (eI k r a) (wI k r j) = B a j := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]
@[simp] theorem mk_es (a b : Fin r) : mkM A B C E F (eI k r a) (esI k r b) = C a b := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]
@[simp] theorem mk_we (j : Fin (k + 1)) (b : Fin r) : mkM A B C E F (wI k r j) (eI k r b) = 0 := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]
@[simp] theorem mk_ww (j c : Fin (k + 1)) :
    mkM A B C E F (wI k r j) (wI k r c) = if j = c then 1 else 0 := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]
@[simp] theorem mk_ws (j : Fin (k + 1)) (b : Fin r) : mkM A B C E F (wI k r j) (esI k r b) = E j b := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]
@[simp] theorem mk_se (a b : Fin r) : mkM A B C E F (esI k r a) (eI k r b) = 0 := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]
@[simp] theorem mk_sw (a : Fin r) (j : Fin (k + 1)) : mkM A B C E F (esI k r a) (wI k r j) = 0 := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]
@[simp] theorem mk_ss (a b : Fin r) : mkM A B C E F (esI k r a) (esI k r b) = F a b := by
  simp only [mkM, symm_eI, symm_wI, symm_esI, blk]

theorem bA_mk : bA (mkM A B C E F) = A := by
  ext a b
  exact mk_ee A B C E F a b
theorem bB_mk : bB (mkM A B C E F) = B := by
  ext a j
  exact mk_ew A B C E F a j
theorem bC_mk : bC (mkM A B C E F) = C := by
  ext a b
  exact mk_es A B C E F a b
theorem bE_mk : bE (mkM A B C E F) = E := by
  ext j b
  exact mk_ws A B C E F j b
theorem bF_mk : bF (mkM A B C E F) = F := by
  ext a b
  exact mk_ss A B C E F a b

def LowId (A : Matrix (Fin r) (Fin r) ℂ) : Prop := ∀ a b : Fin r, b ≤ a → A a b = if a = b then 1 else 0

private theorem mkM_pos_lemma (p q : Ix k r) :
    mkM A B C E F (posE k r p) (posE k r q) = blk A B C E F p q := by
  simp only [mkM, Equiv.symm_apply_apply]

theorem col_mk (hA : LowId A) : UnitaryGroupBasics.col k r (mkM A B C E F) := by
  have v1 : ∀ a : Fin r, ((posE k r (Sum.inl a) : Fin (2 * r + k + 1)) : ℕ) = a := fun _ => rfl
  have v2 : ∀ j : Fin (k + 1), ((posE k r (Sum.inr (Sum.inl j)) : Fin (2 * r + k + 1)) : ℕ) = r + j := fun _ => rfl
  have v3 : ∀ a : Fin r, ((posE k r (Sum.inr (Sum.inr a)) : Fin (2 * r + k + 1)) : ℕ) = 2 * r + k - a := fun _ => rfl
  intro i j hj hij
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rw [mkM_pos_lemma]
  simp only [(posE k r).apply_eq_iff_eq]
  rcases p with a | j' | a <;> rcases q with b | c | b <;> simp only [v1, v2, v3] at hj hij
  · have hba : b ≤ a := by
      rcases hij with h | h
      · exact h
      · exact absurd h (not_le.mpr a.isLt)
    simpa [blk] using hA a b hba
  · have := a.isLt
    omega
  · have := b.isLt
    omega
  · simp [blk]
  · simp [blk]
  · have := b.isLt
    omega
  · simp [blk]
  · simp [blk]
  · have := b.isLt
    omega

private theorem hpkE_lemma (a : Fin r) (y : Fin (2 * r + k + 1)) :
    Hpk k r (posE k r (Sum.inl a)) y = if y = posE k r (Sum.inr (Sum.inr a)) then 1 else 0 := by
  have v1 : ((posE k r (Sum.inl a) : Fin (2 * r + k + 1)) : ℕ) = a := rfl
  have v3 : ((posE k r (Sum.inr (Sum.inr a)) : Fin (2 * r + k + 1)) : ℕ) = 2 * r + k - a := rfl
  have ha := a.isLt
  have hy := y.isLt
  simp only [Hpk, Fin.ext_iff, v1, v3]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem hpkW_lemma_2 (c : Fin (k + 1)) (y : Fin (2 * r + k + 1)) :
    Hpk k r (posE k r (Sum.inr (Sum.inl c))) y =
      if y = posE k r (Sum.inr (Sum.inl c)) then (if c.val = k then -1 else 1) else 0 := by
  have v2 : ((posE k r (Sum.inr (Sum.inl c)) : Fin (2 * r + k + 1)) : ℕ) = r + c := rfl
  have hc := c.isLt
  have hy := y.isLt
  simp only [Hpk, Fin.ext_iff, v2]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem hpkS_lemma_3 (a : Fin r) (y : Fin (2 * r + k + 1)) :
    Hpk k r (posE k r (Sum.inr (Sum.inr a))) y = if y = posE k r (Sum.inl a) then 1 else 0 := by
  have v1 : ((posE k r (Sum.inl a) : Fin (2 * r + k + 1)) : ℕ) = a := rfl
  have v3 : ((posE k r (Sum.inr (Sum.inr a)) : Fin (2 * r + k + 1)) : ℕ) = 2 * r + k - a := rfl
  have ha := a.isLt
  have hy := y.isLt
  simp only [Hpk, Fin.ext_iff, v1, v3]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem uhE_lemma_4 (g : Mx k r) (i j : Fin (2 * r + k + 1)) :
    (gᴴ * Hpk k r * g) i j =
      ∑ a : Fin r, star (g (posE k r (Sum.inl a)) i) * g (posE k r (Sum.inr (Sum.inr a))) j +
      (∑ c : Fin (k + 1), star (g (posE k r (Sum.inr (Sum.inl c))) i) *
          ((if c.val = k then -1 else 1) * g (posE k r (Sum.inr (Sum.inl c))) j) +
        ∑ a : Fin r, star (g (posE k r (Sum.inr (Sum.inr a))) i) * g (posE k r (Sum.inl a)) j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, ← (posE k r).sum_comp]
  simp only [Fintype.sum_sum_type, Matrix.conjTranspose_apply, Matrix.mul_apply, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem uh_mk (h2 : Aᴴ * F = 1) (h3 : E = -(dD k * (Bᴴ * F)))
    (h4 : Fᴴ * C + (Fᴴ * C)ᴴ + Eᴴ * dD k * E = 0) : mkM A B C E F ∈ UH (Hpk k r) := by
  show (mkM A B C E F)ᴴ * Hpk k r * mkM A B C E F = Hpk k r
  have hs : ∀ (P : Prop) [Decidable P], star (if P then (1 : ℂ) else 0) = if P then 1 else 0 := by
    intro P _
    split_ifs <;> simp
  have hmz : ∀ (P : Prop) [Decidable P] (a b : ℂ), a * (if P then b else 0) = if P then a * b else 0 := by
    intro P _ a b
    split_ifs <;> simp
  have hDD : dD k * dD k = 1 := by
    unfold dD
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases h : j.val = k <;> simp [h]
  have hDh : (dD k)ᴴ = dD k := by
    unfold dD
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    by_cases h : j.val = k <;> simp [h]
  have hDE : ∀ j b, (dD k * E) j b = (if j.val = k then -1 else 1) * E j b := fun j b => by
    unfold dD
    exact Matrix.diagonal_mul _ _ _ _
  have hED : ∀ a j, (Eᴴ * dD k) a j = star (E j a) * (if j.val = k then -1 else 1) := fun a j => by
    unfold dD
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  have h3' : Bᴴ * F + dD k * E = 0 := by
    rw [h3, Matrix.mul_neg, ← Matrix.mul_assoc, hDD, Matrix.one_mul, add_neg_cancel]
  have h2' : Fᴴ * A = 1 := by
    have := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at this
  have e2 : ∀ a b, ∑ c, star (A c a) * F c b = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun h2 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.conjTranspose_apply] using this
  have e2' : ∀ a b, ∑ c, star (F c a) * A c b = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun h2' a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.conjTranspose_apply] using this
  have e3 : ∀ j b, ∑ c, star (B c j) * F c b + (if j.val = k then -1 else 1) * E j b = 0 := fun j b => by
    have := congrFun (congrFun h3' j) b
    rw [Matrix.add_apply, hDE, Matrix.mul_apply, Matrix.zero_apply] at this
    simpa only [Matrix.conjTranspose_apply] using this
  have h3'' : Fᴴ * B + Eᴴ * dD k = 0 := by
    have := congrArg Matrix.conjTranspose h3'
    rwa [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hDh, Matrix.conjTranspose_zero] at this
  have e3' : ∀ a j, ∑ c, star (F c a) * B c j + star (E j a) * (if j.val = k then -1 else 1) = 0 :=
    fun a j => by
      have := congrFun (congrFun h3'' a) j
      rw [Matrix.add_apply, hED, Matrix.mul_apply, Matrix.zero_apply] at this
      simpa only [Matrix.conjTranspose_apply] using this
  have h4' : Cᴴ * F + Eᴴ * (dD k * E) + Fᴴ * C = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc Eᴴ] at h4
    rw [← h4]
    abel
  have e4 : ∀ a b, ∑ c, star (C c a) * F c b +
      (∑ j, star (E j a) * (if j.val = k then -1 else 1) * E j b + ∑ c, star (F c a) * C c b) = 0 :=
    fun a b => by
      have := congrFun (congrFun h4' a) b
      rw [Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
        Matrix.zero_apply] at this
      simp only [Matrix.conjTranspose_apply, hDE, ← mul_assoc] at this
      linear_combination this
  ext i j
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rw [uhE_lemma_4]
  simp only [mkM_pos_lemma]
  rcases p with a' | c' | a' <;> rcases q with b | c'' | b
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
    all_goals
      rw [e2 a' b]
      by_cases h : a' = b
      · subst h; simp
      · simp [h, Ne.symm h]
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
    all_goals
      by_cases h : c' = c''
      · subst h; simp
      · simp [h, Ne.symm h]
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
    all_goals linear_combination e3 c' b
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
    all_goals
      rw [e2' a' b]
      by_cases h : a' = b
      · subst h; simp
      · simp [h, Ne.symm h]
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, hmz]
    all_goals linear_combination e3' a' c''
  · simp only [blk, hpkE_lemma, hpkW_lemma_2, hpkS_lemma_3, (posE k r).apply_eq_iff_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hs, ← mul_assoc, boole_mul, mul_boole, ite_zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
    all_goals linear_combination e4 a' b

end mk

abbrev UP (r : ℕ) := {p : Fin r × Fin r // p.1 < p.2}

abbrev CI (k r : ℕ) := UP r ⊕ ((Fin r × Fin (k + 1)) ⊕ UP r)

def cA (x : CI k r → ℂ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : a < b then x (Sum.inl ⟨(a, b), h⟩) else if a = b then 1 else 0

def cB (x : CI k r → ℂ) : Matrix (Fin r) (Fin (k + 1)) ℂ := fun a j => x (Sum.inr (Sum.inl (a, j)))

def cK (x : CI k r → ℂ) (s : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : a < b then x (Sum.inr (Sum.inr ⟨(a, b), h⟩))
  else if h' : b < a then -star (x (Sum.inr (Sum.inr ⟨(b, a), h'⟩))) else (s a : ℂ) * Complex.I

def cF (x : CI k r → ℂ) : Matrix (Fin r) (Fin r) ℂ := (cA x).adjugateᴴ

def cE (x : CI k r → ℂ) : Matrix (Fin (k + 1)) (Fin r) ℂ := -(dD k * ((cB x)ᴴ * cF x))

def cM (x : CI k r → ℂ) (s : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  cK x s - (1 / 2 : ℂ) • ((cE x)ᴴ * dD k * cE x)

def cC (x : CI k r → ℂ) (s : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ := cA x * cM x s

def phi0 (x : CI k r → ℂ) (s : Fin r → ℝ) : Mx k r := mkM (cA x) (cB x) (cC x s) (cE x) (cF x)

def mof (g : Mx k r) : Matrix (Fin r) (Fin r) ℂ := (bF g)ᴴ * bC g

def kof (g : Mx k r) : Matrix (Fin r) (Fin r) ℂ := fun a b => (mof g a b - star (mof g b a)) / 2

def psiC (g : Mx k r) : CI k r → ℂ
  | Sum.inl p => g (eI k r p.1.1) (eI k r p.1.2)
  | Sum.inr (Sum.inl q) => g (eI k r q.1) (wI k r q.2)
  | Sum.inr (Sum.inr p) => kof g p.1.1 p.1.2

def psiR (g : Mx k r) : Fin r → ℝ := fun a => (mof g a a).im

theorem lowId_cA (x : CI k r → ℂ) : LowId (cA x) := by
  intro a b hba
  simp only [cA]
  rw [dif_neg (not_lt.mpr hba)]

theorem det_of_lowId {A : Matrix (Fin r) (Fin r) ℂ} (hA : LowId A) : A.det = 1 := by
  have ht : A.BlockTriangular id := fun i j hij => by
    have hij' : j < i := hij
    rw [hA i j hij'.le, if_neg (ne_of_gt hij')]
  rw [Matrix.det_of_upperTriangular ht]
  exact Finset.prod_eq_one fun a _ => by rw [hA a a le_rfl, if_pos rfl]

theorem cF_cA (x : CI k r → ℂ) : (cF x)ᴴ * cA x = 1 := by
  unfold cF
  rw [Matrix.conjTranspose_conjTranspose, Matrix.adjugate_mul, det_of_lowId (lowId_cA x), one_smul]

theorem cA_cF (x : CI k r → ℂ) : (cA x)ᴴ * cF x = 1 := by
  unfold cF
  rw [← Matrix.conjTranspose_mul, Matrix.adjugate_mul, det_of_lowId (lowId_cA x), one_smul,
    Matrix.conjTranspose_one]

theorem nilpotent_chart_matrix_eq (x : CI k r → ℂ) (s : Fin r → ℝ) : mof (phi0 x s) = cM x s := by
  unfold mof phi0
  rw [bF_mk, bC_mk]
  unfold cC
  rw [← Matrix.mul_assoc, cF_cA, Matrix.one_mul]

theorem test_vector_mem_schwartz_bruhat (x : CI k r → ℂ) (s : Fin r → ℝ) : phi0 x s ∈ Nset k r := by
  have hD : (dD k)ᴴ = dD k := by
    unfold dD
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    by_cases h : j.val = k <;> simp [h]
  have hX : ((cE x)ᴴ * dD k * cE x)ᴴ = (cE x)ᴴ * dD k * cE x := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
      Matrix.mul_assoc]
  have hK : (cK x s)ᴴ = -cK x s := by
    ext a b
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [cK, h, not_lt.mpr h.le]
    · simp [cK]
    · simp [cK, h, not_lt.mpr h.le]
  have hFC : (cF x)ᴴ * cC x s = cM x s := by
    unfold cC
    rw [← Matrix.mul_assoc, cF_cA, Matrix.one_mul]
  have hh : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have h4 : (cF x)ᴴ * cC x s + ((cF x)ᴴ * cC x s)ᴴ + (cE x)ᴴ * dD k * cE x = 0 := by
    rw [hFC]
    unfold cM
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hK, hX, hh]
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul]
    ring
  have hc := col_mk (cA x) (cB x) (cC x s) (cE x) (cF x) (lowId_cA x)
  refine ⟨uh_mk _ _ _ _ _ (cA_cF x) rfl h4, fun a i hai => hc i (eI k r a) ?_ (Or.inl hai),
    fun i j h1 h2 h3 => hc i j h2 (Or.inr h3)⟩
  have := a.isLt
  show (a : ℕ) ≤ r + k
  omega

theorem nilpotent_chart_right_inverse (x : CI k r → ℂ) (s : Fin r → ℝ) : psiC (phi0 x s) = x ∧ psiR (phi0 x s) = s := by
  have hm := nilpotent_chart_matrix_eq x s
  have hD : (dD k)ᴴ = dD k := by
    unfold dD
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    by_cases h : j.val = k <;> simp [h]
  have hX : ((cE x)ᴴ * dD k * cE x)ᴴ = (cE x)ᴴ * dD k * cE x := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD,
      Matrix.mul_assoc]
  have hXs : ∀ a b, star (((cE x)ᴴ * dD k * cE x) b a) = ((cE x)ᴴ * dD k * cE x) a b := fun a b => by
    rw [← Matrix.conjTranspose_apply, hX]
  have hh : star (1 / 2 : ℂ) = 1 / 2 := by simp
  constructor
  · funext i
    rcases i with ⟨⟨a, b⟩, hab⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, hab⟩
    · show phi0 x s (eI k r a) (eI k r b) = x (Sum.inl ⟨(a, b), hab⟩)
      unfold phi0
      rw [mk_ee]
      simp only [cA, dif_pos hab]
    · show phi0 x s (eI k r a) (wI k r j) = x (Sum.inr (Sum.inl (a, j)))
      unfold phi0
      rw [mk_ew]
      rfl
    · show (mof (phi0 x s) a b - star (mof (phi0 x s) b a)) / 2 = x (Sum.inr (Sum.inr ⟨(a, b), hab⟩))
      rw [hm]
      simp only [cM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, star_sub, star_mul', hXs, hh]
      simp only [cK, dif_pos hab, dif_neg (not_lt.mpr hab.le), star_neg, star_star]
      ring
  · funext a
    show (mof (phi0 x s) a a).im = s a
    rw [hm]
    have h1 := congrArg Complex.im (hXs a a)
    rw [Complex.star_def, Complex.conj_im] at h1
    have h0 : (((cE x)ᴴ * dD k * cE x) a a).im = 0 := by linarith
    have hhalf : ((1 / 2 : ℂ) * ((cE x)ᴴ * dD k * cE x) a a).im = 0 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by simp, Complex.im_ofReal_mul, h0, mul_zero]
    have hk : (cK x s a a).im = s a := by simp [cK]
    simp only [cM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.sub_im, hk, hhalf, sub_zero]

theorem mk_blocks {g : Mx k r} (hc : ColB g) : mkM (bA g) (bB g) (bC g) (bE g) (bF g) = g := by
  ext i j
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rw [mkM_pos_lemma]
  rcases p with a | j' | a <;> rcases q with b | c | b <;> simp only [blk] <;>
    first
    | rfl
    | exact (hc.wa _ _).symm
    | exact (hc.ww _ _).symm
    | exact (hc.sa _ _).symm
    | exact (hc.sw _ _).symm

theorem cA_psi {g : Mx k r} (hc : ColB g) : cA (psiC g) = bA g := by
  ext a b
  by_cases h : a < b
  · simp only [cA, dif_pos h]
    all_goals rfl
  · simp only [cA, dif_neg h]
    exact (hc.aa a b (not_lt.mp h)).symm

theorem cB_psi (g : Mx k r) : cB (psiC g) = bB g := by
  ext a j
  rfl

theorem adj_eq {g : Mx k r} (hc : ColB g) (hu : g ∈ UH (Hpk k r)) : (bA g).adjugate = (bF g)ᴴ := by
  have hu' : gᴴ * Hpk k r * g = Hpk k r := hu
  have hAF : (bA g)ᴴ * bF g = 1 := by
    ext a b
    have h := congrFun (congrFun hu' (posE k r (Sum.inl a))) (posE k r (Sum.inr (Sum.inr b)))
    rw [uhE_lemma_4, hpkE_lemma] at h
    have hw : ∀ j, g (posE k r (Sum.inr (Sum.inl j))) (posE k r (Sum.inl a)) = 0 := fun j => hc.wa j a
    have hs : ∀ c, g (posE k r (Sum.inr (Sum.inr c))) (posE k r (Sum.inl a)) = 0 := fun c => hc.sa c a
    simp only [hw, hs, star_zero, zero_mul, Finset.sum_const_zero, add_zero, (posE k r).apply_eq_iff_eq,
      Sum.inr.injEq, @eq_comm _ b a] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.conjTranspose_apply]
    exact h
  have hFA : (bF g)ᴴ * bA g = 1 := by
    have := congrArg Matrix.conjTranspose hAF
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at this
  have hdet : (bA g).det = 1 := det_of_lowId (fun a b hba => hc.aa a b hba)
  calc (bA g).adjugate = (bF g)ᴴ * bA g * (bA g).adjugate := by rw [hFA, Matrix.one_mul]
    _ = (bF g)ᴴ := by rw [Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]

theorem cF_psi {g : Mx k r} (hc : ColB g) (hu : g ∈ UH (Hpk k r)) : cF (psiC g) = bF g := by
  unfold cF
  rw [cA_psi hc, adj_eq hc hu, Matrix.conjTranspose_conjTranspose]

theorem cE_psi {g : Mx k r} (hc : ColB g) (hu : g ∈ UH (Hpk k r)) : cE (psiC g) = bE g := by
  have hu' : gᴴ * Hpk k r * g = Hpk k r := hu
  have hs : ∀ (P : Prop) [Decidable P], star (if P then (1 : ℂ) else 0) = if P then 1 else 0 := by
    intro P _
    split_ifs <;> simp
  unfold cE
  rw [cB_psi, cF_psi hc hu]
  ext j b
  have h := congrFun (congrFun hu' (posE k r (Sum.inr (Sum.inl j)))) (posE k r (Sum.inr (Sum.inr b)))
  rw [uhE_lemma_4, hpkW_lemma_2] at h
  have hww : ∀ c, g (posE k r (Sum.inr (Sum.inl c))) (posE k r (Sum.inr (Sum.inl j))) =
      if c = j then 1 else 0 := fun c => hc.ww c j
  have hsw : ∀ c, g (posE k r (Sum.inr (Sum.inr c))) (posE k r (Sum.inr (Sum.inl j))) = 0 := fun c => hc.sw c j
  have hB' : ∀ x y, g (posE k r (Sum.inl x)) (posE k r (Sum.inr (Sum.inl y))) = bB g x y := fun _ _ => rfl
  have hF' : ∀ x y, g (posE k r (Sum.inr (Sum.inr x))) (posE k r (Sum.inr (Sum.inr y))) = bF g x y :=
    fun _ _ => rfl
  have hE' : ∀ x y, g (posE k r (Sum.inr (Sum.inl x))) (posE k r (Sum.inr (Sum.inr y))) = bE g x y :=
    fun _ _ => rfl
  simp only [hww, hsw, hB', hF', hE', star_zero, zero_mul, Finset.sum_const_zero, add_zero, hs, boole_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, (posE k r).apply_eq_iff_eq,
    Sum.inr.injEq, reduceCtorEq] at h
  have hd2 : (if (j : ℕ) = k then (-1 : ℂ) else 1) * (if (j : ℕ) = k then -1 else 1) = 1 := by
    split_ifs <;> norm_num
  rw [Matrix.neg_apply]
  unfold dD
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  clear hww hsw hB' hF' hE' hs hu' hu hc
  linear_combination (-(if (j : ℕ) = k then (-1 : ℂ) else 1)) * h + bE g j b * hd2

theorem cK_psi (g : Mx k r) : cK (psiC g) (psiR g) = kof g := by
  ext a b
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [cK, dif_pos h]
    all_goals rfl
  · simp only [cK, dif_neg (lt_irrefl a)]
    show ((psiR g a : ℝ) : ℂ) * Complex.I = (mof g a a - star (mof g a a)) / 2
    unfold psiR
    rw [Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  · simp only [cK, dif_neg (not_lt.mpr h.le), dif_pos h]
    show -star (kof g b a) = kof g a b
    unfold kof
    rw [Complex.star_def, map_div₀, map_sub, Complex.conj_conj, map_ofNat]
    ring

theorem cM_psi {g : Mx k r} (hc : ColB g) (hu : g ∈ UH (Hpk k r)) : cM (psiC g) (psiR g) = mof g := by
  have hu' : gᴴ * Hpk k r * g = Hpk k r := hu
  unfold cM
  rw [cK_psi, cE_psi hc hu]
  ext a b
  have h := congrFun (congrFun hu' (posE k r (Sum.inr (Sum.inr a)))) (posE k r (Sum.inr (Sum.inr b)))
  rw [uhE_lemma_4, hpkS_lemma_3] at h
  simp only [(posE k r).apply_eq_iff_eq, reduceCtorEq, ↓reduceIte] at h
  have hDE' : ∀ j c, (dD k * bE g) j c = (if (j : ℕ) = k then -1 else 1) * bE g j c := fun j c => by
    unfold dD
    exact Matrix.diagonal_mul _ _ _ _
  have h' : ((bC g)ᴴ * bF g) a b + (((bE g)ᴴ * (dD k * bE g)) a b + ((bF g)ᴴ * bC g) a b) = 0 := by
    rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hDE']
    exact h
  have hM : (bC g)ᴴ * bF g = (mof g)ᴴ := by
    unfold mof
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [hM, Matrix.conjTranspose_apply, ← Matrix.mul_assoc] at h'
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, kof]
  show (((bF g)ᴴ * bC g) a b - star (mof g b a)) / 2 - 1 / 2 * ((bE g)ᴴ * dD k * bE g) a b =
    ((bF g)ᴴ * bC g) a b
  linear_combination (-1 / 2 : ℂ) * h'

theorem cC_psi {g : Mx k r} (hc : ColB g) (hu : g ∈ UH (Hpk k r)) : cC (psiC g) (psiR g) = bC g := by
  unfold cC
  rw [cA_psi hc, cM_psi hc hu]
  unfold mof
  have hdet : (bA g).det = 1 := det_of_lowId (fun a b hba => hc.aa a b hba)
  rw [← Matrix.mul_assoc, ← adj_eq hc hu, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]

theorem nilpotent_chart_left_inverse {g : Mx k r} (hg : g ∈ Nset k r) : phi0 (psiC g) (psiR g) = g := by
  obtain ⟨hu, h1, h2⟩ := hg
  have hc : ColB g := by
    refine ⟨fun a b hba => ?_, fun j b => ?_, fun a b => ?_, fun j c => ?_, fun a j => ?_⟩
    · rw [h1 b (eI k r a) hba]
      simp only [show (eI k r a = eI k r b) = (posE k r (Sum.inl a) = posE k r (Sum.inl b)) from rfl,
        (posE k r).apply_eq_iff_eq, Sum.inl.injEq]
    · have hb := b.isLt
      rw [h1 b (wI k r j) (by show (b : ℕ) ≤ r + j; omega)]
      simp only [show (wI k r j = eI k r b) = (posE k r (Sum.inr (Sum.inl j)) = posE k r (Sum.inl b)) from rfl,
        (posE k r).apply_eq_iff_eq, reduceCtorEq, ↓reduceIte]
    · have ha := a.isLt
      have hb := b.isLt
      rw [h1 b (esI k r a) (by show (b : ℕ) ≤ 2 * r + k - a; omega)]
      simp only [show (esI k r a = eI k r b) = (posE k r (Sum.inr (Sum.inr a)) = posE k r (Sum.inl b)) from rfl,
        (posE k r).apply_eq_iff_eq, reduceCtorEq, ↓reduceIte]
    · have hc' := c.isLt
      rw [h2 (wI k r j) (wI k r c) (by show r ≤ r + (c : ℕ); omega) (by show r + (c : ℕ) ≤ r + k; omega)
        (by show r ≤ r + (j : ℕ); omega)]
      simp only [show (wI k r j = wI k r c) =
        (posE k r (Sum.inr (Sum.inl j)) = posE k r (Sum.inr (Sum.inl c))) from rfl,
        (posE k r).apply_eq_iff_eq, Sum.inr.injEq, Sum.inl.injEq]
    · have ha := a.isLt
      have hj := j.isLt
      rw [h2 (esI k r a) (wI k r j) (by show r ≤ r + (j : ℕ); omega) (by show r + (j : ℕ) ≤ r + k; omega)
        (by show r ≤ 2 * r + k - a; omega)]
      simp only [show (esI k r a = wI k r j) =
        (posE k r (Sum.inr (Sum.inr a)) = posE k r (Sum.inr (Sum.inl j))) from rfl,
        (posE k r).apply_eq_iff_eq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte]
  unfold phi0
  rw [cA_psi hc, cB_psi, cC_psi hc hu, cE_psi hc hu, cF_psi hc hu]
  exact mk_blocks hc

theorem continuous_cA : Continuous (cA (k := k) (r := r)) := by
  refine continuous_matrix fun a b => ?_
  by_cases h : a < b
  · simp only [cA, dif_pos h]
    exact continuous_apply _
  · simp only [cA, dif_neg h]
    exact continuous_const

theorem continuous_cB : Continuous (cB (k := k) (r := r)) := by
  refine continuous_matrix fun a j => ?_
  simp only [cB]
  exact continuous_apply _

theorem continuous_cF : Continuous (cF (k := k) (r := r)) := by
  show Continuous fun x => (cA x).adjugateᴴ
  exact continuous_cA.matrix_adjugate.matrix_conjTranspose

theorem continuous_cE : Continuous (cE (k := k) (r := r)) := by
  show Continuous fun x => -(dD k * ((cB x)ᴴ * cF x))
  exact (continuous_const.matrix_mul (continuous_cB.matrix_conjTranspose.matrix_mul continuous_cF)).neg

theorem continuous_cK : Continuous fun t : (CI k r → ℂ) × (Fin r → ℝ) => cK t.1 t.2 := by
  refine continuous_matrix fun a b => ?_
  by_cases h : a < b
  · simp only [cK, dif_pos h]
    fun_prop
  · by_cases h' : b < a
    · simp only [cK, dif_neg h, dif_pos h']
      fun_prop
    · simp only [cK, dif_neg h, dif_neg h']
      fun_prop

private theorem contMk_lemma {A : (CI k r → ℂ) × (Fin r → ℝ) → Matrix (Fin r) (Fin r) ℂ}
    {B : (CI k r → ℂ) × (Fin r → ℝ) → Matrix (Fin r) (Fin (k + 1)) ℂ}
    {C : (CI k r → ℂ) × (Fin r → ℝ) → Matrix (Fin r) (Fin r) ℂ}
    {E : (CI k r → ℂ) × (Fin r → ℝ) → Matrix (Fin (k + 1)) (Fin r) ℂ}
    {F : (CI k r → ℂ) × (Fin r → ℝ) → Matrix (Fin r) (Fin r) ℂ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hE : Continuous E) (hF : Continuous F) :
    Continuous fun t => mkM (A t) (B t) (C t) (E t) (F t) := by
  refine continuous_matrix fun i j => ?_
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  simp only [mkM, Equiv.symm_apply_apply]
  rcases p with a | j' | a <;> rcases q with b | c | b <;> simp only [blk] <;>
    first
    | exact continuous_const
    | exact hA.matrix_elem _ _
    | exact hB.matrix_elem _ _
    | exact hC.matrix_elem _ _
    | exact hE.matrix_elem _ _
    | exact hF.matrix_elem _ _

theorem continuous_nilpotent_chart : Continuous fun t : (CI k r → ℂ) × (Fin r → ℝ) => phi0 t.1 t.2 := by
  have hA : Continuous fun t : (CI k r → ℂ) × (Fin r → ℝ) => cA t.1 := continuous_cA.comp continuous_fst
  have hB : Continuous fun t : (CI k r → ℂ) × (Fin r → ℝ) => cB t.1 := continuous_cB.comp continuous_fst
  have hE : Continuous fun t : (CI k r → ℂ) × (Fin r → ℝ) => cE t.1 := continuous_cE.comp continuous_fst
  have hF : Continuous fun t : (CI k r → ℂ) × (Fin r → ℝ) => cF t.1 := continuous_cF.comp continuous_fst
  have hD : Continuous fun _ : (CI k r → ℂ) × (Fin r → ℝ) => dD k := continuous_const
  have hM : Continuous fun t : (CI k r → ℂ) × (Fin r → ℝ) => cM t.1 t.2 :=
    continuous_cK.sub (((hE.matrix_conjTranspose.matrix_mul hD).matrix_mul hE).const_smul (1 / 2 : ℂ))
  exact contMk_lemma hA hB (hA.matrix_mul hM) hE hF

theorem continuous_bF : Continuous (bF (k := k) (r := r)) := by
  refine continuous_matrix fun a b => ?_
  exact continuous_id.matrix_elem (esI k r a) (esI k r b)

theorem continuous_bC : Continuous (bC (k := k) (r := r)) := by
  refine continuous_matrix fun a b => ?_
  exact continuous_id.matrix_elem (eI k r a) (esI k r b)

theorem continuous_mof : Continuous (mof (k := k) (r := r)) := by
  show Continuous fun g : Mx k r => (bF g)ᴴ * bC g
  exact continuous_bF.matrix_conjTranspose.matrix_mul continuous_bC

theorem continuous_psiC : Continuous (psiC (k := k) (r := r)) := by
  refine continuous_pi fun i => ?_
  rcases i with p | q | p
  · exact continuous_id.matrix_elem (eI k r p.1.1) (eI k r p.1.2)
  · exact continuous_id.matrix_elem (eI k r q.1) (wI k r q.2)
  · show Continuous fun g : Mx k r => (mof g p.1.1 p.1.2 - star (mof g p.1.2 p.1.1)) / 2
    exact ((continuous_mof.matrix_elem _ _).sub (continuous_mof.matrix_elem _ _).star).div_const _

theorem continuous_psiR : Continuous (psiR (k := k) (r := r)) := by
  refine continuous_pi fun a => ?_
  exact Complex.continuous_im.comp (continuous_mof.matrix_elem a a)

end WlocSk.NB
