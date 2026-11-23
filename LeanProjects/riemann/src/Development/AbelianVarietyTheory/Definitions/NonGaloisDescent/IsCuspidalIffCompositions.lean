import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

open Matrix Formalism.L2.DIV GlobalTheory.FiniteGL GlobalTheory.PRep
open scoped TensorProduct

namespace GlobalTheory.Parabolic

section Groups

variable {k : Type} [Field k] {N : ℕ}

theorem blockDiag_iff {b : Fin N → ℕ} {M : Matrix (Fin N) (Fin N) k} :
    (∀ i j, b i ≠ b j → M i j = 0) ↔ M.BlockTriangular b ∧ M.BlockTriangular (OrderDual.toDual ∘ b) := by
  constructor
  · exact fun h => ⟨fun i j hij => h i j (ne_of_gt hij), fun i j hij => h i j (ne_of_lt (OrderDual.toDual_lt_toDual.1 hij))⟩
  · rintro ⟨h1, h2⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 (OrderDual.toDual_lt_toDual.2 h)
    · exact h1 h

variable (k) in

def levi (b : Fin N → ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {g | ∀ i j, b i ≠ b j → (g : Matrix (Fin N) (Fin N) k) i j = 0}
  one_mem' := fun i j hij => by
    rw [Units.val_one, Matrix.one_apply_ne (fun e => hij (congrArg b e))]
  mul_mem' := by
    intro x y hx hy
    have hx' := blockDiag_iff.1 hx
    have hy' := blockDiag_iff.1 hy
    refine blockDiag_iff.2 ?_
    rw [Units.val_mul]
    exact ⟨hx'.1.mul hy'.1, hx'.2.mul hy'.2⟩
  inv_mem' := by
    intro x hx
    have hx' := blockDiag_iff.1 hx
    letI := x.invertible
    refine blockDiag_iff.2 ?_
    rw [Matrix.coe_units_inv]
    exact ⟨blockTriangular_inv_of_blockTriangular hx'.1, blockTriangular_inv_of_blockTriangular hx'.2⟩

theorem mem_levi {b : Fin N → ℕ} {g : GL (Fin N) k} :
    g ∈ levi k b ↔ ∀ i j, b i ≠ b j → (g : Matrix (Fin N) (Fin N) k) i j = 0 := Iff.rfl

theorem levi_congr {b b' : Fin N → ℕ} (h : ∀ i j, b i = b j ↔ b' i = b' j) : levi k b = levi k b' := by
  ext g
  simp only [mem_levi, ne_eq, h]

theorem levi_le_blockTri (b : Fin N → ℕ) : levi k b ≤ blockTri b := fun _ hg i j hij => hg i j (ne_of_gt hij)

theorem unipRadical_le_blockTri (b : Fin N → ℕ) : unipRadical k b ≤ blockTri b :=
  fun _ hu => blockTriangular_of_sub_one hu

def diagPart (b : Fin N → ℕ) (M : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  Matrix.of fun i j => if b i = b j then M i j else 0

theorem diagPart_apply (b : Fin N → ℕ) (M : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    diagPart b M i j = if b i = b j then M i j else 0 := rfl

theorem diagPart_mul {b : Fin N → ℕ} {X Y : Matrix (Fin N) (Fin N) k} (hX : X.BlockTriangular b)
    (hY : Y.BlockTriangular b) : diagPart b (X * Y) = diagPart b X * diagPart b Y := by
  ext i j
  simp only [diagPart_apply, Matrix.mul_apply]
  split_ifs with hij
  · refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (b l) (b i) with h | h | h
    · rw [hX h, if_neg h.ne', zero_mul, zero_mul]
    · rw [if_pos h.symm, if_pos (h.trans hij)]
    · rw [hY (hij ▸ h), if_neg h.ne, mul_zero, zero_mul]
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    by_cases h : b i = b l
    · rw [if_neg (fun h' : b l = b j => hij (h.trans h')), mul_zero]
    · rw [if_neg h, zero_mul]

def diagPartHom (b : Fin N → ℕ) : blockTri (κ := k) b →* Matrix (Fin N) (Fin N) k where
  toFun p := diagPart b ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp [diagPart_apply]
    · simp [diagPart_apply, Matrix.one_apply_ne h]
  map_mul' x y := diagPart_mul x.2 y.2

def leviProj (b : Fin N → ℕ) : blockTri (κ := k) b →* levi k b :=
  MonoidHom.codRestrict (diagPartHom (k := k) b).toHomUnits (levi k b) fun p i j hij =>
    (if_neg hij : diagPart b ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0)

theorem leviProj_apply (b : Fin N → ℕ) (p : blockTri (κ := k) b) (i j : Fin N) :
    (((leviProj b p : levi k b) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      if b i = b j then ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j else 0 := rfl

theorem leviProj_inclusion (b : Fin N → ℕ) (m : levi k b) :
    leviProj b (Subgroup.inclusion (levi_le_blockTri b) m) = m := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [leviProj_apply]
  split_ifs with h
  · rfl
  · exact (m.2 i j h).symm

theorem leviProj_eq_one_iff (b : Fin N → ℕ) (p : blockTri (κ := k) b) :
    leviProj b p = 1 ↔ (p : GL (Fin N) k) ∈ unipRadical k b := by
  rw [mem_unipRadical]
  constructor
  · intro h i j hij
    have e := leviProj_apply b p i j
    rw [h] at e
    rcases hij.eq_or_lt with h' | h'
    · rw [if_pos h'.symm] at e
      rw [Matrix.sub_apply, ← e]
      simp
    · rw [Matrix.sub_apply, p.2 h', Matrix.one_apply_ne (fun e => by rw [e] at h'; exact lt_irrefl _ h'), sub_zero]
  · intro h
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [leviProj_apply]
    split_ifs with h'
    · have := h i j h'.ge
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simpa using this
    · simp [Matrix.one_apply_ne (fun e => h' (congrArg b e))]

theorem ker_leviProj (b : Fin N → ℕ) :
    (leviProj (k := k) b).ker = (unipRadical k b).subgroupOf (blockTri b) :=
  Subgroup.ext fun p => leviProj_eq_one_iff b p

theorem blockTri_le_normalizer (b : Fin N → ℕ) :
    blockTri b ≤ Subgroup.normalizer ((unipRadical k b : Subgroup (GL (Fin N) k)) : Set (GL (Fin N) k)) := by
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (unipRadical_le_blockTri b), ← ker_leviProj]
  infer_instance

def relProj (a c : Fin N → ℕ) : (blockTri (κ := k) c).subgroupOf (levi k a) →* ↥(levi k a ⊓ levi k c) :=
  ((levi k c).subtype.comp ((leviProj c).comp
    (((levi k a).subtype.comp (Subgroup.subtype _)).codRestrict (blockTri c) fun p => p.2))).codRestrict _
    fun p => ⟨fun i j hij => by
      show (if c i = c j then (((p : levi k a) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j else 0) = 0
      rw [(p : levi k a).2 i j hij, ite_self], fun _ _ hij => if_neg hij⟩

theorem inclusion_mem_normalizer (a c : Fin N → ℕ) (m : ↥(levi k a ⊓ levi k c)) :
    Subgroup.inclusion (inf_le_left : levi k a ⊓ levi k c ≤ levi k a) m ∈
      Subgroup.normalizer (((unipRadical k c).subgroupOf (levi k a) : Subgroup (levi k a)) : Set (levi k a)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  exact Subgroup.mem_normalizer_iff.1 (blockTri_le_normalizer c (levi_le_blockTri c m.2.2)) u

variable (k) in

def permGL : Equiv.Perm (Fin N) →* GL (Fin N) k := (Matrix.permMatrixHom (R := k)).toHomUnits

theorem permGL_apply (w : Equiv.Perm (Fin N)) (i j : Fin N) :
    ((permGL k w : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = if i = w j then 1 else 0 := by
  show (w⁻¹.permMatrix k) i j = _
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]

theorem conj_permGL_apply (w : Equiv.Perm (Fin N)) (g : GL (Fin N) k) (i j : Fin N) :
    ((permGL k w * g * (permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (w i) (w j) =
      (g : Matrix (Fin N) (Fin N) k) i j := by
  rw [← map_inv, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_apply, permGL_apply]
  simp

theorem conj_mem_iff {w : Equiv.Perm (Fin N)} {g : GL (Fin N) k} (R : Fin N → Fin N → Prop) (c : Matrix (Fin N) (Fin N) k)
    (hc : ∀ i j, c (w i) (w j) = c i j) :
    (∀ i j, R i j → ((permGL k w * g * (permGL k w)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = c i j) ↔
      ∀ i j, R (w i) (w j) → (g : Matrix (Fin N) (Fin N) k) i j = c i j := by
  constructor
  · intro h i j hij
    rw [← conj_permGL_apply w, h _ _ hij, hc]
  · intro h i j hij
    obtain ⟨i, rfl⟩ := w.surjective i
    obtain ⟨j, rfl⟩ := w.surjective j
    rw [conj_permGL_apply, h _ _ hij, hc]

theorem conj_mem_blockTri {b : Fin N → ℕ} {w : Equiv.Perm (Fin N)} {g : GL (Fin N) k} :
    permGL k w * g * (permGL k w)⁻¹ ∈ blockTri b ↔ g ∈ blockTri (b ∘ w) :=
  conj_mem_iff (fun i j => b j < b i) 0 fun _ _ => rfl

theorem conj_mem_levi {b : Fin N → ℕ} {w : Equiv.Perm (Fin N)} {g : GL (Fin N) k} :
    permGL k w * g * (permGL k w)⁻¹ ∈ levi k b ↔ g ∈ levi k (b ∘ w) :=
  conj_mem_iff (fun i j => b i ≠ b j) 0 fun _ _ => rfl

theorem conj_mem_unipRadical {b : Fin N → ℕ} {w : Equiv.Perm (Fin N)} {g : GL (Fin N) k} :
    permGL k w * g * (permGL k w)⁻¹ ∈ unipRadical k b ↔ g ∈ unipRadical k (b ∘ w) := by
  simp only [mem_unipRadical, Matrix.sub_apply, sub_eq_zero]
  exact conj_mem_iff (fun i j => b j ≤ b i) 1 fun i j => by simp [Matrix.one_apply]

def leviConj (b : Fin N → ℕ) (w : Equiv.Perm (Fin N)) : levi k (b ∘ w) ≃* levi k b where
  toFun x := ⟨permGL k w * x * (permGL k w)⁻¹, conj_mem_levi.2 x.2⟩
  invFun y := ⟨(permGL k w)⁻¹ * y * permGL k w, conj_mem_levi.1 (by simpa [mul_assoc] using y.2)⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem comp_symm_comp (b : Fin N → ℕ) (w : Equiv.Perm (Fin N)) : (b ∘ w.symm) ∘ w = b := by
  ext i; simp

def relConj (a b : Fin N → ℕ) (w : Equiv.Perm (Fin N)) :
    ↥(levi k b ⊓ levi k (a ∘ w)) ≃* ↥(levi k a ⊓ levi k (b ∘ w.symm)) where
  toFun x := ⟨permGL k w * x * (permGL k w)⁻¹, conj_mem_levi.2 x.2.2,
    conj_mem_levi.2 (by rw [comp_symm_comp]; exact x.2.1)⟩
  invFun y := ⟨(permGL k w)⁻¹ * y * permGL k w, by
      have h : (permGL k w)⁻¹ * y * permGL k w ∈ levi k ((b ∘ w.symm) ∘ w) :=
        conj_mem_levi.1 (by simpa [mul_assoc] using y.2.2)
      rwa [comp_symm_comp] at h,
    conj_mem_levi.1 (by simpa [mul_assoc] using y.2.1)⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

end Groups

section Blocks

variable {k : Type} [Field k] {N : ℕ}

def leviBlock (b : Fin N → ℕ) {n : ℕ} (f : Fin n → Fin N) (hf : Function.Injective f)
    (hr : ∀ i j, b (f i) = b j → j ∈ Set.range f) : levi k b →* GL (Fin n) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => ((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix f f
      map_one' := by
        ext i j
        simp [Matrix.one_apply, hf.eq_iff]
      map_mul' := by
        intro x y
        show ((x.1 * y.1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix _ _ = _
        rw [Units.val_mul]
        refine submatrix_mul_of_zero _ hf _ _ fun i j l hl => ?_
        rw [x.2 _ _ fun e => hl (hr i l e), zero_mul] }

variable {h : ℕ} {d : Fin h → ℕ}

def blockOf (e : (Σ a, Fin (d a)) ≃ Fin N) : Fin N → ℕ := fun i => ((e.symm i).1 : ℕ)

@[simp] theorem blockOf_apply (e : (Σ a, Fin (d a)) ≃ Fin N) (x : Σ a, Fin (d a)) : blockOf e (e x) = x.1 := by
  simp [blockOf]

def blockAt (e : (Σ a, Fin (d a)) ≃ Fin N) (a : Fin h) : levi k (blockOf e) →* GL (Fin (d a)) k :=
  leviBlock (blockOf e) (fun i => e ⟨a, i⟩) (fun _ _ hij => sigma_mk_injective (β := fun a => Fin (d a)) (e.injective hij)) fun i j hij => by
    obtain ⟨⟨c, l⟩, rfl⟩ := e.surjective j
    obtain rfl : a = c := Fin.ext (by simpa using hij)
    exact ⟨l, rfl⟩

def blockDiagHom (e : (Σ a, Fin (d a)) ≃ Fin N) : (∀ a, GL (Fin (d a)) k) →* levi k (blockOf e) :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.blockDiagonal' fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) k)).submatrix e.symm e.symm
      map_one' := by
        have : (fun a => ((1 : ∀ a, GL (Fin (d a)) k) a : Matrix (Fin (d a)) (Fin (d a)) k)) = 1 := rfl
        rw [this, Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        rfl }) _
    fun x i j hij => Matrix.blockDiagonal'_apply_ne
      (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) k)) (e.symm i).2 (e.symm j).2 fun e' => hij (congrArg Fin.val e')

def leviEquiv (e : (Σ a, Fin (d a)) ≃ Fin N) : levi k (blockOf e) ≃* ∀ a, GL (Fin (d a)) k :=
  MonoidHom.toMulEquiv (Pi.monoidHom (blockAt e)) (blockDiagHom e)
    (by
      ext g i j
      obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective j
      show Matrix.blockDiagonal' (fun a => (blockAt e a g : Matrix (Fin (d a)) (Fin (d a)) k))
        (e.symm (e ⟨a, i⟩)) (e.symm (e ⟨c, j⟩)) = _
      rw [e.symm_apply_apply, e.symm_apply_apply]
      by_cases hac : a = c
      · subst hac
        rw [Matrix.blockDiagonal'_apply_eq]
        rfl
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hac]
        exact (g.2 _ _ (by simpa [Fin.val_inj] using hac)).symm)
    (by
      ext x a i j
      show Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) k))
        (e.symm (e ⟨a, i⟩)) (e.symm (e ⟨a, j⟩)) = _
      rw [e.symm_apply_apply, e.symm_apply_apply, Matrix.blockDiagonal'_apply_eq]
      rfl)

theorem leviEquiv_apply (e : (Σ a, Fin (d a)) ≃ Fin N) (g : levi k (blockOf e)) (a : Fin h) (i j : Fin (d a)) :
    ((leviEquiv e g a : GL (Fin (d a)) k) : Matrix (Fin (d a)) (Fin (d a)) k) i j =
      ((g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := rfl

def stdEquiv (d : Fin h → ℕ) (hd : ∑ a, d a = N) : (Σ a, Fin (d a)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr hd)

theorem stdEquiv_val (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (i : Fin (d a)) :
    (stdEquiv d hd ⟨a, i⟩ : ℕ) = ∑ c ∈ Finset.Iio a, d c + i := by
  show (finSigmaFinEquiv ⟨a, i⟩ : ℕ) = _
  rw [finSigmaFinEquiv_apply]
  congr 1
  refine Finset.sum_bij (fun c _ => Fin.castLE a.2.le c) (fun c _ => ?_) (fun _ _ _ _ e => Fin.castLE_injective _ e)
    (fun c hc => ⟨⟨c, (Finset.mem_Iio.1 hc : c < a)⟩, Finset.mem_univ _, rfl⟩) fun _ _ => rfl
  exact Finset.mem_Iio.2 c.2

theorem blockOf_stdEquiv_two {r t : ℕ} (hd : ∑ c, (![r, t] : Fin 2 → ℕ) c = N) :
    blockOf (stdEquiv ![r, t] hd) = twoBlocks N r := by
  funext i
  obtain ⟨⟨c, l⟩, rfl⟩ := (stdEquiv _ hd).surjective i
  have hl := l.2
  rw [blockOf_apply, twoBlocks, stdEquiv_val]
  fin_cases c
  · have : Finset.Iio (0 : Fin 2) = ∅ := by decide
    simp at hl
    simp [this, hl]
  · have : Finset.Iio (1 : Fin 2) = {0} := by decide
    simp [this]

def IsTwoBlock (r : ℕ) (b : Fin N → ℕ) : Prop := ∀ i j, b i = b j ↔ ((i : ℕ) < r ↔ (j : ℕ) < r)

theorem isTwoBlock_twoBlocks (N r : ℕ) : IsTwoBlock r (twoBlocks N r) := by
  intro i j
  simp only [twoBlocks]
  split_ifs <;> simp [*]

def oppTwoBlocks (N r : ℕ) : Fin N → ℕ := fun i => if (i : ℕ) < r then 1 else 0

variable {r t : ℕ}

def twoEquiv (hN : r + t = N) : Fin r ⊕ Fin t ≃ Fin N := finSumFinEquiv.trans (finCongr hN)

@[simp] theorem twoEquiv_inl (hN : r + t = N) (i : Fin r) : (twoEquiv hN (Sum.inl i) : ℕ) = i := rfl

@[simp] theorem twoEquiv_inr (hN : r + t = N) (i : Fin t) : (twoEquiv hN (Sum.inr i) : ℕ) = r + i := rfl

def twoDiagHom (hN : r + t = N) {b : Fin N → ℕ} (hb : IsTwoBlock r b) : GL (Fin r) k × GL (Fin t) k →* levi k b :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.fromBlocks (x.1 : Matrix (Fin r) (Fin r) k) 0 0 (x.2 : Matrix (Fin t) (Fin t) k)).submatrix
        (twoEquiv hN).symm (twoEquiv hN).symm
      map_one' := by simp
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
        simp }) _
    fun x i j hij => by
      obtain ⟨i, rfl⟩ := (twoEquiv hN).surjective i
      obtain ⟨j, rfl⟩ := (twoEquiv hN).surjective j
      show Matrix.fromBlocks (x.1 : Matrix (Fin r) (Fin r) k) 0 0 (x.2 : Matrix (Fin t) (Fin t) k)
        ((twoEquiv hN).symm (twoEquiv hN i)) ((twoEquiv hN).symm (twoEquiv hN j)) = 0
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rw [ne_eq, hb] at hij
      rcases i with i | i <;> rcases j with j | j <;> simp at hij ⊢

def fstBlock (hN : r + t = N) {b : Fin N → ℕ} (hb : IsTwoBlock r b) : levi k b →* GL (Fin r) k :=
  leviBlock b (fun i => twoEquiv hN (Sum.inl i)) (fun _ _ e => Sum.inl_injective ((twoEquiv hN).injective e))
    fun i j hij => by
      obtain ⟨j | j, rfl⟩ := (twoEquiv hN).surjective j
      · exact ⟨j, rfl⟩
      · rw [hb] at hij; simp at hij

def sndBlock (hN : r + t = N) {b : Fin N → ℕ} (hb : IsTwoBlock r b) : levi k b →* GL (Fin t) k :=
  leviBlock b (fun i => twoEquiv hN (Sum.inr i)) (fun _ _ e => Sum.inr_injective ((twoEquiv hN).injective e))
    fun i j hij => by
      obtain ⟨j | j, rfl⟩ := (twoEquiv hN).surjective j
      · rw [hb] at hij; simp at hij
      · exact ⟨j, rfl⟩

def leviTwo (hN : r + t = N) {b : Fin N → ℕ} (hb : IsTwoBlock r b) : levi k b ≃* GL (Fin r) k × GL (Fin t) k :=
  MonoidHom.toMulEquiv ((fstBlock hN hb).prod (sndBlock hN hb)) (twoDiagHom hN hb)
    (by
      ext g i j
      obtain ⟨i, rfl⟩ := (twoEquiv hN).surjective i
      obtain ⟨j, rfl⟩ := (twoEquiv hN).surjective j
      show Matrix.fromBlocks (fstBlock hN hb g : Matrix (Fin r) (Fin r) k) 0 0 (sndBlock hN hb g : Matrix (Fin t) (Fin t) k)
        ((twoEquiv hN).symm (twoEquiv hN i)) ((twoEquiv hN).symm (twoEquiv hN j)) = _
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · exact (g.2 _ _ (by rw [ne_eq, hb]; simp)).symm
      · exact (g.2 _ _ (by rw [ne_eq, hb]; simp)).symm
      · rfl)
    (by
      refine MonoidHom.ext fun x => Prod.ext (Units.ext ?_) (Units.ext ?_)
      · ext i j
        show Matrix.fromBlocks (x.1 : Matrix (Fin r) (Fin r) k) 0 0 (x.2 : Matrix (Fin t) (Fin t) k)
          ((twoEquiv hN).symm (twoEquiv hN (Sum.inl i))) ((twoEquiv hN).symm (twoEquiv hN (Sum.inl j))) = _
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rfl
      · ext i j
        show Matrix.fromBlocks (x.1 : Matrix (Fin r) (Fin r) k) 0 0 (x.2 : Matrix (Fin t) (Fin t) k)
          ((twoEquiv hN).symm (twoEquiv hN (Sum.inr i))) ((twoEquiv hN).symm (twoEquiv hN (Sum.inr j))) = _
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        rfl)

end Blocks

section General

variable {G H : Type} [Group G] [Group H] {V W X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

theorem mem_fixed {ρ : Representation ℂ G V} {U : Subgroup G} {v : V} : v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  constructor
  · intro h u hu
    simpa using h ⟨u, hu⟩
  · intro h u
    simpa using h u u.2

theorem bijective_fixed_mkQ (ρ : Representation ℂ G V) (U : Subgroup G) [Finite U] :
    Function.Bijective ((twKer ρ U 1).mkQ ∘ₗ (fixed ρ U).subtype) := by
  classical
  letI := Fintype.ofFinite U
  have hc : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let S : V →ₗ[ℂ] V := ∑ u : U, ρ u
  have hS : ∀ v, S v = ∑ u : U, ρ u v := fun v => LinearMap.sum_apply _ _ _
  have hker : twKer ρ U 1 ≤ LinearMap.ker S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, SetLike.mem_coe, LinearMap.mem_ker]
    rw [map_sub, hS, hS, sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.mulRight n) _ _ fun u => by simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : S v = 0 := hker ((Submodule.Quotient.mk_eq_zero _).1 hv)
    rw [hS, Finset.sum_congr rfl fun (u : U) _ => mem_fixed.1 v.2 u u.2, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ] at h1
    exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left hc)
  · intro q
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ q
    have hf : (Fintype.card U : ℂ)⁻¹ • S v ∈ fixed ρ U := by
      refine Submodule.smul_mem _ _ (mem_fixed.2 fun n hn => ?_)
      rw [hS, map_sum]
      exact Fintype.sum_equiv (Equiv.mulLeft (⟨n, hn⟩ : U)) _ _ fun u => by simp
    refine ⟨⟨_, hf⟩, ?_⟩
    show (twKer ρ U 1).mkQ ((Fintype.card U : ℂ)⁻¹ • S v) = _
    have h2 : ∀ u : U, (twKer ρ U 1).mkQ (ρ u v) = (twKer ρ U 1).mkQ v := fun u =>
      (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨u, v, by simp⟩)
    rw [map_smul, hS, map_sum, Finset.sum_congr rfl fun u _ => h2 u, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

def Embeds (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ f : ρ.IntertwiningMap σ, Function.Injective f

theorem Embeds.refl (ρ : Representation ℂ G V) : Embeds ρ ρ := ⟨.id ρ, fun _ _ h => h⟩

theorem Embeds.trans {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}
    (h : Embeds ρ σ) (h' : Embeds σ τ) : Embeds ρ τ := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := h'
  exact ⟨g.comp f, hg.comp hf⟩

theorem Embeds.of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) : Embeds ρ σ :=
  ⟨e.toIntertwiningMap, e.toLinearEquiv.injective⟩

theorem isIrreducible_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact IsSimpleModule.congr (LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ e.symm.toIntertwiningMap) e.symm.toLinearEquiv.bijective)

def extTprod (ρ : Representation ℂ G V) (σ : Representation ℂ H W) : Representation ℂ (G × H) (V ⊗[ℂ] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

@[simp] theorem extTprod_tmul (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (x : G × H) (v : V) (w : W) :
    extTprod ρ σ x (v ⊗ₜ w) = ρ x.1 v ⊗ₜ σ x.2 w := rfl

def extTensor {ι : Type} {Γ Y : ι → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (ρ : ∀ a, Representation ℂ (Γ a) (Y a)) : Representation ℂ (∀ a, Γ a) (⨂[ℂ] a, Y a) :=
  PiTensorProduct.mapMonoidHom.comp (Pi.monoidHom fun a => (ρ a).comp (Pi.evalMonoidHom Γ a))

@[simp] theorem extTensor_tprod {ι : Type} {Γ Y : ι → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (Y a)) (x : ∀ a, Γ a) (v : ∀ a, Y a) :
    extTensor ρ x (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun a => ρ a (x a) (v a) :=
  PiTensorProduct.map_tprod _ _

variable (G) in

def isoSetoid : Setoid (FDRep ℂ G) where
  r A B := Nonempty (Representation.Equiv A.ρ B.ρ)
  iseqv := ⟨fun _ => ⟨.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

variable (G) in

def RepClass : Type 1 := Quotient (isoSetoid G)

def cls [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : RepClass G := Quotient.mk (isoSetoid G) (FDRep.of ρ)

theorem cls_eq_iff [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) : cls ρ = cls σ ↔ Nonempty (ρ.Equiv σ) :=
  Quotient.eq (r := isoSetoid G)

end General

section Functors

variable {k : Type} [Field k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def hcRes (b : Fin N → ℕ) (ρ : Representation ℂ (GL (Fin N) k) V) :
    Representation ℂ (levi k b) (fixed ρ (unipRadical k b)) :=
  onFixed ρ (unipRadical k b) (levi k b).subtype fun m => blockTri_le_normalizer b (levi_le_blockTri b m.2)

@[simp] theorem hcRes_apply (b : Fin N → ℕ) (ρ : Representation ℂ (GL (Fin N) k) V) (m : levi k b)
    (v : fixed ρ (unipRadical k b)) : (hcRes b ρ m v : V) = ρ m v := rfl

def hcCoinv (b : Fin N → ℕ) (ρ : Representation ℂ (GL (Fin N) k) V) :
    Representation ℂ (levi k b) (Jacquet ρ (unipRadical k b)) :=
  jacquet ρ (unipRadical k b) (levi k b).subtype fun m => blockTri_le_normalizer b (levi_le_blockTri b m.2)

def hcResEquivCoinv [Finite k] (b : Fin N → ℕ) (ρ : Representation ℂ (GL (Fin N) k) V) :
    (hcRes b ρ).Equiv (hcCoinv b ρ) :=
  Representation.Equiv.mk (LinearEquiv.ofBijective _ (bijective_fixed_mkQ ρ (unipRadical k b))) fun _ => rfl

def inflate (b : Fin N → ℕ) (σ : Representation ℂ (levi k b) W) : Representation ℂ (blockTri (κ := k) b) W :=
  σ.comp (leviProj b)

@[simp] theorem inflate_apply (b : Fin N → ℕ) (σ : Representation ℂ (levi k b) W) (p : blockTri (κ := k) b) :
    inflate b σ p = σ (leviProj b p) := rfl

abbrev IndSpace (b : Fin N → ℕ) (σ : Representation ℂ (levi k b) W) : Submodule ℂ (GL (Fin N) k → W) :=
  Representation.coindV (blockTri (κ := k) b).subtype (inflate b σ)

theorem mem_indSpace {b : Fin N → ℕ} {σ : Representation ℂ (levi k b) W} {f : GL (Fin N) k → W} :
    f ∈ IndSpace b σ ↔ ∀ (p : blockTri (κ := k) b) (g : GL (Fin N) k), f (p * g) = σ (leviProj b p) (f g) := Iff.rfl

def hcInd (b : Fin N → ℕ) (σ : Representation ℂ (levi k b) W) : Representation ℂ (GL (Fin N) k) (IndSpace b σ) :=
  GlobalTheory.FinGL.parInd b (inflate b σ)

@[simp] theorem hcInd_apply (b : Fin N → ℕ) (σ : Representation ℂ (levi k b) W) (g x : GL (Fin N) k)
    (f : IndSpace b σ) : (hcInd b σ g f : GL (Fin N) k → W) x = (f : GL (Fin N) k → W) (x * g) := rfl

def hcResMap (b : Fin N → ℕ) {ρ : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (f : ρ.IntertwiningMap σ) : (hcRes b ρ).IntertwiningMap (hcRes b σ) where
  toLinearMap := f.toLinearMap.restrict fun v hv => mem_fixed.2 fun u hu => by
    rw [f.toLinearMap_apply, ← f.isIntertwining, mem_fixed.1 hv u hu]
  isIntertwining' m := LinearMap.ext fun v => Subtype.ext (f.isIntertwining _ _ (m : GL (Fin N) k) (v : V))

@[simp] theorem hcResMap_apply (b : Fin N → ℕ) {ρ : Representation ℂ (GL (Fin N) k) V}
    {σ : Representation ℂ (GL (Fin N) k) W} (f : ρ.IntertwiningMap σ) (v : fixed ρ (unipRadical k b)) :
    (hcResMap b f v : W) = f v := rfl

def hcIndMap (b : Fin N → ℕ) {ρ : Representation ℂ (levi k b) V} {σ : Representation ℂ (levi k b) W}
    (f : ρ.IntertwiningMap σ) : (hcInd b ρ).IntertwiningMap (hcInd b σ) :=
  Representation.coindMap (blockTri (κ := k) b).subtype
    (⟨f.toLinearMap, fun p => f.isIntertwining' (leviProj b p)⟩ : (inflate b ρ).IntertwiningMap (inflate b σ))

@[simp] theorem hcIndMap_apply (b : Fin N → ℕ) {ρ : Representation ℂ (levi k b) V} {σ : Representation ℂ (levi k b) W}
    (f : ρ.IntertwiningMap σ) (φ : IndSpace b ρ) (x : GL (Fin N) k) :
    (hcIndMap b f φ : GL (Fin N) k → W) x = f ((φ : GL (Fin N) k → V) x) := rfl

theorem Embeds.hcRes (b : Fin N → ℕ) {ρ : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (h : Embeds ρ σ) : Embeds (hcRes b ρ) (hcRes b σ) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨hcResMap b f, fun _ _ e => Subtype.ext (hf (congrArg Subtype.val e))⟩

theorem Embeds.hcInd (b : Fin N → ℕ) {ρ : Representation ℂ (levi k b) V} {σ : Representation ℂ (levi k b) W}
    (h : Embeds ρ σ) : Embeds (hcInd b ρ) (hcInd b σ) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨hcIndMap b f, fun _ _ e => Subtype.ext (funext fun x => hf (congrFun (congrArg Subtype.val e) x))⟩

def toHcInd (b : Fin N → ℕ) (ρ : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (levi k b) W) (L : V →ₗ[ℂ] W)
    (hL : ∀ (p : blockTri (κ := k) b) (v : V), L (ρ p v) = σ (leviProj b p) (L v)) : ρ.IntertwiningMap (hcInd b σ) where
  toLinearMap := (LinearMap.pi fun g => L ∘ₗ ρ g).codRestrict (IndSpace b σ) fun v => mem_indSpace.2 fun p g => by
    simp [hL]
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext (funext fun x => by
    show L (ρ x (ρ g v)) = L (ρ (x * g) v)
    simp)

@[simp] theorem toHcInd_apply (b : Fin N → ℕ) (ρ : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (levi k b) W)
    (L : V →ₗ[ℂ] W) (hL : ∀ (p : blockTri (κ := k) b) (v : V), L (ρ p v) = σ (leviProj b p) (L v)) (v : V)
    (x : GL (Fin N) k) : (toHcInd b ρ σ L hL v : GL (Fin N) k → W) x = L (ρ x v) := rfl

theorem toHcInd_injective (b : Fin N → ℕ) (ρ : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (levi k b) W)
    (L : V →ₗ[ℂ] W) (hL : ∀ (p : blockTri (κ := k) b) (v : V), L (ρ p v) = σ (leviProj b p) (L v))
    (hi : Function.Injective L) : Function.Injective (toHcInd b ρ σ L hL) := fun v w e => by
  have h := congrFun (congrArg Subtype.val e) 1
  simp only [toHcInd_apply, map_one, Module.End.one_apply] at h
  exact hi h

def relRes (a c : Fin N → ℕ) (ρ : Representation ℂ (levi k a) V) :
    Representation ℂ ↥(levi k a ⊓ levi k c) (fixed ρ ((unipRadical k c).subgroupOf (levi k a))) :=
  onFixed ρ _ (Subgroup.inclusion inf_le_left) (inclusion_mem_normalizer a c)

@[simp] theorem relRes_apply (a c : Fin N → ℕ) (ρ : Representation ℂ (levi k a) V) (m : ↥(levi k a ⊓ levi k c))
    (v : fixed ρ ((unipRadical k c).subgroupOf (levi k a))) : (relRes a c ρ m v : V) = ρ ⟨m, m.2.1⟩ v := rfl

abbrev RelIndSpace (a c : Fin N → ℕ) (σ : Representation ℂ ↥(levi k a ⊓ levi k c) W) : Submodule ℂ (levi k a → W) :=
  Representation.coindV ((blockTri (κ := k) c).subgroupOf (levi k a)).subtype (σ.comp (relProj a c))

def relInd (a c : Fin N → ℕ) (σ : Representation ℂ ↥(levi k a ⊓ levi k c) W) :
    Representation ℂ (levi k a) (RelIndSpace a c σ) :=
  Representation.coind ((blockTri (κ := k) c).subgroupOf (levi k a)).subtype (σ.comp (relProj a c))

@[simp] theorem relInd_apply (a c : Fin N → ℕ) (σ : Representation ℂ ↥(levi k a ⊓ levi k c) W) (g x : levi k a)
    (f : RelIndSpace a c σ) : (relInd a c σ g f : levi k a → W) x = (f : levi k a → W) (x * g) := rfl

def relTwist (a b : Fin N → ℕ) (w : Equiv.Perm (Fin N)) (σ : Representation ℂ ↥(levi k a ⊓ levi k (b ∘ w.symm)) W) :
    Representation ℂ ↥(levi k b ⊓ levi k (a ∘ w)) W :=
  σ.comp (relConj a b w).toMonoidHom

@[simp] theorem relTwist_apply (a b : Fin N → ℕ) (w : Equiv.Perm (Fin N))
    (σ : Representation ℂ ↥(levi k a ⊓ levi k (b ∘ w.symm)) W) (x : ↥(levi k b ⊓ levi k (a ∘ w))) :
    relTwist a b w σ x = σ (relConj a b w x) := rfl

instance [Finite k] [FiniteDimensional ℂ W] (b : Fin N → ℕ) (σ : Representation ℂ (levi k b) W) :
    FiniteDimensional ℂ (IndSpace b σ) := inferInstance

variable {h : ℕ} {d : Fin h → ℕ} {Y : Fin h → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

def leviTensor (e : (Σ a, Fin (d a)) ≃ Fin N) (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a)) :
    Representation ℂ (levi k (blockOf e)) (⨂[ℂ] a, Y a) :=
  (extTensor ρ).comp (leviEquiv e).toMonoidHom

@[simp] theorem leviTensor_tprod (e : (Σ a, Fin (d a)) ≃ Fin N) (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (m : levi k (blockOf e)) (v : ∀ a, Y a) :
    leviTensor e ρ m (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun a => ρ a (leviEquiv e m a) (v a) :=
  extTensor_tprod _ _ _

def prodInd (d : Fin h → ℕ) (hd : ∑ a, d a = N) (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a)) :
    Representation ℂ (GL (Fin N) k) (IndSpace (blockOf (stdEquiv d hd)) (leviTensor (stdEquiv d hd) ρ)) :=
  hcInd _ (leviTensor (stdEquiv d hd) ρ)

def prodRes (d : Fin h → ℕ) (hd : ∑ a, d a = N) (ρ : Representation ℂ (GL (Fin N) k) V) :
    Representation ℂ (∀ a, GL (Fin (d a)) k) (fixed ρ (unipRadical k (blockOf (stdEquiv d hd)))) :=
  (hcRes _ ρ).comp (leviEquiv (stdEquiv d hd)).symm.toMonoidHom

variable {r t : ℕ}

def twoInd (hN : r + t = N) {b : Fin N → ℕ} (hb : IsTwoBlock r b) (σ : Representation ℂ (GL (Fin r) k × GL (Fin t) k) W) :
    Representation ℂ (GL (Fin N) k) (IndSpace b (σ.comp (leviTwo hN hb).toMonoidHom)) :=
  hcInd b _

def twoRes (hN : r + t = N) {b : Fin N → ℕ} (hb : IsTwoBlock r b) (ρ : Representation ℂ (GL (Fin N) k) V) :
    Representation ℂ (GL (Fin r) k × GL (Fin t) k) (fixed ρ (unipRadical k b)) :=
  (hcRes b ρ).comp (leviTwo hN hb).symm.toMonoidHom

end Functors

section Cuspidal

variable {k : Type} [Field k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fixed_eq_bot_iff {ρ : Representation ℂ (GL (Fin N) k) V} {U : Subgroup (GL (Fin N) k)} :
    fixed ρ U = ⊥ ↔ ∀ v : V, (∀ u ∈ U, ρ u v = v) → v = 0 := by
  simp only [Submodule.eq_bot_iff, mem_fixed]

theorem isCuspidal_iff_forall (ρ : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal ρ ↔ ∀ b : Fin N → ℕ, (∃ i j, b i ≠ b j) → fixed ρ (unipRadical k b) = ⊥ := by
  refine ⟨fun h b ⟨i, j, hij⟩ => fixed_eq_bot_iff.2 fun v hv => ?_, fun h b _ hb => fixed_eq_bot_iff.1 (h b hb)⟩
  set w := Tuple.sort b
  have h0 : ρ (permGL k w)⁻¹ v = 0 := by
    refine h (b ∘ w) (Tuple.monotone_sort b) ⟨w.symm i, w.symm j, by simpa using hij⟩ _ fun u hu => ?_
    conv_rhs => rw [← hv _ (conj_mem_unipRadical.2 hu)]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have h1 := congrArg (ρ (permGL k w)) h0
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero, Module.End.one_apply] at h1

theorem Embeds.isCuspidal {ρ : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (h : Embeds ρ σ) (hσ : IsCuspidal σ) : IsCuspidal ρ := by
  obtain ⟨f, hf⟩ := h
  intro b hb hne v hv
  refine hf ?_
  rw [map_zero]
  exact hσ b hb hne _ fun u hu => by rw [← f.isIntertwining, hv u hu]

variable (k) in

abbrev GradedClass : Type 1 := Σ n : ℕ, RepClass (GL (Fin n) k)

def classes {h : ℕ} {d : Fin h → ℕ} {Y : Fin h → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    [∀ a, FiniteDimensional ℂ (Y a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a)) : Multiset (GradedClass k) :=
  Finset.univ.val.map fun a => ⟨d a, cls (ρ a)⟩

def HasCuspSupport (κ : Representation ℂ (GL (Fin N) k) V) (s : Multiset (GradedClass k)) : Prop :=
  κ.IsIrreducible ∧ ∃ (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (Y : Fin h → Type) (_ : ∀ a, AddCommGroup (Y a))
    (_ : ∀ a, Module ℂ (Y a)) (_ : ∀ a, FiniteDimensional ℂ (Y a)) (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a)),
    (∀ a, 0 < d a) ∧ (∀ a, (ρ a).IsIrreducible) ∧ (∀ a, IsCuspidal (ρ a)) ∧ Embeds κ (prodInd d hd ρ) ∧ s = classes ρ

theorem HasCuspSupport.sum_fst {κ : Representation ℂ (GL (Fin N) k) V} {s : Multiset (GradedClass k)}
    (h : HasCuspSupport κ s) : (s.map Sigma.fst).sum = N := by
  obtain ⟨-, h, d, hd, Y, _, _, _, ρ, -, -, -, -, rfl⟩ := h
  rw [classes, Multiset.map_map]
  exact hd

theorem HasCuspSupport.of_mem {κ : Representation ℂ (GL (Fin N) k) V} {s : Multiset (GradedClass k)}
    (h : HasCuspSupport κ s) {n : ℕ} [FiniteDimensional ℂ W] {σ : Representation ℂ (GL (Fin n) k) W}
    (hσ : (⟨n, cls σ⟩ : GradedClass k) ∈ s) : 0 < n ∧ σ.IsIrreducible ∧ IsCuspidal σ := by
  obtain ⟨-, h, d, hd, Y, _, _, _, ρ, hpos, hi, hc, -, rfl⟩ := h
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 hσ
  obtain rfl : d a = n := congrArg Sigma.fst ha
  obtain ⟨e⟩ := (cls_eq_iff _ _).1 (sigma_mk_injective (β := fun n => RepClass (GL (Fin n) k)) ha)
  exact ⟨hpos a, isIrreducible_of_equiv e (hi a), (Embeds.of_equiv e.symm).isCuspidal (hc a)⟩

theorem HasCuspSupport.of_equiv {κ : Representation ℂ (GL (Fin N) k) V} {κ' : Representation ℂ (GL (Fin N) k) W}
    {s : Multiset (GradedClass k)} (h : HasCuspSupport κ s) (e : κ.Equiv κ') : HasCuspSupport κ' s := by
  obtain ⟨hκ, h, d, hd, Y, _, _, _, ρ, hpos, hi, hc, he, rfl⟩ := h
  exact ⟨isIrreducible_of_equiv e hκ, h, d, hd, Y, _, _, _, ρ, hpos, hi, hc, (Embeds.of_equiv e.symm).trans he, rfl⟩

def detRep (N : ℕ) (χ : kˣ →* ℂˣ) : Representation ℂ (GL (Fin N) k) (Fin 1 → ℂ) :=
  lineRep ((Units.coeHom ℂ).comp (χ.comp Matrix.GeneralLinearGroup.det))

theorem hasCuspSupport_self [FiniteDimensional ℂ V] (hN : 0 < N) {κ : Representation ℂ (GL (Fin N) k) V}
    (hi : κ.IsIrreducible) (hc : IsCuspidal κ) : HasCuspSupport κ {⟨N, cls κ⟩} := by
  have hd : ∑ _ : Fin 1, N = N := by simp
  refine ⟨hi, 1, fun _ => N, hd, fun _ => V, inferInstance, inferInstance, inferInstance, fun _ => κ, fun _ => hN,
    fun _ => hi, fun _ => hc, ?_, by simp [classes]⟩
  let L := (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0).symm
  have hL : ∀ v, L v = PiTensorProduct.tprod ℂ fun _ => v := fun v => by
    rw [LinearEquiv.symm_apply_eq]
    simp
  refine ⟨toHcInd _ κ _ L.toLinearMap fun p v => ?_, toHcInd_injective _ _ _ _ _ L.injective⟩
  rw [LinearEquiv.coe_coe, hL, hL, leviTensor_tprod]
  congr 1
  funext a
  congr 2
  apply Units.ext
  ext i j
  have he : ∀ i : Fin N, stdEquiv (fun _ : Fin 1 => N) hd ⟨a, i⟩ = i := fun i => Fin.ext (by
    rw [stdEquiv_val, Subsingleton.elim a 0]
    simp)
  rw [leviEquiv_apply, leviProj_apply, blockOf_apply, blockOf_apply, if_pos rfl, he, he]

example : HasCuspSupport (lineRep signGL₂) {⟨2, cls (lineRep signGL₂)⟩} :=
  hasCuspSupport_self two_pos signGL₂_cuspidal.1 signGL₂_cuspidal.2

example {κ : Representation ℂ (GL (Fin N) k) V} {s : Multiset (GradedClass k)} (h : HasCuspSupport κ s) :
    (⟨2, cls (Representation.trivial ℂ (GL (Fin 2) k) ℂ)⟩ : GradedClass k) ∉ s :=
  fun hm => not_isCuspidal_trivial le_rfl (h.of_mem hm).2.2

example (hd : ∑ a, (![1, 1] : Fin 2 → ℕ) a = 2) :
    transvGL₂ ∈ unipRadical (ZMod 2) (blockOf (stdEquiv ![1, 1] hd)) ∧
      transvGL₂ ∉ unipRadical (ZMod 2) (oppTwoBlocks 2 1) := by
  rw [blockOf_stdEquiv_two, mem_unipRadical, mem_unipRadical]
  refine ⟨fun i j hij => ?_, fun h => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [transvGL₂, twoBlocks] at hij ⊢
  · simpa [transvGL₂] using h 0 1 (by simp [oppTwoBlocks])

example : ((permGL ℚ (finRotate 3) : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) 1 0 = 1 := by
  rw [permGL_apply]; simp

end Cuspidal

end GlobalTheory.Parabolic
