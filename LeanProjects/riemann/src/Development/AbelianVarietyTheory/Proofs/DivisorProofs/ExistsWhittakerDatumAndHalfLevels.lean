import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount.Inh

variable {A : Type} [CommRing A] {n : ℕ}

theorem isUniUp_one : IsUniUp (1 : Matrix (Fin n) (Fin n) A) := by
  intro a b
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => ?_⟩
  subst h; exact Matrix.one_apply_eq a

theorem diag_mul_of_tri {M N : Matrix (Fin n) (Fin n) A} (hM : ∀ a c : Fin n, c < a → M a c = 0)
    (hN : ∀ a c : Fin n, c < a → N a c = 0) (a : Fin n) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hM a c h, zero_mul]
    · rw [hN c a h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem isUniUp_mul {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) : IsUniUp (M * N) := by
  intro a b
  constructor
  · intro hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [(hM a c).1 h, zero_mul]
    · rw [(hN c b).1 (lt_of_lt_of_le hba h), mul_zero]
  · rintro rfl
    rw [diag_mul_of_tri (fun a c h => (hM a c).1 h) (fun a c h => (hN a c).1 h), (hM a a).2 rfl, (hN a a).2 rfl, one_mul]

theorem isUniUp_inv (u : GL (Fin n) A) (hu : IsUniUp (u : Matrix (Fin n) (Fin n) A)) :
    IsUniUp ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  have hb : Matrix.BlockTriangular (u : Matrix (Fin n) (Fin n) A) id := fun i j h => (hu i j).1 h
  have hinv : Matrix.BlockTriangular ((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) id := by
    rw [Matrix.coe_units_inv]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  intro a b
  refine ⟨fun h => hinv h, ?_⟩
  rintro rfl
  have h1 : (((u⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * (u : Matrix (Fin n) (Fin n) A)) a a = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [diag_mul_of_tri (fun a c h => hinv h) (fun a c h => hb h), (hu a a).2 rfl, mul_one] at h1
  exact h1

def uniUpGL : Subgroup (GL (Fin n) A) where
  carrier := {u | IsUniUp (u : Matrix (Fin n) (Fin n) A)}
  mul_mem' := fun {a b} ha hb => by
    rw [Set.mem_setOf_eq, Units.val_mul]; exact isUniUp_mul ha hb
  one_mem' := by rw [Set.mem_setOf_eq, Units.val_one]; exact isUniUp_one
  inv_mem' := fun {u} hu => isUniUp_inv u hu

theorem mem_uniUpGL (u : GL (Fin n) A) : u ∈ (uniUpGL : Subgroup (GL (Fin n) A)) ↔ IsUniUp (u : Matrix (Fin n) (Fin n) A) :=
  Iff.rfl

def sd (M : Matrix (Fin n) (Fin n) A) : A := ∑ i ∈ Finset.range (n - 1), entN M i (i + 1)

theorem entN_mul_super {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) {i : ℕ} (hi : i + 1 < n) :
    entN (M * N) i (i + 1) = entN M i (i + 1) + entN N i (i + 1) := by
  have h0 : i < n := by omega
  simp only [entN, dif_pos (And.intro h0 hi)]
  rw [Matrix.mul_apply, Fintype.sum_eq_add (⟨i, h0⟩ : Fin n) ⟨i + 1, hi⟩]
  · rw [(hM _ _).2 rfl, (hN _ _).2 rfl, one_mul, mul_one, add_comm]
  · simp [Fin.ext_iff]
  · rintro c ⟨h1, h2⟩
    have h1' : c.val ≠ i := fun h => h1 (Fin.ext h)
    have h2' : c.val ≠ i + 1 := fun h => h2 (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne h1' with h | h
    · rw [(hM ⟨i, h0⟩ c).1 (by change c.val < i; omega), zero_mul]
    · rw [(hN c ⟨i + 1, hi⟩).1 (by change i + 1 < c.val; omega), mul_zero]

theorem sd_mul {M N : Matrix (Fin n) (Fin n) A} (hM : IsUniUp M) (hN : IsUniUp N) : sd (M * N) = sd M + sd N := by
  unfold sd
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => entN_mul_super hM hN ?_
  have := Finset.mem_range.1 hi; omega

theorem sd_one : sd (1 : Matrix (Fin n) (Fin n) A) = 0 := by
  unfold sd
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold entN
  split_ifs with h
  · exact Matrix.one_apply_ne (fun e => by simpa using congrArg Fin.val e)
  · rfl

variable (D : D7)

def whitP : Subgroup (G0g D.nd) := Subgroup.pi Set.univ fun _ => uniUpGL

theorem mem_whitP (g : G0g D.nd) :
    g ∈ whitP D ↔ ∀ kv, IsUniUp (g kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  rw [whitP, Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_uniUpGL]

def whitChar (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) : whitP D →* ℂ where
  toFun g := ∏ kv, ψ kv (sd ((g : G0g D.nd) kv : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))
  map_one' := by
    refine Finset.prod_eq_one fun kv _ => ?_
    simp [sd_one]
  map_mul' g h := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [← AddChar.map_add_eq_mul, ← sd_mul ((mem_whitP D _).1 g.2 kv) ((mem_whitP D _).1 h.2 kv)]
    rfl

def halfH (k : Fin 2) : Subgroup (G0g D.nd) := Subgroup.pi {kv | kv.1 ≠ k} fun _ => uniUpGL

theorem isHalf_halfH (k : Fin 2) : IsHalf D k (halfH D k) := by
  intro g
  rw [halfH, Subgroup.mem_pi]
  simp only [Set.mem_setOf_eq, mem_uniUpGL]

theorem isWhit_whitP (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (hψ : ∀ kv, ψ kv ≠ 1) :
    IsWhit D (whitP D) (whitChar D ψ).toHomUnits ψ :=
  ⟨hψ, mem_whitP D, fun _ => rfl⟩

theorem exists_whit_half : ∀ (D : D7) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ),
    (∀ kv, ψ kv ≠ 1) → (∃ (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ), IsWhit D P lam ψ) ∧ ∀ k, ∃ H, IsHalf D k H :=
  fun D ψ hψ => ⟨⟨whitP D, _, isWhit_whitP D ψ hψ⟩, fun k => ⟨halfH D k, isHalf_halfH D k⟩⟩

end GlobalTheory.BadCount.Inh
