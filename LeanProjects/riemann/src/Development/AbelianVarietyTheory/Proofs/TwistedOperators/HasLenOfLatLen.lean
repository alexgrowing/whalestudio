import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

noncomputable section

open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section Len

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def IsInt {ι κ : Type} (M : Matrix ι κ L) : Prop := ∀ i j, M i j ∈ intL L

theorem IsInt.mul {ι κ μ : Type} [Fintype κ] {M : Matrix ι κ L} {N : Matrix κ μ L} (hM : IsInt M) (hN : IsInt N) :
    IsInt (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => mul_mem (hM i k) (hN k j)

theorem IsInt.add {ι κ : Type} {M N : Matrix ι κ L} (hM : IsInt M) (hN : IsInt N) : IsInt (M + N) :=
  fun i j => add_mem (hM i j) (hN i j)

theorem isInt_one {ι : Type} [DecidableEq ι] : IsInt (1 : Matrix ι ι L) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem isInt_zero {ι κ : Type} : IsInt (0 : Matrix ι κ L) := fun _ _ => zero_mem _

theorem IsInt.v_det_le {M : Matrix (Fin n) (Fin n) L} (hM : IsInt M) : Valued.v M.det ≤ 1 :=
  P.cartan_det_mem (intL L) M hM

def IsFrac (g U V C : Matrix (Fin n) (Fin n) L) : Prop :=
  IsInt U ∧ IsInt V ∧ IsInt C ∧ IsInt (g * C) ∧ (U + V * g) * C = 1

def HasLen (g : Matrix (Fin n) (Fin n) L) (k : ℕ) : Prop :=
  ∃ U V C, IsFrac g U V C ∧ Valued.v C.det = WithZero.exp (-(k : ℤ))

def len (g : Matrix (Fin n) (Fin n) L) : ℕ := sInf {k | HasLen g k}

theorem IsFrac.v_det_le {g U V C U' V' C' : Matrix (Fin n) (Fin n) L} (h : IsFrac g U V C) (h' : IsFrac g U' V' C') :
    Valued.v C'.det ≤ Valued.v C.det := by
  have e : C' = C * (U * C' + V * (g * C')) := by
    rw [← Matrix.mul_assoc V, ← Matrix.add_mul, ← Matrix.mul_assoc, mul_eq_one_comm.1 h.2.2.2.2, Matrix.one_mul]
  rw [e, Matrix.det_mul, map_mul]
  exact mul_le_of_le_one_right' ((h.1.mul h'.2.2.1).add (h.2.1.mul h'.2.2.2.1)).v_det_le

theorem HasLen.unique {g : Matrix (Fin n) (Fin n) L} {k k' : ℕ} (h : HasLen g k) (h' : HasLen g k') : k = k' := by
  obtain ⟨U, V, C, h, e⟩ := h
  obtain ⟨U', V', C', h', e'⟩ := h'
  have := le_antisymm (h.v_det_le h') (h'.v_det_le h)
  rw [e, e', WithZero.exp_inj] at this
  omega

theorem HasLen.len_eq {g : Matrix (Fin n) (Fin n) L} {k : ℕ} (h : HasLen g k) : len g = k :=
  HasLen.unique (Nat.sInf_mem (s := {k | HasLen g k}) ⟨k, h⟩) h

theorem hasLen_of_isInt {g : Matrix (Fin n) (Fin n) L} (hg : IsInt g) : HasLen g 0 :=
  ⟨1, 0, 1, ⟨isInt_one, isInt_zero, isInt_one, by simpa using hg, by simp⟩, by simp⟩

theorem v_det_eq_one {a a' : Matrix (Fin n) (Fin n) L} (ha : IsInt a) (ha' : IsInt a') (e : a * a' = 1) :
    Valued.v a.det = 1 := by
  obtain ⟨U, hU, rfl⟩ := P.cartan_exists_glint (intL L) a a' e ha ha'
  exact P.cartan_val_det (intL L) Valued.v (fun _ => Iff.rfl) U hU

theorem HasLen.mul_mul {g a a' b b' : Matrix (Fin n) (Fin n) L} {k : ℕ} (h : HasLen g k) (ha : IsInt a)
    (ha' : IsInt a') (hb : IsInt b) (hb' : IsInt b') (ea : a' * a = 1) (eb : b * b' = 1) : HasLen (a * g * b) k := by
  obtain ⟨U, V, C, ⟨h1, h2, h3, h4, h5⟩, e⟩ := h
  refine ⟨U * b, V * a', b' * C, ⟨h1.mul hb, h2.mul ha', hb'.mul h3, ?_, ?_⟩, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc b, eb, Matrix.one_mul, Matrix.mul_assoc]
    exact ha.mul h4
  · calc _ = (U + V * (a' * a) * g) * (b * b') * C := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [ea, eb, Matrix.mul_one, Matrix.mul_one, h5]
  · rw [Matrix.det_mul, map_mul, v_det_eq_one hb' hb (mul_eq_one_comm.1 eb), one_mul, e]

theorem len_mul_mul {g a a' b b' : Matrix (Fin n) (Fin n) L} (ha : IsInt a)
    (ha' : IsInt a') (hb : IsInt b) (hb' : IsInt b') (ea : a' * a = 1) (eb : b * b' = 1) : len (a * g * b) = len g := by
  unfold len
  congr 1
  ext k
  refine ⟨fun h => ?_, fun h => HasLen.mul_mul h ha ha' hb hb' ea eb⟩
  have := HasLen.mul_mul h ha' ha hb' hb (mul_eq_one_comm.1 ea) (mul_eq_one_comm.1 eb)
  rwa [show a' * (a * g * b) * b' = (a' * a) * g * (b * b') by simp only [Matrix.mul_assoc], ea, eb, Matrix.one_mul,
    Matrix.mul_one] at this

theorem len_mat_mul {σ : L →+* L} {a b : GU σ n} (ha : a ∈ KU σ n) (hb : b ∈ KU σ n) (g : GU σ n) :
    len (mat (a * g * b)) = len (mat g) :=
  len_mul_mul (P.fSatake_K_int ha) (P.fSatake_K_int (inv_mem ha)) (P.fSatake_K_int hb) (P.fSatake_K_int (inv_mem hb))
    (mat_inv_mul a) (mat_mul_inv b)

def rowLat {ι : Type} (M : Matrix ι (Fin n) L) : Submodule (intL L) (Fin n → L) :=
  Submodule.span (intL L) (Set.range fun i => M i)

theorem row_mem_rowLat {ι : Type} (M : Matrix ι (Fin n) L) (i : ι) : M i ∈ rowLat M :=
  Submodule.subset_span ⟨i, rfl⟩

theorem mem_rowLat {ι : Type} [Fintype ι] {M : Matrix ι (Fin n) L} {w : Fin n → L} :
    w ∈ rowLat M ↔ ∃ ρ : ι → L, (∀ i, ρ i ∈ intL L) ∧ w = ρ ᵥ* M := by
  rw [rowLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (c i).2, by rw [Matrix.vecMul_eq_sum]; rfl⟩
  · rintro ⟨ρ, h, rfl⟩
    exact ⟨fun i => ⟨ρ i, h i⟩, by rw [Matrix.vecMul_eq_sum]; rfl⟩

theorem rowLat_le {ι : Type} {M : Matrix ι (Fin n) L} {R : Submodule (intL L) (Fin n → L)} :
    rowLat M ≤ R ↔ ∀ i, M i ∈ R := by
  rw [rowLat, Submodule.span_le, Set.range_subset_iff]
  rfl

def LatLen (R : Submodule (intL L) (Fin n → L)) (k : ℤ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) L, Valued.v M.det = WithZero.exp k ∧ R = rowLat M

theorem hasLen_of_latLen {g : Matrix (Fin n) (Fin n) L} {k : ℕ}
    (h : LatLen (rowLat (1 : Matrix (Fin n) (Fin n) L) ⊔ rowLat g) k) : HasLen g k := by
  obtain ⟨M, hM, e⟩ := h
  have h0 : M.det ≠ 0 := fun h => by rw [h, map_zero] at hM; exact WithZero.exp_ne_zero hM.symm
  have hu : IsUnit M.det := h0.isUnit
  have h1 : ∀ i, ∃ ρ ρ' : Fin n → L, (∀ i, ρ i ∈ intL L) ∧ (∀ i, ρ' i ∈ intL L) ∧ M i = ρ + ρ' ᵥ* g := fun i => by
    obtain ⟨x, hx, y, hy, e'⟩ := Submodule.mem_sup.1 (e ▸ row_mem_rowLat M i)
    obtain ⟨ρ, hρ, rfl⟩ := mem_rowLat.1 hx
    obtain ⟨ρ', hρ', rfl⟩ := mem_rowLat.1 hy
    exact ⟨ρ, ρ', hρ, hρ', by rw [← e', Matrix.vecMul_one]⟩
  choose U V hU hV hUV using h1
  have h2 : ∀ A : Matrix (Fin n) (Fin n) L, rowLat A ≤ rowLat M → IsInt (A * M⁻¹) := fun A hA i j => by
    obtain ⟨ρ, hρ, e'⟩ := mem_rowLat.1 (hA (row_mem_rowLat A i))
    have : (A * M⁻¹) i = ρ := by
      rw [show (A * M⁻¹) i = A i ᵥ* M⁻¹ from rfl, e', Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu,
        Matrix.vecMul_one]
    rw [this]
    exact hρ j
  refine ⟨Matrix.of U, Matrix.of V, M⁻¹, ⟨hU, hV, by simpa using h2 1 (e ▸ le_sup_left), h2 g (e ▸ le_sup_right), ?_⟩, ?_⟩
  · rw [show Matrix.of U + Matrix.of V * g = M from funext fun i => (hUV i).symm, Matrix.mul_nonsing_inv _ hu]
  · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, map_inv₀, hM, WithZero.exp_neg]

def intV (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : AddSubgroup (Fin n → L) :=
  AddSubgroup.pi Set.univ fun _ => (intL L).toAddSubgroup

def preLat (A : Matrix (Fin n) (Fin n) L) : AddSubgroup (Fin n → L) := (intV L n).comap A.vecMulLinear.toAddMonoidHom

theorem mem_intV {r : Fin n → L} : r ∈ intV L n ↔ ∀ i, r i ∈ intL L := by simp [intV, AddSubgroup.mem_pi]

theorem mem_preLat {A : Matrix (Fin n) (Fin n) L} {r : Fin n → L} : r ∈ preLat A ↔ ∀ i, (r ᵥ* A) i ∈ intL L := mem_intV

def traceZero (σ : L →+* L) (c : L) : AddSubgroup L :=
  (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft c) ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker

theorem mem_traceZero {σ : L →+* L} {c x : L} : x ∈ traceZero σ c ↔ c * x ∈ intL L ∧ σ x + x = 0 := Iff.rfl

theorem exists_trace_one {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) : ∃ τ ∈ intL L, τ + σ τ = 1 := by
  obtain ⟨hσσ, hσ, -, -, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hx0 : σ x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  refine ⟨σ x * (σ x - x)⁻¹, mul_mem (by rw [GlobalTheory.UnitarySwap.mem_int, hσ]; exact hx)
    (by rw [GlobalTheory.UnitarySwap.mem_int, map_inv₀, hx1, inv_one]), ?_⟩
  rw [map_mul, map_inv₀, map_sub, hσσ, ← neg_sub (σ x) x, inv_neg]
  linear_combination mul_inv_cancel₀ hx0

end Len

section Parabolic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

def mid (i : Fin N) : Fin (N + 2) := i.castSucc.succ

def blk (N : ℕ) (i : Fin (N + 2)) : ℕ := if i = 0 then 0 else if i = Fin.last (N + 1) then 2 else 1

@[simp] theorem val_mid (i : Fin N) : (mid i).val = i.val + 1 := rfl
theorem mid_ne_zero (i : Fin N) : mid i ≠ 0 := Fin.succ_ne_zero _
theorem mid_ne_last (i : Fin N) : mid i ≠ Fin.last (N + 1) := fun h => by
  have := congrArg Fin.val h; have := i.2; simp at *; omega
theorem mid_injective : Function.Injective (mid : Fin N → Fin (N + 2)) := fun i j h => by
  have := congrArg Fin.val h; simp at this; exact Fin.ext this
theorem mid_rev (i : Fin N) : mid i.rev = (mid i).rev := by
  have := i.2; ext; simp [Fin.val_rev]; omega
theorem last_ne_zero : Fin.last (N + 1) ≠ 0 := by simp
@[simp] theorem blk_zero : blk N 0 = 0 := by simp [blk]
@[simp] theorem blk_mid (i : Fin N) : blk N (mid i) = 1 := by simp [blk, mid_ne_zero, mid_ne_last]
@[simp] theorem blk_last : blk N (Fin.last (N + 1)) = 2 := by simp [blk]

theorem idx_cases (i : Fin (N + 2)) : i = 0 ∨ (∃ j, i = mid j) ∨ i = Fin.last (N + 1) := by
  induction i using Fin.cases with
  | zero => exact Or.inl rfl
  | succ i =>
    induction i using Fin.lastCases with
    | last => exact Or.inr (Or.inr rfl)
    | cast i => exact Or.inr (Or.inl ⟨i, rfl⟩)

theorem sum_idx {M : Type} [AddCommMonoid M] (f : Fin (N + 2) → M) :
    ∑ i, f i = f 0 + ∑ j, f (mid j) + f (Fin.last (N + 1)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, add_assoc (f 0)]
  rfl

abbrev radQ (σ : L →+* L) (N : ℕ) : Subgroup (GU σ (N + 2)) := radU σ (blk N)

abbrev RadQuot (σ : L →+* L) (N : ℕ) : Type := radQ σ N ⧸ (KU σ (N + 2)).subgroupOf (radQ σ N)

def rowOf (u : GU σ (N + 2)) : Fin N → L := fun j => mat u 0 (mid j)

def colOf (u : GU σ (N + 2)) : Fin N → L := fun i => mat u (mid i) (Fin.last (N + 1))

def cornerOf (u : GU σ (N + 2)) : L := mat u 0 (Fin.last (N + 1))

def IsLeviElt (ϖ : L) (a : ℤ) (g₀ : GU σ N) (m : GU σ (N + 2)) : Prop :=
  m ∈ leviU σ (blk N) ∧ mat m 0 0 = ϖ ^ a ∧ mat m (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) ∧
    ∀ i j, mat m (mid i) (mid j) = mat g₀ i j

def Small (ϖ : L) (e f : ℕ) (C D : Matrix (Fin N) (Fin N) L) (u : GU σ (N + 2)) : Prop :=
  (∀ j, ϖ ^ e * (rowOf u ᵥ* C) j ∈ intL L) ∧ ϖ ^ f * (cornerOf u - rowOf u ⬝ᵥ (D *ᵥ colOf u)) ∈ intL L

end Parabolic

def zVal (q n : ℕ) (X y : ℂ) {m : ℕ} (α : Fin m → ℂ) : ℂ :=
  (∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X)) *
    (∏ i, (1 - y * α i)⁻¹ * (1 - y / α i)⁻¹) * (if Odd n then (1 - y)⁻¹ else 1)

def jFac (q N : ℕ) (X : ℂ) : ℂ := (1 - X) * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2)

def Smith : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (n : ℕ),
    Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ g : Matrix (Fin n) (Fin n) L, g.det ≠ 0 →
    ∃ (d : Fin n → ℤ) (a a' b b' : Matrix (Fin n) (Fin n) L), IsInt a ∧ IsInt a' ∧ IsInt b ∧ IsInt b' ∧
      a' * a = 1 ∧ b * b' = 1 ∧ g = a * Matrix.diagonal (fun i => ϖ ^ d i) * b

def FracExists : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (n : ℕ),
    Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ g : Matrix (Fin n) (Fin n) L, g.det ≠ 0 → HasLen g (len g)

def Completion : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (g : GU σ n) (U V C : Matrix (Fin n) (Fin n) L), IsFrac (mat g) U V C →
    ∃ k ∈ UJ σ (GlobalTheory.Doubling.dblGram (finSumFinEquiv (m := n) (n := n)) (antiJ L n)), k ∈ GLint (Fin (n + n)) (intL L) ∧
      ∀ x : Fin n → L, (k : Matrix (Fin (n + n)) (Fin (n + n)) L) *ᵥ
      GlobalTheory.Doubling.pairVec finSumFinEquiv x x = GlobalTheory.Doubling.pairVec finSumFinEquiv (C *ᵥ x) ((mat g * C) *ᵥ x)

def AddVec : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (M : Matrix (Fin n) (Fin n) L) (k : ℤ)
    (ρ : Fin n → L) (e : ℕ), Valued.v M.det = WithZero.exp k → (∀ i, Valued.v (ρ i) ≤ WithZero.exp (e : ℤ)) →
    (e = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e : ℤ)) →
    LatLen (rowLat M ⊔ Submodule.span (intL L) {ρ ᵥ* M}) (k + e)

def Dual : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (g : GU σ N) (U V C : Matrix (Fin N) (Fin N) L), IsFrac (mat g) U V C →
    ∀ (r b : Fin N → L) (t : L), (∀ j, r j = -σ (b j.rev)) →
    ((∀ j, t * (r ᵥ* C) j ∈ intL L) ↔
      (∀ i, t * ((C * V * mat g) *ᵥ b) i ∈ intL L) ∧ ∀ i, t * ((mat g * C * U) *ᵥ b) i ∈ intL L)

def SpanEq : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (N : ℕ) (a : ℤ)
    (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (g₀ U V C : Matrix (Fin N) (Fin N) L) (r b : Fin N → L) (c y : L),
    Valued.v ϖ = WithZero.exp (-1 : ℤ) → IsFrac g₀ U V C →
    g 0 0 = ϖ ^ a → (∀ j, g 0 (mid j) = ϖ ^ a * r j) → g 0 (Fin.last (N + 1)) = ϖ ^ a * c →
    (∀ i, g (mid i) 0 = 0) → (∀ i j, g (mid i) (mid j) = g₀ i j) → (∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) →
    g (Fin.last (N + 1)) 0 = 0 → (∀ j, g (Fin.last (N + 1)) (mid j) = 0) →
    g (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) →
    WithZero.exp (a.toNat : ℤ) ≤ Valued.v y → (∀ i, Valued.v (((C * V * g₀) *ᵥ b) i) ≤ Valued.v y) →
    (∀ i, Valued.v (((g₀ * C * U) *ᵥ b) i) ≤ Valued.v y) →
    (Valued.v y = WithZero.exp (a.toNat : ℤ) ∨ (∃ i, Valued.v y = Valued.v (((C * V * g₀) *ᵥ b) i)) ∨
      ∃ i, Valued.v y = Valued.v (((g₀ * C * U) *ᵥ b) i)) →
    ∃ (P : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (ρ : Fin (N + 2) → L),
      Valued.v P.det = WithZero.exp ((-a).toNat : ℤ) * (Valued.v C.det)⁻¹ * Valued.v y ∧ ρ 0 = 0 ∧
      (∀ j, ρ (mid j) = ϖ ^ a.toNat * (r ᵥ* C) j) ∧
      ρ (Fin.last (N + 1)) = ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y ∧
      rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g = rowLat P ⊔ Submodule.span (intL L) {ρ ᵥ* P}

def Heis : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q →
    (∀ u ∈ radQ σ N, (∀ j, rowOf u j = -σ (colOf u j.rev)) ∧
      cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u ∧
      (u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L)) ∧
    (∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u') ∧
    ∀ (r : Fin N → L) (c : L), c + σ c = -∑ j, r j * σ (r j.rev) → ∃ u ∈ radQ σ N, rowOf u = r ∧ cornerOf u = c

def Pointwise : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (a : ℤ) (g₀ : GU σ N) (m : GU σ (N + 2)), IsLeviElt ϖ a g₀ m →
    ∀ (U V C : Matrix (Fin N) (Fin N) L) (l : ℕ), IsFrac (mat g₀) U V C → Valued.v C.det = WithZero.exp (-(l : ℤ)) →
    ∀ u ∈ radQ σ N, a.natAbs + l ≤ len (mat (m * u)) ∧
      ∀ j : ℕ, len (mat (m * u)) ≤ a.natAbs + l + j ↔ Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u

def LatIndex : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (A : Matrix (Fin n) (Fin n) L) (k : ℕ), IsInt A → Valued.v A.det = WithZero.exp (-(k : ℤ)) →
    (intV L n).relIndex (preLat A) = q ^ (2 * k)

def TraceIndex : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q f : ℕ),
    IsUnramInv ϖ σ q → (traceZero σ 1).relIndex (traceZero σ (ϖ ^ f)) = q ^ f

def SmallCorner : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (g₀ : GU σ N) (U V C : Matrix (Fin N) (Fin N) L), IsFrac (mat g₀) U V C →
    ∀ (e f : ℕ) (r : Fin N → L), 2 * e ≤ f → (∀ j, ϖ ^ e * (r ᵥ* C) j ∈ intL L) →
    ∃ u ∈ radQ σ N, rowOf u = r ∧ Small ϖ e f C (C * V * mat g₀) u

def Count : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (C D : Matrix (Fin N) (Fin N) L) (l e f : ℕ), IsInt C →
    Valued.v C.det = WithZero.exp (-(l : ℤ)) →
    (∀ r : Fin N → L, (∀ j, ϖ ^ e * (r ᵥ* C) j ∈ intL L) → ∃ u ∈ radQ σ N, rowOf u = r ∧ Small ϖ e f C D u) →
    (∀ u ∈ radQ σ N, ∀ k ∈ radQ σ N, k ∈ KU σ (N + 2) → Small ϖ e f C D u → Small ϖ e f C D (u * k)) →
    Nat.card {x : RadQuot σ N // Small ϖ e f C D (x.out : radQ σ N).1} = q ^ (2 * (l + N * e) + f)

def LeviExists : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (a : ℤ) (g₀ : GU σ N), ∃ m : GU σ (N + 2), IsLeviElt ϖ a g₀ m

def CosetSurj : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ g : GU σ (N + 2), ∃ (a : ℤ) (y : GU σ N ⧸ KU σ N), ∀ m, IsLeviElt ϖ a y.out m →
      ∃ u ∈ radQ σ N, ∃ k ∈ KU σ (N + 2), g = m * u * k

def CosetInj : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N : ℕ),
    IsUnramInv ϖ σ q → ∀ (a a' : ℤ) (g₀ g₀' : GU σ N) (m m' : GU σ (N + 2)), IsLeviElt ϖ a g₀ m → IsLeviElt ϖ a' g₀' m' →
      ∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, (m * u)⁻¹ * (m' * u') ∈ KU σ (N + 2) → a = a' ∧ g₀⁻¹ * g₀' ∈ KU σ N

def SphTrans : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q N r : ℕ),
    IsUnramInv ϖ σ q → 2 * r ≤ N → ∀ (α : Fin (r + 1) → ℂ) (φ : GU σ (N + 2) → ℂ) (φ₀ : GU σ N → ℂ), (∀ i, α i ≠ 0) →
    IsSphericalU q α φ → φ 1 = 1 → IsSphericalU q (Fin.tail α) φ₀ → φ₀ 1 = 1 →
    ∀ (a : ℤ) (g₀ : GU σ N) (m : GU σ (N + 2)), IsLeviElt ϖ a g₀ m → ∀ u ∈ radQ σ N,
      φ (m * u) = α 0 ^ a * (q : ℂ) ^ (-a * ((N : ℤ) + 1)) * φ₀ g₀

def SmallRank : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ),
    IsUnramInv ϖ σ q → n ≤ 1 → ∀ g : GU σ n, g ∈ KU σ n

def CosetIntegral : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 →
    ∀ (F : G → ℂ) (Z : ℂ), (∀ g, ∀ k ∈ K, F (g * k) = F g) → HasSum (fun x : G ⧸ K => F x.out) Z →
    Integrable F μ ∧ ∫ g, F g ∂μ = Z

def DosetSwap : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (F w φ : G → ℂ) (Z : ℂ), IsBiInv K F → IsBiInv K w →
    (∀ g, hAct K (dosetInd ℂ K g) w 1 = hAct K (dosetInd ℂ K g) φ 1) →
    HasSum (fun x : G ⧸ K => F x.out * φ x.out) Z → HasSum (fun x : G ⧸ K => F x.out * w x.out) Z

def GenFun : Prop :=
  ∀ (ι : Type) (f : ι → ℕ) (l c q N : ℕ) (X : ℂ), 1 ≤ c → 1 ≤ q → (∀ i, l ≤ f i) →
    (∀ j : ℕ, Nat.card {i // f i ≤ l + j} = c * q ^ (2 * N * (j / 2) + j)) → ‖(q : ℂ) ^ (N + 1) * X‖ < 1 →
    HasSum (fun i => X ^ f i) (c * X ^ l * jFac q N X)

def Step : Prop :=
  ∀ (Y C : Type) (q N : ℕ) (ℓ : ℤ → Y → C → ℕ) (l : Y → ℕ) (φ₀ : Y → ℂ) (α X y Z : ℂ), 1 ≤ q → α ≠ 0 →
    y = (q : ℂ) ^ (N + 1) * X → ‖y‖ < 1 → ‖y‖ * ‖α‖ < 1 → ‖y‖ * ‖α‖⁻¹ < 1 →
    (∀ X' : ℂ, ‖(q : ℂ) ^ (N + 1) * X'‖ < 1 → ∀ a b, HasSum (fun c => X' ^ ℓ a b c)
      ((q : ℂ) ^ (2 * l b + (2 * N + 2) * a.toNat) * X' ^ (a.natAbs + l b) * jFac q N X')) →
    HasSum (fun b => ((q : ℂ) ^ 2 * X) ^ l b * φ₀ b) Z →
    HasSum (fun p : (ℤ × Y) × C => X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2))
      ((1 - X) * (1 + q * X) * ((1 - y * α)⁻¹ * (1 - y / α)⁻¹) * Z)

end GlobalTheory.InertZeta

end
