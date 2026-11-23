import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.MinuscTop

section Comb

variable {n : ℕ}

theorem tail_sum_le {μ : Fin n → ℕ} (hμ : Antitone μ) (j : ℕ) (S : Finset (Fin n))
    (hS : (Finset.univ.filter fun i : Fin n => j ≤ (i : ℕ)).card = S.card) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), μ i ≤ ∑ i ∈ S, μ i := by
  set T := Finset.univ.filter fun i : Fin n => j ≤ (i : ℕ) with hT
  refine Finset.sum_sdiff_le_sum_sdiff.1 ?_
  have hc := Finset.card_sdiff_comm hS
  have h1 : ∑ i ∈ T \ S, μ i ≤ (T \ S).card • (T \ S).sup μ :=
    Finset.sum_le_card_nsmul _ _ _ fun i hi => Finset.le_sup (f := μ) hi
  have h2 : (S \ T).card • (T \ S).sup μ ≤ ∑ i ∈ S \ T, μ i := by
    refine Finset.card_nsmul_le_sum _ _ _ fun y hy => Finset.sup_le fun i hi => hμ ?_
    have hy' : ¬ j ≤ (y : ℕ) := by
      have := (Finset.mem_sdiff.1 hy).2
      simpa [hT] using this
    have hi' : j ≤ (i : ℕ) := by
      have := (Finset.mem_sdiff.1 hi).1
      simpa [hT] using this
    exact Fin.le_def.2 (by omega)
  rw [hc] at h1
  exact h1.trans h2

theorem abel_head (a x : Fin n → ℤ) (ha : Antitone a)
    (hH : ∀ j : ℕ, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), x i) (j : ℕ) (hj : j ≤ n) (c : ℤ)
    (hc : ∀ i : Fin n, (i : ℕ) < j → c ≤ a i) :
    c * ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), x i ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), x i * a i := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
    have hjn : j < n := hj
    have e : Finset.univ.filter (fun i : Fin n => (i : ℕ) < j + 1) =
        insert (⟨j, hjn⟩ : Fin n) (Finset.univ.filter fun i : Fin n => (i : ℕ) < j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hn : (⟨j, hjn⟩ : Fin n) ∉ Finset.univ.filter fun i : Fin n => (i : ℕ) < j := by simp
    have h1 := ih (by omega) (a ⟨j, hjn⟩) fun i hi => ha (Fin.le_def.2 (by simpa using hi.le))
    have h2 := hH (j + 1)
    have h3 := hc ⟨j, hjn⟩ (by simp)
    rw [e, Finset.sum_insert hn] at h2 ⊢
    rw [Finset.sum_insert hn]
    nlinarith [mul_nonneg (sub_nonneg.2 h3) h2]

theorem sq_lt {d d' : Fin n → ℕ} (hd' : Antitone d') (htot : ∑ i, d' i = ∑ i, d i)
    (hT : ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), d i ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), d' i) :
    d' = d ∨ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2 := by
  by_cases hne : d' = d
  · exact Or.inl hne
  refine Or.inr ?_
  let x : Fin n → ℤ := fun i => (d i : ℤ) - d' i
  let a : Fin n → ℤ := fun i => d' i
  have hH : ∀ j : ℕ, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), x i := by
    intro j
    have e1 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < j) d
    have e2 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < j) d'
    simp only [not_lt] at e1 e2
    have := hT j
    simp only [x, Finset.sum_sub_distrib, ← Nat.cast_sum]
    omega
  have ha : Antitone a := fun i j h => by simpa [a] using hd' h
  have hA := abel_head a x ha hH n le_rfl 0 fun i _ => by simp [a]
  have e : Finset.univ.filter (fun i : Fin n => (i : ℕ) < n) = Finset.univ := by
    ext i; simp
  rw [e, zero_mul] at hA
  have hx : 0 < ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
    have : x i ≠ 0 := by
      simp only [x]; omega
    positivity
  have key : ((∑ i, d i ^ 2 : ℕ) : ℤ) = ∑ i, (d' i : ℤ) ^ 2 + ∑ i, x i ^ 2 + 2 * ∑ i, x i * a i := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [x, a]; ring
  have : ((∑ i, d' i ^ 2 : ℕ) : ℤ) < ((∑ i, d i ^ 2 : ℕ) : ℤ) := by
    rw [key]; push_cast; linarith
  exact_mod_cast this

end Comb

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

local notation "Γ" => WithZero (Multiplicative ℤ)

def MinorLe (c : Γ) (r : ℕ) (M : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ I J : Fin r → Fin n, Valued.v (M.submatrix I J).det ≤ c

theorem mem_intL_iff {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem det_submatrix_mul_expand {r : ℕ} (A M : Matrix (Fin n) (Fin n) L) (I J : Fin r → Fin n) :
    ((A * M).submatrix I J).det =
      ∑ f : Fin r → Fin n, (∏ i, A (I i) (f i)) * (M.submatrix f J).det := by
  have h := (Matrix.detRowAlternating (R := L) (n := Fin r)).toMultilinearMap.map_sum
    (fun (i : Fin r) (k : Fin n) => A (I i) k • (fun j => M k (J j)))
  have e : (fun i => ∑ k, A (I i) k • (fun j => M k (J j))) = (A * M).submatrix I J := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [e] at h
  refine h.trans (Finset.sum_congr rfl fun f _ => ?_)
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem minorLe_mul_left {c : Γ} {r : ℕ} {A M : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (h : MinorLe c r M) : MinorLe c r (A * M) := by
  intro I J
  rw [det_submatrix_mul_expand]
  refine Valuation.map_sum_le _ fun f _ => ?_
  rw [map_mul]
  have h1 : Valued.v (∏ i, A (I i) (f i)) ≤ 1 :=
    mem_intL_iff.1 (prod_mem fun i _ => hA _ _)
  calc _ ≤ 1 * c := mul_le_mul' h1 (h f J)
    _ = c := one_mul c

theorem minorLe_transpose {c : Γ} {r : ℕ} {M : Matrix (Fin n) (Fin n) L} (h : MinorLe c r M) :
    MinorLe c r M.transpose := by
  intro I J
  have : (M.transpose.submatrix I J) = (M.submatrix J I).transpose := by ext; rfl
  rw [this, Matrix.det_transpose]
  exact h J I

theorem minorLe_mul_right {c : Γ} {r : ℕ} {B M : Matrix (Fin n) (Fin n) L}
    (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (h : MinorLe c r M) : MinorLe c r (M * B) := by
  have := minorLe_transpose (minorLe_mul_left (A := B.transpose) (fun i j => hB j i) (minorLe_transpose h))
  rwa [← Matrix.transpose_mul, Matrix.transpose_transpose] at this

theorem det_int {r : ℕ} (M : Matrix (Fin r) (Fin r) L) (h : ∀ i j, M i j ∈ Formalism.UG.intL L) :
    Valued.v M.det ≤ 1 := by
  refine mem_intL_iff.1 ?_
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

theorem glint_entry {g : GL (Fin n) L} (hg : g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) (i j : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  obtain ⟨g0, rfl⟩ := hg
  exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) i j).2

theorem glint_det {g : GL (Fin n) L} (hg : g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) :
    Valued.v (g : Matrix (Fin n) (Fin n) L).det = 1 := by
  have h1 := det_int _ (glint_entry hg)
  have h2 := det_int _ (glint_entry (inv_mem hg))
  have h3 : (g : Matrix (Fin n) (Fin n) L).det * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  refine le_antisymm h1 ?_
  calc (1 : Γ) = _ := h4.symm
    _ ≤ Valued.v (g : Matrix (Fin n) (Fin n) L).det * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

variable {ϖ : L}

theorem v_pow_anti {q : Γ} (hq : q < 1) (h0 : 0 < q) {a b : ℕ} (h : q ^ a ≤ q ^ b) : b ≤ a := by
  by_contra hc
  exact absurd (pow_lt_pow_right_of_lt_one₀ h0 hq (not_le.1 hc)) (not_lt.2 h)

theorem sum_inj_image {M : Type} [AddCommMonoid M] {r : ℕ} (f : Fin n → M) {I : Fin r → Fin n}
    (hI : Function.Injective I) : ∑ t, f (I t) = ∑ i ∈ Finset.univ.image I, f i :=
  (Finset.sum_image fun _ _ _ _ h => hI h).symm

theorem minorLe_diag (q : Γ) (hq : q < 1) (hϖ : Valued.v ϖ = q) {μ ω : Fin n → ℕ} (hμ : Antitone μ) (hω : Antitone ω)
    {h : Matrix (Fin n) (Fin n) L} (hh : ∀ i j, h i j ∈ Formalism.UG.intL L) (j : ℕ) :
    MinorLe (q ^ (∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), μ i +
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), ω i))
      (Finset.univ.filter fun i : Fin n => j ≤ (i : ℕ)).card
      (Matrix.diagonal (fun i => ϖ ^ μ i) * h * Matrix.diagonal (fun i => ϖ ^ ω i)) := by
  intro I J
  by_cases hI : Function.Injective I
  swap
  · obtain ⟨a, b, e, ne⟩ := Function.not_injective_iff.1 hI
    rw [Matrix.det_zero_of_row_eq ne (by ext c; simp [e]), map_zero]
    exact zero_le
  by_cases hJ : Function.Injective J
  swap
  · obtain ⟨a, b, e, ne⟩ := Function.not_injective_iff.1 hJ
    rw [Matrix.det_zero_of_column_eq ne (by intro c; simp [e]), map_zero]
    exact zero_le
  have e : (Matrix.diagonal (fun i => ϖ ^ μ i) * h * Matrix.diagonal (fun i => ϖ ^ ω i)).submatrix I J =
      Matrix.diagonal (fun t => ϖ ^ μ (I t)) * h.submatrix I J * Matrix.diagonal (fun t => ϖ ^ ω (J t)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, map_pow, map_pow, hϖ, sum_inj_image μ hI,
    sum_inj_image ω hJ]
  have c1 : (Finset.univ.image I).card = (Finset.univ.filter fun i : Fin n => j ≤ (i : ℕ)).card := by
    rw [Finset.card_image_of_injective _ hI]; simp
  have c2 : (Finset.univ.image J).card = (Finset.univ.filter fun i : Fin n => j ≤ (i : ℕ)).card := by
    rw [Finset.card_image_of_injective _ hJ]; simp
  have t1 := tail_sum_le hμ j _ c1.symm
  have t2 := tail_sum_le hω j _ c2.symm
  have hd := det_int (h.submatrix I J) fun a b => hh _ _
  calc _ ≤ q ^ (∑ i ∈ Finset.univ.image I, μ i) * 1 * q ^ (∑ i ∈ Finset.univ.image J, ω i) :=
        mul_le_mul' (mul_le_mul' le_rfl hd) le_rfl
    _ = q ^ (∑ i ∈ Finset.univ.image I, μ i + ∑ i ∈ Finset.univ.image J, ω i) := by
        rw [mul_one, pow_add]
    _ ≤ _ := pow_le_pow_right_of_le_one' hq.le (add_le_add t1 t2)

theorem tail_of_minorLe (q : Γ) (hq : q < 1) (h0 : 0 < q) (hϖ : Valued.v ϖ = q) {d' : Fin n → ℕ} {t : ℕ} (j : ℕ)
    (h : MinorLe (q ^ t) (Finset.univ.filter fun i : Fin n => j ≤ (i : ℕ)).card
      (Matrix.diagonal fun i => ϖ ^ d' i)) :
    t ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), d' i := by
  set T := Finset.univ.filter fun i : Fin n => j ≤ (i : ℕ)
  have hI : Function.Injective (T.orderEmbOfFin rfl) := (T.orderEmbOfFin rfl).injective
  have := h (T.orderEmbOfFin rfl) (T.orderEmbOfFin rfl)
  rw [Matrix.submatrix_diagonal _ _ hI, Matrix.det_diagonal] at this
  simp only [Function.comp] at this
  rw [Finset.prod_pow_eq_pow_sum, map_pow, hϖ, sum_inj_image d' hI] at this
  have e : Finset.univ.image (T.orderEmbOfFin rfl) = T := by
    simpa using Finset.image_orderEmbOfFin_univ T rfl
  rw [e] at this
  exact v_pow_anti hq h0 this

end Val

theorem elemDiv_mul_minuscule : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (n : ℕ), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → ∀ (d : Fin n → ℕ) (k : ℕ), Antitone d → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ (g a : GL (Fin n) L), (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * g * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => ϖ ^ (d i - 1)) → (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * a * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < k then ϖ else 1) → ∀ d' : Fin n → ℕ, Antitone d' → (∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L), ((k₁ * (g * a) * k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => ϖ ^ d' i) → d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2) := by
  intro L _ _ ϖ n hϖ d k hd hk g a ⟨k₁, hk₁, k₂, hk₂, eg⟩ ⟨l₁, hl₁, l₂, hl₂, ea⟩ d' hd' ⟨m₁, hm₁, m₂, hm₂, e⟩
  obtain ⟨q, hqdef⟩ : ∃ q : WithZero (Multiplicative ℤ), q = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := ⟨_, rfl⟩
  rw [← hqdef] at hϖ
  have hq0 : 0 < q := by rw [hqdef]; exact WithZero.zero_lt_coe _
  have hq1 : q < 1 := by
    rw [hqdef, ← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    norm_num
  let μ : Fin n → ℕ := fun i => d i - 1
  let ω : Fin n → ℕ := fun i => if (i : ℕ) < k then 1 else 0
  have hμ : Antitone μ := fun i j h => Nat.sub_le_sub_right (hd h) 1
  have hω : Antitone ω := fun i j h => by
    have h' : (i : ℕ) ≤ j := h
    simp only [ω]
    split_ifs <;> omega
  have hdμ : ∀ i, d i = μ i + ω i := fun i => by
    have := hk i
    simp only [μ, ω]
    split_ifs <;> omega
  have ea' : ((l₁ * a * l₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => ϖ ^ ω i := by
    rw [ea]
    congr 1
    funext i
    simp only [ω]
    split_ifs <;> simp
  have hA : m₁ * k₁⁻¹ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) := mul_mem hm₁ (inv_mem hk₁)
  have hh : k₂⁻¹ * l₁⁻¹ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) := mul_mem (inv_mem hk₂) (inv_mem hl₁)
  have hB : l₂⁻¹ * m₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) := mul_mem (inv_mem hl₂) hm₂
  have key : m₁ * (g * a) * m₂ = (m₁ * k₁⁻¹) * ((k₁ * g * k₂) * (k₂⁻¹ * l₁⁻¹) * (l₁ * a * l₂)) * (l₂⁻¹ * m₂) := by
    group
  have em : (Matrix.diagonal fun i => ϖ ^ d' i) =
      ((m₁ * k₁⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((Matrix.diagonal fun i => ϖ ^ μ i) * ((k₂⁻¹ * l₁⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (Matrix.diagonal fun i => ϖ ^ ω i)) * ((l₂⁻¹ * m₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [← e, key, ← ea', Units.val_mul, Units.val_mul (m₁ * k₁⁻¹), Units.val_mul (k₁ * g * k₂ * (k₂⁻¹ * l₁⁻¹)),
      Units.val_mul (k₁ * g * k₂) (k₂⁻¹ * l₁⁻¹), eg]
  have hT : ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), d i ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ)), d' i := by
    intro j
    have m := minorLe_mul_right (glint_entry hB) (minorLe_mul_left (glint_entry hA)
      (minorLe_diag (ϖ := ϖ) q hq1 hϖ hμ hω (glint_entry hh) j))
    rw [← em] at m
    have := tail_of_minorLe q hq1 hq0 hϖ j m
    rwa [← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => (hdμ i).symm] at this
  have htot : ∑ i, d' i = ∑ i, d i := by
    have h1 := congrArg (fun M => Valued.v (Matrix.det M)) em
    simp only [Matrix.det_mul, Matrix.det_diagonal, map_mul, glint_det hA, glint_det hB, glint_det hh,
      Finset.prod_pow_eq_pow_sum, map_pow, hϖ, one_mul, mul_one] at h1
    rw [← pow_add] at h1
    have h2 : ∑ i, d' i = ∑ i, μ i + ∑ i, ω i :=
      le_antisymm (v_pow_anti hq1 hq0 h1.ge) (v_pow_anti hq1 hq0 h1.le)
    rw [h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (hdμ i).symm
  rcases sq_lt hd' htot hT with h | h
  · exact Or.inl h
  · exact Or.inr ⟨htot, h⟩

end GlobalTheory.Hk3.MinuscTop
