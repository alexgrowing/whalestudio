import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IwEmb

open Matrix GlobalTheory.LeviElem

variable {R0 A : Type} [CommRing R0] [CommRing A] [Algebra R0 A]

def frame {b : ℕ} (x y : Fin (b + 2) → A) (ι : Matrix (Fin (b + 2)) (Fin b) A) :
    Matrix (Fin (b + 2)) (Fin b ⊕ Fin 2) A :=
  fromCols ι (cols2 x y)

def IsUnipMat {b : ℕ} (x : Fin (b + 2) → A) (ι : Matrix (Fin (b + 2)) (Fin b) A)
    (X : Matrix (Fin (b + 2)) (Fin (b + 2)) A) : Prop :=
  X *ᵥ x = x ∧ ∀ z, ∃ a : A, X *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x

theorem isUnipMat_one {b : ℕ} (x : Fin (b + 2) → A) (ι : Matrix (Fin (b + 2)) (Fin b) A) : IsUnipMat x ι 1 :=
  ⟨by simp, fun _ => ⟨0, by simp⟩⟩

theorem IsUnipMat.mul {b : ℕ} {x : Fin (b + 2) → A} {ι : Matrix (Fin (b + 2)) (Fin b) A} {X Y : Matrix (Fin (b + 2)) (Fin (b + 2)) A}
    (hX : IsUnipMat x ι X) (hY : IsUnipMat x ι Y) : IsUnipMat x ι (X * Y) := by
  refine ⟨by rw [← mulVec_mulVec, hY.1, hX.1], fun z => ?_⟩
  obtain ⟨a, ha⟩ := hY.2 z
  obtain ⟨a', ha'⟩ := hX.2 z
  exact ⟨a' + a, by rw [← mulVec_mulVec, ha, mulVec_add, ha', mulVec_smul, hX.1, add_smul, add_assoc]⟩

theorem IsUnipMat.inv {b : ℕ} {x : Fin (b + 2) → A} {ι : Matrix (Fin (b + 2)) (Fin b) A} {X Y : Matrix (Fin (b + 2)) (Fin (b + 2)) A}
    (hX : IsUnipMat x ι X) (hYX : Y * X = 1) : IsUnipMat x ι Y := by
  have hx : Y *ᵥ x = x := by
    conv_lhs => rw [← hX.1]
    rw [mulVec_mulVec, hYX, one_mulVec]
  refine ⟨hx, fun z => ?_⟩
  obtain ⟨a, ha⟩ := hX.2 z
  refine ⟨-a, ?_⟩
  have h1 : Y *ᵥ (X *ᵥ (ι *ᵥ z)) = ι *ᵥ z := by rw [mulVec_mulVec, hYX, one_mulVec]
  have h2 : Y *ᵥ (X *ᵥ (ι *ᵥ z)) = Y *ᵥ (ι *ᵥ z) + a • x := by rw [ha, mulVec_add, mulVec_smul, hx]
  rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, ← h2, h1]

def unipSub (c : A →ₐ[R0] A) {b : ℕ} (J : Matrix (Fin (b + 2)) (Fin (b + 2)) A) (x : Fin (b + 2) → A)
    (ι : Matrix (Fin (b + 2)) (Fin b) A) : Subgroup (UG c J) where
  carrier := {u | IsUnipMat x ι u.1.1}
  one_mem' := isUnipMat_one x ι
  mul_mem' := fun ha hb => IsUnipMat.mul ha hb
  inv_mem' := fun {u} hu => IsUnipMat.inv hu (Units.inv_mul u.1)

def tau {b : ℕ} (Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) A) (x : Fin (b + 2) → A)
    (X : Matrix (Fin (b + 2)) (Fin (b + 2)) A) : A :=
  (Q *ᵥ (X *ᵥ x)) (Sum.inr 0)

def gam {b : ℕ} (Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) A) (ι : Matrix (Fin (b + 2)) (Fin b) A)
    (X : Matrix (Fin (b + 2)) (Fin (b + 2)) A) : Matrix (Fin b) (Fin b) A :=
  toRows₁ (Q * X * ι)

end GlobalTheory.IwEmb

namespace GlobalTheory.IwEmb

open Matrix GlobalTheory.LeviElem

variable {A : Type} [CommRing A] {b : ℕ} {x y : Fin (b + 2) → A} {ι : Matrix (Fin (b + 2)) (Fin b) A}
  {Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) A}

def leviM (x y : Fin (b + 2) → A) (ι : Matrix (Fin (b + 2)) (Fin b) A) (Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) A)
    (G : Matrix (Fin b) (Fin b) A) (t s : A) : Matrix (Fin (b + 2)) (Fin (b + 2)) A :=
  frame x y ι * blk G t s * Q

theorem frame_mul_Q (hQP : Q * frame x y ι = 1) : frame x y ι * Q = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP

theorem frame_alt : frame x y ι *ᵥ Pi.single (Sum.inr 0) 1 = x := by
  rw [mulVec_single_one]; ext i; simp [frame, cols2]

theorem frame_ι (z : Fin b → A) : frame x y ι *ᵥ Sum.elim z 0 = ι *ᵥ z := by
  ext i; simp [frame, mulVec, dotProduct, Fintype.sum_sum_type]

theorem frame_inverse_mulVec_x (hQP : Q * frame x y ι = 1) : Q *ᵥ x = Pi.single (Sum.inr 0) 1 := by
  conv_lhs => rw [← frame_alt (x := x) (y := y) (ι := ι)]
  rw [mulVec_mulVec, hQP, one_mulVec]

theorem Q_ι (hQP : Q * frame x y ι = 1) (z : Fin b → A) : Q *ᵥ (ι *ᵥ z) = Sum.elim z 0 := by
  rw [← frame_ι (x := x) (y := y) z, mulVec_mulVec, hQP, one_mulVec]

theorem block_matrix_mulVec_basis (G : Matrix (Fin b) (Fin b) A) (t s : A) :
    blk G t s *ᵥ Pi.single (Sum.inr 0) 1 = t • Pi.single (Sum.inr 0) 1 := by
  rw [mulVec_single_one]; ext (i | i)
  · simp [blk]
  · fin_cases i <;> simp [blk, diagonal]

theorem blk_ι (G : Matrix (Fin b) (Fin b) A) (t s : A) (z : Fin b → A) :
    blk G t s *ᵥ Sum.elim z 0 = Sum.elim (G *ᵥ z) 0 := by
  ext (i | i) <;> simp [blk, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks]

theorem leviM_mulVec_x (hQP : Q * frame x y ι = 1) (G : Matrix (Fin b) (Fin b) A) (t s : A) :
    leviM x y ι Q G t s *ᵥ x = t • x := by
  rw [leviM, ← mulVec_mulVec, ← mulVec_mulVec, frame_inverse_mulVec_x hQP, block_matrix_mulVec_basis, mulVec_smul, frame_alt]

theorem leviM_ι (hQP : Q * frame x y ι = 1) (G : Matrix (Fin b) (Fin b) A) (t s : A) (z : Fin b → A) :
    leviM x y ι Q G t s *ᵥ (ι *ᵥ z) = ι *ᵥ (G *ᵥ z) := by
  rw [leviM, ← mulVec_mulVec, ← mulVec_mulVec, Q_ι hQP, blk_ι, frame_ι]

theorem gam_apply (X : Matrix (Fin (b + 2)) (Fin (b + 2)) A) (i j : Fin b) :
    gam Q ι X i j = (Q *ᵥ (X *ᵥ (ι *ᵥ Pi.single j 1))) (Sum.inl i) := by
  rw [mulVec_mulVec, mulVec_mulVec, mulVec_single_one]; rfl

theorem Q_line (hQP : Q * frame x y ι = 1) (v : Fin (b + 2) → A) (a : A) :
    Q *ᵥ (v + a • x) = Q *ᵥ v + a • Pi.single (Sum.inr 0) 1 := by
  rw [mulVec_add, mulVec_smul, frame_inverse_mulVec_x hQP]

theorem tau_mul_leviM (hQP : Q * frame x y ι = 1) {N : Matrix (Fin (b + 2)) (Fin (b + 2)) A} (hN : IsUnipMat x ι N)
    (G : Matrix (Fin b) (Fin b) A) (t s : A) : tau Q x (N * leviM x y ι Q G t s) = t := by
  rw [tau, ← mulVec_mulVec, leviM_mulVec_x hQP, mulVec_smul, hN.1, mulVec_smul, frame_inverse_mulVec_x hQP]; simp

theorem tau_leviM_mul (hQP : Q * frame x y ι = 1) {N : Matrix (Fin (b + 2)) (Fin (b + 2)) A} (hN : IsUnipMat x ι N)
    (G : Matrix (Fin b) (Fin b) A) (t s : A) : tau Q x (leviM x y ι Q G t s * N) = t := by
  rw [tau, ← mulVec_mulVec, hN.1, leviM_mulVec_x hQP, mulVec_smul, frame_inverse_mulVec_x hQP]; simp

theorem gam_mul_leviM (hQP : Q * frame x y ι = 1) {N : Matrix (Fin (b + 2)) (Fin (b + 2)) A} (hN : IsUnipMat x ι N)
    (G : Matrix (Fin b) (Fin b) A) (t s : A) : gam Q ι (N * leviM x y ι Q G t s) = G := by
  ext i j
  obtain ⟨a, ha⟩ := hN.2 (G *ᵥ Pi.single j 1)
  rw [gam_apply, ← mulVec_mulVec, leviM_ι hQP, ha, Q_line hQP, Q_ι hQP]
  simp [mulVec_single_one]

theorem gam_leviM_mul (hQP : Q * frame x y ι = 1) {N : Matrix (Fin (b + 2)) (Fin (b + 2)) A} (hN : IsUnipMat x ι N)
    (G : Matrix (Fin b) (Fin b) A) (t s : A) : gam Q ι (leviM x y ι Q G t s * N) = G := by
  ext i j
  obtain ⟨a, ha⟩ := hN.2 (Pi.single j 1)
  rw [gam_apply, ← mulVec_mulVec, ha, mulVec_add, mulVec_smul, leviM_ι hQP, leviM_mulVec_x hQP, smul_smul, Q_line hQP, Q_ι hQP]
  simp [mulVec_single_one]

theorem leviM_mul_leviM (hQP : Q * frame x y ι = 1) {G G' : Matrix (Fin b) (Fin b) A} {t t' s s' : A}
    (hG : G * G' = 1) (ht : t * t' = 1) (hs : s * s' = 1) : leviM x y ι Q G t s * leviM x y ι Q G' t' s' = 1 := by
  have hb : blk G t s * blk G' t' s' = 1 := by
    simp only [blk, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal, hG]
    rw [← fromBlocks_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal, ht, hs]
  calc leviM x y ι Q G t s * leviM x y ι Q G' t' s' = frame x y ι * (blk G t s * (Q * frame x y ι) * blk G' t' s') * Q := by
        simp only [leviM, Matrix.mul_assoc]
    _ = 1 := by rw [hQP, Matrix.mul_one, hb, Matrix.mul_one, frame_mul_Q hQP]

theorem eq_leviM (hQP : Q * frame x y ι = 1) {M : Matrix (Fin (b + 2)) (Fin (b + 2)) A} {G : Matrix (Fin b) (Fin b) A}
    {t s : A} (hx : M *ᵥ x = t • x) (hy : M *ᵥ y = s • y) (hι : M * ι = ι * G) : M = leviM x y ι Q G t s := by
  have h : M * frame x y ι = frame x y ι * blk G t s := by
    simp only [frame, blk, mul_fromCols, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add, hι]
    congr 1
    ext i k
    fin_cases k
    · have := congrFun hx i
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      simp [cols2, Matrix.mul_apply, diagonal, Fin.sum_univ_two]
      rw [this, mul_comm]
    · have := congrFun hy i
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      simp [cols2, Matrix.mul_apply, diagonal, Fin.sum_univ_two]
      rw [this, mul_comm]
  calc M = M * (frame x y ι * Q) := by rw [frame_mul_Q hQP, Matrix.mul_one]
    _ = leviM x y ι Q G t s := by rw [← Matrix.mul_assoc, h]; rfl

end GlobalTheory.IwEmb

namespace GlobalTheory.IwEmb

open Matrix GlobalTheory.LeviElem Topology

variable {R0 A : Type} [CommRing R0] [CommRing A] [Algebra R0 A] [TopologicalSpace A] [IsTopologicalRing A]
  {b : ℕ} {x y : Fin (b + 2) → A} {ι : Matrix (Fin (b + 2)) (Fin b) A} {Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) A}

theorem continuous_blk {X : Type} [TopologicalSpace X] {G : X → Matrix (Fin b) (Fin b) A} {t s : X → A}
    (hG : Continuous G) (ht : Continuous t) (hs : Continuous s) : Continuous fun p => blk (G p) (t p) (s p) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j
  · simp only [blk, fromBlocks_apply₁₁]; exact (continuous_apply j).comp ((continuous_apply i).comp hG)
  · simp [blk]; exact continuous_const
  · simp [blk]; exact continuous_const
  · fin_cases i <;> fin_cases j <;> simp [blk, diagonal] <;> first | exact continuous_const | assumption

theorem continuous_leviM {X : Type} [TopologicalSpace X] {G : X → Matrix (Fin b) (Fin b) A} {t s : X → A}
    (hG : Continuous G) (ht : Continuous t) (hs : Continuous s) :
    Continuous fun p => leviM x y ι Q (G p) (t p) (s p) :=
  (continuous_const.matrix_mul (continuous_blk hG ht hs)).matrix_mul continuous_const

variable [T2Space A]

theorem isClosed_line (hQP : Q * frame x y ι = 1) : IsClosed {v : Fin (b + 2) → A | ∃ a : A, v = a • x} := by
  have : {v : Fin (b + 2) → A | ∃ a : A, v = a • x} = {v | v = (Q *ᵥ v) (Sum.inr 0) • x} := by
    ext v; constructor
    · rintro ⟨a, rfl⟩; show a • x = (Q *ᵥ (a • x)) (Sum.inr 0) • x; rw [mulVec_smul, frame_inverse_mulVec_x hQP]; simp
    · intro h; exact ⟨_, h⟩
  rw [this]
  exact isClosed_eq continuous_id
    (((continuous_apply _).comp (continuous_const.matrix_mulVec continuous_id)).smul continuous_const)

theorem isClosed_unipMat (hQP : Q * frame x y ι = 1) :
    IsClosed {X : Matrix (Fin (b + 2)) (Fin (b + 2)) A | IsUnipMat x ι X} := by
  have h1 : IsClosed {X : Matrix (Fin (b + 2)) (Fin (b + 2)) A | X *ᵥ x = x} :=
    isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const
  have h2 : ∀ z : Fin b → A, IsClosed {X : Matrix (Fin (b + 2)) (Fin (b + 2)) A | ∃ a : A, X *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} := by
    intro z
    have : {X : Matrix (Fin (b + 2)) (Fin (b + 2)) A | ∃ a : A, X *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} =
        (fun X => X *ᵥ (ι *ᵥ z) - ι *ᵥ z) ⁻¹' {v | ∃ a : A, v = a • x} := by
      ext X; simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_eq_iff_eq_add']
    rw [this]
    exact (isClosed_line hQP).preimage ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)
  have : {X : Matrix (Fin (b + 2)) (Fin (b + 2)) A | IsUnipMat x ι X} =
      {X | X *ᵥ x = x} ∩ ⋂ z, {X | ∃ a : A, X *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} := by
    ext X; simp [IsUnipMat]
  rw [this]
  exact h1.inter (isClosed_iInter h2)

end GlobalTheory.IwEmb

namespace GlobalTheory.IwEmb

open Matrix GlobalTheory.LeviElem Topology

variable {R0 A : Type} [CommRing R0] [CommRing A] [Algebra R0 A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  {b : ℕ} {x y : Fin (b + 2) → A} {ι : Matrix (Fin (b + 2)) (Fin b) A} {Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) A}

theorem continuous_mat (c : A →ₐ[R0] A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) :
    Continuous fun g : UG c J => (g.1 : Matrix (Fin n) (Fin n) A) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_matInv (c : A →ₐ[R0] A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) :
    Continuous fun g : UG c J => ((g⁻¹).1 : Matrix (Fin n) (Fin n) A) :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem mat_levi_inv (c : A →ₐ[R0] A) (J : Matrix (Fin (b + 2)) (Fin (b + 2)) A) (J₁ : Matrix (Fin b) (Fin b) A)
    (hQP : Q * frame x y ι = 1) (m : Aˣ → UG c J₁ → UG c J)
    (hm : ∀ l g₀, (m l g₀).1.1 *ᵥ x = l.1 • x ∧ (m l g₀).1.1 *ᵥ y = c (l⁻¹).1 • y ∧ (m l g₀).1.1 * ι = ι * g₀.1.1)
    (l : Aˣ) (g₀ : UG c J₁) :
    (m l g₀).1.1 = leviM x y ι Q g₀.1.1 l.1 (c (l⁻¹).1) ∧
      ((m l g₀)⁻¹).1.1 = leviM x y ι Q (g₀⁻¹).1.1 (l⁻¹).1 (c l.1) := by
  have h1 : (m l g₀).1.1 = leviM x y ι Q g₀.1.1 l.1 (c (l⁻¹).1) :=
    eq_leviM hQP (hm l g₀).1 (hm l g₀).2.1 (hm l g₀).2.2
  refine ⟨h1, ?_⟩
  show (((m l g₀).1)⁻¹ : GL (Fin (b + 2)) A).1 = _
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [h1]
  refine leviM_mul_leviM hQP (Units.mul_inv g₀.1) (Units.mul_inv l) ?_
  rw [← map_mul, Units.inv_mul, map_one]

theorem continuous_levi (c : A →ₐ[R0] A) (hc : Continuous c) (J : Matrix (Fin (b + 2)) (Fin (b + 2)) A)
    (J₁ : Matrix (Fin b) (Fin b) A) (hQP : Q * frame x y ι = 1) (m : Aˣ → UG c J₁ → UG c J)
    (hm : ∀ l g₀, (m l g₀).1.1 *ᵥ x = l.1 • x ∧ (m l g₀).1.1 *ᵥ y = c (l⁻¹).1 • y ∧ (m l g₀).1.1 * ι = ι * g₀.1.1) :
    Continuous fun p : Aˣ × UG c J₁ => m p.1 p.2 := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · have : (Units.val ∘ fun p : Aˣ × UG c J₁ => (m p.1 p.2).1) =
        fun p => leviM x y ι Q p.2.1.1 p.1.1 (c (p.1⁻¹).1) := by
      funext p; exact (mat_levi_inv c J J₁ hQP m hm p.1 p.2).1
    rw [this]
    exact continuous_leviM ((continuous_mat c J₁).comp continuous_snd) (Units.continuous_val.comp continuous_fst)
      (hc.comp (Units.continuous_coe_inv.comp continuous_fst))
  · have : (fun p : Aˣ × UG c J₁ => (((m p.1 p.2).1)⁻¹ : GL (Fin (b + 2)) A).1) =
        fun p => leviM x y ι Q (p.2⁻¹).1.1 (p.1⁻¹).1 (c p.1.1) := by
      funext p; exact (mat_levi_inv c J J₁ hQP m hm p.1 p.2).2
    rw [this]
    exact continuous_leviM ((continuous_matInv c J₁).comp continuous_snd) (Units.continuous_coe_inv.comp continuous_fst)
      (hc.comp (Units.continuous_val.comp continuous_fst))

end GlobalTheory.IwEmb

namespace GlobalTheory.IwEmb

open Matrix GlobalTheory.LeviElem Topology

variable {R0 A : Type} [CommRing R0] [CommRing A] [Algebra R0 A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  {b : ℕ} {x y : Fin (b + 2) → A} {ι : Matrix (Fin (b + 2)) (Fin b) A} {Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) A}

theorem continuous_gam {X : Type} [TopologicalSpace X] {f : X → Matrix (Fin (b + 2)) (Fin (b + 2)) A}
    (hf : Continuous f) : Continuous fun p => gam Q ι (f p) := by
  have h := (continuous_const (y := Q)).matrix_mul hf |>.matrix_mul (continuous_const (y := ι))
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply (Sum.inl i)).comp h)

theorem closedEmb (c : A →ₐ[R0] A) (hc : Continuous c) (J : Matrix (Fin (b + 2)) (Fin (b + 2)) A)
    (J₁ : Matrix (Fin b) (Fin b) A) (hQP : Q * frame x y ι = 1) (m : Aˣ → UG c J₁ → UG c J)
    (hm : ∀ l g₀, (m l g₀).1.1 *ᵥ x = l.1 • x ∧ (m l g₀).1.1 *ᵥ y = c (l⁻¹).1 • y ∧ (m l g₀).1.1 * ι = ι * g₀.1.1) :
    IsClosed ((unipSub c J x ι : Subgroup (UG c J)) : Set (UG c J)) ∧
      IsClosedEmbedding (fun p : unipSub c J x ι × (Aˣ × UG c J₁) => (p.1 : UG c J) * m p.2.1 p.2.2) := by
  have hmat := continuous_mat c J
  have hmatI := continuous_matInv c J
  have hmc := continuous_levi c hc J J₁ hQP m hm
  refine ⟨(isClosed_unipMat hQP).preimage hmat, ?_⟩
  set Rg : Set (UG c J) := {g | tau Q x g.1.1 * tau Q x (g⁻¹).1.1 = 1 ∧ gam Q ι g.1.1 * gam Q ι (g⁻¹).1.1 = 1 ∧
      (gam Q ι g.1.1)ᵀ * J₁ * (gam Q ι g.1.1).map c = J₁ ∧
      IsUnipMat x ι (g.1.1 * leviM x y ι Q (gam Q ι (g⁻¹).1.1) (tau Q x (g⁻¹).1.1) (c (tau Q x g.1.1)))} with hRg
  have hτ : Continuous fun g : UG c J => tau Q x g.1.1 :=
    (continuous_apply _).comp (continuous_const.matrix_mulVec (hmat.matrix_mulVec continuous_const))
  have hτI : Continuous fun g : UG c J => tau Q x (g⁻¹).1.1 :=
    (continuous_apply _).comp (continuous_const.matrix_mulVec (hmatI.matrix_mulVec continuous_const))
  have hγ : Continuous fun g : UG c J => gam Q ι g.1.1 := continuous_gam hmat
  have hγI : Continuous fun g : UG c J => gam Q ι (g⁻¹).1.1 := continuous_gam hmatI
  have hclosed : IsClosed Rg := by
    refine (isClosed_eq (hτ.mul hτI) continuous_const).inter ((isClosed_eq (hγ.matrix_mul hγI) continuous_const).inter
      ((isClosed_eq ((hγ.matrix_transpose.matrix_mul continuous_const).matrix_mul (hγ.matrix_map hc))
        continuous_const).inter ((isClosed_unipMat hQP).preimage (hmat.matrix_mul
          (continuous_leviM hγI hτI (hc.comp hτ))))))

  obtain ⟨lf, hlfc, hlf⟩ : ∃ lf : Rg → Aˣ, Continuous lf ∧
      ∀ g, (lf g).1 = tau Q x g.1.1.1 ∧ ((lf g)⁻¹).1 = tau Q x (g.1⁻¹).1.1 := by
    refine ⟨fun g => ⟨tau Q x g.1.1.1, tau Q x (g.1⁻¹).1.1, g.2.1, by rw [mul_comm]; exact g.2.1⟩,
      Units.continuous_iff.2 ⟨hτ.comp continuous_subtype_val, hτI.comp continuous_subtype_val⟩, fun g => ⟨rfl, rfl⟩⟩
  obtain ⟨gf, hgfc, hgf⟩ : ∃ gf : Rg → UG c J₁, Continuous gf ∧
      ∀ g, (gf g).1.1 = gam Q ι g.1.1.1 ∧ ((gf g)⁻¹).1.1 = gam Q ι (g.1⁻¹).1.1 := by
    let u : Rg → GL (Fin b) A := fun g =>
      ⟨gam Q ι g.1.1.1, gam Q ι (g.1⁻¹).1.1, g.2.2.1, (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 g.2.2.1⟩
    have hu : Continuous u :=
      Units.continuous_iff.2 ⟨hγ.comp continuous_subtype_val, hγI.comp continuous_subtype_val⟩
    exact ⟨fun g => ⟨u g, g.2.2.2.1⟩, hu.subtype_mk _, fun g => ⟨rfl, rfl⟩⟩
  have hn : ∀ g : Rg, g.1 * (m (lf g) (gf g))⁻¹ ∈ unipSub c J x ι := by
    intro g
    show IsUnipMat x ι (g.1.1.1 * ((m (lf g) (gf g))⁻¹).1.1)
    rw [(mat_levi_inv c J J₁ hQP m hm _ _).2, (hlf g).1, (hlf g).2, (hgf g).2]
    exact g.2.2.2.2

  have hrange : Set.range (fun p : unipSub c J x ι × (Aˣ × UG c J₁) => (p.1 : UG c J) * m p.2.1 p.2.2) = Rg := by
    ext g
    constructor
    · rintro ⟨⟨n, l, g₀⟩, rfl⟩
      have hN : IsUnipMat x ι n.1.1.1 := n.2
      have hNI : IsUnipMat x ι ((n⁻¹ : unipSub c J x ι) : UG c J).1.1 := (n⁻¹).2
      obtain ⟨h1, h2⟩ := mat_levi_inv c J J₁ hQP m hm l g₀
      have e1 : ((n : UG c J) * m l g₀).1.1 = n.1.1.1 * (m l g₀).1.1 := rfl
      have e2 : (((n : UG c J) * m l g₀)⁻¹).1.1 = ((m l g₀)⁻¹).1.1 * ((n⁻¹ : unipSub c J x ι) : UG c J).1.1 := by
        rw [_root_.mul_inv_rev]; rfl
      have t1 : tau Q x ((n : UG c J) * m l g₀).1.1 = l.1 := by rw [e1, h1, tau_mul_leviM hQP hN]
      have t2 : tau Q x (((n : UG c J) * m l g₀)⁻¹).1.1 = (l⁻¹).1 := by rw [e2, h2, tau_leviM_mul hQP hNI]
      have g1 : gam Q ι ((n : UG c J) * m l g₀).1.1 = g₀.1.1 := by rw [e1, h1, gam_mul_leviM hQP hN]
      have g2 : gam Q ι (((n : UG c J) * m l g₀)⁻¹).1.1 = (g₀⁻¹).1.1 := by rw [e2, h2, gam_leviM_mul hQP hNI]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [t1, t2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      · rw [g1, g2]; exact Units.mul_inv g₀.1
      · rw [g1]; exact g₀.2
      · rw [t1, t2, g2, e1, h1, Matrix.mul_assoc, leviM_mul_leviM (G' := (g₀⁻¹).1.1) hQP (Units.mul_inv g₀.1) (Units.mul_inv l)
          (by rw [← map_mul, Units.inv_mul, map_one]), Matrix.mul_one]
        exact hN
    · intro hg
      exact ⟨(⟨g * (m (lf ⟨g, hg⟩) (gf ⟨g, hg⟩))⁻¹, hn ⟨g, hg⟩⟩, lf ⟨g, hg⟩, gf ⟨g, hg⟩), inv_mul_cancel_right _ _⟩
  have hsub : ∀ p : unipSub c J x ι × (Aˣ × UG c J₁), (p.1 : UG c J) * m p.2.1 p.2.2 ∈ Rg :=
    fun p => hrange ▸ Set.mem_range_self p
  have hφc : Continuous fun p : unipSub c J x ι × (Aˣ × UG c J₁) => (p.1 : UG c J) * m p.2.1 p.2.2 :=
    (continuous_subtype_val.comp continuous_fst).mul (hmc.comp continuous_snd)
  set φ' : unipSub c J x ι × (Aˣ × UG c J₁) → Rg := fun p => ⟨(p.1 : UG c J) * m p.2.1 p.2.2, hsub p⟩ with hφ'
  set R : Rg → unipSub c J x ι × (Aˣ × UG c J₁) :=
    fun g => (⟨g.1 * (m (lf g) (gf g))⁻¹, hn g⟩, lf g, gf g) with hR
  have hRc : Continuous R :=
    (Continuous.subtype_mk (continuous_subtype_val.mul (hmc.comp (hlfc.prodMk hgfc)).inv) _).prodMk
      (hlfc.prodMk hgfc)
  have hleft : Function.LeftInverse R φ' := by
    rintro ⟨n, l, g₀⟩
    have hN : IsUnipMat x ι n.1.1.1 := n.2
    obtain ⟨h1, -⟩ := mat_levi_inv c J J₁ hQP m hm l g₀
    have el : lf (φ' (n, l, g₀)) = l := by
      ext; rw [(hlf _).1]; show tau Q x (n.1.1.1 * (m l g₀).1.1) = l.1; rw [h1, tau_mul_leviM hQP hN]
    have eg : gf (φ' (n, l, g₀)) = g₀ := by
      apply Subtype.ext; apply Units.ext
      rw [(hgf _).1]; show gam Q ι (n.1.1.1 * (m l g₀).1.1) = g₀.1.1; rw [h1, gam_mul_leviM hQP hN]
    simp only [hR, el, eg]
    refine Prod.ext (Subtype.ext ?_) rfl
    show (n : UG c J) * m l g₀ * (m l g₀)⁻¹ = n
    exact mul_inv_cancel_right _ _
  have hemb : IsEmbedding φ' := hleft.isEmbedding hRc (Continuous.subtype_mk hφc _)
  exact IsClosedEmbedding.mk (IsEmbedding.subtypeVal.comp hemb) (hrange ▸ hclosed)

end GlobalTheory.IwEmb

namespace GlobalTheory.IwEmb

open Matrix GlobalTheory.LeviElem Topology

theorem unip_closedEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    IsClosed ((unip σ G.V H : Subgroup (UA σ G.V.J)) : Set (UA σ G.V.J)) ∧
    IsClosedEmbedding (fun p : unip σ G.V H × ((AE F E)ˣ × UA σ G₁.V.J) => (p.1 : UA σ G.V.J) * m p.2.1 p.2.2) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ m hm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hPf : P.map f = frame (incV F H.x) (incV F H.y) (incM F H.ι) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * frame (incV F H.x) (incV F H.y) (incM F H.ι) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (AE F E) := by
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
    exact e.isEmbedding.t2Space
  have hc : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hU : unip σ G.V H = unipSub (cA σ) (incM F G.V.J) (incV F H.x) (incM F H.ι) :=
    Subgroup.closure_eq (unipSub (cA σ) (incM F G.V.J) (incV F H.x) (incM F H.ι))
  rw [hU]
  exact closedEmb (cA σ) hc (incM F G.V.J) (incM F G₁.V.J) hQP' m hm

end GlobalTheory.IwEmb
