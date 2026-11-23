import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.UniSp

noncomputable section

section Abstract
variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
  {S : Matrix ι K ℂ} {S' : Matrix K ι ℂ}

theorem transport (h1 : S * S' = 1) (h2 : S' * S = 1) {a b c d T W Qi : Matrix K K ℂ}
    (hQ : (c * T + d) * Qi = 1) (hW : (a * T + b) * Qi = W) {den : Matrix ι ι ℂ}
    (hden : den = S'ᵀ * c * S' * (S * T * Sᵀ) + S'ᵀ * d * Sᵀ) :
    den.det = (c * T + d).det ∧
    (S * a * S' * (S * T * Sᵀ) + S * b * Sᵀ) * den⁻¹ = S * W * Sᵀ ∧
    ∀ w : K → ℂ, (S *ᵥ w) ᵥ* den⁻¹ = S *ᵥ (w ᵥ* Qi) ∧
      (S *ᵥ w) ⬝ᵥ (den⁻¹ * (S'ᵀ * c * S')) *ᵥ (S *ᵥ w) = w ⬝ᵥ (Qi * c) *ᵥ w := by
  have t1 : S'ᵀ * Sᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  have t2 : Sᵀ * S'ᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have c2 : ∀ X : Matrix K ι ℂ, S' * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have c3 : ∀ X : Matrix K ι ℂ, Sᵀ * (S'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, t2, Matrix.one_mul]
  have e : den = S'ᵀ * (c * T + d) * Sᵀ := by
    simp only [hden, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, c2]
  have ei : den⁻¹ = S'ᵀ * Qi * Sᵀ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [e]
    simp only [Matrix.mul_assoc, c3]
    rw [← Matrix.mul_assoc _ Qi, hQ, Matrix.one_mul, t1]
  refine ⟨by rw [e, Matrix.det_conj_of_mul_eq_one t1 t2], ?_, fun w => ⟨?_, ?_⟩⟩
  · rw [ei, ← hW]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, c2, c3]
  · rw [ei, ← vecMul_transpose, ← vecMul_transpose, vecMul_vecMul, vecMul_vecMul]
    simp only [Matrix.mul_assoc, c3]
  · rw [ei, dotProduct_mulVec, ← vecMul_transpose S w, vecMul_vecMul, ← dotProduct_mulVec,
      vecMul_transpose, mulVec_mulVec]
    simp only [Matrix.mul_assoc, c3, h2, Matrix.mul_one]

theorem transport_sp (h1 : S * S' = 1) (h2 : S' * S = 1) {a b c d : Matrix K K ℂ}
    (e1 : b * aᵀ = a * bᵀ) (e2 : a * dᵀ = b * cᵀ + 1) (e3 : d * aᵀ = c * bᵀ + 1)
    (e4 : d * cᵀ = c * dᵀ) :
    fromBlocks (S * a * S') (S * b * Sᵀ) (S'ᵀ * c * S') (S'ᵀ * d * Sᵀ) * Matrix.J ι ℂ *
      (fromBlocks (S * a * S') (S * b * Sᵀ) (S'ᵀ * c * S') (S'ᵀ * d * Sᵀ))ᵀ = Matrix.J ι ℂ := by
  have t1 : S'ᵀ * Sᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  have t2 : Sᵀ * S'ᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have c2 : ∀ X : Matrix K ι ℂ, S' * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have c3 : ∀ X : Matrix K ι ℂ, Sᵀ * (S'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, t2, Matrix.one_mul]
  have f : ∀ (x y : Matrix K K ℂ) (X : Matrix K ι ℂ), x * (y * X) = (x * y) * X :=
    fun x y X => (Matrix.mul_assoc _ _ _).symm
  rw [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
    Matrix.neg_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc, c2, c3]
  simp only [f, e1, e2, e3, e4, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, h1, t1]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

variable {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]

theorem vecMul_bd (w : m × o → ℂ) (M : o → Matrix m m ℂ) (p : m × o) :
    (w ᵥ* blockDiagonal M) p = ((fun i => w (i, p.2)) ᵥ* M p.2) p.1 := by
  simp [vecMul, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]

theorem quad_bd (w : m × o → ℂ) (M : o → Matrix m m ℂ) :
    w ⬝ᵥ blockDiagonal M *ᵥ w = ∑ t, (fun i => w (i, t)) ⬝ᵥ M t *ᵥ fun i => w (i, t) := by
  simp only [dotProduct_mulVec]
  simp only [dotProduct, vecMul_bd]
  rw [Fintype.sum_prod_type_right]

variable [DecidableEq m]

def dl (X : Matrix m m ℂ) : Matrix (m ⊕ m) (m ⊕ m) ℂ := fromBlocks X 0 0 Xᴴᵀ

def sw (m : Type) [DecidableEq m] : Matrix (m ⊕ m) (m ⊕ m) ℂ := fromBlocks 0 1 1 0

theorem sw_sw : sw m * sw m = 1 := by simp [sw, fromBlocks_multiply]

theorem local_sp {A B C D : Matrix m m ℂ} (h1 : A * Bᴴ = B * Aᴴ) (h2 : A * Dᴴ = B * Cᴴ + 1)
    (h3 : D * Aᴴ = C * Bᴴ + 1) (h4 : C * Dᴴ = D * Cᴴ) :
    dl B * sw m * (dl A)ᵀ = dl A * (dl B * sw m)ᵀ ∧
    dl A * (sw m * dl D * sw m)ᵀ = dl B * sw m * (sw m * dl C)ᵀ + 1 ∧
    sw m * dl D * sw m * (dl A)ᵀ = sw m * dl C * (dl B * sw m)ᵀ + 1 ∧
    sw m * dl D * sw m * (sw m * dl C)ᵀ = sw m * dl C * (sw m * dl D * sw m)ᵀ := by
  have g1 := congrArg transpose h1
  have g2 := congrArg transpose h2
  have g3 := congrArg transpose h3
  have g4 := congrArg transpose h4
  simp only [transpose_mul, transpose_add, transpose_one] at g1 g2 g3 g4
  rw [← fromBlocks_one]
  simp only [dl, sw, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_add, transpose_zero,
    transpose_transpose, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero,
    zero_add, h1, h2, h3, h4, g1, g2, g3, g4, and_self]

theorem local_den (C D Z : Matrix m m ℂ) :
    sw m * dl C * fromBlocks 0 Z Zᵀ 0 + sw m * dl D * sw m =
      fromBlocks (Z * Cᴴ + Dᴴ)ᵀ 0 0 (C * Z + D) := by
  simp [dl, sw, fromBlocks_multiply, fromBlocks_add]

theorem local_num (A B Z : Matrix m m ℂ) :
    dl A * fromBlocks 0 Z Zᵀ 0 + dl B * sw m =
      fromBlocks 0 (A * Z + B) (Z * Aᴴ + Bᴴ)ᵀ 0 := by
  simp [dl, sw, fromBlocks_multiply, fromBlocks_add]

theorem local_quad {C D Z : Matrix m m ℂ} (h4 : C * Dᴴ = D * Cᴴ) (hP : (Z * Cᴴ + Dᴴ).det ≠ 0)
    (hQ : (C * Z + D).det ≠ 0) (z z' : m → ℂ) :
    Sum.elim z z' ⬝ᵥ (fromBlocks ((Z * Cᴴ + Dᴴ)⁻¹)ᵀ 0 0 (C * Z + D)⁻¹ * (sw m * dl C)) *ᵥ
      Sum.elim z z' = 2 * (z' ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ z) := by
  have e : Cᴴ * (Z * Cᴴ + Dᴴ)⁻¹ = (C * Z + D)⁻¹ * C := by
    have e0 : (C * Z + D) * Cᴴ = C * (Z * Cᴴ + Dᴴ) := by
      rw [Matrix.add_mul, Matrix.mul_add, h4, Matrix.mul_assoc]
    calc _ = (C * Z + D)⁻¹ * ((C * Z + D) * Cᴴ) * (Z * Cᴴ + Dᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hQ), Matrix.one_mul]
      _ = _ := by
          rw [e0, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hP),
            Matrix.mul_one]
  simp only [dl, sw, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.one_mul, add_zero, zero_add, ← transpose_mul, e, fromBlocks_mulVec, zero_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
  rw [mulVec_transpose, dotProduct_comm z, ← dotProduct_mulVec, two_mul]

end Abstract

open Classical

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def Sm (Ψ : Finset (E →+* ℂ)) (N : ℕ) : Matrix (QI E N) ((Fin N ⊕ Fin N) × Ψ) ℂ :=
  Matrix.of fun p q => Sum.elim
    (fun b => if p.1 = b then q.2.1 (Module.finBasis ℚ E p.2) else 0)
    (fun b => if p.1 = b then conj (q.2.1 (Module.finBasis ℚ E p.2)) else 0) q.1

variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}

theorem zeta_eq (z z' : CM Ψ n N) (k : Fin n) :
    zetaOf Ψ z z' k = Sm Ψ N *ᵥ fun q => Sum.elim (z q.2 k) (z' q.2 k) q.1 := by
  funext p
  simp [zetaOf, Sm, mulVec, dotProduct, Fintype.sum_prod_type_right, Fintype.sum_sum_type,
    mul_comm]

theorem conj_apply (M : Ψ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ) (p q : QI E N) :
    (Sm Ψ N * blockDiagonal M * (Sm Ψ N)ᵀ) p q = ∑ τ : Ψ,
      (fun i => Sm Ψ N p (i, τ)) ᵥ* M τ ⬝ᵥ fun i => Sm Ψ N q (i, τ) := by
  change ∑ x, (Sm Ψ N p ᵥ* blockDiagonal M) x * Sm Ψ N q x = _
  simp only [vecMul_bd]
  rw [Fintype.sum_prod_type_right]
  rfl

theorem tau_eq (Z : CM Ψ N N) :
    tauOf Ψ Z = Sm Ψ N * blockDiagonal (fun τ => fromBlocks 0 (Z τ) (Z τ)ᵀ 0) * (Sm Ψ N)ᵀ := by
  ext p q
  rw [conj_apply]
  simp only [tauOf, Matrix.of_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [Sm, vecMul, dotProduct, Fintype.sum_sum_type]
  ring

theorem exists_inv (hΨ : IsType Ψ) : ∃ S' : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ,
    Sm Ψ N * S' = 1 ∧ S' * Sm Ψ N = 1 := by
  choose z z' h using fun p : QI E N =>
    Dict.zetaOf_surj (n := 1) hΨ fun _ => (Pi.single p 1 : QI E N → ℂ)
  have h1 : Sm Ψ N * (Matrix.of fun (q : (Fin N ⊕ Fin N) × Ψ) (p : QI E N) =>
      Sum.elim (z p q.2 0) (z' p q.2 0) q.1) = 1 := by
    ext q p
    have := congrFun (congrFun (h p) 0) q
    rw [zeta_eq, Pi.single_apply] at this
    rw [Matrix.one_apply, ← this]
    rfl
  have hc : Fintype.card (QI E N) = Fintype.card ((Fin N ⊕ Fin N) × Ψ) := by
    have := Dict.sum_type hΨ (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul, mul_one,
      mul_add] at this
    have h2 : Module.finrank ℚ E = Fintype.card Ψ + Fintype.card Ψ := by exact_mod_cast this
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, h2]
    ring
  exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hc)).1 h1⟩

theorem qm_mul {α β δ : Type} [Fintype β] (X : Matrix α β ℚ) (Y : Matrix β δ ℚ) :
    qm (X * Y) = qm X * qm Y := by
  ext i j
  simp [qm, Matrix.mul_apply]

theorem qm_inj {α β : Type} {X Y : Matrix α β ℚ} (h : qm X = qm Y) : X = Y := by
  ext i j
  have := congrFun (congrFun h i) j
  simpa [qm] using this

theorem qm_one {α : Type} [DecidableEq α] : qm (1 : Matrix α α ℚ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [qm, Matrix.one_apply, h]

theorem qm_J {α : Type} [DecidableEq α] : qm (Matrix.J α ℚ) = Matrix.J α ℂ := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;> simp [qm, Matrix.J, Matrix.one_apply, h]

theorem exists_reg (X : Matrix (Fin N) (Fin N) E) : ∃ R : Matrix (QI E N) (QI E N) ℚ,
    qm R * Sm Ψ N = Sm Ψ N * blockDiagonal fun τ : Ψ => dl (X.map τ.1) := by
  refine ⟨Matrix.of fun p q =>
    (Module.finBasis ℚ E).repr (Module.finBasis ℚ E p.2 * X p.1 q.1) q.2, ?_⟩
  ext p ⟨i, τ⟩
  change _ = (Sm Ψ N p ᵥ* _) _
  rw [vecMul_bd]
  have key : ∀ x : E, ∑ j, (((Module.finBasis ℚ E).repr x j : ℚ) : ℂ) *
      τ.1 (Module.finBasis ℚ E j) = τ.1 x := fun x => by
    conv_rhs => rw [← (Module.finBasis ℚ E).sum_repr x]
    simp [Algebra.smul_def]
  have key' : ∀ x : E, ∑ j, (((Module.finBasis ℚ E).repr x j : ℚ) : ℂ) *
      conj (τ.1 (Module.finBasis ℚ E j)) = conj (τ.1 x) := fun x => by
    rw [← key x]
    simp
  rcases i with b | b
  · simp [Matrix.mul_apply, qm, Sm, Fintype.sum_prod_type_right, vecMul, dotProduct, dl, key, -Module.Basis.repr_self]
  · simp [Matrix.mul_apply, qm, Sm, Fintype.sum_prod_type_right, vecMul, dotProduct, dl, key', -Module.Basis.repr_self]

theorem exists_gram [IsCMField E] (hΨ : IsType Ψ) : ∃ G : Matrix (QI E N) (QI E N) ℚ,
    qm G = Sm Ψ N * blockDiagonal (fun _ : Ψ => sw (Fin N)) * (Sm Ψ N)ᵀ := by
  refine ⟨Matrix.of fun p q => if p.1 = q.1 then
    Algebra.trace ℚ E (Module.finBasis ℚ E p.2 * cc (Module.finBasis ℚ E q.2)) else 0, ?_⟩
  ext p q
  rw [conj_apply]
  have key : ∀ x : E, ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : Ψ, (τ.1 x + conj (τ.1 x)) := by
    intro x
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)
    have h2 := Dict.sum_type hΨ (fun σ => σ x)
    simp only [ComplexEmbedding.conjugate_coe_eq] at h2
    rw [← h2, ← eq_ratCast (algebraMap ℚ ℂ), h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)) _ _ fun _ => rfl).symm
  by_cases h : p.1 = q.1
  · simp only [qm, Matrix.map_apply, Matrix.of_apply, if_pos h, key]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp [Sm, sw, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, h, HAct.emb_cc]
    ring
  · simp [qm, Sm, sw, vecMul, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, h, Ne.symm h]

theorem exists_blocks [IsCMField E] (hΨ : IsType Ψ)
    {S' : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ} (h1 : Sm Ψ N * S' = 1) (h2 : S' * Sm Ψ N = 1)
    (A B C D : Matrix (Fin N) (Fin N) E) :
    ∃ σ : Matrix (QI E N ⊕ QI E N) (QI E N ⊕ QI E N) ℚ,
      qm σ.toBlocks₁₁ = Sm Ψ N * blockDiagonal (fun τ : Ψ => dl (A.map τ.1)) * S' ∧
      qm σ.toBlocks₁₂ = Sm Ψ N * blockDiagonal (fun τ : Ψ => dl (B.map τ.1) * sw _) * (Sm Ψ N)ᵀ ∧
      qm σ.toBlocks₂₁ = S'ᵀ * blockDiagonal (fun τ : Ψ => sw _ * dl (C.map τ.1)) * S' ∧
      qm σ.toBlocks₂₂ = S'ᵀ * blockDiagonal (fun τ : Ψ => sw _ * dl (D.map τ.1) * sw _) *
        (Sm Ψ N)ᵀ := by
  have hR : ∀ X : Matrix (Fin N) (Fin N) E, ∃ R : Matrix (QI E N) (QI E N) ℚ,
      qm R = Sm Ψ N * (blockDiagonal fun τ : Ψ => dl (X.map τ.1)) * S' := fun X => by
    obtain ⟨R, hR⟩ := exists_reg (Ψ := Ψ) X
    exact ⟨R, by rw [← hR, Matrix.mul_assoc, h1, Matrix.mul_one]⟩
  choose R hR using hR
  obtain ⟨G, hG⟩ := exists_gram (N := N) hΨ
  have t2 : (Sm Ψ N)ᵀ * S'ᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have c2 : ∀ X : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ,
      S' * (Sm Ψ N * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have c3 : ∀ X : Matrix ((Fin N ⊕ Fin N) × Ψ) (QI E N) ℂ,
      (Sm Ψ N)ᵀ * (S'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, t2, Matrix.one_mul]
  have hGi : qm G * (S'ᵀ * blockDiagonal (fun _ : Ψ => sw (Fin N)) * S') = 1 := by
    rw [hG]
    simp only [Matrix.mul_assoc, c3]
    rw [← Matrix.mul_assoc (blockDiagonal _), ← blockDiagonal_mul]
    simp only [sw_sw]
    rw [show (fun _ : Ψ => (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)) = 1 from rfl,
      blockDiagonal_one, Matrix.one_mul, h1]
  have hdet : G.det ≠ 0 := by
    intro h0
    have e : (qm G).det = ((G.det : ℚ) : ℂ) := ((Rat.castHom ℂ).map_det G).symm
    have := congrArg det hGi
    rw [det_mul, e, h0] at this
    simp at this
  have hGinv : qm G⁻¹ = S'ᵀ * blockDiagonal (fun _ : Ψ => sw (Fin N)) * S' := by
    rw [← Matrix.mul_one (qm G⁻¹), ← hGi, ← Matrix.mul_assoc, ← qm_mul,
      nonsing_inv_mul _ (Ne.isUnit hdet), qm_one, Matrix.one_mul]
  refine ⟨fromBlocks (R A) (R B * G) (G⁻¹ * R C) (G⁻¹ * R D * G), hR A, ?_, ?_, ?_⟩
  all_goals
    simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, qm_mul, hR,
      hGinv, hG, blockDiagonal_mul, Matrix.mul_assoc, c2]

end

end GlobalTheory.SW.UniSp

open GlobalTheory.SW.UniSp GlobalTheory.SW.HAct Classical in

theorem GlobalTheory.SW.exists_symplectic_of_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (γ : M2 E N), γ ∈ UU E N → ∃ σ ∈ Matrix.symplecticGroup (QI E N) ℚ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Z ∈ Hn Ψ N, spAct σ (tauOf Ψ Z) = tauOf Ψ (hAct Ψ γ Z) ∧ (spDen σ (tauOf Ψ Z)).det = c * ∏ τ, (hDen Ψ γ Z τ).det ^ 2 ∧ ∀ z z' : CM Ψ n N, (zetaOf Ψ (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (hDen Ψ γ Z τ)⁻¹) = fun k => zetaOf Ψ z z' k ᵥ* (spDen σ (tauOf Ψ Z))⁻¹) ∧ ∀ k, zetaOf Ψ z z' k ⬝ᵥ ((spDen σ (tauOf Ψ Z))⁻¹ * qm σ.toBlocks₂₁) *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ ((hDen Ψ γ Z τ)⁻¹ * γ.toBlocks₂₁.map τ.1) *ᵥ z τ k := by
  intro E _ _ _ Ψ hΨ n N γ hγ
  obtain ⟨S', h1, h2⟩ := exists_inv (N := N) hΨ
  obtain ⟨σ, s1, s2, s3, s4⟩ := exists_blocks hΨ h1 h2 γ.toBlocks₁₁ γ.toBlocks₁₂ γ.toBlocks₂₁
    γ.toBlocks₂₂
  have hb := fun τ : Ψ => blocks (map_blocks τ.1 γ ▸ map_mem τ.1 hγ)
  have hb' : ∀ τ : Ψ, _ := fun τ : Ψ => by
    have h := map_mem τ.1 (group_part hγ).2.2.1
    rw [map_ccT, map_blocks τ.1 γ, fromBlocks_conjTranspose] at h
    have h' := blocks h
    simp only [conjTranspose_conjTranspose] at h'
    exact h'
  have one : ∀ {m : Type} [DecidableEq m],
      blockDiagonal (fun _ : Ψ => (1 : Matrix m m ℂ)) = 1 := fun {m} _ => blockDiagonal_one
  have add : ∀ {m : Type} (X Y : Ψ → Matrix m m ℂ),
      blockDiagonal X + blockDiagonal Y = blockDiagonal fun τ => X τ + Y τ :=
    fun X Y => (blockDiagonal_add X Y).symm
  have hl := fun τ : Ψ => local_sp (hb' τ).1 (hb' τ).2.1 (hb' τ).2.2.1 (hb' τ).2.2.2
  refine ⟨σ, ?_, ∏ τ : Ψ, (τ.1 γ.det)⁻¹, ?_, fun Z hZ => ?_⟩
  · rw [SymplecticGroup.mem_iff]
    apply qm_inj
    have e : qm σ = fromBlocks (qm σ.toBlocks₁₁) (qm σ.toBlocks₁₂) (qm σ.toBlocks₂₁)
        (qm σ.toBlocks₂₂) := by
      simp only [qm]
      rw [← fromBlocks_map, fromBlocks_toBlocks]
    rw [qm_mul, qm_mul, qm_J, show qm σᵀ = (qm σ)ᵀ from rfl, e, s1, s2, s3, s4]
    refine transport_sp h1 h2 ?_ ?_ ?_ ?_
    all_goals
      simp only [blockDiagonal_transpose, ← blockDiagonal_mul, ← one, add]
      congr 1
      funext τ
    exacts [(hl τ).1, (hl τ).2.1, (hl τ).2.2.1, (hl τ).2.2.2]
  · simp [norm_prod, norm_det _ hγ]
  obtain ⟨hA, -⟩ := (unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  have hQ : ∀ τ, (hDen Ψ γ Z τ).det ≠ 0 := fun τ => (hA τ).1
  have hP : ∀ τ, (hDen' Ψ γ Z τ).det ≠ 0 := fun τ h => hQ τ (by rw [← (hA τ).2.1, h, zero_mul])
  have hden : blockDiagonal (fun τ : Ψ => sw _ * dl (γ.toBlocks₂₁.map τ.1)) *
      blockDiagonal (fun τ => fromBlocks 0 (Z τ) (Z τ)ᵀ 0) +
      blockDiagonal (fun τ : Ψ => sw _ * dl (γ.toBlocks₂₂.map τ.1) * sw _) =
      blockDiagonal fun τ => fromBlocks (hDen' Ψ γ Z τ)ᵀ 0 0 (hDen Ψ γ Z τ) := by
    simp only [← blockDiagonal_mul, add, local_den]
    rfl
  obtain ⟨t1, t2, t3⟩ := transport h1 h2
    (a := blockDiagonal fun τ : Ψ => dl (γ.toBlocks₁₁.map τ.1))
    (b := blockDiagonal fun τ : Ψ => dl (γ.toBlocks₁₂.map τ.1) * sw _)
    (c := blockDiagonal fun τ : Ψ => sw _ * dl (γ.toBlocks₂₁.map τ.1))
    (d := blockDiagonal fun τ : Ψ => sw _ * dl (γ.toBlocks₂₂.map τ.1) * sw _)
    (T := blockDiagonal fun τ => fromBlocks 0 (Z τ) (Z τ)ᵀ 0)
    (W := blockDiagonal fun τ => fromBlocks 0 (hAct Ψ γ Z τ) (hAct Ψ γ Z τ)ᵀ 0)
    (Qi := blockDiagonal fun τ => fromBlocks ((hDen' Ψ γ Z τ)⁻¹)ᵀ 0 0 (hDen Ψ γ Z τ)⁻¹)
    (den := spDen σ (tauOf Ψ Z))
    (by
      rw [hden, ← blockDiagonal_mul, ← one]
      congr 1
      funext τ
      simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        ← transpose_mul, nonsing_inv_mul _ (Ne.isUnit (hP τ)), mul_nonsing_inv _ (Ne.isUnit (hQ τ)),
        transpose_one, fromBlocks_one])
    (by
      simp only [← blockDiagonal_mul, add, local_num]
      congr 1
      funext τ
      have hd : hDen' Ψ γ Z τ * hAct Ψ γ Z τ = _ :=
        den'_act (hb τ).1 (hb τ).2.1 (hb τ).2.2.1 (hb τ).2.2.2 (hQ τ)
      simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        ← transpose_mul, ← hd, nonsing_inv_mul_cancel_left _ _ (Ne.isUnit (hP τ))]
      rfl)
    (by rw [spDen, s3, s4, tau_eq])
  refine ⟨?_, ?_, fun z z' => ⟨?_, fun k => ?_⟩⟩
  · rw [spAct, s1, s2, tau_eq (hAct Ψ γ Z), ← t2, ← tau_eq]
  · rw [t1, hden, det_blockDiagonal, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h0 : τ.1 γ.det ≠ 0 := fun h => by
      have := norm_det τ.1 hγ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    rw [det_fromBlocks_zero₂₁, det_transpose, ← (hA τ).2.1]
    field_simp
  · funext k
    rw [zeta_eq, zeta_eq, (t3 _).1]
    congr 1
    funext ⟨i, τ⟩
    rw [vecMul_bd]
    change _ = (Sum.elim (z τ k) (z' τ k) ᵥ* fromBlocks _ _ _ _) i
    rw [vecMul_fromBlocks]
    rcases i with a | a <;> simp [vecMul_transpose]
  · rw [zeta_eq, s3, (t3 _).2, ← blockDiagonal_mul, quad_bd, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => local_quad (hb' τ).2.2.2 (hP τ) (hQ τ) (z τ k) (z' τ k)
