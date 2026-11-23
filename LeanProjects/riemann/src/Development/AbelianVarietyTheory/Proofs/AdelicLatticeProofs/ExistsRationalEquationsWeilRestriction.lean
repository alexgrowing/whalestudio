import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordsLeftMulMatrixConstBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalCoordPolynomialBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RestrictScalarsMatrixOfBasisHomInjectiveIsUnitStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.WeilEqs

noncomputable def coordOf {κ β R : Type} [Fintype β] [CommRing R] [Algebra ℚ R] (c : β → ℚ)
    (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) : R :=
  ∑ l, y (Sum.inl (i, k)) (Sum.inl (j, l)) * algebraMap ℚ R (c l)

noncomputable def gen (ι : Type) : Matrix ι ι (MvPolynomial (ι × ι) ℚ) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

section
variable {κ β R : Type} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] [CommRing R] [Algebra ℚ R]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_coordOf (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) (i j : κ) (k : β) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (coordOf c (gen ((κ × β) ⊕ Unit)) i j k) = coordOf c y i j k := by
  simp only [coordOf, gen, map_sum, map_mul, Matrix.of_apply, MvPolynomial.aeval_X, AlgHom.commutes]

theorem aeval_det (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      ((gen ((κ × β) ⊕ Unit)).toBlocks₁₁.det) = y.toBlocks₁₁.det := by
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp [gen, Matrix.toBlocks₁₁]

omit [Fintype κ] [DecidableEq κ] [DecidableEq β] in
theorem aeval_comp_coord (c : β → ℚ) (y : Matrix ((κ × β) ⊕ Unit) ((κ × β) ⊕ Unit) R)
    (Q : MvPolynomial ((κ × κ) × β) ℚ) :
    MvPolynomial.aeval (fun ij : ((κ × β) ⊕ Unit) × ((κ × β) ⊕ Unit) => y ij.1 ij.2)
      (MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c (gen ((κ × β) ⊕ Unit)) p.1.1 p.1.2 p.2) Q) =
      MvPolynomial.aeval (fun p : (κ × κ) × β => coordOf c y p.1.1 p.1.2 p.2) Q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [aeval_coordOf]

variable {A : Type} [CommRing A] [Algebra R A]

theorem sum_leftMul_one (b : Module.Basis β R A) (x : A) (k : β) :
    ∑ l, Algebra.leftMulMatrix b x k l * b.repr 1 l = b.repr x k := by
  have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b x 1) k
  simpa [Matrix.mulVec, dotProduct] using h

theorem leftMul_expand (b : Module.Basis β R A) (x : A) (k l : β) :
    Algebra.leftMulMatrix b x k l = ∑ m, b.repr x m * Algebra.leftMulMatrix b (b m) k l := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end

theorem exists_equations : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), ∃ S' : Set (MvPolynomial (((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit)) ℚ), ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ y : Matrix ((Fin n × β) ⊕ Unit) ((Fin n × β) ⊕ Unit) R, (∀ f ∈ S', ev f y = 0) ↔ ∃ g : GL (Fin n) A, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) P = 0) ∧ y = emb b g := by
  intro F β _ _ _ _ ω n S
  choose Q hQ using fun P : MvPolynomial (Fin n × Fin n) F => GlobalTheory.T.exists_rational_coord_polynomial_baseChange F β ω (Fin n × Fin n) P
  let c : β → ℚ := fun l => ω.repr 1 l
  let X := gen ((Fin n × β) ⊕ Unit)
  refine ⟨{f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ?_⟩
  intro R A _ _ _ _ _ b hb y
  have hm := GlobalTheory.T.coords_leftMulMatrix_const_baseChange F β ω R A b hb
  obtain ⟨h1, hmul, -, hunit⟩ := GlobalTheory.T.restrictScalarsMatrixOfBasis_hom_injective_isUnit R A β (Fin n) b
  have hc : ∀ l, algebraMap ℚ R (c l) = b.repr 1 l := fun l => by
    have := (hm 1).1 l
    rw [map_one] at this
    exact this.symm
  have hL : ∀ m k l, algebraMap ℚ R (Algebra.leftMulMatrix ω (ω m) k l) =
      Algebra.leftMulMatrix b (b m) k l := fun m k l => by
    rw [hb m, (hm (ω m)).2, Matrix.map_apply]
  have hX : ∀ p q, MvPolynomial.aeval
      (fun ij : ((Fin n × β) ⊕ Unit) × ((Fin n × β) ⊕ Unit) => y ij.1 ij.2) (X p q) = y p q := fun p q => by
    simp [X, gen]
  have hinv : ∀ g : GL (Fin n) A, (res b (g : Matrix (Fin n) (Fin n) A)).det *
      (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det = 1 := fun g => by
    rw [← Matrix.det_mul, ← hmul, Units.mul_inv, h1, Matrix.det_one]
  have key : (∀ f ∈ {f | (∃ p u, f = X (Sum.inl p) (Sum.inr u)) ∨ (∃ p u, f = X (Sum.inr u) (Sum.inl p)) ∨
    (∃ i j k l, f = X (Sum.inl (i, k)) (Sum.inl (j, l)) -
      ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) ∨
    f = X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1 ∨
    ∃ P ∈ S, ∃ k, f = MvPolynomial.aeval
      (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)}, ev f y = 0) ↔
      ((∀ p u, y (Sum.inl p) (Sum.inr u) = 0) ∧ (∀ p u, y (Sum.inr u) (Sum.inl p) = 0) ∧
       (∀ i j k l, y (Sum.inl (i, k)) (Sum.inl (j, l)) =
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l) ∧
       y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) = 1 ∧
       ∀ P ∈ S, ∀ k, MvPolynomial.aeval
          (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) = 0) := by
    have e3 : ∀ i j k l, ev (X (Sum.inl (i, k)) (Sum.inl (j, l)) -
        ∑ m, coordOf c X i j m * algebraMap ℚ _ (Algebra.leftMulMatrix ω (ω m) k l)) y =
        y (Sum.inl (i, k)) (Sum.inl (j, l)) -
          ∑ m, coordOf c y i j m * Algebra.leftMulMatrix b (b m) k l := fun i j k l => by
      simp only [ev, map_sub, map_sum, map_mul, hX, AlgHom.commutes, hL]
      simp only [X, aeval_coordOf]
    have e4 : ev (X.toBlocks₁₁.det * X (Sum.inr ()) (Sum.inr ()) - 1) y =
        y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ()) - 1 := by
      simp only [ev, map_sub, map_mul, hX, map_one]
      simp only [X, aeval_det]
    have e5 : ∀ P k, ev (MvPolynomial.aeval
        (fun p : (Fin n × Fin n) × β => coordOf c X p.1.1 p.1.2 p.2) (Q P k)) y =
        MvPolynomial.aeval (fun p : (Fin n × Fin n) × β => coordOf c y p.1.1 p.1.2 p.2) (Q P k) :=
      fun P k => aeval_comp_coord c y (Q P k)
    have e1 : ∀ p q, ev (X p q) y = y p q := hX
    constructor
    · intro h
      refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
      · rw [← e1]; exact h _ (Or.inl ⟨p, u, rfl⟩)
      · rw [← e1]; exact h _ (Or.inr (Or.inl ⟨p, u, rfl⟩))
      · rw [← sub_eq_zero, ← e3]; exact h _ (Or.inr (Or.inr (Or.inl ⟨i, j, k, l, rfl⟩)))
      · rw [← sub_eq_zero, ← e4]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · rw [← e5]; exact h _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨P, hP, k, rfl⟩))))
    · rintro ⟨a1, a2, a3, a4, a5⟩ f (⟨p, u, rfl⟩ | ⟨p, u, rfl⟩ | ⟨i, j, k, l, rfl⟩ | rfl | ⟨P, hP, k, rfl⟩)
      · rw [e1, a1]
      · rw [e1, a2]
      · rw [e3, ← a3, sub_self]
      · rw [e4, a4, sub_self]
      · rw [e5, a5 P hP]
  rw [key]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5⟩
    let G : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => b.equivFun.symm (coordOf c y i j)
    have hG : ∀ i j k, b.repr (G i j) k = coordOf c y i j k := fun i j k => by
      have := congrFun (b.equivFun.apply_symm_apply (coordOf c y i j)) k
      rw [Module.Basis.equivFun_apply] at this
      exact this
    have hres : res b G = y.toBlocks₁₁ := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [res, Matrix.of_apply, Matrix.toBlocks₁₁]
      rw [a3, leftMul_expand]
      simp only [hG]
    have hu : IsUnit G := hunit G (by rw [hres]; exact IsUnit.of_mul_eq_one _ a4)
    obtain ⟨g, hg⟩ := hu
    refine ⟨g, fun P hP => ?_, ?_⟩
    · apply b.repr.injective
      ext k
      rw [hQ P R A b hb, hg]
      simp only [hG]
      simpa using a5 P hP k
    · have hi := hinv g
      rw [hg, hres] at hi
      have hcorner : y (Sum.inr ()) (Sum.inr ()) =
          (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by
        calc y (Sum.inr ()) (Sum.inr ()) = (y.toBlocks₁₁.det *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det) * y (Sum.inr ()) (Sum.inr ()) := by
              rw [hi, one_mul]
          _ = (y.toBlocks₁₁.det * y (Sum.inr ()) (Sum.inr ())) *
              (res b ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)).det := by ring
          _ = _ := by rw [a4, one_mul]
      ext (p | u) (q | v)
      · simp only [emb, Matrix.fromBlocks_apply₁₁, hg, hres, Matrix.toBlocks₁₁, Matrix.of_apply]
      · simp only [emb, Matrix.fromBlocks_apply₁₂, a1, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₁, a2, Matrix.zero_apply]
      · simp only [emb, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
        exact hcorner
  · rintro ⟨g, hg, rfl⟩
    have hco : ∀ i j k, coordOf c (emb b g) i j k = b.repr ((g : Matrix (Fin n) (Fin n) A) i j) k :=
      fun i j k => by
        simp only [coordOf, emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply, hc]
        exact sum_leftMul_one b _ k
    refine ⟨fun p u => ?_, fun p u => ?_, fun i j k l => ?_, ?_, fun P hP k => ?_⟩
    · simp [emb]
    · simp [emb]
    · simp only [hco]
      rw [← leftMul_expand]
      simp only [emb, Matrix.fromBlocks_apply₁₁, res, Matrix.of_apply]
    · simp only [emb, Matrix.toBlocks_fromBlocks₁₁, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      exact hinv g
    · simp only [hco]
      rw [← hQ P R A b hb (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) A) ij.1 ij.2) k, hg P hP]
      simp

end GlobalTheory.ClassFin.WeilEqs
