import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintInv

theorem rStab_comp_equiv {H : Type} [Group H] (φ : H ≃* H) (u : H → ℂ) :
    rStab (u ∘ φ) = (rStab u).comap (φ : H →* H) := by
  ext k
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  show (∀ x, u (φ (x * k)) = u (φ x)) ↔ ∀ x, u (x * φ k) = u x
  constructor
  · intro h x
    have := h (φ.symm x)
    simpa using this
  · intro h x
    rw [map_mul]; exact h _

theorem hint_comp_equiv {H : Type} [Group H] (K : Subgroup H) (φ : H ≃* H) (hK : K.map (φ : H →* H) = K)
    (u : H → ℂ) : hint K (u ∘ φ) = hint K u := by
  set S := rStab u ⊓ K with hS
  have hS' : rStab (u ∘ φ) ⊓ K = S.comap (φ : H →* H) := by
    rw [rStab_comp_equiv, hS, Subgroup.comap_inf]
    congr 1
    have h1 : (K.map (φ : H →* H)).comap (φ : H →* H) = K :=
      Subgroup.comap_map_eq_self_of_injective φ.injective K
    rw [hK] at h1
    exact h1.symm
  unfold hint
  rw [hS', Subgroup.relIndex_comap, hK]
  congr 1
  let e : H ⧸ S.comap (φ : H →* H) ≃ H ⧸ S :=
    Quotient.congr φ.toEquiv (fun a b => by
      simp only [QuotientGroup.leftRel_apply, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rfl)
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (φ q.out)
  have he : e q = ((φ q.out : H) : H ⧸ S) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [he, hs]
  exact ((Subgroup.mem_inf.1 s.2).1 _).symm

section Integral

variable {L : Type} [Field L] {a b : ℕ}

theorem entries_of_mem_GLint {O : Subring L} {A : GL (Fin a) L} (hA : A ∈ GLint (Fin a) O) (i j : Fin a) :
    A.val i j ∈ O ∧ (A⁻¹).val i j ∈ O := by
  obtain ⟨y, rfl⟩ := hA
  rw [← map_inv]
  exact ⟨(y.val i j).2, ((y⁻¹).val i j).2⟩

theorem mul_mul_mem {O : Subring L} {P : Matrix (Fin a) (Fin a) L} {X : Matrix (Fin a) (Fin b) L}
    {Q : Matrix (Fin b) (Fin b) L} (hP : ∀ i j, P i j ∈ O) (hX : ∀ i j, X i j ∈ O) (hQ : ∀ i j, Q i j ∈ O)
    (i : Fin a) (j : Fin b) : (P * X * Q) i j ∈ O := by
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ (hQ l j)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hP i k) (hX k l)

def lrEquiv (A : GL (Fin a) L) (B : GL (Fin b) L) : Matrix (Fin a) (Fin b) L ≃+ Matrix (Fin a) (Fin b) L where
  toFun X := A.val * X * B.val
  invFun X := (A⁻¹).val * X * (B⁻¹).val
  left_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A.val X, ← Matrix.mul_assoc (A⁻¹).val, ← Matrix.mul_assoc (A⁻¹).val]
    rw [Units.inv_mul, Matrix.one_mul, Units.mul_inv, Matrix.mul_one]
  right_inv X := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (A⁻¹).val X, ← Matrix.mul_assoc A.val, ← Matrix.mul_assoc A.val]
    rw [Units.mul_inv, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]

end Integral

theorem map_intMat {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (A : GLw a w) (B : GLw b w)
    (hA : A ∈ GlobalTheory.LFun.KGL w a) (hB : B ∈ GlobalTheory.LFun.KGL w b) :
    (intMat a b w).map ((lrEquiv A B).toMultiplicative : _ →* _) = intMat a b w := by
  have hint' : ∀ X : Matrix (Fin a) (Fin b) (w.adicCompletion E),
      (∀ i j, Valued.v (X i j) ≤ 1) ↔ ∀ i j, X i j ∈ Ov E w := fun X =>
    forall_congr' fun i => forall_congr' fun j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hA1 := fun i j => (entries_of_mem_GLint hA i j).1
  have hA2 := fun i j => (entries_of_mem_GLint hA i j).2
  have hB1 := fun i j => (entries_of_mem_GLint hB i j).1
  have hB2 := fun i j => (entries_of_mem_GLint hB i j).2
  have key : ∀ (P : GLw a w) (Q : GLw b w), (∀ i j, P.val i j ∈ Ov E w) → (∀ i j, Q.val i j ∈ Ov E w) →
      (intMat a b w).map ((lrEquiv P Q).toMultiplicative : _ →* _) ≤ intMat a b w := by
    intro P Q hP hQ
    rw [intMat, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Subgroup.subset_closure ?_
    show ∀ i j, Valued.v ((P.val * Multiplicative.toAdd X * Q.val) i j) ≤ 1
    rw [hint']
    exact mul_mul_mem hP ((hint' _).1 hX) hQ
  refine le_antisymm (key A B hA1 hB1) ?_
  have h2 := key A⁻¹ B⁻¹ hA2 hB2
  intro X hX
  refine ⟨(lrEquiv A⁻¹ B⁻¹).toMultiplicative X, h2 ⟨X, hX, rfl⟩, ?_⟩
  show Multiplicative.ofAdd (A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val) = X
  rw [show A.val * ((A⁻¹).val * Multiplicative.toAdd X * (B⁻¹).val) * B.val = Multiplicative.toAdd X from
    (lrEquiv A B).right_inv _]
  rfl

theorem hint_intMat_mul_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) → ℂ) (A : GLw a w) (B : GLw b w),
    A ∈ GlobalTheory.LFun.KGL w a → B ∈ GlobalTheory.LFun.KGL w b →
    hint (intMat a b w) (fun X => u (Multiplicative.ofAdd (A.val * Multiplicative.toAdd X * B.val))) =
      hint (intMat a b w) u := by
  intro E _ _ _ a b w u A B hA hB
  exact hint_comp_equiv (intMat a b w) (lrEquiv A B).toMultiplicative (map_intMat a b w A B hA hB) u

end GlobalTheory.BCT.HintInv
