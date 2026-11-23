import Mathlib

theorem UpperTheory.Reformulated.B.Qh12.ell :
    ∀ (O Λ Γ X : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : Algebra O Λ]
    [inst_3 : CommGroup Γ] [inst_4 : AddCommGroup X] [inst_5 : _root_.Module O X] (th₀ : Λ →ₐ[O] O) (d : Λ →ₗ[O] X)
    (χ : Γ →* Multiplicative X),
    (∀ (a b : Λ), (d : Λ → X) (a * b) = (th₀ : Λ → O) a • (d : Λ → X) b + (th₀ : Λ → O) b • (d : Λ → X) a) →
      ∃ (th : MonoidAlgebra Λ Γ →ₐ[O] O) (ell : MonoidAlgebra Λ Γ →ₗ[O] X),
        (∀ (g : Γ) (a : Λ), (th : MonoidAlgebra Λ Γ → O) (MonoidAlgebra.single g a) = (th₀ : Λ → O) a) ∧
          (∀ (a b : MonoidAlgebra Λ Γ),
              (ell : MonoidAlgebra Λ Γ → X) (a * b) =
                (th : MonoidAlgebra Λ Γ → O) a • (ell : MonoidAlgebra Λ Γ → X) b +
                  (th : MonoidAlgebra Λ Γ → O) b • (ell : MonoidAlgebra Λ Γ → X) a) ∧
            ∀ (g : Γ) (a : Λ),
              (ell : MonoidAlgebra Λ Γ → X) (MonoidAlgebra.single g a) =
                (d : Λ → X) a +
                  (th₀ : Λ → O) a • (Multiplicative.toAdd : Multiplicative X → X) ((χ : Γ → Multiplicative X) g) := by
  intro O Λ Γ X _ _ _ _ _ _ th₀ d χ hd
  classical
  let th : MonoidAlgebra Λ Γ →ₐ[O] O :=
    MonoidAlgebra.liftNCAlgHom th₀ (1 : Γ →* O) (fun _ _ => Commute.all _ _)
  have hth : ∀ (g : Γ) (a : Λ), th (MonoidAlgebra.single g a) = th₀ a := by
    intro g a
    simp [th]
  let ell : MonoidAlgebra Λ Γ →ₗ[O] X :=
    (Finsupp.lsum O (fun g : Γ => d + th₀.toLinearMap.smulRight (Multiplicative.toAdd (χ g)))) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv O).toLinearMap
  have hell : ∀ (g : Γ) (a : Λ), ell (MonoidAlgebra.single g a)
      = d a + th₀ a • Multiplicative.toAdd (χ g) := by
    intro g a
    simp [ell]
  refine ⟨th, ell, hth, ?_, hell⟩
  intro a b
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    simp only [add_mul, map_add, ha, ha', add_smul, smul_add]
    abel
  | single g a =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      simp only [mul_add, map_add, hb, hb', add_smul, smul_add]
      abel
    | single h b =>
      rw [MonoidAlgebra.single_mul_single, hell, hell, hell, hth, hth, hd, map_mul, map_mul,
        toAdd_mul]
      module
