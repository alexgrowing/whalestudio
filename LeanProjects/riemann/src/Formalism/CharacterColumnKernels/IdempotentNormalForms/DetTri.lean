import Formalism.CharacterColumnKernels.Statement

open Finset

noncomputable section

namespace Formalism.NG

theorem detTri : StatDetTri := by
  unfold StatDetTri bigMat
  intro R O _ g d _ _ _ _ α _ ρ b hb Θ
  have hM : Matrix.BlockTriangular (fun p q : g × d => ρ (Θ p.1 q.1) p.2 q.2) (fun p => b p.2) := by
    intro i j hij
    exact hb (Θ i.1 j.1) hij
  rw [hM.det]
  rcases isEmpty_or_nonempty g with hg | ⟨⟨g0⟩⟩
  · haveI := hg
    rw [Finset.univ_eq_empty, Finset.image_empty, Finset.prod_empty]
    symm
    apply Finset.prod_eq_one
    intro k _
    exact Matrix.det_isEmpty
  · have himg : (univ : Finset (g × d)).image (fun p => b p.2) = (univ : Finset d).image b := by
      ext k
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
      constructor
      · rintro ⟨_, i, hi⟩
        exact ⟨i, hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨g0, i, hi⟩
    rw [himg]
    apply Finset.prod_congr rfl
    intro k _
    let e : g × {i : d // b i = k} ≃ {p : g × d // b p.2 = k} :=
      { toFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
        invFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc _ = Matrix.det ((Matrix.toSquareBlock _ (fun p : g × d => b p.2) k).submatrix e e) :=
          (Matrix.det_submatrix_equiv_self e _).symm
      _ = _ := congrArg Matrix.det (Matrix.ext fun x y => rfl)

end Formalism.NG
