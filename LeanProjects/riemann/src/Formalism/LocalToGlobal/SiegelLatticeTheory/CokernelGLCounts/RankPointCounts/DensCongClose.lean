import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensCongPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefDens

noncomputable section

namespace Formalism.L2.SG.Pf

theorem density_congruence_holds : Coef.DensCong := by
  intro F E _ _ _ _ _ _ _ M V _ _ H ϖ abelian₂ ι _ _ G A hA hdet
  obtain ⟨y, hy, hyd⟩ := hdet
  have hyd' : y * A.det = 1 := by rw [mul_comm]; exact hyd
  set B : Matrix ι ι E := y • A.adjugate with hBdef
  have hB : ∀ i j, B i j ∈ M.L.O := fun i j => by
    simp only [hBdef, Matrix.smul_apply, smul_eq_mul]
    exact M.L.O.mul_mem hy (DensCongPf.adj_mem A hA i j)
  have hAB : A * B = 1 := by
    rw [hBdef, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hyd', one_smul]
  have hBA : B * A = 1 := by
    rw [hBdef, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hyd', one_smul]
  have hm : ∀ X Y : Matrix ι ι E, (X * Y).map M.L.cj = X.map M.L.cj * Y.map M.L.cj := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply, map_sum, map_mul]
  have hone : (1 : Matrix ι ι E).map M.L.cj = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hG : (B.map M.L.cj).transpose * ((A.map M.L.cj).transpose * G * A) * B = G := by
    calc _ = ((A * B).map M.L.cj).transpose * G * (A * B) := by
          rw [hm, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hAB, hone, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  unfold MainNotions.S.Loc.HermSp.dens
  congr 2
  have fwd : ∀ (K P Q : Matrix ι ι E) (hP : ∀ i j, P i j ∈ M.L.O), (∀ i j, Q i j ∈ M.L.O) →
      P * Q = 1 → Q * P = 1 → ∀ x, x ∈ Set.range (fun (v : {v : ι → V // H.Prim abelian₂ v ∧
        ∀ a b, H.h (v b) (v a) - K a b ∈ (M.L.O ∙ (algebraMap F E) ↑ϖ)}) (a : ι) =>
          (Submodule.Quotient.mk (p := H.smulLat ((algebraMap F E) ↑ϖ) abelian₂) (v.1 a))) →
      DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) P hP x ∈ Set.range (fun (v : {v : ι → V //
        H.Prim abelian₂ v ∧ ∀ a b, H.h (v b) (v a) - ((P.map M.L.cj).transpose * K * P) a b ∈
          (M.L.O ∙ (algebraMap F E) ↑ϖ)}) (a : ι) =>
          (Submodule.Quotient.mk (p := H.smulLat ((algebraMap F E) ↑ϖ) abelian₂) (v.1 a))) := by
    rintro K P Q hP hQ hPQ hQP x ⟨⟨v, hv1, hv2⟩, rfl⟩
    exact ⟨⟨DensCongPf.act P v, DensCongPf.prim_act H abelian₂ P Q hP hQ hPQ hQP v hv1,
      DensCongPf.cong_act H _ P K hP v hv2⟩, (DensCongPf.psi_mk H abelian₂ _ P hP v).symm⟩
  refine Nat.card_congr
    { toFun := fun x => ⟨DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) B hB x.1, by
        have h := fwd _ B A hB hA hBA hAB x.1 x.2
        rw [hG] at h
        exact h⟩
      invFun := fun x => ⟨DensCongPf.psi H abelian₂ ((algebraMap F E) ↑ϖ) A hA x.1,
        fwd G A B hA hB hAB hBA x.1 x.2⟩
      left_inv := fun x => Subtype.ext (DensCongPf.psi_psi H abelian₂ _ B A hB hA hBA x.1)
      right_inv := fun x => Subtype.ext (DensCongPf.psi_psi H abelian₂ _ A B hA hB hAB x.1) }

end Formalism.L2.SG.Pf
