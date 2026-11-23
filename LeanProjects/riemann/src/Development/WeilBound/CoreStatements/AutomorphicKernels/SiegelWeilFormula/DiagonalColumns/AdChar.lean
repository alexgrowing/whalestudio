import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelD

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Ald.Ldx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem crdB_zero {m n : ℕ} (bs : Module.Basis (Fin 2) F E) : crdB bs (0 : Mx F E m n) = 0 := by
  funext k
  simp [crdB]

theorem diagCols_eq {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ tb : GL (Fin n) E, (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      incM F b.1.toCols₁ * incM F (tb⁻¹).1 := by
  obtain ⟨tb, htb⟩ := frame_fromRows hb
  refine ⟨tb, ?_⟩
  have e : (incM F b.1).toCols₁ = incM F b.1.toCols₁ := rfl
  rw [mul_fromRows_one_zero, e] at htb
  rw [htb, cancel_r']

theorem adaptedChar : AdaptedChar := by
  intro F E _ _ _ _ _ σ m n bs A Y b dd had hb
  obtain ⟨tb, htb⟩ := diagCols_eq (F := F) hb
  have key : ∀ z : Matrix (Fin m) (Fin n) (AE F E),
      z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ =
        (z * (incM F (tb⁻¹).1)ᵀ) * (incM F b.1.toCols₁)ᵀ + (0 : Mx F E m n) * (incM F b.1.toCols₂)ᵀ := by
    intro z
    rw [htb, Matrix.transpose_mul, Matrix.zero_mul, add_zero, Matrix.mul_assoc]
  refine ⟨fun z => ?_, fun y => ?_⟩
  · rw [key, had, crdB_zero]
  · set w := dd.e.symm (0, y) with hw
    have hd := frame_decomp (F := F) b w
    have hew : dd.e w = (0, y) := by rw [hw, LinearEquiv.apply_symm_apply]
    rw [hd, had] at hew
    have hy : (fun k => Bf σ A.J (frQ b w).toCols₁ (Ek bs k)) = y := (Prod.mk.inj hew).2
    refine ⟨(frQ b w).toCols₁ * (incM F tb.1)ᵀ, ?_⟩
    rw [key, had, crdB_zero, ← hy]
    congr 3
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, incM_inv_mul, Matrix.transpose_one, Matrix.mul_one]

end PositivityTheory.SiegelWeilFormula.Ald.Ldx

end
