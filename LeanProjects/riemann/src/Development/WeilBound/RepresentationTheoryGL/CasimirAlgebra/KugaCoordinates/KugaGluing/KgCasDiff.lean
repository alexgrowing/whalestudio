import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgLieOpComm
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgFormRTensor

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a) (Ξ : AlgRep E a) (σ : ℝ)

theorem kg_casR (τ : E →+* ℂ) (t : ℝ) (htrX : ∑ i, cx τ Ξ.dmat i i = algebraMap ℂ _ (-(t : ℂ))) :
    ∑ i, ∑ j, cx τ (kgR π Ξ σ) i j * cx τ (kgR π Ξ σ) j i =
      (Matrix.toLin' (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)).lTensor π.V +
        ((2 * (σ / 2 : ℂ)) * (-(t : ℂ)) + (a : ℂ) * (σ / 2 : ℂ) ^ 2) • 1 := by
  let ΦR := (Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) π.V).comp (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin Ξ.d)).toAlgHom
  have hΦR : ∀ A : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ, (Matrix.toLin' A).lTensor π.V = ΦR A := fun A => rfl
  simp only [cx_kgR, hΦR]
  refine (kg_cas_shift (fun i j => ΦR (cx τ Ξ.dmat i j)) (σ / 2 : ℂ)).trans ?_
  simp only [← map_mul, ← map_sum, htrX, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
  module

theorem kg_casA (τ : E →+* ℂ) (c t : ℝ)
    (hcas : ∑ i, ∑ j, cx τ (lieOp π) i j * cx τ (lieOp π) j i = algebraMap ℂ _ (c : ℂ))
    (htr : ∑ i, cx τ (lieOp π) i i = algebraMap ℂ _ (t : ℂ)) :
    ∑ i, ∑ j, cx τ (kgA π Ξ σ) i j * cx τ (kgA π Ξ σ) j i =
      ((c : ℂ) + (2 * (-(σ / 2 : ℂ))) * (t : ℂ) + (a : ℂ) * (-(σ / 2 : ℂ)) ^ 2) • 1 := by
  let ΦA := Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)
  have hΦA : ∀ f : Module.End ℂ π.V, f.rTensor (Fin Ξ.d → ℂ) = ΦA f := fun f => rfl
  simp only [cx_kgA, hΦA]
  refine (kg_cas_shift (fun i j => ΦA (cx τ (lieOp π) i j)) (-(σ / 2) : ℂ)).trans ?_
  simp only [← map_mul, ← map_sum, hcas, htr, Algebra.algebraMap_eq_smul_one, map_smul, map_one]
  module

theorem kg_casDiff (hC : FrameCas) (cc tt : (E →+* ℂ) → ℝ)
    (hcas : ∀ τ, ∑ i, ∑ j, cx τ (lieOp π) i j * cx τ (lieOp π) j i = algebraMap ℂ _ (cc τ : ℂ))
    (htr : ∀ τ, ∑ i, cx τ (lieOp π) i i = algebraMap ℂ _ (tt τ : ℂ))
    (htrX : ∀ τ, ∑ i, cx τ Ξ.dmat i i = algebraMap ℂ _ (-(tt τ : ℂ))) :
    ((∑ k, kgR π Ξ σ (toL (fr k).1) * kgR π Ξ σ (toL (fr k).1) -
        ∑ k, kgR π Ξ σ (toL (iM (fr k).1)) * kgR π Ξ σ (toL (iM (fr k).1))) -
      (∑ k, kgA π Ξ σ (toL (fr k).1) * kgA π Ξ σ (toL (fr k).1) -
        ∑ k, kgA π Ξ σ (toL (iM (fr k).1)) * kgA π Ξ σ (toL (iM (fr k).1))) :
        Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) =
      (2 : ℂ) • ∑ τ, ((Matrix.toLin' (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)).lTensor π.V - (cc τ : ℂ) • 1) := by
  rw [hC E a _ (kgR π Ξ σ), hC E a _ (kgA π Ξ σ)]
  refine (smul_sub (2 : ℂ) (_ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) _).symm.trans (congrArg _ ?_)
  refine (Finset.sum_sub_distrib (G := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) _ _).symm.trans
    (Finset.sum_congr rfl fun τ _ => ?_)
  rw [kg_casR π Ξ σ τ (tt τ) (htrX τ), kg_casA π Ξ σ τ (cc τ) (tt τ) (hcas τ) (htr τ)]
  module

end
end PositivityTheory.Rg.Cz
