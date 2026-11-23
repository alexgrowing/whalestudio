import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriMemParab

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
open GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim

noncomputable section

namespace GlobalTheory.ParahoricPerm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ₁ : Representation ℂ (GL (Fin r) k) V} {σ₂ : Representation ℂ (GL (Fin t) k) W}

theorem act_incl {χ : kˣ →* ℂˣ} {f : IndSp (part r t) ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)}
    (hf : IsParahoricVec χ (prod₂ σ₁ σ₂) f) {h : GL (Fin (r + t)) 𝒪[k]} {a : GL (Fin r) 𝒪[k]}
    {d : GL (Fin t) 𝒪[k]} (hb : HasBlocks h a d) :
    prod₂ σ₁ σ₂ (incl k (r + t) h) f = (χ (Matrix.GeneralLinearGroup.det (incl k t d)) : ℂ) • f := by
  refine hf (incl k (r + t) h) ⟨h, rfl⟩ (fun i j => ?_) _ ?_
  · rw [incl_val]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp (hb.2.2 i j)
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    exact Matrix.ext fun i j => by rw [Matrix.submatrix_apply, incl_val, incl_val, hb.2.1]

theorem val_mul_of_smul {f : IndSp (part r t) ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)}
    (x y : GL (Fin (r + t)) k) (c : ℂ) (hy : prod₂ σ₁ σ₂ y f = c • f) : f.1.1 (x * y) = c • f.1.1 x := by
  have : f.1.1 (x * y) = (prod₂ σ₁ σ₂ y f).1.1 x := rfl
  rw [this, hy]
  rfl

theorem exists_perm_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), f ≠ 0 → IsParahoricVec χ (prod₂ σ₁ σ₂) f → ∃ w : Equiv.Perm (Fin (r + t)), f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 := by
  intro k _ _ _ _ r t χ V _ _ W _ _ σ₁ σ₂ f hf0 hf
  by_contra hall
  push_neg at hall
  apply hf0
  have hg : ∀ g, f.1.1 g = 0 := by
    intro g
    obtain ⟨p, w, S, a, a₁, h, d, -, -, hb, rfl⟩ := GlobalTheory.TypeDim.Coset.coset k r t g
    have h1 : f.1.1 (GlobalTheory.Parabolic.permGL k w * diagOne k r t a) = 0 := by
      rw [← incl_diagO_one, val_mul_of_smul _ _ _ (act_incl hf (hasBlocks_diagO a 1)), hall w, smul_zero]
    have h2 : f.1.1 (GlobalTheory.Parabolic.permGL k w * diagOne k r t a * incl k (r + t) h) = 0 := by
      rw [val_mul_of_smul _ _ _ (act_incl hf hb), h1, smul_zero]
    rw [f.1.2 p _, h2]
    simp
  exact Subtype.ext (Subtype.ext (funext hg))

end GlobalTheory.ParahoricPerm
