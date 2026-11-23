import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

open GlobalTheory.Twist (resM resM_resM resM_smul)

theorem trCo_res_mul {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U₁ U₂ U₃ : X.Opens} {f₁ : Fin r → Γ(M, U₁)}
    {f₂ : Fin r → Γ(M, U₂)} (h₁ : VB.IsFrame f₁) (h₂ : VB.IsFrame f₂) (f₃ : Fin r → Γ(M, U₃)) (c a : Fin r) :
    resG X (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₃ from le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (trCo h₁ f₃ c a) =
      ∑ b, resG X (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₂ from inf_le_left) (trCo h₁ f₂ c b) *
        resG X (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₂ ⊓ U₃ from le_inf (inf_le_left.trans inf_le_right) inf_le_right)
          (trCo h₂ f₃ b a) := by
  have hW1 : U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ := inf_le_left.trans inf_le_left
  have hW2 : U₁ ⊓ U₂ ⊓ U₃ ≤ U₂ := inf_le_left.trans inf_le_right
  have hW3 : U₁ ⊓ U₂ ⊓ U₃ ≤ U₃ := inf_le_right
  have e13 : resG X (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₃ from le_inf hW1 hW3) (trCo h₁ f₃ c a) =
      (h₁.basis hW1).repr (resM M hW3 (f₃ a)) c := by
    unfold trCo
    rw [← h₁.repr_resM inf_le_left (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₃ from le_inf hW1 hW3), resM_resM]
  have e12 (b : Fin r) : resG X (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₂ from inf_le_left) (trCo h₁ f₂ c b) =
      (h₁.basis hW1).repr (resM M hW2 (f₂ b)) c := by
    unfold trCo
    rw [← h₁.repr_resM inf_le_left (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₂ from inf_le_left), resM_resM]
  have e23 (b : Fin r) : resG X (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₂ ⊓ U₃ from le_inf hW2 hW3) (trCo h₂ f₃ b a) =
      (h₂.basis hW2).repr (resM M hW3 (f₃ a)) b := by
    unfold trCo
    rw [← h₂.repr_resM inf_le_left (show U₁ ⊓ U₂ ⊓ U₃ ≤ U₂ ⊓ U₃ from le_inf hW2 hW3), resM_resM]
  rw [e13]
  simp only [e12, e23]
  conv_lhs => rw [← (h₂.basis hW2).sum_repr (resM M hW3 (f₃ a))]
  simp only [VB.IsFrame.basis_apply, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem trCo_chain : ∀ {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U₁ U₂ U₃ : X.Opens} {f₁ : Fin r → Γ(M, U₁)} {f₂ : Fin r → Γ(M, U₂)} (h₁ : VB.IsFrame f₁) (h₂ : VB.IsFrame f₂) (f₃ : Fin r → Γ(M, U₃)) {K : Type} [CommRing K] (x : Sp K ⟶ X) (h₁₂ : ⊤ ≤ x ⁻¹ᵁ (U₁ ⊓ U₂)) (h₂₃ : ⊤ ≤ x ⁻¹ᵁ (U₂ ⊓ U₃)) (h₁₃ : ⊤ ≤ x ⁻¹ᵁ (U₁ ⊓ U₃)) (c a : Fin r), ∑ b, TangentOrigin.evalPt x _ h₁₂ (trCo h₁ f₂ c b) * TangentOrigin.evalPt x _ h₂₃ (trCo h₂ f₃ b a) = TangentOrigin.evalPt x _ h₁₃ (trCo h₁ f₃ c a) := by
  intro X M r U₁ U₂ U₃ f₁ f₂ h₁ h₂ f₃ K _ x h₁₂ h₂₃ h₁₃ c a
  have hW : ⊤ ≤ x ⁻¹ᵁ (U₁ ⊓ U₂ ⊓ U₃) := fun p hp => ⟨h₁₂ hp, (h₂₃ hp).2⟩
  rw [← TangentOrigin.evalPt_res x (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h₁₃ hW,
    trCo_res_mul h₁ h₂ f₃ c a, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, TangentOrigin.evalPt_res x _ h₁₂ hW, TangentOrigin.evalPt_res x _ h₂₃ hW]

end GlobalTheory.ArLieBase

end
