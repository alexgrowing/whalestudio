import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Equiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ ((G.map τ) *ᵥ star w) := by
  simp [hermC, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem star_mulVec' (A : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    star (A *ᵥ w) = (A.map (starRingEnd ℂ)) *ᵥ star w := by
  funext a
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

end Equiv

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def GamExt {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (M : ModelsOf F r) : Prop :=
  ModelBase M → ∀ k (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La),
    (∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) →
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b, gam a = a + l.M • b) →
    (∀ a, ∃ b, gam a = a + l.A • b) →
    ∃ g0 ∈ (M.X k).Γ, ∀ a, (g0 : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) = (M.φ k (gam a) : Fin r → E)

def FrDet {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (M : ModelsOf F r) : Prop :=
  ModelBase M → IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) →
    ∀ k (x' x'' : Frame (M.X k).Ψ r), (∀ τ, (mat x' τ).det ≠ 0) → (∀ τ, (mat x'' τ).det ≠ 0) →
      ∀ C : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ,
        (∀ τ (i j : Fin (Dw.mult τ)), j < i → C τ i j = 0) → (∀ τ i, C τ i i ≠ 0) →
        (∀ a, pmOf e M k x'' a = blkL e C (pmOf e M k x' a)) → ∃ b ∈ Bor (M.X k).Ψ r, x' = rmul x'' b

end Fam

end Formalism.L2.Pj
