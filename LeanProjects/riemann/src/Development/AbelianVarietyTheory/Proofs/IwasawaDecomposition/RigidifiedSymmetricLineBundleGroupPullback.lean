import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigSymBaseChange

theorem rigidified_and_sym_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (β : B.left ⟶ G.left), IsGrpPullback B G f β → ∀ (L : RigLB G) (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1])), σ.IsGen → Rigidified B (L.L.pull β) ∧ Out.Sym B (L.L.pull β) := by
  intro S S' f G _ B _ β gp L σ hσ
  refine ⟨PolBaseChange.rigidified_pull gp ⟨L.rig, L.rigGen⟩, fun _ => ⟨⊤, trivial, ?_⟩⟩
  refine gen_chartPull (chartPullLinComb L.L β (K := Fin 2) _
    ![(GrpObj.inv : G ⟶ G).left, 𝟙 G.left] ![1, -1] ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) fun k => ?_) σ hσ
  fin_cases k
  · show ((B.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : B ⟶ B).left) ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ (GrpObj.inv : G ⟶ G).left
    rw [Category.assoc, PolBaseChange.inv_comm gp, Category.assoc]
  · show (B.hom ⁻¹ᵁ ⊤).ι ≫ β = ((B.hom ⁻¹ᵁ ⊤).ι ≫ β) ≫ 𝟙 G.left
    rw [Category.comp_id]

end GlobalTheory.RigSymBaseChange
