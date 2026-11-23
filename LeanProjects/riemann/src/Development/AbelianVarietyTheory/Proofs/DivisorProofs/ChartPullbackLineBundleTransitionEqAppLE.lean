import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem chartPull_g_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  intro Y Y' A' A h cp i j
  have e : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (cp.idx i) ⊓ A.U (cp.idx j)) :=
    le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j))
  apply TopCat.Presheaf.section_ext Y'.sheaf (A'.U i ⊓ A'.U j)
  intro y hy
  have h1 := congrArg Units.val (cp.g y i j hy.1 hy.2)
  rw [gm_val _ y _ hy, gm_val h y _ (e hy)] at h1
  refine h1.trans ?_
  show _ = (Y'.presheaf.germ _ y hy).hom ((Y'.presheaf.map (homOfLE e).op).hom ((h.app _).hom _))
  exact (TopCat.Presheaf.germ_res_apply Y'.presheaf _ y hy _).symm

end GlobalTheory
