import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorsEqEigenFrameMulInvertible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameVectors_eq_eigenFrame_mul_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (b : A.B) (S₀ : Type) [CommRing S₀] [Algebra c.F S₀] (P₀ : FrPt Xo c S₀), ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V → ∀ σ : E →+* ℂ, ∃ T : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S₀, IsUnit T.det ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (ψ : S₀ →ₐ[c.F] S') (P' : FrPt Xo c S'), FrMap ψ P₀ P' → ∀ (h' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).V) (hM' : ⊤ ≤ (frX P' ≫ Y.j) ⁻¹ᵁ (A.k b).M.U) (j : Fin (Dw.mult σ)), frVec Y P' rfl σ j = vec (A.k b).M.toMChart _ hM' (fun r => ((((A.k b).u σ).map (ev _ _ h')) * T.map ψ) r j) := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.frVec_eq_eigFrame_mul | exact GlobalTheory.FlagMod.FieldFlag.frVec_eq_eigFrame_mul | (intros; apply GlobalTheory.FlagMod.FieldFlag.frVec_eq_eigFrame_mul <;> assumption)
