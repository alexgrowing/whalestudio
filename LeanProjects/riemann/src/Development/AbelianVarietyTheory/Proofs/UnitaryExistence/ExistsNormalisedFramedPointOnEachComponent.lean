import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsThetaPtStatement
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem normConst_pos_of_ne_zero {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) {ξ₀ : E} (h : ξ₀ ≠ 0) :
    0 < normConst ty ξ₀ := by
  unfold normConst
  refine Real.sqrt_pos.mpr (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))
  have := norm_pos_iff.mpr ((map_ne_zero (ty j)).mpr h)
  positivity

theorem exists_isNormUn : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∃ un, IsNormUn T un := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T
  have key : ∀ x : (M.X k).dom, ∃ y : FrPt Xo c (CAt σ), ∃ κ : ℂ,
      κ ^ 2 = (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det ∧
        IsThetaPt T (T.co.symm x.1) κ y := by
    intro x
    have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
      simpa using x.2
    have hne : (normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (normConst_pos_of_ne_zero _ (M.X k).ξ0_ne).ne')
        (T.norm _ hb).1.ne_zero
    obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq
      ((normConst (fun j => relab c σ (e j).1) (M.X k).ξ0 : ℂ) * (T.h (T.co.symm x.1)).det) (n := 2) two_pos
    have hκ0 : κ ≠ 0 := by
      rintro rfl
      exact hne (by rw [← hκ]; simp)
    obtain ⟨y, hy⟩ := GlobalTheory.T.exists_isThetaPt' hS E H Dw l Xo c σ g e F r M k T _ hb κ hκ0
    exact ⟨y, κ, hκ, hy⟩
  choose un hun using key
  exact ⟨un, hun⟩

end GlobalTheory.FrameUnif
