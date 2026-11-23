import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellFrameChangeTriangular

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}

theorem uvec_cv (b : A.B) (w : Pm Dw.mult) (z : Let Dw.mult) (r : Fin (A.N + 1)) :
    uvec (A.cv b) w z r = ((A.A b).map (cC A b) * uC A b w z.1) r z.2 := by
  obtain ⟨τ, j⟩ := z
  simp only [uvec, cellVec, Atlas.cv, uC, cellMat, cC, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul, id,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
  ring

variable {Z : Scheme.{0}} {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]
  {S : Type} [CommRing S]

theorem eq_spMap_ev (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    spMap ((ev z _ hz).comp (cellθ κ k).toRingHom) ≫ κ k.1 k.2 = z := by
  rw [← spMap_comp', Category.assoc, spMap_cellθ, spMap_ev]

end GlobalTheory.FlagMod.FieldFlag
