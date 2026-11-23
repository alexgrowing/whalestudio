import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MBLow

theorem lbIso_sec_onto : ∀ (X : Scheme.{0}) (A B : LB X) (w : LB.Iso A B), A.IsLB → B.IsLB → w.IsGen →
    ∀ b : B.Sec, ∃ a : A.Sec, SecMaps w a b := by
  intro X A B w hA hB hw b
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso b hw hA hB, fun p => ?_⟩
  obtain ⟨p, q⟩ := p
  have hV : B.U p ⊓ A.U q ≤ A.U q ⊓ B.U p := fun _ h => ⟨h.2, h.1⟩
  have e := congrArg (ReciprocityTheory.ChartRestriction.G.DVR.rs hV) (ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec b hw hA hB q p)
  rw [ReciprocityTheory.ChartRestriction.G.DVR.isoCand_rs] at e
  have hs : res (hV.trans (ReciprocityTheory.ChartRestriction.G.DVR.divLe (A := A) (B := B) q p)) (w.s (p, q)) = w.s (p, q) :=
    Units.ext (GlobalTheory.Cartier.resG_self _ _)
  rw [hs] at e
  have e2 : resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso b hw hA hB).f q) =
      (((w.s (p, q))⁻¹ : Γ(X, B.U p ⊓ A.U q)ˣ) : Γ(X, B.U p ⊓ A.U q)) * resG X inf_le_left (b.f p) := by
    refine Eq.trans ?_ e
    exact (GlobalTheory.Cartier.resG_resG _ _ _).symm
  change resG X inf_le_left (b.f p) = ((@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)ˣ) : Γ(X, B.U p ⊓ A.U q)) * _
  simp only [id]
  rw [e2]
  exact (Units.mul_inv_cancel_left _ _).symm

end GlobalTheory.MBLow
