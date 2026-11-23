import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

namespace GlobalTheory.TangentVecUnique

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

theorem eq_of_isDiff_of_isTangent : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (n : ℕ) (u : HolUnif A L n)
    (v : epsR ℂ ⟶ A) (w w' : Fin n → ℂ), IsTangent v → u.IsDiff w v → u.IsDiff w' v → w = w' := by
  intro A _ L n u v w w' hv h h'
  have hd : u.IsDiff (w - w') (toUnit (epsR ℂ) ≫ η[A]) := by
    intro U h₁ f
    have hv₁ : ⊤ ≤ v.left ⁻¹ᵁ U := (GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) hv U).2
      ((GlobalTheory.TangentOrigin.tangent_mem_iff (u := u) (GlobalTheory.ArchMetricCompare.isTangent_zero A) U).1 h₁)
    rw [GlobalTheory.ArchMetricCompare.isDiff_zero u U h₁ f, map_zero, map_sub, ← h U hv₁ f, ← h' U hv₁ f, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.ArchMetricCompare.eq_zero_of_isDiff u hd)

end GlobalTheory.TangentVecUnique
