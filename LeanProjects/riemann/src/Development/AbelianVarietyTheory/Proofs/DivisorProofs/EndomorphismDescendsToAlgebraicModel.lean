import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodRatioAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem Obj.exists_end_descend_algebraic :
    ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X₀ : Obj F 𝔠 (Sp Qb)) (X : Obj F 𝔠 (Sp ℂ))
    (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
      ∀ (α : X.A ⟶ X.A) [IsMonHom α], ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left := by
  intro F _ _ 𝔠 X₀ X p hp α _
  haveI : Countable Qb :=
    (Algebraic.countable ℚ ℂ).mono (fun z hz => mem_algebraicClosure_iff.1 hz) |>.to_subtype
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨L, u, -⟩ := Obj.exists_holUnif_ringHom_lift F 𝔠 X
  exact GlobalTheory.CMLiePeriod.descend X₀.ab X₀.ab X.ab X.ab X.dim X.dim u u hp.grp hp.grp α

end GlobalTheory.RealMult
