import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem hasSupport_of_isSubquotient_prinSeries :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i)) (π : IrrRep (GL (Fin n) k)), GlobalTheory.SmGL.IsSubquotient π.ρ (prinSeries χ) → HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  intro k _ _ _ _ _ n χ hχ π h

  have hd : ∑ a : Fin n, (IrrGL.ofChar (χ a) (hχ a)).1 = n := by
    simp [IrrGL.ofChar]
  refine hasSupport_of_isSubquotient π.irr (fun a => IrrGL.isCusp_ofChar (χ a) (hχ a)) (hd := hd) ?_
  refine h.trans ((GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ).trans ?_)

  have he : stdBlocks (fun a => (IrrGL.ofChar (χ a) (hχ a)).1) hd =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
    ext ⟨a, i⟩
    rw [stdBlocks_val]
    simp [IrrGL.ofChar, Fin.fin_one_eq_zero i]
    rfl
  unfold prodIrr
  rw [he]

  let φ := multiProdEquiv (Equiv.sigmaUnique (Fin n) (fun _ => Fin 1))
    (fun a => equivRep (IrrRep.det (Fin 1) (χ a) (hχ a)))
  exact IsSubquotient.of_injective φ.toIntertwiningMap (fun u v huv => φ.toLinearEquiv.injective huv)

end GlobalTheory.LocLanglands
