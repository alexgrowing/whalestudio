import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.UnitaryBC

namespace GlobalTheory.PolChar

theorem exists_compNorm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {χ : Formalism.L2.Host.HChar E} {u : ℝ},
    χ.IsAbsPow u → ∃ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E),
      GlobalTheory.GalOfCusp.compNorm E ψ = χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹ ∧
        ∀ v : InfinitePlace (maximalRealSubfield E), ψ.locInf v (-1) = 1 := by
  intro E _ _ _ χ u h
  refine ⟨resReal χ, Subtype.ext (MonoidHom.ext fun x => ?_), resReal_locInf_neg_one h⟩
  change χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
    χ.1 x * ((χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹)⁻¹
  rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, ideleConj_eq, inv_inv]

end GlobalTheory.PolChar
