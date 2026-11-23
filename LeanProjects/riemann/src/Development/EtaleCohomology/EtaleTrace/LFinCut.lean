import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Development.EtaleCohomology.KummerTheory.AdicLimPfKer
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LFinCut

theorem normal_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) [Smooth p] : GlobalTheory.IsNormalScheme X := by
  rw [GlobalTheory.isNormalScheme_iff]
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p fun y => ?_
  have hf : IsField ((S k).presheaf.stalk y) := isField_stalk_of_closure_mem_irreducibleComponents (S k) y (by
    have : closure ({y} : Set (S k)) = Set.univ := Set.eq_univ_of_forall fun z => subset_closure (Subsingleton.elim z y)
    rw [this, irreducibleComponents_eq_singleton]; rfl)
  let := hf.toField
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.LFinCut

end
