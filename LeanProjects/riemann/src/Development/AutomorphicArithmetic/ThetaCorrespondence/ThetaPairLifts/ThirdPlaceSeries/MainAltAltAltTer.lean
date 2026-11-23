import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
noncomputable section
namespace GlobalTheory.GaloisFromAdm
theorem main_alt_alt_alt : ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → GlobalTheory.BlockComplement.GaloisRepsCusp D := by
  intro D h i a ha π hc hr
  obtain ⟨ρ, hcont, hss, haway, -⟩ := (_root_.UpperTheory.GalS.weak' h i).1 a ha π hc hr
  refine ⟨ρ, hcont, hss, ?_⟩
  have hfin := placesOver_finite D (D.nd.l i) (Fact.out : (D.nd.l i).Prime).ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.eventually_cofinite_notMem] with w hu hw B φ hB hφ
  rw [D.naut.wdOf_frob i ρ w hw hcont (by rw [(haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]; exact (D.naut.unr_tw _ _).2 hu) B φ hB hφ,
    (haway w hw).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
  rfl
end GlobalTheory.GaloisFromAdm
end
end
