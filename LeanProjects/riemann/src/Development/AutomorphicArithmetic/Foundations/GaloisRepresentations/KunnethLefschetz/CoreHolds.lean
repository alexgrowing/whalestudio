import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGood

namespace UpperTheory.Gal.KunnethLefschetz

theorem core_holds : Core :=
  ⟨GlobalTheory.EtC.etC_c2, UpperTheory.Cb.etale_cohomology_ind_etale_base_change, GlobalTheory.EtC.HomotopyInv.homotopy_invariance_etale, GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing, GlobalTheory.EtC.projectiveBundleFormula_vectorBundle_any_space⟩

end UpperTheory.Gal.KunnethLefschetz
