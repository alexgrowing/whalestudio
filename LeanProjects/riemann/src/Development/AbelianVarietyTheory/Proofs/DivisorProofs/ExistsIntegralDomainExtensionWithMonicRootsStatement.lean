import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralDomainExtensionWithMonicRoots
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_domain_extension_with_monic_roots : ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C), IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧ (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h → ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  first | exact @GlobalTheory.exists_integral_domain_extension_monic_roots | exact GlobalTheory.exists_integral_domain_extension_monic_roots | (intros; apply GlobalTheory.exists_integral_domain_extension_monic_roots <;> assumption)
