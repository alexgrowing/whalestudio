import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem actWCbHom_teichmuller_eq {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (g : GQ l) (c : Cb l) :
    AI.actWCbHom g (WittVector.teichmuller l c) =
      WittVector.teichmuller l (autCb l (AI.actT g) c) :=
  WittVector.map_teichmuller l (autCb l (AI.actT g)).toRingHom c

theorem exists_fix_lift_of_fix_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (H : Set (GQ l)) (x : RW LL)
    (h : ∀ g ∈ H, ∃ r, AI.gRW LL g x - x = (l : RW LL) * r) :
    ∃ y ∈ fixSub AI LL H, ∃ r, y - x = (l : RW LL) * r := by
  obtain ⟨y, hy⟩ : ∃ y : RW LL, ∀ i, crd (basisO LL) i y =
      WittVector.teichmuller l ((crd (basisO LL) i x).coeff 0) :=
    ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ((crd (basisO LL) j x).coeff 0),
      fun i => crd_sum (basisO LL) _ i⟩
  refine ⟨y, mem_fixSub.2 fun g hg => ext_crd (basisO LL) fun i => ?_,
    (dvd_iff_crd LL _).2 fun i => ?_⟩
  · have h1 := (dvd_iff_crd LL _).1 (h g hg) i
    rw [LinearMap.map_sub, sub_coeff_zero, crd_gRW, coeff_actWCbHom] at h1
    rw [crd_gRW, hy, actWCbHom_teichmuller_eq, sub_eq_zero.1 h1]
  · rw [LinearMap.map_sub, sub_coeff_zero, hy, WittVector.teichmuller_coeff_zero, sub_self]

end GlobalTheory.Decompl
