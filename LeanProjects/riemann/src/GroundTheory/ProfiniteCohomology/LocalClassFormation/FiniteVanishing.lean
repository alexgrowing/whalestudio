import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Trivial
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
import GroundTheory.ProfiniteCohomology.EulerCharDefs
import GroundTheory.ProfiniteCohomology.PoincareDuality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

variable (K Ksep : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ} (hn : (n : K) ≠ 0)

include hn in

theorem subsingleton_cohomology_galois (U : OpenSubgroup Gal(Ksep/K))
    (M : Rep (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] (hM : ∀ m : M, n • m = 0)
    (r : ℕ) (hr : 3 ≤ r) : Subsingleton (cohomology M r) :=
  subsingleton_cohomology_of_three_le K Ksep hn U M hM hr

include hn in

theorem finite_cohomology_galois (U : OpenSubgroup Gal(Ksep/K))
    (M : Rep (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) (r : ℕ) : Finite (cohomology M r) := by
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  have : NeZero n := ⟨hn0⟩
  rcases le_or_gt r 2 with hr | hr
  · exact finite_cohomology_of_forall_trivial n 2 (rootsOfUnityFixing K Ksep n)
      (fun V hV A _ _ htriv hA r hr => finite_cohomology_of_trivial K Ksep hn V
        (fun σ hσ ζ hζ => apply_eq_of_mem_rootsOfUnityFixing (hV hσ) hζ) A htriv hA r hr)
      U M hM r hr
  · have := subsingleton_cohomology_galois K Ksep hn U M hM r hr
    exact Finite.of_subsingleton

include hn in

theorem finite_cohomology_galois_le_two : ∀ (U : OpenSubgroup Gal(Ksep/K))
    (M : Rep (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ r ≤ 2, Finite (cohomology M r) :=
  fun U M _ _ hM r _ => finite_cohomology_galois K Ksep hn U M hM r

include hn in

theorem subsingleton_cohomology_three_galois : ∀ (U : OpenSubgroup Gal(Ksep/K))
    (M : Rep (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K))) [IsDiscreteRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (cohomology M 3) :=
  fun U M _ _ hM => subsingleton_cohomology_galois K Ksep hn U M hM 3 le_rfl

include hn in

theorem subsingleton_cohomology_galois_top (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) (r : ℕ) (hr : 3 ≤ r) : Subsingleton (cohomology M r) :=
  have := subsingleton_cohomology_galois K Ksep hn ⊤
    (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hM r hr
  (bijective_cohomologyRes_top M r).1.subsingleton

include hn in

theorem finite_cohomology_galois_top (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) (r : ℕ) : Finite (cohomology M r) :=
  have : Finite (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) :=
    inferInstanceAs (Finite M)
  have := finite_cohomology_galois K Ksep hn ⊤
    (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hM r
  Finite.of_injective _ (bijective_cohomologyRes_top M r).1

theorem hasFiniteCohomology_galois (U : OpenSubgroup Gal(Ksep/K)) :
    HasFiniteCohomology (ULift.{0} ℤ) (U : Subgroup Gal(Ksep/K)) (fun m => (m : K) ≠ 0) :=
  fun A _ _ hA => ⟨finite_cohomology_galois K Ksep hA U A (fun _ => card_nsmul_eq_zero'),
    fun q hq => subsingleton_cohomology_galois K Ksep hA U A (fun _ => card_nsmul_eq_zero') q hq⟩

theorem hasFiniteCohomology_galois_top :
    HasFiniteCohomology (ULift.{0} ℤ) Gal(Ksep/K) (fun m => (m : K) ≠ 0) :=
  fun A _ _ hA => ⟨finite_cohomology_galois_top K Ksep hA A (fun _ => card_nsmul_eq_zero'),
    fun q hq => subsingleton_cohomology_galois_top K Ksep hA A (fun _ => card_nsmul_eq_zero') q hq⟩

end GroundTheory.ProfCoh
