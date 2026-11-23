import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Step

theorem shortExact_lvl_zero {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) :
    (ShortComplex.mk (incl (anti hS) 0) (grπ (anti hS) 0) (incl_grπ (anti hS) 0)).ShortExact := by
  have : Mono (incl (anti hS) 0) := by
    unfold incl
    infer_instance
  have : Epi (grπ (anti hS) 0) := by
    exact coequalizer.π_epi
  exact { exact := ShortComplex.exact_cokernel (incl (anti hS) 0) }

theorem lifts_zero : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ),
    Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (S 0 : X.Modules) H n) 1) → Lifts I H hS n 0 := by
  intro A _ _ I X _ H hH P S hS n hv y
  have hsurj : Function.Surjective
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) 0)).app ⊤) :=
    GlobalTheory.cohOn.app_surjective
      (GlobalTheory.Twist.shortExact_map (GlobalTheory.Twist.isLB_lbZPow hH n) (shortExact_lvl_zero hS)) ⊤ hv
  obtain ⟨c, hc⟩ := hsurj y
  refine ⟨c, hc, ?_⟩
  have htop : Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ 0) = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
  simp only [twPow, htop, Submodule.top_smul]
  trivial

end GlobalTheory.CompanionTheory.GE.Step
