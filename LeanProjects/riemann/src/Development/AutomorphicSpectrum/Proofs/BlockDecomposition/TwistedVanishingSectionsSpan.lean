import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE

theorem span_range_twist_eq_top : ∀ {X : Scheme.{0}} (L : ReciprocityTheory.ChartRestriction.G.Semi.LB X), L.IsLB →
    ∀ {k : ℕ} {P : Fin k → X.Modules} {Q K : X.Modules} (f : ∀ i, P i ⟶ Q) (ι : K ⟶ ⨁ P)
      (w : ι ≫ biproduct.desc f = 0), (ShortComplex.mk ι (biproduct.desc f) w).ShortExact →
      Subsingleton (GlobalTheory.coh (GlobalTheory.twist K L) 1) →
      Submodule.span Γ(X, ⊤) (⋃ i, Set.range ((GlobalTheory.Twist.map L (f i)).app ⊤)) = ⊤ := by
  intro X L hL k P Q K f ι w hS hK
  have hsurj := GlobalTheory.cohOn.app_surjective (GlobalTheory.Twist.shortExact_map hL hS) ⊤ hK
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  have hg : (ShortComplex.map (ShortComplex.mk ι (biproduct.desc f) w) (GlobalTheory.twistFunctor L)).g =
      ∑ i, GlobalTheory.Twist.map L (biproduct.π P i) ≫ GlobalTheory.Twist.map L (f i) := by
    show (GlobalTheory.twistFunctor L).map (biproduct.desc f) = _
    rw [biproduct.desc_eq, Functor.map_sum]
    rfl
  let e : (GlobalTheory.twist (⨁ P) L ⟶ GlobalTheory.twist Q L) →+ Γ(GlobalTheory.twist Q L, ⊤) :=
    { toFun := fun φ => (φ.app ⊤) x
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have key : ((ShortComplex.map (ShortComplex.mk ι (biproduct.desc f) w) (GlobalTheory.twistFunctor L)).g.app ⊤) x =
      ∑ i, ((GlobalTheory.Twist.map L (f i)).app ⊤) (((GlobalTheory.Twist.map L (biproduct.π P i)).app ⊤) x) := by
    rw [hg]
    exact map_sum e _ _
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨i, ?_⟩)
  exact ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.GE
