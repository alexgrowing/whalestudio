import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite

namespace GlobalTheory.CompanionTheory.GE.FormalShift

attribute [local instance] algebraOfOver

theorem restrict_idealPow_lift : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; (∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a)) → ∀ (G : Z.Modules) [G.IsQuasicoherent] (m : ℕ), ∃ g : (idealPow I G m).restrict (φ ⁻¹ᵁ V).ι ⟶ idealPow (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m, g ≫ idealPowι (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m = (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) := by
  intro A _ _ I X Z _ _ φ V hV _
  letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩
  intro hcomp G _ m
  haveI : (G.restrict (φ ⁻¹ᵁ V).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  have hf : (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) ≫
      cokernel.π (idealSumMap (G.restrict (φ ⁻¹ᵁ V).ι)
        (Ideal.map (toFunctions (A := A) V) I ^ m)) = 0 := by
    refine hom_eq_zero_of_affineOpens _ fun U s ↦ ?_
    have hU : IsAffineOpen (U : (φ ⁻¹ᵁ V).toScheme.Opens) := U.2
    have hU' : IsAffineOpen ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) :=
      hU.image_of_isOpenImmersion _
    have h1 : (idealPowι I G m).app ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) s ∈
        (Ideal.map (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m) • ⊤ :
          Submodule _ _) :=
      (Set.ext_iff.1 (range_idealPowι_app I G hU' m) _).1 ⟨s, rfl⟩
    have hJ : ∀ a ∈ Ideal.map
        (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m),
        ((φ ⁻¹ᵁ V).ι.appIso (U : (φ ⁻¹ᵁ V).toScheme.Opens)).hom a ∈
          Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) := by
      intro a ha
      have h := Ideal.mem_map_of_mem ((φ ⁻¹ᵁ V).ι.appIso (U : (φ ⁻¹ᵁ V).toScheme.Opens)).hom.hom ha
      rw [Ideal.map_map] at h
      rw [← Ideal.map_pow, Ideal.map_map]
      convert h using 2
      ext r
      exact (hcomp U r).symm
    have h2 : ∀ x ∈ (Ideal.map
        (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))) (I ^ m) • ⊤ :
          Submodule Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            Γ(G, (φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens))),
        (G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv x ∈
          (Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) • ⊤ :
              Submodule Γ((φ ⁻¹ᵁ V).toScheme, (U : (φ ⁻¹ᵁ V).toScheme.Opens))
                Γ(G.restrict (φ ⁻¹ᵁ V).ι, (U : (φ ⁻¹ᵁ V).toScheme.Opens))) := by
      intro x hx
      refine Submodule.smul_induction_on
        (p := fun x ↦ (G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv x ∈
          (Ideal.map (toFunctions (A := Γ(X, V)) (U : (φ ⁻¹ᵁ V).toScheme.Opens))
            (Ideal.map (toFunctions (A := A) V) I ^ m) • ⊤ :
              Submodule Γ((φ ⁻¹ᵁ V).toScheme, (U : (φ ⁻¹ᵁ V).toScheme.Opens))
                Γ(G.restrict (φ ⁻¹ᵁ V).ι, (U : (φ ⁻¹ᵁ V).toScheme.Opens)))) hx ?_ ?_
      · intro a ha y _
        show _ ∈ _
        rw [Scheme.Modules.smul_restrictAppIso_inv_apply]
        exact Submodule.smul_mem_smul (hJ a ha) Submodule.mem_top
      · intro y z hy hz
        show _ ∈ _
        rw [map_add]
        exact Submodule.add_mem _ hy hz
    obtain ⟨y, hy⟩ := (Set.ext_iff.1 (range_idealPowι_app
      (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) hU m) _).2 (h2 _ h1)
    change (cokernel.π (idealSumMap (G.restrict (φ ⁻¹ᵁ V).ι)
        (Ideal.map (toFunctions (A := A) V) I ^ m))).app (U : (φ ⁻¹ᵁ V).toScheme.Opens)
      ((G.restrictAppIso (φ ⁻¹ᵁ V).ι U).inv
        ((idealPowι I G m).app ((φ ⁻¹ᵁ V).ι ''ᵁ (U : (φ ⁻¹ᵁ V).toScheme.Opens)) s)) = 0
    rw [← hy, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, kernel.condition,
      Scheme.Modules.Hom.zero_app]
    rfl
  exact ⟨kernel.lift _ _ hf, kernel.lift_ι _ _ _⟩

end GlobalTheory.CompanionTheory.GE.FormalShift
