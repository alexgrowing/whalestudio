import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleOfRestrictNormalFiniteIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRepStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

theorem UpperTheory.Gal.NearKilling.killTransfer : KillTransfer := by
  intro I V V' _ _ _ _ _ _ _ ρ ρ' hfin htr x hx
  have h1 : ∀ y : MonoidAlgebra ℂ I,
      LinearMap.trace ℂ V (ρ.asAlgebraHom y) = LinearMap.trace ℂ V' (ρ'.asAlgebraHom y) := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g => simpa [Representation.asAlgebraHom_of] using htr g
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  have h2 : ∀ g : I, LinearMap.trace ℂ V (ρ.asAlgebraHom x * ρ g) = 0 := by
    intro g
    have h3 : ρ.asAlgebraHom x * ρ g = ρ.asAlgebraHom (x * MonoidAlgebra.of ℂ I g) := by
      rw [map_mul, Representation.asAlgebraHom_of]
    rw [h3, h1, map_mul, hx, zero_mul, map_zero]
  let b := Module.finBasis ℂ V
  let φ := LinearMap.toMatrixAlgEquiv (R := ℂ) b
  let r : I →* GL (Fin (Module.finrank ℂ V)) ℂ := (φ.toAlgHom.toMonoidHom.comp ρ).toHomUnits
  have hr : ∀ g, ((r g : GL (Fin (Module.finrank ℂ V)) ℂ) : Matrix _ _ ℂ) = φ (ρ g) := by
    intro g
    simp [r, MonoidHom.coe_toHomUnits]
  have hrange : Finite r.range := by
    have hsub : (Set.range r).Finite := by
      refine Set.Finite.of_finite_image (f := fun u : GL (Fin (Module.finrank ℂ V)) ℂ => (u : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ)) ?_
        (fun _ _ _ _ h => Units.ext h)
      refine (hfin.image φ).subset ?_
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨ρ g, ⟨g, rfl⟩, (hr g).symm⟩
    exact hsub.to_subtype
  have hss : IsSSRep r := by
    refine GlobalTheory.ssRep_of_normal_finiteIndex _ _ _ r r.ker inferInstance inferInstance ?_
    intro W _
    obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
    refine ⟨W', ?_, hW'⟩
    intro g v hv
    have hg : r (g : I) = 1 := g.2
    simpa [hg] using hv
  have hspan : ∀ y : MonoidAlgebra ℂ I, φ (ρ.asAlgebraHom y) ∈
      Submodule.span ℂ (Set.range fun g => ((r g : GL (Fin (Module.finrank ℂ V)) ℂ) : Matrix _ _ ℂ)) := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      rw [Representation.asAlgebraHom_of, ← hr]
      exact Submodule.subset_span ⟨g, rfl⟩
    | add a c ha hc =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hc
    | smul c a ha =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c ha
  have h0 : φ (ρ.asAlgebraHom x) = 0 := by
    refine GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep ℂ I _ r hss _ (hspan x) ?_
    intro g
    rw [hr, ← map_mul, ← h2 g, LinearMap.trace_eq_matrix_trace ℂ b]
    rfl
  exact φ.injective (by rw [h0, map_zero])
