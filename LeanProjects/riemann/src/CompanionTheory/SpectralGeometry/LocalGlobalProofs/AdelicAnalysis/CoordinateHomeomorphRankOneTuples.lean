import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section CoordMap

theorem map_curry_symm_pi {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam]
    (M d : ℕ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam).map
        (MeasurableEquiv.curry (Fin M) (Fin d) R).symm =
      Measure.pi fun _ : Fin M × Fin d => lam := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [(MeasurableEquiv.curry (Fin M) (Fin d) R).symm.map_apply]
  have hpre : (MeasurableEquiv.curry (Fin M) (Fin d) R).symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i : Fin M => Set.pi Set.univ fun k : Fin d => s (i, k) := by
    ext x
    simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall, Function.uncurry]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

theorem coordK_eq_map {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (e : R ⊗[F] E ≃ᵐ (Fin d → R))
    (he : ∀ y k, e y k = (Algebra.TensorProduct.basis R b).repr y k) :
    coordK R b lam = (Measure.pi fun _ => lam).map e.symm := by
  rw [MeasurableEquiv.map_symm]
  have : (e : R ⊗[F] E → Fin d → R) =
      fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k := by
    funext y k; exact he y k
  rw [coordK, this]

theorem coordMap_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ M : ℕ, IsHomeomorph (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ MeasurableEmbedding (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) ∧ (coordW R b lam 1 M).map (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) = Measure.pi fun _ : Fin M × Fin d => lam := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b lam hlam M
  obtain ⟨-, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hlam
  have hSF : SigmaFinite lam := inferInstance
  let e : R ⊗[F] E ≃ₜ (Fin d → R) := (hh d b).homeomorph _
  have he : ∀ y k, e y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  let em : R ⊗[F] E ≃ᵐ (Fin d → R) := e.toMeasurableEquiv
  have hem : ∀ y k, em y k = (Algebra.TensorProduct.basis R b).repr y k := fun _ _ => rfl
  have hK : coordK R b lam = (Measure.pi fun _ => lam).map em.symm := coordK_eq_map b lam em hem
  haveI : SigmaFinite (coordK R b lam) := by
    rw [hK]; exact em.symm.measurableEmbedding.sigmaFinite_map
  have hmp : MeasurePreserving em (coordK R b lam) (Measure.pi fun _ : Fin d => lam) :=
    ⟨em.measurable, by rw [hK]; exact MeasurableEquiv.map_map_symm em⟩
  let Φ : (Fin 1 → Fin M → R ⊗[F] E) ≃ᵐ (Fin M × Fin d → R) :=
    (MeasurableEquiv.funUnique (Fin 1) (Fin M → R ⊗[F] E)).trans
      ((MeasurableEquiv.piCongrRight fun _ : Fin M => em).trans
        (MeasurableEquiv.curry (Fin M) (Fin d) R).symm)
  have hΦ : (fun X : Fin 1 → Fin M → R ⊗[F] E => cv R b (X 0)) = Φ := rfl
  have hsymm : (Φ.symm : (Fin M × Fin d → R) → Fin 1 → Fin M → R ⊗[F] E) =
      fun x _ i => e.symm fun k => x (i, k) := rfl
  have hc1 : Continuous (Φ : (Fin 1 → Fin M → R ⊗[F] E) → Fin M × Fin d → R) := by
    rw [← hΦ]
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2).comp
      (e.continuous.comp ((continuous_apply p.1).comp (continuous_apply 0)))
  have hc2 : Continuous (Φ.symm : (Fin M × Fin d → R) → Fin 1 → Fin M → R ⊗[F] E) := by
    rw [hsymm]
    refine continuous_pi fun _ => continuous_pi fun i => e.symm.continuous.comp ?_
    exact continuous_pi fun k => continuous_apply _
  let Ψ : (Fin 1 → Fin M → R ⊗[F] E) ≃ₜ (Fin M × Fin d → R) :=
    { Φ.toEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }
  refine ⟨Ψ.isHomeomorph, Φ.measurableEmbedding, ?_⟩
  have s1 := measurePreserving_funUnique (Measure.pi fun _ : Fin M => coordK R b lam) (Fin 1)
  have s2 := measurePreserving_pi (fun _ : Fin M => coordK R b lam)
    (fun _ : Fin M => Measure.pi fun _ : Fin d => lam) (fun _ => hmp)
  have h12 := s2.comp s1
  rw [hΦ, ← map_curry_symm_pi lam M d, ← h12.map_eq,
    Measure.map_map (MeasurableEquiv.curry (Fin M) (Fin d) R).symm.measurable h12.measurable]
  rfl

end CoordMap

end GlobalTheory.CompanionTheory.SW.BB
