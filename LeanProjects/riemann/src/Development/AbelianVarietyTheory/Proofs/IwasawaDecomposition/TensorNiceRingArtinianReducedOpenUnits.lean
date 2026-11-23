import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in

theorem _root_.GlobalTheory.GaugeEx.isOpenUnits_of_basis {R S ι : Type} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsOpenUnits R] [CommRing S] [Algebra R S] [TopologicalSpace S]
    [IsModuleTopology R S] [IsTopologicalRing S] [Fintype ι] (b : Module.Basis ι R S) :
    IsOpenUnits S := by
  classical
  have hR : IsOpenEmbedding (Units.val : Rˣ → R) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hLc : Continuous (fun x : S => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hopenR : IsOpen {r : R | IsUnit r} := hR.isOpen_range
  have hinvR : ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by
    rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hR.continuousAt_iff]
    have h : (Ring.inverse ∘ Units.val : Rˣ → R) = fun v => ↑v⁻¹ := by
      funext v
      simp [Ring.inverse_unit]
    rw [h]
    exact Units.continuous_coe_inv.continuousAt
  obtain ⟨g, hg⟩ : ∃ g : S → S, ∀ x, g x =
      b.equivFun.symm (Matrix.mulVec (Algebra.leftMulMatrix b x)⁻¹ (b.equivFun 1)) :=
    ⟨_, fun _ => rfl⟩
  have key : ∀ x, IsUnit (Algebra.leftMulMatrix b x).det → x * g x = 1 := by
    intro x hx
    apply b.equivFun.injective
    rw [Module.Basis.equivFun_apply, ← Algebra.leftMulMatrix_mulVec_repr,
      ← Module.Basis.equivFun_apply, hg, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hx, Matrix.one_mulVec, Module.Basis.equivFun_apply]
  have hunit : ∀ x : S, IsUnit x ↔ IsUnit (Algebra.leftMulMatrix b x).det := by
    intro x
    constructor
    · intro h
      exact (Matrix.isUnit_iff_isUnit_det _).mp (h.map (Algebra.leftMulMatrix b))
    · intro h
      exact ⟨⟨x, g x, key x h, by rw [mul_comm]; exact key x h⟩, rfl⟩
  have hopenS : IsOpen {x : S | IsUnit x} := by
    have h : {x : S | IsUnit x} =
        (fun x : S => (Algebra.leftMulMatrix b x).det) ⁻¹' {r : R | IsUnit r} :=
      Set.ext hunit
    rw [h]
    exact hopenR.preimage hLc.matrix_det
  have hc1 : ContinuousOn (fun x : S => Ring.inverse (Algebra.leftMulMatrix b x).det)
      {x : S | IsUnit x} :=
    hinvR.comp hLc.matrix_det.continuousOn (fun x hx => (hunit x).mp hx)
  have hc2 : ContinuousOn (fun x : S => (Algebra.leftMulMatrix b x)⁻¹) {x : S | IsUnit x} := by
    simp_rw [Matrix.inv_def]
    exact hc1.smul hLc.matrix_adjugate.continuousOn
  have hsymm : Continuous (b.equivFun.symm : (ι → R) → S) :=
    LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hc3 : ContinuousOn g {x : S | IsUnit x} := by
    have h : g = (fun M : Matrix ι ι R => b.equivFun.symm (Matrix.mulVec M (b.equivFun 1))) ∘
        (fun x : S => (Algebra.leftMulMatrix b x)⁻¹) := by
      funext x
      exact hg x
    rw [h]
    exact (hsymm.comp (continuous_id.matrix_mulVec continuous_const)).comp_continuousOn hc2
  have hgu : ∀ u : Sˣ, g u = ↑u⁻¹ := by
    intro u
    calc g u = ↑u⁻¹ * (↑u * g u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑u⁻¹ := by rw [key _ ((hunit _).mp u.isUnit), mul_one]
  exact ⟨⟨Units.isEmbedding_val_mk' hc3 hgu, hopenS⟩⟩

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in

theorem _root_.GlobalTheory.GaugeEx.nice_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], _root_.GlobalTheory.GaugeEx.Nice R → IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsOpenUnits (R ⊗[F] E) := by
  intro F E _ _ _ _ _ R _ _ _ _ _ _ _ _ _ hR
  obtain ⟨hArt, hRed, hOpen, -⟩ := hR
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨?_, ?_, ?_⟩
  · exact IsArtinianRing.of_finite R (R ⊗[F] E)
  · exact _root_.GlobalTheory.ReducedAlg.isReduced_tensor (k := F) R E
  · haveI := _root_.GlobalTheory.GaugeEx.modTopTens (F := F) (E := E) R
    haveI := _root_.GlobalTheory.GaugeEx.topRingTens (F := F) (E := E) R
    exact _root_.GlobalTheory.GaugeEx.isOpenUnits_of_basis
      (Algebra.TensorProduct.basis R (Module.finBasis F E))

end GlobalTheory.GaugeEx
