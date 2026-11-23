import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.Rg.Mass
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassHasse

theorem hasse : Hasse := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ _ _ _ _ _ hmi _ β hβ hne
  by_contra hS
  have hnot : ∀ x : Fin 2 → E, hE σ J x x ≠ algebraMap F E β := fun x hx =>
    hS ⟨fun _ => x, by
      funext a c
      simpa [gramE] using hx⟩
  obtain ⟨τ, c, hc0, hc, hw⟩ := Plane.exists_place hCM J hJ β hβ hnot
  obtain ⟨Φ, hΦ, hΦσ⟩ := Plane.exists_hom hCM τ
  have hscal : algebraMap F (Ainf F) β ⊗ₜ[F] (1 : E) = inclR (Ainf F) (algebraMap F E β) := by
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hempty : (gramR (Ainf F) σ J ⁻¹' {(hermScal (Ainf F) σ (algebraMap F (Ainf F) β)).1} ∩
      {X | IsUnit (gramR (Ainf F) σ J X).det}) = ∅ := by
    ext Y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hY _
    have h00 : hR (Ainf F) σ J (Y 0) (Y 0) = inclR (Ainf F) (algebraMap F E β) :=
      (congrFun (congrFun hY 0) 0).trans hscal
    have h1 := congrArg Φ h00
    rw [hΦ, hc] at h1
    let w : Fin 2 → ℂ := fun i => Φ (Y 0 i)
    have key : Φ (hR (Ainf F) σ J (Y 0) (Y 0)) = star w ⬝ᵥ (J.map τ *ᵥ w) := by
      simp only [hR, hform, JR, map_sum, map_mul, hΦσ, Matrix.map_apply, hΦ, dotProduct, Matrix.mulVec,
        Pi.star_apply, Finset.mul_sum, w, mul_assoc]
    have h2 := hw w
    rw [← key, h1, Complex.ofReal_re] at h2
    exact absurd (mul_self_pos.2 hc0) (not_lt.2 h2)
  apply hne
  have h1 := hmi.1 (hermScal (Ainf F) σ (algebraMap F (Ainf F) β))
  rw [hempty, Set.compl_empty] at h1
  exact Measure.measure_univ_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SW.MassHasse
