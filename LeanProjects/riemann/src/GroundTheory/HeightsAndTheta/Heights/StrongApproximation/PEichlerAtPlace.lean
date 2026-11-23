import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

namespace EichlerAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem sigV_inclV (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    sigV c v (inclV E v x) = inclV E v (c x) := by
  simp [sigV, inclV]

theorem sigA_inclA (c : E ≃ₐ[F] E) (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA]

theorem hf_single_incl (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (u : Fin N → Kv E v) (y : Fin N → E) :
    hf (sigA c) (J.map (inclA F E)) (singleV E v ∘ u) (inclA F E ∘ y) =
      singleV E v (hf (sigV c v).toRingHom (J.map (inclV E v)) u (inclV E v ∘ y)) := by
  simp only [hf, map_sum, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sigA_inclA, sigV_inclV, mul_assoc, ← map_mul (inclA F E), mul_assoc, ← map_mul (inclV E v), hsi]

theorem hf_single_single (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    (hmul : ∀ x y : Kv E v, singleV E v (x * y) = singleV E v x * singleV E v y)
    (hsig : ∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x))
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (u w : Fin N → Kv E v) :
    hf (sigA c) (J.map (inclA F E)) (singleV E v ∘ u) (singleV E v ∘ w) =
      singleV E v (hf (sigV c v).toRingHom (J.map (inclV E v)) u w) := by
  simp only [hf, map_sum, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsig, hmul, hsi]

theorem embed_eich (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (hsi : ∀ (x : Kv E v) (y : E), singleV E v (x * inclV E v y) = singleV E v x * inclA F E y)
    (hsig : ∀ x, sigA c (singleV E v x) = singleV E v (sigV c v x))
    {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (e : Fin N → E) (u : Fin N → Kv E v) (c' : Kv E v) :
    embed E v (eich (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ e) u c') =
      eich (sigA c) (J.map (inclA F E)) (inclA F E ∘ e) (singleV E v ∘ u) (singleV E v c') := by
  have hw : ∀ j, ((J.map (inclV E v)) *ᵥ ((sigV c v).toRingHom ∘ (inclV E v ∘ e))) j =
      inclV E v ((J *ᵥ (c ∘ e)) j) := by
    intro j
    simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, sigV_inclV, map_mul]
  have hwA : ∀ j, ((J.map (inclA F E)) *ᵥ (sigA c ∘ (inclA F E ∘ e))) j =
      inclA F E ((J *ᵥ (c ∘ e)) j) := by
    intro j
    simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply, sigA_inclA,
      map_mul]
  have hz : ∀ j, ((J.map (inclA F E)) *ᵥ (sigA c ∘ (singleV E v ∘ u))) j =
      singleV E v (((J.map (inclV E v)) *ᵥ ((sigV c v).toRingHom ∘ u)) j) := by
    intro j
    simp only [mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsig, mul_comm (inclV E v (J j k)), hsi, mul_comm]
  ext i j
  simp only [embed, eich, Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply,
    vecMulVec_apply, Function.comp_apply, hw, hwA, hz, smul_eq_mul, map_add, map_sub]
  rw [hsi, mul_comm (inclV E v (e i)), hsi, ← map_mul (inclV E v), hsi, map_mul]
  ring

theorem proof (hPM : PlaceMaps.Statement) : EichlerAtPlace.Statement := by
  intro F E _ _ _ _ _ c hF hc v N J
  obtain ⟨-, hv⟩ := hPM F E c hF hc
  obtain ⟨-, -, hmul, -, hsi, hsig, -⟩ := hv v
  have key := fun e u c' => embed_eich c v hsi hsig J e u c'
  refine ⟨key, fun _ e f _ _ _ g hg => ?_⟩
  have along : ∀ a b : Fin N → E,
      g ∈ eichAlong (sigV c v).toRingHom (J.map (inclV E v)) (inclV E v ∘ a) (inclV E v ∘ b) →
      embed E v g ∈ eichAlong (sigA c) (J.map (inclA F E)) (inclA F E ∘ a) (inclA F E ∘ b) := by
    rintro a b ⟨u, c', hua, hub, hc', rfl⟩
    refine ⟨singleV E v ∘ u, singleV E v c', ?_, ?_, ?_, key a u c'⟩
    · rw [hf_single_incl c v hsi J, hua, map_zero]
    · rw [hf_single_incl c v hsi J, hub, map_zero]
    · rw [hf_single_single c v hsi hmul hsig J, hsig, ← map_add, ← map_add]
      exact (congrArg (singleV E v) hc').trans (map_zero _)
  rcases hg with hg | hg
  · exact Or.inl (along e f hg)
  · exact Or.inr (along f e hg)

end EichlerAtPlace

end StrongApprox

end GroundTheory.Heights₂.Heights
