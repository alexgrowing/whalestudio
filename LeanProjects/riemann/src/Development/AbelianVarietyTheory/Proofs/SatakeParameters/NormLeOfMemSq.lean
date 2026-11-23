import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemPrimeOf

open NumberField

noncomputable section

namespace GlobalTheory.EmbSepUnram

open GlobalTheory.Proof.IdempotentLatticeSequence (primeOf mem_primeOf primeOf_isMaximal natCast_mem_primeOf norm_int_le)

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_int_le {E : Type} [Field E] (φ ψ : E →+* ℂ_[p]) (y : 𝓞 E) : ‖φ (y : E) - ψ (y : E)‖ ≤ 1 :=
  by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_int_le φ y) ?_)
  rw [norm_neg]; exact norm_int_le ψ y

theorem exists_algEquiv {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] [IsGalois ℚ E]
    (ψ₁ ψ₂ : E →+* ℂ_[p]) (h : ∀ x : K, ψ₁ (algebraMap K E x) = ψ₂ (algebraMap K E x)) :
    ∃ σ : E ≃ₐ[K] E, ∀ x, ψ₁ x = ψ₂ (σ x) := by
  let _ : Algebra E ℂ_[p] := ψ₂.toAlgebra
  have _ := IsScalarTower.of_algebraMap_eq (R := ℚ) (S := E) (A := ℂ_[p]) fun x => by
    show algebraMap ℚ ℂ_[p] x = ψ₂ (algebraMap ℚ E x)
    rw [eq_ratCast (algebraMap ℚ ℂ_[p]), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let τ : E ≃ₐ[ℚ] E := (ψ₁.toRatAlgHom).restrictNormal' E
  have hτ : ∀ x, ψ₂ (τ x) = ψ₁ x := fun x => (ψ₁.toRatAlgHom).restrictNormal_commutes E x
  let σ : E ≃ₐ[K] E := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) fun x => ψ₂.injective (by
    change ψ₂ (τ _) = _
    rw [hτ]; exact h x)
  exact ⟨σ, fun x => (hτ x).symm⟩

theorem norm_le_of_mem_sq {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ r) {z : 𝓞 E} (hz : z ∈ primeOf φ ^ 2) :
    ‖φ (z : E)‖ ≤ r * r := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · change ‖φ (algebraMap (𝓞 E) E (a * b))‖ ≤ r * r
    rw [map_mul, map_mul, norm_mul]
    exact mul_le_mul (h a ha) (h b hb) (norm_nonneg _) hr
  · change ‖φ (algebraMap (𝓞 E) E (a + b))‖ ≤ r * r
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem embSep : Formalism.L2.Th1.GD.EmbSep := by
  intro p _ K E _ _ _ _ _ _ φ ψ₁ ψ₂ ⟨π, hπ1, hπ⟩ hK hφ hne
  by_contra hc
  push Not at hc
  have h1 : ∀ y : 𝓞 E, ‖ψ₂ (y : E) - ψ₁ (y : E)‖ < 1 := fun y => by
    have a := lt_of_le_of_ne (norm_sub_int_le φ ψ₁ y) (hc y)
    have e : ψ₂ (y : E) - ψ₁ (y : E) = (φ (y : E) - ψ₁ (y : E)) + -(φ (y : E) - ψ₂ (y : E)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a ?_)
    rw [norm_neg]; exact hφ y
  have hP : ∀ z : 𝓞 E, ‖ψ₂ (z : E)‖ < 1 → z ∈ primeOf φ := fun z hz => by
    change ‖φ (z : E)‖ < 1
    rw [← sub_add_cancel (φ (z : E)) (ψ₂ (z : E))]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hφ z) hz)
  obtain ⟨σ, hσ⟩ := exists_algEquiv ψ₁ ψ₂ hK
  have : IsGalois K E := IsGalois.tower_top_of_isGalois ℚ K E
  have := primeOf_isMaximal φ
  have hP0 : primeOf φ ≠ ⊥ := fun h => by
    have := natCast_mem_primeOf φ
    rw [h, Ideal.mem_bot] at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have : IsGaloisGroup (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) := IsGaloisGroup.of_isFractionRing (E ≃ₐ[K] E) (𝓞 K) (𝓞 E) K E
  have hp0 : (primeOf φ).under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0

  set r := ‖φ (algebraMap K E (π : K))‖ with hr
  have hr0 : 0 < r := by
    refine lt_of_lt_of_le ?_ (hπ (p : 𝓞 E) (natCast_mem_primeOf φ))
    rw [norm_pos_iff]
    have : ((p : 𝓞 E) : E) = (p : E) := rfl
    rw [this, map_natCast]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsq : ¬ Ideal.map (algebraMap (𝓞 K) (𝓞 E)) ((primeOf φ).under (𝓞 K)) ≤ primeOf φ ^ 2 := fun hle => by
    have hπP : algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ ^ 2 :=
      hle (Ideal.mem_map_of_mem _ (show algebraMap (𝓞 K) (𝓞 E) π ∈ primeOf φ from hπ1))
    have := norm_le_of_mem_sq φ hr0.le hπ hπP
    change r ≤ r * r at this
    nlinarith
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) ((primeOf φ).under (𝓞 K)) (primeOf φ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) (E ≃ₐ[K] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx ((primeOf φ).under (𝓞 K)) (primeOf φ) hp0,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).1 hsq)] at hcard
  have hs : σ ∈ (primeOf φ).inertia (E ≃ₐ[K] E) := AddSubgroup.mem_inertia.2 fun x => hP _ (by
    change ‖ψ₂ (σ (x : E) - (x : E))‖ < 1
    rw [map_sub, ← hσ]
    exact h1 x |> fun h => by rwa [norm_sub_rev] at h)
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact hne (RingHom.ext fun x => by rw [hσ, hs]; rfl)

end GlobalTheory.EmbSepUnram
