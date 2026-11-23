import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.SpecBC

theorem baseChange_specDecomp : ∀ (g a m : ℕ) (O : Type) [CommRing O] (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (χ : Fin a → (O →+* ℂ)) (ω : O) (l l' : ℂ) (E : Fin a → Matrix (Fin g) (Fin g) ℂ), l ≠ l' → (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → (∀ i, E i * E i = E i) → (∀ i, (E i).trace = (m : ℂ)) → (∀ i c, ρ c * E i = χ i c • E i) → (∀ i c, E i * ρ c = χ i c • E i) → (l - l') • ∑ i, E i = ρ ω - l' • (1 : Matrix (Fin g) (Fin g) ℂ) → (∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'), (ρ ω).map j *ᵥ x = j l • x → ∃ y : Fin a → Fin g → R', (∀ i c, (ρ c).map j *ᵥ y i = j (χ i c) • y i) ∧ x = ∑ i, y i) ∧ ∀ (k : Type) [Field k] (j : ℂ →+* k) (i : Fin a), χ i ω = l → Module.finrank k (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) : Submodule k (Fin g → k)) = m := by
  intro g a m O _ ρ χ ω l l' E hll hsep hidem htr hrE hEr hsum
  have hsm : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (r : ℂ) (M : Matrix (Fin g) (Fin g) ℂ),
      (r • M).map j = j r • M.map j := by
    intro R' _ j r M; ext; simp
  have hmul : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (M N : Matrix (Fin g) (Fin g) ℂ),
      (M * N).map j = M.map j * N.map j := by
    intro R' _ j M N; exact Matrix.map_mul

  have hrel : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'),
      j (l - l') • ∑ i, (E i).map j *ᵥ x = (ρ ω).map j *ᵥ x - j l' • x := by
    intro R' _ j x
    have h := congrArg (fun M => (RingHom.mapMatrix j M) *ᵥ x) hsum
    simp only [RingHom.mapMatrix_apply] at h
    have hs : (∑ i, E i).map j = ∑ i, (E i).map j := by ext; simp [Matrix.sum_apply]
    rw [hsm, hs, Matrix.smul_mulVec, Matrix.sum_mulVec] at h
    rw [h, Matrix.map_sub _ (map_sub j), Matrix.sub_mulVec, hsm, Matrix.smul_mulVec, Matrix.map_one _ (map_zero j) (map_one j),
      Matrix.one_mulVec]
  refine ⟨fun R' _ j x hx => ?_, fun k _ j i hi => ?_⟩
  · refine ⟨fun i => (E i).map j *ᵥ x, fun i c => ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    · have hu : IsUnit (j (l - l')) := (sub_ne_zero.mpr hll).isUnit.map j
      have h := hrel R' j x
      rw [hx, ← sub_smul, ← map_sub] at h
      exact (hu.smul_left_cancel.mp h).symm
  · have hj : ∀ z : ℂ, z ≠ 0 → j z ≠ 0 := fun z hz => (hz.isUnit.map j).ne_zero
    have hK : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) :
        Submodule k (Fin g → k)) = LinearMap.range (Matrix.mulVecLin ((E i).map j)) := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range]
      constructor
      · intro hy
        refine ⟨y, ?_⟩
        have hz : ∀ i', i' ≠ i → (E i').map j *ᵥ y = 0 := by
          intro i' hne
          obtain ⟨c, hc⟩ := hsep i' i hne
          have h1 : (E i').map j *ᵥ ((ρ c).map j *ᵥ y) = j (χ i' c) • ((E i').map j *ᵥ y) := by
            rw [Matrix.mulVec_mulVec, ← hmul, hEr, hsm, Matrix.smul_mulVec]
          rw [hy c, Matrix.mulVec_smul] at h1
          have h2 : (j (χ i' c) - j (χ i c)) • ((E i').map j *ᵥ y) = 0 := by
            rw [sub_smul, ← h1, sub_self]
          rw [← map_sub] at h2
          exact (smul_eq_zero.mp h2).resolve_left (hj _ (sub_ne_zero.mpr hc))
        have h := hrel k j y
        rw [hy ω, hi, ← sub_smul, ← map_sub,
          Finset.sum_eq_single i (fun b _ hb => hz b hb) (by simp)] at h
        exact smul_right_injective _ (hj _ (sub_ne_zero.mpr hll)) h
      · rintro ⟨z, rfl⟩ c
        rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    rw [hK]
    have hPP : (E i).map j * (E i).map j = (E i).map j := by rw [← hmul, hidem]
    have he : IsIdempotentElem (Matrix.mulVecLin ((E i).map j)) := by
      unfold IsIdempotentElem
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hPP]
    have h1 := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
    rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin g)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h1
    have htj : ((E i).map j).trace = j (E i).trace := by
      simp [Matrix.trace, map_sum]
    rw [htj, htr, map_natCast] at h1
    haveI : CharZero k := (RingHom.charZero_iff j.injective).1 inferInstance
    exact_mod_cast h1.symm

end GlobalTheory.SpecBC
