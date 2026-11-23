import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.CovMul

open GlobalTheory.HomCovolume GlobalTheory.SnMass.FrameDual

theorem hasDom_ideLat {E : Type} [Field E] [NumberField E] (hE : IsTotallyComplex E)
    (a : FractionalIdeal (𝓞 E)⁰ E) (ha : a ≠ 0) {c : ℝ} (hc : 0 < c) :
    HasDom volume (ideLat a c : Set (InfinitePlace E → ℂ))
      (ENNReal.ofReal ((FractionalIdeal.absNorm a : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E *
        c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  obtain ⟨L₀, hL₀, hcov⟩ := exists_idealLat E hE a ha
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) := c⁻¹ • LinearMap.id
  have hf : ∀ z, f z = c⁻¹ • z := fun _ => rfl
  have hrank : Module.finrank ℝ (InfinitePlace E → ℂ) = 2 * Fintype.card (InfinitePlace E) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hdet : LinearMap.det f = (c ^ (2 * Fintype.card (InfinitePlace E)))⁻¹ := by
    change LinearMap.det (c⁻¹ • LinearMap.id) = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, hrank, inv_pow]
  have hpos : 0 < c ^ (2 * Fintype.card (InfinitePlace E)) := pow_pos hc _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ ideLat a c := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · have h1 := h w
      rw [hf, Pi.smul_apply, Complex.real_smul] at h1
      rw [← h1, Complex.ofReal_inv, mul_inv_cancel_left₀ (by exact_mod_cast hc.ne')]
    · rw [hf, Pi.smul_apply, Complex.real_smul, h w, Complex.ofReal_inv,
        inv_mul_cancel_left₀ (by exact_mod_cast hc.ne')]
  refine ⟨GlobalTheory.latticeDomain L, GlobalTheory.measurableSet_latticeDomain L, fun v => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := GlobalTheory.existsUnique_add_mem_latticeDomain L v
    refine ⟨z, ⟨(hL _).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hlD⟩
    exact congrArg Subtype.val (hu ⟨l, (hL l).2 hl⟩ hlD)
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (GlobalTheory.isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet,
      abs_of_pos (inv_pos.2 hpos), div_inv_eq_mul] at h
    have hfin : volume (GlobalTheory.latticeDomain L) ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]

theorem value_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (hE : IsTotallyComplex E) (h2 : Module.finrank F E = 2)
    [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] (t t' : ℕ) :
    ((FractionalIdeal.absNorm (dInv E t * dInv E t') : ℚ) : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E =
      (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) *
        |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) := by
  have hD : 0 < |(NumberField.discr F : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  have hdisc : |(discr E : ℝ)| = |(NumberField.discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℝ) (natAbs_discr_sq (F := F) (E := E) h2)
    simpa [Nat.cast_natAbs] using h1
  have hcard : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hexp : |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) =
      ((|(NumberField.discr F : ℝ)| ^ 2)⁻¹ ^ t * (|(NumberField.discr F : ℝ)| ^ 2)⁻¹ ^ t') *
        |(NumberField.discr F : ℝ)| := by
    have e1 : (2 * (t : ℝ)) = ((2 * t : ℕ) : ℝ) := by push_cast; ring
    have e2 : (2 * (t' : ℝ)) = ((2 * t' : ℕ) : ℝ) := by push_cast; ring
    rw [Real.rpow_sub hD, Real.rpow_sub hD, Real.rpow_one, e1, e2, Real.rpow_natCast,
      Real.rpow_natCast, pow_mul, pow_mul, inv_pow, inv_pow]
    field_simp
  rw [map_mul, Rat.cast_mul, absNorm_dInv, absNorm_dInv, vInv_pow E hE, hdisc,
    Real.sqrt_sq hD.le, hcard, hexp]
  ring

theorem hasDom_ideLat_dInv_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hU t t' c hc
  have h := hasDom_ideLat hσ.2.1 (dInv E t * dInv E t')
    (mul_ne_zero (dInv_ne_zero t) (dInv_ne_zero t')) hc
  rwa [value_eq hσ.2.1 hσ.2.2.1 t t'] at h

end GlobalTheory.SnMass.VolN.CovMul
