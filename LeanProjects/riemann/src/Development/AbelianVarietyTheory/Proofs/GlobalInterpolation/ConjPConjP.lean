import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open nonZeroDivisors
noncomputable section
namespace GlobalTheory.CharVal.Vp
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_conjP' (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

omit [StarRing E] in
theorem ne0 (P : HeightOneSpectrum (𝓞 E)) : (P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 P.ne_bot

omit [StarRing E] in
theorem maxV_self (P : HeightOneSpectrum (𝓞 E)) :
    MaxV P ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) (WithZero.exp (-1 : ℤ)) := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using hr)
    simpa using this
  · obtain ⟨r, hr⟩ := P.intValuation_exists_uniformizer
    refine ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, ?_, rfl⟩, ?_⟩
    · have := (P.intValuation_le_pow_iff_mem r 1).1 (by simpa using hr.le)
      simpa using this
    · rw [HeightOneSpectrum.valuation_of_algebraMap, hr]

omit [StarRing E] in
theorem maxV_ne (Q P : HeightOneSpectrum (𝓞 E)) (h : Q ≠ P) :
    MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) 1 := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    exact Q.valuation_le_one r
  · have : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
    obtain ⟨r, hr, hr'⟩ := SetLike.not_le_iff_exists.1 this
    exact ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩,
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).2 hr'⟩

omit [StarRing E] in
theorem maxV_inv {Q P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)} (h0 : γ ≠ 0)
    (h : MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ) :
    MaxV Q (((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ⁻¹ :=
  h.inv h0 (by rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (ne0 P), FractionalIdeal.coe_one])

theorem mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    x ∈ vpIdeal P ↔ ∀ r ∈ (conjPrime₂ P).asIdeal, ∃ s ∈ P.asIdeal, algebraMap _ E s = x * algebraMap _ E r := by
  unfold vpIdeal
  rw [← div_eq_mul_inv, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (ne0 _)]
  constructor
  · intro h r hr
    exact (FractionalIdeal.mem_coeIdeal _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩))
  · intro h y hy
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_coeIdeal _).2 (h r hr)

theorem star_mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : x ∈ vpIdeal P) : star x ∈ vpIdeal (conjPrime₂ P) := by
  rw [mem_vp] at h ⊢
  intro r hr
  rw [conjP_conjP'] at hr
  obtain ⟨s, hs, e⟩ := h (cO E r) (by rwa [mem_conjP, cO_cO])
  refine ⟨cO E s, by rwa [mem_conjP, cO_cO], ?_⟩
  have e1 : algebraMap _ E (cO E s) = star (algebraMap _ E s) := rfl
  have e2 : algebraMap _ E (cO E r) = star (algebraMap _ E r) := rfl
  rw [e1, e, e2, star_mul, star_star, mul_comm]

theorem detLat_vp (P : HeightOneSpectrum (𝓞 E)) : detLat (vpLat P) = vpIdeal P := by
  unfold detLat
  rw [← Submodule.span_eq (vpIdeal P)]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    have := hA _ (single_mem_stdLat (E := E) (0 : Fin 1) 1)
    rw [Matrix.det_fin_one]
    simpa [vpLat, Matrix.mulVec_single] using this
  · intro hx
    refine ⟨Matrix.of fun _ _ => x, fun v hv => ?_, by simp⟩
    obtain ⟨r, hr⟩ := (mem_stdLat v).1 hv 0
    have : (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 = r • x := by
      simp [Matrix.mulVec, dotProduct, ← hr, Algebra.smul_def, mul_comm]
    show (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 ∈ vpIdeal P
    rw [this]
    exact (vpIdeal P).smul_mem r hx

theorem vp_main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), P ≠ conjPrime₂ P → (∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ star x ∈ vpIdeal P) ∧ vpIdeal P * J = 1) ∧ MaxV P (vpIdeal P) (WithZero.exp (-1 : ℤ)) ∧ MaxV (conjPrime₂ P) (vpIdeal P) (WithZero.exp (1 : ℤ)) ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q ≠ conjPrime₂ P → MaxV Q (vpIdeal P) 1) ∧ detLat (vpLat P) = vpIdeal P := by
  intro E _ _ _ P hP
  refine ⟨⟨vpIdeal (conjPrime₂ P), fun x => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩, ?_, ?_, fun Q h1 h2 => ?_, detLat_vp P⟩
  · have := star_mem_vp _ _ h
    rwa [conjP_conjP'] at this
  · simpa using star_mem_vp _ _ h
  · unfold vpIdeal
    rw [conjP_conjP', ← FractionalIdeal.coe_mul, mul_assoc, inv_mul_cancel_left₀ (ne0 _), mul_inv_cancel₀ (ne0 _),
      FractionalIdeal.coe_one]
  · have := (maxV_self P).mul (maxV_inv one_ne_zero (maxV_ne P _ hP))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne _ P hP.symm).mul (maxV_inv WithZero.exp_ne_zero (maxV_self (conjPrime₂ P)))
    rw [one_mul, ← WithZero.exp_neg, neg_neg, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne Q P h1).mul (maxV_inv one_ne_zero (maxV_ne Q _ h2))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this

end GlobalTheory.CharVal.Vp
