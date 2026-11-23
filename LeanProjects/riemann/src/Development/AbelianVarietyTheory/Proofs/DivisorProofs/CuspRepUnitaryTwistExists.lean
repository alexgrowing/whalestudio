import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
open NumberField IsDedekindDomain

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1

namespace GlobalTheory.CuspRep.UnitTwist

def normPowHom (t : ℝ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((‖(z : ℂ)‖ ^ t : ℝ) : ℂ) (by
    have h : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
    exact_mod_cast (Real.rpow_pos_of_pos h t).ne')
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

theorem normPowHom_val (t : ℝ) (z : ℂˣ) : ((normPowHom t z : ℂˣ) : ℂ) = ((‖(z : ℂ)‖ ^ t : ℝ) : ℂ) := rfl

theorem norm_normPowHom (t : ℝ) (z : ℂˣ) : ‖((normPowHom t z : ℂˣ) : ℂ)‖ = ‖(z : ℂ)‖ ^ t := by
  rw [normPowHom_val, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 z.ne_zero) t)]

theorem continuous_normPowHom (t : ℝ) : Continuous (normPowHom t) := by
  refine Units.isEmbedding_val₀.continuous_iff.2 ?_
  exact Complex.continuous_ofReal.comp ((continuous_norm.comp Units.continuous_val).rpow_const
    fun z => Or.inl (norm_ne_zero_iff.2 z.ne_zero))

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_val_lt_one (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen {x : w.adicCompletion E | Valued.v x < 1} := by
  have := Valued.isOpen_ball (w.adicCompletion E) 1
  simpa [Valuation.restrict_lt_one_iff] using this

theorem isCompact_isUnitAt (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact {x : (w.adicCompletion E)ˣ | IsUnitAt w x} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have e : ((↑) : (w.adicCompletion E)ˣ → w.adicCompletion E) '' {x | IsUnitAt w x} =
      (w.adicCompletionIntegers E : Set (w.adicCompletion E)) \ {x | Valued.v x < 1} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, not_lt, IsUnitAt]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.le, hx.ge⟩
    · rintro ⟨h1, h2⟩
      have hy : Valued.v y = 1 := le_antisymm h1 h2
      have h0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      exact ⟨Units.mk0 y h0, hy, rfl⟩
  rw [e]
  exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w).diff (isOpen_val_lt_one w)

theorem norm_loc_eq_one (χ : HChar E) {w : HeightOneSpectrum (𝓞 E)} {x : (w.adicCompletion E)ˣ}
    (hx : IsUnitAt w x) : ‖((χ.loc w x : ℂˣ) : ℂ)‖ = 1 := by
  let S := {x : (w.adicCompletion E)ˣ | IsUnitAt w x}
  let g : (w.adicCompletion E)ˣ → ℝ := fun x => ‖((χ.loc w x : ℂˣ) : ℂ)‖
  have hχ : Continuous (χ.1 : Ideles E → ℂˣ) := χ.2.1
  have hg : Continuous g :=
    continuous_norm.comp (Units.continuous_val.comp (hχ.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele w)))
  obtain ⟨M, hM⟩ := (isCompact_isUnitAt w).bddAbove_image hg.continuousOn
  have hpow : ∀ y ∈ S, ∀ n : ℕ, y ^ n ∈ S := fun y hy n => by
    change Valued.v ((y ^ n : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact (congrArg (· ^ n) hy).trans (one_pow n)
  have hgpow : ∀ y n, g (y ^ n) = g y ^ n := fun y n => by
    simp only [g, map_pow, Units.val_pow_eq_pow_val, norm_pow]
  have hle : ∀ y ∈ S, g y ≤ 1 := fun y hy => by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    have := hM ⟨y ^ n, hpow y hy n, rfl⟩
    rw [hgpow] at this
    linarith
  have hinv : x⁻¹ ∈ S := by
    change Valued.v ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact (congrArg (·⁻¹) hx).trans inv_one
  have hpos : 0 < g x := norm_pos_iff.2 (Units.ne_zero _)
  have h1 := hle x hx
  have h2 := hle _ hinv
  have e : g x⁻¹ = (g x)⁻¹ := by
    simp only [g, map_inv, Units.val_inv_eq_inv_val, norm_inv]
  rw [e] at h2
  exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)

end GlobalTheory.CuspRep.UnitTwist

namespace GlobalTheory.CuspRep

open UnitTwist

theorem exists_unramified_twist_isUnitary : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (a : ℕ)
    (π : GlobalTheory.CuspRep.CG E a), 1 ≤ a →
    ∃ ν : Formalism.L2.Host.HChar E, (∀ w, ν.UnrAt w) ∧ (π.twist ν).IsUnitary := by
  intro E _ _ _ a π ha
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar π
  have hωc : Continuous (ω.1 : Ideles E → ℂˣ) := ω.2.1
  let t : ℝ := -(1 / (a : ℝ))
  let ν : HChar E := ⟨(normPowHom t).comp ω.1, (continuous_normPowHom t).comp hωc, fun k => by
    change normPowHom t (ω.1 (diagUnits E k)) = 1
    rw [ω.2.2 k, map_one]⟩
  refine ⟨ν, fun w x hx => ?_, ω * ν ^ a, fun x => ?_, hω.twist ν⟩
  · change normPowHom t (ω.loc w x) = 1
    ext
    rw [normPowHom_val, norm_loc_eq_one ω hx, Real.one_rpow]
    simp
  · change ‖((ω.1 x * (normPowHom t (ω.1 x)) ^ a : ℂˣ) : ℂ)‖ = 1
    have hr : 0 < ‖((ω.1 x : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
    rw [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, norm_normPowHom, ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le]
    have : t * (a : ℝ) = -1 := by
      simp only [t]
      field_simp
    rw [this, Real.rpow_neg_one, mul_inv_cancel₀ hr.ne']

end GlobalTheory.CuspRep
