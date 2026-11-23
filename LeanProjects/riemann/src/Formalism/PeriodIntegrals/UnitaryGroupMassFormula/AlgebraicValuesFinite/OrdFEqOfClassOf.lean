import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

def piU (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ :=
  Classical.choose (exists_isUniformiserAt L v)

theorem piU_spec (v : HeightOneSpectrum (𝓞 L)) :
    IsUniformiserAt L v ((piU v : (v.adicCompletion L)ˣ) : v.adicCompletion L) :=
  Classical.choose_spec (exists_isUniformiserAt L v)

def eU (v : HeightOneSpectrum (𝓞 L)) : Ideles L := localIdele L v (piU v)

theorem ordAt_eU (v w : HeightOneSpectrum (𝓞 L)) [Decidable (w = v)] :
    ordAt L w (eU v) = if w = v then 1 else 0 := by
  classical
  unfold eU
  rw [ordAt_localIdele L v w (piU v) (piU_spec v)]
  congr 1

theorem ordAt_pow' (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) (n : ℕ) :
    ordAt L w (a ^ n) = n * ordAt L w a := by
  unfold ordAt
  have h : ((a ^ n : Ideles L) : AdeleRing (𝓞 L) L).2 w = ((a : AdeleRing (𝓞 L) L).2 w) ^ n := by
    rw [Units.val_pow_eq_pow_val]
    rfl
  rw [h, map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

theorem ordF_eq_of_classOf (a : Ideles L) (ha : classOf L a = 1) :
    ∃ k : Lˣ, ∀ w : HeightOneSpectrum (𝓞 L), ordF w k = ordAt L w a := by
  obtain ⟨k, u, hu, rfl⟩ := (classOf_eq_one_iff L a).1 ha
  refine ⟨k, fun w => ?_⟩
  rw [ordAt_mul, ordAt_diag, (ordAt_eq_zero_iff L w u).2 ((rayUnits_top_iff L u).1 hu w), add_zero]
  rfl

theorem classSame : ClassSame L := by
  classical
  refine ⟨ClassGroup (𝓞 L), inferInstance, fun v => classOf L (eU v), fun v w hvw => ?_⟩
  have h1 : classOf L (eU v * (eU w)⁻¹) = 1 := by
    have hvw' : classOf L (eU v) = classOf L (eU w) := hvw
    rw [map_mul, map_inv, hvw', mul_inv_cancel]
  obtain ⟨k, hk⟩ := ordF_eq_of_classOf _ h1
  refine ⟨k, fun u => ?_⟩
  rw [hk, ordAt_mul, ordAt_inv, ordAt_eU, ordAt_eU]
  ring

theorem classPow : ClassPow L := by
  classical
  refine ⟨Fintype.card (ClassGroup (𝓞 L)), Fintype.card_pos, fun v => ?_⟩
  have h1 : classOf L (eU v ^ Fintype.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨k, hk⟩ := ordF_eq_of_classOf _ h1
  refine ⟨k, fun u => ?_⟩
  rw [hk, ordAt_pow', ordAt_eU]
  split_ifs <;> simp

end PI.AlgValsFin.W
