import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproxF

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_smul_one {A : Type} [CommRing A] (ρ : A →+* A) (a : A) :
    PI.UnitaryApproxDefs.cT ρ (a • (1 : Matrix n n A)) = ρ a • 1 := by
  ext i j
  simp only [PI.UnitaryApproxDefs.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

def scU {A : Type} [CommRing A] (a b : A) (h : a * b = 1) : GL n A :=
  ⟨a • 1, b • 1, by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, h, one_smul],
    by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm, h, one_smul]⟩

theorem scU_val {A : Type} [CommRing A] (a b : A) (h : a * b = 1) :
    ((scU (n := n) a b h : GL n A) : Matrix n n A) = a • 1 := rfl

theorem scU_mem_UJ {A : Type} [CommRing A] (ρ : A →+* A) (J : Matrix n n A) (a b : A) (h : a * b = 1)
    (hρ : ρ a * a = 1) : scU (n := n) a b h ∈ PI.UnitaryApproxDefs.UJ ρ J := by
  show PI.UnitaryApproxDefs.cT ρ ((scU (n := n) a b h : GL n A) : Matrix n n A) * J *
    ((scU (n := n) a b h : GL n A) : Matrix n n A) = J
  rw [scU_val, cT_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    mul_comm, hρ, one_smul]

end General

section Tensor

variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

theorem sigR_inclE (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    PI.UnitaryApproxDefs.sigR σ R (PI.UnitaryApproxDefs.inclE (F := F) R e) = PI.UnitaryApproxDefs.inclE (F := F) R (σ e) := by
  first
  | rfl
  | simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]

end Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_intOE_of_isIntegral {x : E} (h : IsIntegral ℤ x) : x ∈ PI.UnitaryApproxDefs.intOE E := RingHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩

theorem algebraMap_mem_intOE (a : 𝓞 F) : algebraMap F E (a : F) ∈ PI.UnitaryApproxDefs.intOE E := mem_intOE_of_isIntegral (IsIntegral.algebraMap (NumberField.RingOfIntegers.isIntegral_coe a))

theorem exists_nat_mul (x : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * x ∈ PI.UnitaryApproxDefs.intOE E := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  rw [zsmul_eq_mul] at hyint
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, mem_intOE_of_isIntegral ?_⟩
  rw [Nat.cast_natAbs]
  rcases abs_choice y with h | h
  · rw [h]
    exact hyint
  · rw [h]
    push_cast
    rw [neg_mul]
    exact hyint.neg

theorem exists_int_mul (x : E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ algebraMap F E (c : F) * x ∈ PI.UnitaryApproxDefs.intOE E := by
  obtain ⟨m, hm, hx⟩ := exists_nat_mul x
  refine ⟨(m : 𝓞 F), by exact_mod_cast hm.ne', ?_⟩
  simpa using hx

theorem inclE_mem_Sv (v : HeightOneSpectrum (𝓞 F)) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) :
    PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) x ∈ Sv E v := Subring.subset_closure (Set.mem_union_left _ ⟨⟨x, hx⟩, rfl⟩)

theorem one_tmul_mem_Sv (v : HeightOneSpectrum (𝓞 F)) {t : v.adicCompletion F}
    (ht : t ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] t ∈ Sv E v := Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)

theorem dv_mem_Sv (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) : dv E v d ∈ Sv E v := inclE_mem_Sv v (algebraMap_mem_intOE d)

theorem dv_mul (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) : dv E v (a * b) = dv E v a * dv E v b := by
  unfold dv
  rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul, map_mul]

end PI.UnitaryApproxFinWork

end
