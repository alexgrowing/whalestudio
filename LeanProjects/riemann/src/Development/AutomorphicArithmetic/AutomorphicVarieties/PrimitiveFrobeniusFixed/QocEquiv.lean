import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise TensorProduct

section

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
  [Module.Finite ℤ_[l] O]

private theorem qoc_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  have hl : (l : O) ≠ 0 := by
    intro h0
    have hz : ∀ t : O ⊗[ℤ_[l]] (ℚ_[l] ⧸ ZlSub l), t = 0 := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | tmul o q =>
        obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        have hlq : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
        have hr : (Submodule.Quotient.mk r : ℚ_[l] ⧸ ZlSub l) =
            (l : ℤ_[l]) • Submodule.Quotient.mk (r / l) := by
          rw [← Submodule.Quotient.mk_smul]
          congr 1
          rw [Algebra.smul_def, map_natCast, mul_div_cancel₀ _ hlq]
        rw [hr, ← TensorProduct.smul_tmul, Algebra.smul_def, map_natCast, h0, zero_mul,
          TensorProduct.zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    haveI : Subsingleton (QO l O) := ⟨fun x y => (hz x).trans (hz y).symm⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have h4 := (UpperTheory.V.Base.qoFacts l O).2.2.2 ϖ
    rw [IsDiscreteValuationRing.addVal_uniformizer hϖ, Module.length_eq_zero] at h4
    exact zero_ne_one h4
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  rw [PadicInt.unitCoeff_spec hne, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact ((PadicInt.unitCoeff hne).isUnit.map (algebraMap ℤ_[l] O)).ne_zero h
  · exact hl ((pow_eq_zero_iff' (M₀ := O)).mp h).1

private theorem qoc_ann (w : QO l O) : ∃ a : O, a ≠ 0 ∧ ∀ y : O, y • w = 0 ↔ a ∣ y := by
  obtain ⟨n, hn⟩ := (UpperTheory.V.Base.qoFacts l O).2.1 w
  set I : Ideal O := LinearMap.ker (LinearMap.toSpanSingleton O (QO l O) w) with hI
  have key : ∀ y : O, y • w = 0 ↔ Submodule.IsPrincipal.generator I ∣ y := by
    intro y
    rw [← Ideal.mem_span_singleton, Ideal.span_singleton_generator, hI, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply]
  refine ⟨Submodule.IsPrincipal.generator I, ?_, key⟩
  intro h0
  have h1 : ((l : O) ^ n) • w = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hn
  rw [key, h0, zero_dvd_iff] at h1
  have hl : (l : O) ≠ 0 := by
    intro h
    apply (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero : (l : ℤ_[l]) ≠ 0)
    apply qoc_inj l O
    rw [map_natCast, map_zero]
    exact h
  exact hl ((pow_eq_zero_iff' (M₀ := O)).mp h1).1

private theorem qoc_ex (a : O) (ha : a ≠ 0) : ∃ w : QO l O, ∀ y : O, y • w = 0 ↔ a ∣ y := by
  by_cases hu : IsUnit a
  · exact ⟨0, fun y => by simp [hu.dvd]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖa : ϖ ∣ a := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
    exact ENat.one_le_iff_ne_zero.mpr hu
  obtain ⟨b, rfl⟩ := hϖa
  have hb : b ≠ 0 := right_ne_zero_of_mul ha
  have hT : Module.length O (LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O)) = 1 := by
    rw [(UpperTheory.V.Base.qoFacts l O).2.2.2 ϖ, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  have hnt : Nontrivial (LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O)) := by
    rw [← Module.length_pos_iff (R := O), hT]
    exact zero_lt_one
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O))
  have hz1 : ϖ • (z : QO l O) = 0 := LinearMap.mem_ker.mp z.2
  have hz2 : (z : QO l O) ≠ 0 := fun h => hz (Subtype.ext h)
  obtain ⟨w, hw⟩ := (UpperTheory.V.Base.qoFacts l O).2.2.1 b hb (z : QO l O)
  obtain ⟨c, hc, hC⟩ := qoc_ann l O w
  refine ⟨w, fun y => ?_⟩
  have hca : c ∣ ϖ * b := (hC _).mp (by rw [mul_smul, hw, hz1])
  have hcb : ¬ c ∣ b := fun h => hz2 (by rw [← hw]; exact (hC b).mpr h)
  have hac : ϖ * b ∣ c := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd] at hca hcb ⊢
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hϖ, add_comm]
    exact Order.add_one_le_of_lt (not_le.mp hcb)
  rw [hC y]
  exact ⟨fun h => hac.trans h, fun h => hca.trans h⟩

private theorem length_quotient_span_eq_addVal' {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr u.isUnit, zero_add,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]

private theorem qoc_gen (a : O) (w : QO l O) (ha : a ≠ 0) (h : ∀ y : O, y • w = 0 ↔ a ∣ y) (w' : QO l O)
    (h' : a • w' = 0) : ∃ y : O, w' = y • w := by
  set T := LinearMap.ker (a • LinearMap.id : QO l O →ₗ[O] QO l O) with hT
  have hTlen : Module.length O T = IsDiscreteValuationRing.addVal O a :=
    (UpperTheory.V.Base.qoFacts l O).2.2.2 a
  have hfin : Module.length O T ≠ ⊤ := by
    rw [hTlen, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact ha
  have hwT : w ∈ T := by simp [hT, (h a).mpr dvd_rfl]
  let g : O →ₗ[O] T := LinearMap.toSpanSingleton O T ⟨w, hwT⟩
  have hker : LinearMap.ker g = Ideal.span {a} := by
    ext y
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton, ← h y]
    simp [g, Subtype.ext_iff]
  have hrange : Module.length O (LinearMap.range g) = Module.length O T := by
    rw [← (LinearMap.quotKerEquivRange g).length_eq, hker, length_quotient_span_eq_addVal' a ha, hTlen]
  have htop : LinearMap.range g = ⊤ := by
    have hfl : IsFiniteLength O T := Module.length_ne_top_iff.mp hfin
    haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
    haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
    by_contra hne
    have hlt := Submodule.length_lt hne
    rw [hrange] at hlt
    exact lt_irrefl _ hlt
  have hw'T : w' ∈ T := by simp [hT, h']
  have hmem : (⟨w', hw'T⟩ : T) ∈ LinearMap.range g := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
  exact ⟨y, by simpa [g] using (congrArg Subtype.val hy).symm⟩

end

theorem UpperTheory.V.ML.qoCyc :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
    (∀ w : QO l O, ∃ a : O, a ≠ 0 ∧ ∀ y : O, y • w = 0 ↔ a ∣ y) ∧ (∀ a : O, a ≠ 0 → ∃ w : QO l O, ∀ y : O, y • w = 0 ↔ a ∣ y) ∧
    (∀ (a : O) (w : QO l O), a ≠ 0 → (∀ y : O, y • w = 0 ↔ a ∣ y) → ∀ w' : QO l O, a • w' = 0 → ∃ y : O, w' = y • w) ∧
    (∀ w w' : QO l O, (∃ y : O, w' = y • w) ∨ ∃ y : O, w = y • w') ∧
    ∀ (V : Type) [AddCommGroup V] [Module O V] (f : V →ₗ[O] QO l O) (y : O), (∀ v, y • f v = 0) → Module.length O V ≤ Module.length O (LinearMap.ker f) + IsDiscreteValuationRing.addVal O y := by
  intro l _ O _ _ _ _ _
  refine ⟨qoc_ann l O, qoc_ex l O, fun a w ha h w' h' => qoc_gen l O a w ha h w' h', ?_, ?_⟩
  · intro w w'
    obtain ⟨a, ha, hA⟩ := qoc_ann l O w
    obtain ⟨b, hb, hB⟩ := qoc_ann l O w'
    rcases le_total (IsDiscreteValuationRing.addVal O a) (IsDiscreteValuationRing.addVal O b) with hab | hab
    · rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
      right
      exact qoc_gen l O b w' hb hB w ((hA b).mpr hab)
    · rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
      left
      exact qoc_gen l O a w ha hA w' ((hB a).mpr hab)
  · intro V _ _ f y hy
    have hle : LinearMap.range f ≤ LinearMap.ker (y • LinearMap.id : QO l O →ₗ[O] QO l O) := by
      rintro _ ⟨v, rfl⟩
      simp [hy v]
    rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
      (LinearMap.quotKerEquivRange f).length_eq, ← (UpperTheory.V.Base.qoFacts l O).2.2.2 y]
    exact add_le_add le_rfl
      (Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle))
