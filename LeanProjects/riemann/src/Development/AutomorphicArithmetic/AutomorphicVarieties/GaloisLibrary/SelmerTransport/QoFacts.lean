import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.RestrictScalarsTwistInvOver

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base
open TensorProduct nonZeroDivisors

section

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
  [Module.Finite ℤ_[l] O]

private theorem qo_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  have hint : Algebra.IsIntegral ℤ_[l] O := Algebra.IsIntegral.of_finite ℤ_[l] O
  have hm : (⊥ : Ideal O) < IsLocalRing.maximalIdeal O :=
    bot_lt_iff_ne_bot.mpr (IsDiscreteValuationRing.not_a_field O)
  have hlt := Ideal.IsIntegral.comap_lt_comap (R := ℤ_[l]) hm
  have hP : ((⊥ : Ideal O).comap (algebraMap ℤ_[l] O)).IsPrime := Ideal.comap_isPrime _ _
  have hQ : (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) ≠ ⊤ :=
    Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hbot : (⊥ : Ideal O).comap (algebraMap ℤ_[l] O) = ⊥ := by
    by_contra hne
    have hmax := hP.isMaximal hne
    exact hlt.ne (hmax.eq_of_le hQ hlt.le)
  rw [← RingHom.ker_eq_comap_bot] at hbot
  exact (RingHom.injective_iff_ker_eq_bot _).mpr hbot

private theorem exists_padicInt_multiple_of_ne_zero (b : O) (hb : b ≠ 0) :
    ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ d : O, algebraMap ℤ_[l] O c = b * d := by
  have hint : Algebra.IsIntegral ℤ_[l] O := Algebra.IsIntegral.of_finite ℤ_[l] O
  have hne : Ideal.span {b} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have h := Ideal.IsIntegral.comap_ne_bot ℤ_[l] hne
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp h
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hc
  obtain ⟨d, hd⟩ := hc
  exact ⟨c, hc0, d, by rw [← hd, mul_comm]⟩

private theorem fractionRing_exists_padicInt_clear_denom (x : FractionRing O) :
    ∃ o : O, ∃ c : ℤ_[l], c ≠ 0 ∧
      x * algebraMap ℤ_[l] (FractionRing O) c = algebraMap O (FractionRing O) o := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  obtain ⟨c, hc, d, hd⟩ := exists_padicInt_multiple_of_ne_zero l O b (nonZeroDivisors.ne_zero hb)
  refine ⟨a * d, c, hc, ?_⟩
  have hb' : algebraMap O (FractionRing O) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  rw [IsScalarTower.algebraMap_apply ℤ_[l] O (FractionRing O), hd, map_mul, map_mul]
  field_simp

omit [IsDomain O] [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] in
private theorem tmul_qz_inv_mul_eq (o : O) (c d : ℤ_[l]) (hd : d ≠ 0) :
    (o ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] c)⁻¹ : QZ l)) =
      (o * algebraMap ℤ_[l] O d) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c * d))⁻¹ : QZ l) := by
  have hd' : algebraMap ℤ_[l] ℚ_[l] d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hd
  rw [mul_comm o, ← Algebra.smul_def, TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul,
    Algebra.smul_def, map_mul]
  congr 2
  rw [mul_inv, mul_comm (algebraMap ℤ_[l] ℚ_[l] c)⁻¹, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

private theorem qo_equiv : Nonempty (QO l O ≃ₗ[O] KStar.Selmer.FracMod O (FractionRing O)) := by
  classical
  have hinjK : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O), RingHom.coe_comp]
    exact (IsFractionRing.injective O (FractionRing O)).comp (qo_inj l O)
  let ι : ℚ_[l] →+* FractionRing O := IsFractionRing.lift hinjK
  have hι : ∀ z : ℤ_[l], ι (algebraMap ℤ_[l] ℚ_[l] z) = algebraMap ℤ_[l] (FractionRing O) z :=
    fun z => IsFractionRing.lift_algebraMap hinjK z
  let g₁ : ℚ_[l] →ₗ[ℤ_[l]] FractionRing O :=
    { toFun := ι
      map_add' := map_add ι
      map_smul' := fun z q => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hι] }
  let g₂ : ℚ_[l] →ₗ[ℤ_[l]] KStar.Selmer.FracMod O (FractionRing O) :=
    ((1 : Submodule O (FractionRing O)).mkQ.restrictScalars ℤ_[l]).comp g₁
  have hg₂ : ZlSub l ≤ LinearMap.ker g₂ := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (ι (algebraMap ℤ_[l] ℚ_[l] z)) :
      KStar.Selmer.FracMod O (FractionRing O)) = 0
    rw [Submodule.Quotient.mk_eq_zero, hι, Submodule.mem_one]
    exact ⟨algebraMap ℤ_[l] O z, (IsScalarTower.algebraMap_apply ℤ_[l] O _ z).symm⟩
  let g₃ : QZ l →ₗ[ℤ_[l]] KStar.Selmer.FracMod O (FractionRing O) := (ZlSub l).liftQ g₂ hg₂
  let φ : QO l O →ₗ[O] KStar.Selmer.FracMod O (FractionRing O) := LinearMap.liftBaseChange O g₃
  have hφ : ∀ (a : O) (r : ℚ_[l]), φ (a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l)) =
      a • (Submodule.Quotient.mk (ι r) : KStar.Selmer.FracMod O (FractionRing O)) :=
    fun a r => LinearMap.liftBaseChange_tmul O g₃ a _
  have hrep := fractionRing_exists_padicInt_clear_denom l O
  choose o c hc hx using hrep
  let ψ₀ : FractionRing O → QO l O := fun x =>
    (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l))
  have spec : ∀ (x : FractionRing O) (p : O) (e : ℤ_[l]), e ≠ 0 →
      x * algebraMap ℤ_[l] (FractionRing O) e = algebraMap O (FractionRing O) p →
      ψ₀ x = (p ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] e)⁻¹ : QZ l)) := by
    intro x p e he hxe
    show (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) = _
    rw [tmul_qz_inv_mul_eq l O (o x) (c x) e he, tmul_qz_inv_mul_eq l O p e (c x) (hc x), mul_comm e (c x)]
    refine congrArg (· ⊗ₜ[ℤ_[l]] _) ?_
    apply IsFractionRing.injective O (FractionRing O)
    simp only [map_mul, ← IsScalarTower.algebraMap_apply, ← hx x, ← hxe]
    ring
  have ψ₀_add : ∀ x y, ψ₀ (x + y) = ψ₀ x + ψ₀ y := by
    intro x y
    rw [spec (x + y) (o x * algebraMap ℤ_[l] O (c y) + o y * algebraMap ℤ_[l] O (c x)) (c x * c y)
      (mul_ne_zero (hc x) (hc y)) ?_, TensorProduct.add_tmul]
    · show _ = (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) +
        (o y ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c y))⁻¹ : QZ l))
      rw [tmul_qz_inv_mul_eq l O (o x) (c x) (c y) (hc y), tmul_qz_inv_mul_eq l O (o y) (c y) (c x) (hc x),
        mul_comm (c y) (c x)]
    · simp only [map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← hx x, ← hx y]
      ring
  have ψ₀_smul : ∀ (a : O) x, ψ₀ (a • x) = a • ψ₀ x := by
    intro a x
    rw [spec (a • x) (a * o x) (c x) (hc x) ?_]
    · show _ = a • (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l))
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    · rw [Algebra.smul_def, mul_assoc, hx x, map_mul]
  have ψ₀_one : ∀ p : O, ψ₀ (algebraMap O (FractionRing O) p) = 0 := by
    intro p
    rw [spec _ p 1 one_ne_zero (by rw [map_one, mul_one]), map_one, inv_one]
    have h1 : (Submodule.Quotient.mk (1 : ℚ_[l]) : QZ l) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range.mpr ⟨1, by simp⟩
    rw [h1, TensorProduct.tmul_zero]
    rfl
  let ψL : FractionRing O →ₗ[O] QO l O :=
    { toFun := ψ₀
      map_add' := ψ₀_add
      map_smul' := ψ₀_smul }
  have hker : (1 : Submodule O (FractionRing O)) ≤ LinearMap.ker ψL := by
    intro x hx'
    obtain ⟨p, rfl⟩ := Submodule.mem_one.mp hx'
    exact ψ₀_one p
  let ψ : KStar.Selmer.FracMod O (FractionRing O) →ₗ[O] QO l O :=
    (1 : Submodule O (FractionRing O)).liftQ ψL hker
  refine ⟨LinearEquiv.ofLinear φ ψ ?_ ?_⟩
  · apply Submodule.linearMap_qext
    ext x
    show φ (o x ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk (algebraMap ℤ_[l] ℚ_[l] (c x))⁻¹ : QZ l)) =
      Submodule.Quotient.mk x
    have hne : algebraMap ℤ_[l] (FractionRing O) (c x) ≠ 0 := (map_ne_zero_iff _ hinjK).mpr (hc x)
    rw [hφ, map_inv₀, hι, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, ← hx x, mul_inv_cancel_right₀ hne]
  · refine LinearMap.ext fun (t : O ⊗[ℤ_[l]] QZ l) => ?_
    induction t using TensorProduct.induction_on with
    | zero => exact ((ψ ∘ₗ φ).map_zero).trans (LinearMap.id (R := O) (M := QO l O)).map_zero.symm
    | tmul a q =>
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) q
      show ψ (φ (a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l))) =
        a ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk r : QZ l)
      rw [hφ, map_smul]
      show a • ψ₀ (ι r) = _
      obtain ⟨z, e, he, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) r
      have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
      rw [spec _ (algebraMap ℤ_[l] O z) e he0 ?_]
      · rw [Algebra.algebraMap_eq_smul_one (A := O) z, TensorProduct.smul_tmul,
          ← Submodule.Quotient.mk_smul]
        show a • ((1 : O) ⊗ₜ[ℤ_[l]]
          (Submodule.Quotient.mk (z • (algebraMap ℤ_[l] ℚ_[l] e)⁻¹) : QZ l)) = _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.smul_def, div_eq_mul_inv]
      · rw [map_div₀, hι, hι, div_mul_cancel₀ _ ((map_ne_zero_iff _ hinjK).mpr he0),
          IsScalarTower.algebraMap_apply ℤ_[l] O (FractionRing O)]
    | add t₁ t₂ h₁ h₂ =>
      have hadd := (ψ ∘ₗ φ).map_add t₁ t₂
      rw [h₁, h₂] at hadd
      exact hadd

private theorem qo_len (a : O) :
    Module.length O (LinearMap.ker (a • (LinearMap.id : QO l O →ₗ[O] QO l O))) = IsDiscreteValuationRing.addVal O a := by
  obtain ⟨e⟩ := qo_equiv l O
  rw [← KStar.TotallyRealRoots.length_torsionBy_fracMod (FractionRing O) a]
  apply LinearEquiv.length_eq
  refine e.ofSubmodules _ _ ?_
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_torsionBy_iff,
    LinearMap.smul_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [← map_smul, hm, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [← map_smul, hy, map_zero]

omit [IsDomain O] [IsDiscreteValuationRing O] [Module.Finite ℤ_[l] O] in
private theorem qo_tor (m : QO l O) : ∃ n : ℕ, l ^ n • m = 0 := by
  refine TensorProduct.induction_on (motive := fun m : O ⊗[ℤ_[l]] QZ l => ∃ n : ℕ, l ^ n • m = 0)
    m ?_ ?_ ?_
  · exact ⟨0, smul_zero _⟩
  · intro o q
    have hq : ∃ n : ℕ, l ^ n • q = 0 := by
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) q
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖r‖ hl
      refine ⟨n, ?_⟩
      have hle : ‖((l ^ n : ℕ) : ℚ_[l]) * r‖ ≤ 1 := by
        rw [norm_mul, Nat.cast_pow, norm_pow, Padic.norm_p, inv_pow,
          inv_mul_le_iff₀ (by positivity), mul_one]
        exact hn.le
      have hmem : ((l ^ n : ℕ) : ℚ_[l]) * r ∈ ZlSub l :=
        LinearMap.mem_range.mpr ⟨⟨_, hle⟩, rfl⟩
      show (Submodule.Quotient.mk (l ^ n • r) : ℚ_[l] ⧸ ZlSub l) = 0
      rw [nsmul_eq_mul, Submodule.Quotient.mk_eq_zero]
      exact hmem
    obtain ⟨n, hn⟩ := hq
    refine ⟨n, ?_⟩
    have h := map_nsmul (TensorProduct.mk ℤ_[l] O (QZ l) o) (l ^ n) q
    rw [hn, map_zero] at h
    exact h.symm
  · rintro x y ⟨n, hn⟩ ⟨k, hk⟩
    refine ⟨n + k, ?_⟩
    have h1 : l ^ (n + k) • x = 0 := by rw [pow_add, mul_comm, mul_smul, hn, smul_zero]
    have h2 : l ^ (n + k) • y = 0 := by rw [pow_add, mul_smul, hk, smul_zero]
    rw [smul_add, h1, h2, add_zero]

end

theorem UpperTheory.V.Base.qoFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
      (∀ m : QO l O, Module.length O (Submodule.span O {m}) ≠ ⊤) ∧ (∀ m : QO l O, ∃ n : ℕ, l ^ n • m = 0) ∧
      (∀ a : O, a ≠ 0 → ∀ m : QO l O, ∃ m' : QO l O, a • m' = m) ∧
      ∀ a : O, Module.length O (LinearMap.ker (a • (LinearMap.id : QO l O →ₗ[O] QO l O))) = IsDiscreteValuationRing.addVal O a := by
  intro l _ O _ _ _ _ _
  obtain ⟨e⟩ := qo_equiv l O
  refine ⟨fun m => ?_, qo_tor l O, fun a ha m => ?_, qo_len l O⟩
  · obtain ⟨n, hn⟩ := qo_tor l O m
    have hb : ((l ^ n : ℕ) : O) ≠ 0 := by
      rw [← map_natCast (algebraMap ℤ_[l] O), map_ne_zero_iff _ (qo_inj l O), Nat.cast_ne_zero]
      exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have hle : Submodule.span O {m} ≤
        LinearMap.ker (((l ^ n : ℕ) : O) • (LinearMap.id : QO l O →ₗ[O] QO l O)) := by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul O, hn]
    intro htop
    have hlen := Module.length_le_of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
    rw [htop, qo_len l O, top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff] at hlen
    exact hb hlen
  · obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (e m)
    have ha' : algebraMap O (FractionRing O) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr ha
    refine ⟨e.symm (Submodule.Quotient.mk (x / algebraMap O (FractionRing O) a)), ?_⟩
    have hdiv : a • (x / algebraMap O (FractionRing O) a) = x := by
      rw [Algebra.smul_def]
      field_simp
    rw [← map_smul, ← Submodule.Quotient.mk_smul, hdiv, hx, e.symm_apply_apply]
