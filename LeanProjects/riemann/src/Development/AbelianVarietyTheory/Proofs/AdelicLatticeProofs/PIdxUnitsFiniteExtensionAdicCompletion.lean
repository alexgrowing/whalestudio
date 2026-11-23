import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowIndexTorsionKerRangeMul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexTopOfGroupFg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CardQuotSpanAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteSpanAlgebraMapOfFreeFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormCoeffMinpolyLeOneOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexUnitsOfIsAdicCompleteStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_range_of_injective (p : ℕ) {A B : Type} [CommGroup A] [CommGroup B] (j : A →* B)
    (hj : Function.Injective j) : pIdx p j.range = pIdx p (⊤ : Subgroup A) := by
  have h : pows p j.range = (pows p (⊤ : Subgroup A)).map j := by
    ext x
    simp only [pows, Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_top,
      true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, map_pow _ _ _⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, (map_pow _ _ _).symm⟩
  unfold pIdx
  rw [h, MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hj]

theorem pTor_range_of_injective (p : ℕ) {A B : Type} [CommGroup A] [CommGroup B] (j : A →* B)
    (hj : Function.Injective j) : pTor p j.range = pTor p (⊤ : Subgroup A) := by
  unfold pTor
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨j x.1, ⟨x.1, rfl⟩, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩)
  · intro x y h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  · rintro ⟨_, ⟨a, rfl⟩, h⟩
    exact ⟨⟨a, trivial, hj (by rw [map_pow, h, map_one])⟩, rfl⟩

theorem pTor_pIdx_subgroup_int (p : ℕ) (hp : 0 < p) (H : Subgroup (Multiplicative ℤ))
    (hH : H ≠ ⊥) : pTor p H = 1 ∧ pIdx p H = p := by
  have htor : ∀ U : Subgroup (Multiplicative ℤ), pTor p U = 1 := by
    intro U
    unfold pTor
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, U.one_mem, one_pow _⟩⟩⟩
    rw [(pow_eq_one_iff_left hp.ne').1 x.2.2, (pow_eq_one_iff_left hp.ne').1 y.2.2]
  refine ⟨htor H, ?_⟩
  obtain ⟨d, hd⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top H).1 inferInstance
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hH (by rw [← hd, Subgroup.zpowers_one_eq_bot])
  have hr : H = (zpowersHom (Multiplicative ℤ) d).range := by
    rw [← hd]; rfl
  have hinj : Function.Injective (zpowersHom (Multiplicative ℤ) d) := by
    intro a b h
    simp only [zpowersHom_apply] at h
    have h2 := congrArg Multiplicative.toAdd h
    simp only [toAdd_zpow, smul_eq_mul] at h2
    have hd0 : d.toAdd ≠ 0 := fun h0 => hd1 (by simpa using h0)
    exact Multiplicative.toAdd.injective (mul_right_cancel₀ hd0 h2)
  rw [hr, pIdx_range_of_injective p _ hinj]
  have h := (pIdx_top_of_fg p (Multiplicative ℤ) hp).2
  have hf : Module.finrank ℤ (Additive (Multiplicative ℤ)) = 1 := by
    rw [(AddEquiv.additiveMultiplicative ℤ).toIntLinearEquiv.finrank_eq]
    exact Module.finrank_self ℤ
  rw [h, htor, hf, pow_one, mul_one]

theorem pIdx_of_ker_eq_range (p : ℕ) (hp : 0 < p) {A B : Type} [CommGroup A] [CommGroup B]
    (j : A →* B) (hj : Function.Injective j) (g : B →* Multiplicative ℤ) (hk : g.ker = j.range)
    (hg : g.range ≠ ⊥) (N : ℕ) (hN : N ≠ 0) (h1 : pTor p (⊤ : Subgroup A) ≠ 0)
    (h2 : pIdx p (⊤ : Subgroup A) = N * pTor p (⊤ : Subgroup A)) :
    pTor p (⊤ : Subgroup B) ≠ 0 ∧ pIdx p (⊤ : Subgroup B) = p * N * pTor p (⊤ : Subgroup B) := by
  obtain ⟨r1, r2⟩ := pTor_pIdx_subgroup_int p hp g.range hg
  have k1 : pTor p g.ker = pTor p (⊤ : Subgroup A) := by
    rw [hk, pTor_range_of_injective p j hj]
  have k2 : pIdx p g.ker = N * pTor p (⊤ : Subgroup A) := by
    rw [hk, pIdx_range_of_injective p j hj, h2]
  obtain ⟨-, a2, a3⟩ := pIdx_pTor_ker_range p B (Multiplicative ℤ) g
    (by rw [k2]; exact mul_ne_zero hN h1) (by rw [k1]; exact h1) (by rw [r2]; exact hp.ne')
    (by rw [r1]; exact one_ne_zero)
  refine ⟨a2, ?_⟩
  rw [k1, k2, r1, r2] at a3
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h1)
  linarith

theorem pIdx_units_finite_extension_adicCompletion (p : ℕ) (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ) (L : Type) [Field L] [Algebra (v.adicCompletion F) L]
    [FiniteDimensional (v.adicCompletion F) L] (hp : 0 < p)
    (he : v.valuation F (p : F) = WithZero.exp (-(e : ℤ))) :
    pTor p (⊤ : Subgroup Lˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Lˣ) =
      p * (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L *
        pTor p (⊤ : Subgroup Lˣ) := by
  letI : Algebra (v.adicCompletionIntegers F) L :=
    ((algebraMap (v.adicCompletion F) L).comp
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  haveI : IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  haveI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap (v.adicCompletion F) L).injective
  have hinjRL : Function.Injective (algebraMap (v.adicCompletionIntegers F) L) :=
    (algebraMap (v.adicCompletion F) L).injective.comp Subtype.val_injective
  haveI : FaithfulSMul (v.adicCompletionIntegers F) L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinjRL
  let O : Type := integralClosure (v.adicCompletionIntegers F) L
  haveI : Module.Finite (v.adicCompletionIntegers F) O :=
    IsIntegralClosure.finite (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  haveI : Module.Free (v.adicCompletionIntegers F) O :=
    IsIntegralClosure.module_free (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  have hrank : Module.finrank (v.adicCompletionIntegers F) O =
      Module.finrank (v.adicCompletion F) L :=
    IsIntegralClosure.rank (v.adicCompletionIntegers F) (v.adicCompletion F) L O
  obtain ⟨⟨π₀, -, hπ₀⟩, hval, -⟩ := exists_uniformizer_and_residue_representatives F v
  obtain ⟨hc, hcard⟩ := isAdicComplete_and_card_quotient_adicCompletionIntegers F v
  have hlt : (WithZero.exp (-1) : ℤᵐ⁰) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  let π : v.adicCompletionIntegers F := ⟨algebraMap F (v.adicCompletion F) π₀, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπ₀]; exact hlt.le⟩
  have hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1) := hπ₀
  have hπK : (π : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπL : algebraMap (v.adicCompletion F) L π ≠ 0 := by
    simpa using hπK
  have hvp : Valued.v (((p : v.adicCompletionIntegers F)) : v.adicCompletion F) =
      WithZero.exp (-(e : ℤ)) := by
    rw [← he, ← hval]; simp
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hπO : algebraMap (v.adicCompletionIntegers F) O π ≠ 0 := by
    intro h
    exact hπL (congrArg Subtype.val h)
  have hcomp := isAdicComplete_span_algebraMap_of_free_finite (v.adicCompletionIntegers F) O π
    (hc π (by rw [hπ]; exact hlt))
  have hc1 : Nat.card (O ⧸ Ideal.span {(p : O)}) =
      (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank (v.adicCompletion F) L := by
    have := card_quot_span_algebraMap (v.adicCompletionIntegers F) O (p : _)
    rw [map_natCast, hcard _ e hvp, hrank] at this
    exact this
  have hc2 : Nat.card (O ⧸ Ideal.span
      {(p : O) * algebraMap (v.adicCompletionIntegers F) O π}) ≠ 0 := by
    have := card_quot_span_algebraMap (v.adicCompletionIntegers F) O ((p : _) * π)
    rw [map_mul, map_natCast, hcard _ (e + 1) (by
      rw [MulMemClass.coe_mul, map_mul, hvp, hπ, ← WithZero.exp_add]
      congr 1; push_cast; ring)] at this
    rw [this]
    exact pow_ne_zero _ (pow_ne_zero _ hq)
  obtain ⟨u1, u2⟩ := GlobalTheory.T.subgroupPowRelIndex_units_of_isAdicComplete p O _ hp hπO hcomp hc2
  rw [hc1] at u2
  have hN : ∀ x : Lˣ, Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) ≠ 0 := by
    intro x
    rw [Ne, map_eq_zero, Algebra.norm_eq_zero_iff]
    exact x.ne_zero
  let g : Lˣ →* Multiplicative ℤ :=
    { toFun := fun x => Multiplicative.ofAdd
        (WithZero.log (Valued.v (Algebra.norm (v.adicCompletion F) (x : L))))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [Units.val_mul, map_mul, map_mul, WithZero.log_mul (hN x) (hN y), ofAdd_add] }
  have hg : ∀ x : Lˣ, g x = 1 ↔ Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) = 1 := by
    intro x
    change Multiplicative.ofAdd (WithZero.log _) = 1 ↔ _
    rw [ofAdd_eq_one]
    constructor
    · intro h
      rw [← WithZero.exp_log (hN x), h, WithZero.exp_zero]
    · intro h
      rw [h, WithZero.log_one]
  have hmul : ∀ x : Lˣ, Valued.v (Algebra.norm (v.adicCompletion F) (x : L)) *
      Valued.v (Algebra.norm (v.adicCompletion F) ((x⁻¹ : Lˣ) : L)) = 1 := by
    intro x
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let j : Oˣ →* Lˣ := Units.map ((integralClosure (v.adicCompletionIntegers F) L).val : O →* L)
  refine pIdx_of_ker_eq_range p hp j (Units.map_injective Subtype.val_injective) g ?_ ?_ _
    (pow_ne_zero _ (pow_ne_zero _ hq)) u1 u2
  · ext x
    rw [MonoidHom.mem_ker, hg]
    constructor
    · intro h
      have h' := hmul x
      rw [h, one_mul] at h'
      have i1 := (isIntegral_iff_valued_norm_le_one F v L (x : L)).2 h.le
      have i2 := (isIntegral_iff_valued_norm_le_one F v L ((x⁻¹ : Lˣ) : L)).2 h'.le
      exact ⟨⟨⟨x, i1⟩, ⟨(x⁻¹ : Lˣ), i2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩,
        Units.ext rfl⟩
    · rintro ⟨u, rfl⟩
      have i1 := (isIntegral_iff_valued_norm_le_one F v L ((j u : Lˣ) : L)).1 (u : O).2
      have i2 := (isIntegral_iff_valued_norm_le_one F v L (((j u)⁻¹ : Lˣ) : L)).1
        ((u⁻¹ : Oˣ) : O).2
      exact eq_one_of_one_le_mul_left i1 i2 (hmul _).ge
  · intro h
    have h1 : g (Units.mk0 _ hπL) = 1 := by
      rw [← Subgroup.mem_bot, ← h]; exact ⟨_, rfl⟩
    rw [hg, Units.val_mk0, Algebra.norm_algebraMap, map_pow, hπ] at h1
    exact (pow_lt_one₀ zero_le' hlt Module.finrank_pos.ne').ne h1

end GlobalTheory.CNorm
