import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegersOfMemHatO

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LUnit

theorem intAt_mul {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have e : ((n * m : ℕ) : ℂ) * (a * b) = (n * a) * (m * b) := by push_cast; ring
  rw [e]; exact ha.mul hb

theorem intAt_one (l : ℕ) : IntAt l 1 := ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one⟩

theorem unitAt_one (l : ℕ) : UnitAt l 1 := ⟨one_ne_zero, intAt_one l, by rw [inv_one]; exact intAt_one l⟩

theorem unitAt_mul {l : ℕ} {a b : ℂ} (ha : UnitAt l a) (hb : UnitAt l b) : UnitAt l (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, intAt_mul ha.2.1 hb.2.1, by rw [mul_inv]; exact intAt_mul ha.2.2 hb.2.2⟩

theorem unitAt_inv {l : ℕ} {a : ℂ} (ha : UnitAt l a) : UnitAt l a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unitAt_pow {l : ℕ} {a : ℂ} (ha : UnitAt l a) (n : ℕ) : UnitAt l (a ^ n) := by
  induction n with
  | zero => simpa using unitAt_one l
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih ha

theorem unitAt_zpow {l : ℕ} {a : ℂ} (ha : UnitAt l a) (n : ℤ) : UnitAt l (a ^ n) := by
  cases n with
  | ofNat n => simpa using unitAt_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact unitAt_inv (unitAt_pow ha _)

theorem unitAt_prod {l : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitAt l (f i)) :
    UnitAt l (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one l
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitAt_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitAt_neg {l : ℕ} {a : ℂ} (ha : UnitAt l a) : UnitAt l (-a) := by
  have h1 : UnitAt l (-1) := ⟨by norm_num, ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one.neg⟩,
    ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one.neg⟩⟩
  simpa using unitAt_mul h1 ha

theorem intAt_of_pow {l : ℕ} {a : ℂ} {h : ℕ} (hh : 0 < h) (ha : IntAt l (a ^ h)) : IntAt l a := by
  obtain ⟨n, hn, hi⟩ := ha
  refine ⟨n, hn, IsIntegral.of_pow hh ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have e : ((n : ℂ) * a) ^ (k + 1) = (n : ℂ) ^ k * ((n : ℂ) * a ^ (k + 1)) := by ring
  rw [e]; exact ((isIntegral_natCast (R := ℤ) n).pow _).mul hi

theorem unitAt_of_pow {l : ℕ} {a : ℂ} {h : ℕ} (hh : 0 < h) (ha : UnitAt l (a ^ h)) : UnitAt l a :=
  ⟨fun h0 => ha.1 (by rw [h0, zero_pow hh.ne']), intAt_of_pow hh ha.2.1,
    intAt_of_pow hh (by rw [inv_pow]; exact ha.2.2)⟩

variable {E : Type} [Field E] [NumberField E]

theorem exists_coprime_mul_mem {l : ℕ} (hl : l.Prime) (α : E)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E α ≤ 1) :
    ∃ n : ℕ, n.Coprime l ∧ ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * α := by
  have hal : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨d, hd0, hd⟩ := hal.exists_integral_multiple
  have hD0 : IsIntegral ℤ (((d.natAbs : ℤ)) • α) := by
    rcases Int.natAbs_eq d with e | e
    · rw [← e]; exact hd
    · have : (d.natAbs : ℤ) = -d := by omega
      rw [this, neg_smul]; exact hd.neg
  have hD : IsIntegral ℤ ((d.natAbs : E) * α) := by
    have : ((d.natAbs : ℤ) • α) = (d.natAbs : E) * α := by rw [zsmul_eq_mul, Int.cast_natCast]
    rw [← this]; exact hD0
  obtain ⟨e, m, hm, hDm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hd0) l hl.one_lt.ne'
  refine ⟨m, (Nat.Prime.coprime_iff_not_dvd hl).2 hm |>.symm, ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun w => ?_
  have hval_nat : ∀ k : ℕ, w.valuation E (k : E) ≤ 1 := fun k => by
    have : (k : E) = algebraMap (𝓞 E) E (k : 𝓞 E) := by simp
    rw [this]; exact w.valuation_le_one _
  by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
  · rw [map_mul]
    exact (mul_le_mul' (hval_nat m) (h w hw)).trans_eq (one_mul _)
  · have h1 : w.valuation E ((l : E) ^ e) = 1 := by
      have : (l : E) = algebraMap (𝓞 E) E (l : 𝓞 E) := by simp
      rw [map_pow, this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hw, one_pow]
    have h2 : w.valuation E ((d.natAbs : E) * α) ≤ 1 := by
      have : (d.natAbs : E) * α = algebraMap (𝓞 E) E ⟨_, hD⟩ := rfl
      rw [this]; exact w.valuation_le_one _
    rw [hDm] at h2
    push_cast at h2
    rw [mul_assoc, map_mul, h1, one_mul] at h2
    exact h2

theorem unitAt_embed {l : ℕ} (hl : l.Prime) (α : Eˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1) (σ : E →+* ℂ) :
    UnitAt l (σ α) := by
  have key : ∀ x : E, (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E x ≤ 1) → IntAt l (σ x) := by
    intro x hx
    obtain ⟨n, hn, b, hb⟩ := exists_coprime_mul_mem hl x hx
    refine ⟨n, hn, ?_⟩
    have : (n : ℂ) * σ x = σ.toIntAlgHom (algebraMap (𝓞 E) E b) := by
      rw [hb]; simp
    rw [this]
    exact (RingOfIntegers.isIntegral_coe b).map _
  refine ⟨by simp, key _ fun w hw => (h w hw).le, ?_⟩
  rw [← map_inv₀]
  exact key _ fun w hw => by rw [map_inv₀, h w hw, inv_one]

end GlobalTheory.CMVal.LUnit

namespace GlobalTheory.CMVal.LUnit

variable {E : Type} [Field E] [NumberField E]

theorem mul_coord' (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z * z') w = z w * z' w := rfl

theorem pow_coord (z : Af E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (z ^ n) w = (z w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem val_coord_of_mem_hatOUnits {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((u : Af E) w) = 1 := by
  have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Conv.mem_integers_of_mem_hatO hu.1 w)
  have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Conv.mem_integers_of_mem_hatO hu.2 w)
  have h3 : Valued.v ((u : Af E) w) * Valued.v ((↑u⁻¹ : Af E) w) = 1 := by
    rw [← map_mul, ← mul_coord', Units.mul_inv]
    exact map_one _
  refine le_antisymm h1 ?_
  by_contra hlt
  rw [not_le] at hlt
  have h4 : Valued.v ((u : Af E) w) * Valued.v ((↑u⁻¹ : Af E) w) ≤ Valued.v ((u : Af E) w) * 1 := mul_le_mul' le_rfl h2
  rw [h3, mul_one] at h4
  exact absurd h4 (not_le.2 hlt)

theorem modF_of_mem_hatOUnits {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) : modF u = 1 := by
  unfold modF
  simp [val_coord_of_mem_hatOUnits hu]

theorem modF_pow (y : (Af E)ˣ) (n : ℕ) : modF (y ^ n) = modF y ^ n := by
  induction n with
  | zero =>
    unfold modF
    simp only [pow_zero, Units.val_one]
    exact finprod_eq_one_of_forall_eq_one fun w => by
      have : (1 : Af E) w = 1 := rfl
      rw [this, map_one]; simp
  | succ n ih => rw [pow_succ, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, ih, pow_succ]

theorem unitAt_norm {l : ℕ} (hl : l.Prime) (α : Eˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1) :
    UnitAt l (((|(Algebra.norm ℚ (α : E) : ℝ)| : ℝ) : ℂ)) := by
  have h1 : UnitAt l (((Algebra.norm ℚ (α : E) : ℝ) : ℂ)) := by
    have e : (((Algebra.norm ℚ (α : E) : ℝ) : ℂ)) = algebraMap ℚ ℂ (Algebra.norm ℚ (α : E)) := by simp
    rw [e, Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact unitAt_prod _ _ fun σ _ => unitAt_embed hl α h σ.toRingHom
  rcases abs_choice ((Algebra.norm ℚ (α : E) : ℝ)) with e | e
  · rw [e]; exact h1
  · rw [e, Complex.ofReal_neg]; exact unitAt_neg h1

end GlobalTheory.CMVal.LUnit

open GlobalTheory.CMVal.LUnit in

theorem GlobalTheory.CMVal.value_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (l : ℕ), c ≠ ⊥ → l.Prime →
    HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ y ∈ hatOUnits c, finPart χ y = 1) → ∀ y : (Af E)ˣ,
    (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v ((y : Af E) w) = 1) →
    UnitAt l ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)) := by
  intro E _ _ _ I _ φ _ s κ c χ l hc hl hinf hχ y hy
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)

  have hval : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1 := by
    intro w hw
    have e1 : Units.map (algebraMap E (Af E)).toMonoidHom α = y ^ h * u⁻¹ := eq_mul_inv_of_mul_eq hpu
    have e2 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom α : (Af E)ˣ) : Af E) w) = w.valuation E (α : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (α : E)
    rw [← e2, e1, Units.val_mul, mul_coord', Units.val_pow_eq_pow_val, pow_coord, map_mul, map_pow, hy w hw, one_pow,
      one_mul, val_coord_of_mem_hatOUnits (inv_mem hu) w]

  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hm : modF y ^ h = (|(Algebra.norm ℚ (α : E) : ℝ)|)⁻¹ := by
    rw [← modF_pow, ← hpu, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, modF_of_mem_hatOUnits hu, mul_one,
      (GlobalTheory.CMVal.modF_mul_pos_principal E).2.2]
  have hpow : ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)) ^ h =
      ((χ.inf α : ℂˣ) : ℂ)⁻¹ * ((((|(Algebra.norm ℚ (α : E) : ℝ)| : ℝ) : ℂ))⁻¹) ^ s := by
    rw [mul_pow, hf, ← Complex.ofReal_pow, ← pow_mul, mul_comm s h, pow_mul, hm]
    push_cast
    ring
  refine unitAt_of_pow hpos ?_
  rw [hpow]
  refine unitAt_mul (unitAt_inv ?_) (unitAt_pow (unitAt_inv (unitAt_norm hl α hval)) s)
  rw [(hasInfRatio_iff χ φ _).1 hinf α]
  refine unitAt_prod _ _ fun i _ => unitAt_zpow (unitAt_mul (unitAt_embed hl α hval (φ i)) (unitAt_inv ?_)) _
  exact unitAt_embed hl α hval ((starRingEnd ℂ).comp (φ i))
