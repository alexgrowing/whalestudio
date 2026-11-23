import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FourierColumnIndicator

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

noncomputable section

namespace GlobalTheory.LastSteps

section Values

variable {K : Type} [Field K]

theorem mem_Zmu_of_pow {g : ℕ} {ζ : K} (h : ζ ^ g = 1) : ζ ∈ Zmu K g :=
  Algebra.subset_adjoin (by simp only [Set.mem_setOf_eq]; rw [pow_mul, h, one_pow])

theorem mem_Zmu_of_pow_pred {g : ℕ} {ζ : K} (h : ζ ^ (g - 1) = 1) : ζ ∈ Zmu K g :=
  Algebra.subset_adjoin (by simp only [Set.mem_setOf_eq]; rw [mul_comm, pow_mul, h, one_pow])

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem addChar_mem (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K) (c : 𝓞 E ⧸ P.asIdeal) : ψ c ∈ Zmu K (qOf P) := by
  refine mem_Zmu_of_pow ?_
  have h0 : ((qOf P : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 qOf_mem
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, h0, zero_mul, AddChar.map_zero_eq_one]

theorem char_pow (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (u : (𝓞 E ⧸ P.asIdeal)ˣ) : ((χ u : Kˣ) : K) ^ (qOf P - 1) = 1 := by
  have := P.isMaximal
  have h : Nat.card (𝓞 E ⧸ P.asIdeal)ˣ = qOf P - 1 := by
    letI := Ideal.Quotient.field P.asIdeal
    rw [Nat.card_units]
    rfl
  rw [← h, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem unitV_mem (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : LocE.unitV χ a ∈ Zmu K (qOf P) := by
  unfold LocE.unitV
  split_ifs
  · exact mem_Zmu_of_pow_pred (char_pow χ _)
  · exact zero_mem _

theorem unitV_inv_mem (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : (LocE.unitV χ a)⁻¹ ∈ Zmu K (qOf P) := by
  unfold LocE.unitV
  split_ifs
  · exact mem_Zmu_of_pow_pred (by rw [inv_pow, char_pow, inv_one])
  · rw [inv_zero]; exact zero_mem _

theorem unitV_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) :
    LocE.unitV χ a = LocE.unitV χ b := by
  unfold LocE.unitV
  rw [h]

end Values

section Congr

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_add_iff {a z : E} (hz : IntAt P z) : IntAt P (a + z) ↔ IntAt P a :=
  ⟨fun h => by simpa using intAt_sub h hz, fun h => h.add hz⟩

theorem intAt_add_q {a z : E} (hz : IntAt P z) : IntAt P (a + (qOf P : E) * z) ↔ IntAt P a :=
  intAt_add_iff ((intAt_nat _).mul hz)

theorem intAt_add_q_div {a z : E} (hz : IntAt P z) :
    IntAt P ((a + (qOf P : E) * z) / (qOf P : E)) ↔ IntAt P (a / (qOf P : E)) := by
  rw [add_div, mul_div_cancel_left₀ _ qOf_ne_zero]
  exact intAt_add_iff hz

theorem redP_add_q {a z : E} (hz : IntAt P z) : redP P (a + (qOf P : E) * z) = redP P a := by
  by_cases ha : IntAt P a
  · rw [reduction_add ha ((intAt_nat _).mul hz), reduction_mul (intAt_nat _) hz, reduction_absNorm_eq_zero, zero_mul, add_zero]
  · rw [reduction_eq_zero_of_not_integral P ha, reduction_eq_zero_of_not_integral P (fun h => ha ((intAt_add_q hz).1 h))]

theorem redP_det_add_q {n : ℕ} {A Z : Fin n → Fin n → E} (hA : ∀ i j, IntAt P (A i j)) (hZ : ∀ i j, IntAt P (Z i j)) :
    redP P (Matrix.det (Matrix.of fun i j => A i j + (qOf P : E) * Z i j)) = redP P (Matrix.det (Matrix.of fun i j => A i j)) := by
  rw [(det_int (A := Matrix.of fun i j => A i j + (qOf P : E) * Z i j) fun i j => (intAt_add_q (hZ i j)).2 (hA i j)).2,
    (det_int (A := Matrix.of fun i j => A i j) hA).2]
  congr 1
  ext i j
  exact redP_add_q (hZ i j)

theorem intAt_of_isUnit {a : E} (h : IsUnit (redP P a)) : IntAt P a := by
  by_contra hn
  rw [reduction_eq_zero_of_not_integral P hn] at h
  exact not_isUnit_zero h

theorem not_isUnit_q_pow {a : E} (ha : IntAt P a) (k : ℕ) : ¬ IsUnit (redP P (a * (qOf P : E) ^ (k + 1))) := by
  rw [pow_succ, ← mul_assoc, reduction_mul (ha.mul (intAt_pow (intAt_nat _) _)) (intAt_nat _), reduction_absNorm_eq_zero, mul_zero]
  exact not_isUnit_zero

theorem vP_unit {a : E} (h : IsUnit (redP P a)) : LocE.vP P (qOf P) a = 0 := by
  have h1 : IsUnit (redP P (a / (qOf P : E) ^ LocE.vP P (qOf P) a)) :=
    Classical.epsilon_spec (p := fun z : ℤ => IsUnit (redP P (a / (qOf P : E) ^ z))) ⟨0, by simpa using h⟩
  generalize LocE.vP P (qOf P) a = z at h1
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  rcases lt_trichotomy z 0 with hz | hz | hz
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = -((k + 1 : ℕ) : ℤ) := ⟨(-z - 1).toNat, by omega⟩
    rw [zpow_neg, div_inv_eq_mul, zpow_natCast] at h1
    exact absurd h1 (not_isUnit_q_pow (intAt_of_isUnit h) k)
  · exact hz
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = ((k + 1 : ℕ) : ℤ) := ⟨(z - 1).toNat, by omega⟩
    have := not_isUnit_q_pow (intAt_of_isUnit h1) k
    rw [zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ hq)] at this
    exact absurd h this

theorem locChar_unit {K : Type} [Field K] (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (h : IsUnit (redP P a)) :
    LocE.locChar (qOf P) cq χ a = LocE.unitV χ a := by
  unfold LocE.locChar
  rw [vP_unit h]
  simp

theorem exists_int_congr {a : E} (ha : IntAt P a) : ∃ r : 𝓞 E, IntAt P ((a - algebraMap (𝓞 E) E r) / (qOf P : E)) := by
  obtain ⟨r, s, hs, h⟩ := ha
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hq' : ((qOf P : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hq (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((qOf P : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hq')
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => Ideal.Quotient.mk (Ideal.span {((qOf P : ℕ) : 𝓞 E)}) (s ^ k))
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm he.symm (by omega)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 he)
  have hc' := congrArg (algebraMap (𝓞 E) E) hc
  simp only [map_mul, map_natCast, map_sub, map_pow] at hc'
  refine ⟨r * s ^ d, c * r, s ^ (i + 1), fun hm => hs (P.isPrime.mem_of_pow_mem _ hm), ?_⟩
  simp only [map_mul, map_pow]
  rw [← h]
  field_simp
  linear_combination (-(algebraMap (𝓞 E) E s * a)) * hc'

end Congr

section Good

variable {E K : Type} [Field E] [NumberField E] [Field K]

def Good (P : HeightOneSpectrum (𝓞 E)) {V : Type} [AddCommGroup V] [Module E V] (H : Set V) (Φ : V → K) : Prop :=
  (∀ x, Φ x ≠ 0 → x ∈ H) ∧ (∀ x z, z ∈ H → Φ (x + (qOf P : E) • z) = Φ x) ∧ ∀ x, Φ x ∈ Zmu K (qOf P)

variable {P : HeightOneSpectrum (𝓞 E)} {V W U : Type} [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]
  [AddCommGroup U] [Module E U]

theorem Good.comp {H : Set V} {Φ : V → K} (h : Good P H Φ) {H' : Set W} (T : W → V)
    (hT : ∀ x z, T (x + (qOf P : E) • z) = T x + (qOf P : E) • T z) (hH : ∀ w, w ∈ H' ↔ T w ∈ H) :
    Good P H' fun w => Φ (T w) :=
  ⟨fun x hx => (hH x).2 (h.1 _ hx), fun x z hz => by
    dsimp only
    rw [hT, h.2.1 _ _ ((hH z).1 hz)], fun x => h.2.2 _⟩

theorem Good.mul {H₁ : Set V} {Φ₁ : V → K} (h₁ : Good P H₁ Φ₁) {H₂ : Set U} {Φ₂ : U → K} (h₂ : Good P H₂ Φ₂) {H' : Set W}
    (T₁ : W → V) (T₂ : W → U) (hT₁ : ∀ x z, T₁ (x + (qOf P : E) • z) = T₁ x + (qOf P : E) • T₁ z)
    (hT₂ : ∀ x z, T₂ (x + (qOf P : E) • z) = T₂ x + (qOf P : E) • T₂ z) (hH : ∀ w, w ∈ H' ↔ T₁ w ∈ H₁ ∧ T₂ w ∈ H₂) :
    Good P H' fun w => Φ₁ (T₁ w) * Φ₂ (T₂ w) :=
  ⟨fun x hx => (hH x).2 ⟨h₁.1 _ (left_ne_zero_of_mul hx), h₂.1 _ (right_ne_zero_of_mul hx)⟩, fun x z hz => by
    dsimp only
    rw [hT₁, hT₂, h₁.2.1 _ _ ((hH z).1 hz).1, h₂.2.1 _ _ ((hH z).1 hz).2], fun x => mul_mem (h₁.2.2 _) (h₂.2.2 _)⟩

theorem Good.const_mul {H : Set V} {Φ : V → K} (h : Good P H Φ) {c : K} (hc : c ∈ Zmu K (qOf P)) :
    Good P H fun x => c * Φ x :=
  ⟨fun x hx => h.1 _ (right_ne_zero_of_mul hx), fun x z hz => by
    dsimp only
    rw [h.2.1 _ _ hz], fun x => mul_mem hc (h.2.2 _)⟩

theorem Good.sum {H : Set V} {ι : Type} (s : Finset ι) {Φ : ι → V → K} (h : ∀ i ∈ s, Good P H (Φ i)) :
    Good P H fun x => ∑ i ∈ s, Φ i x :=
  ⟨fun x hx => by
    obtain ⟨i, hi, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact (h i hi).1 _ h0, fun x z hz => Finset.sum_congr rfl fun i hi => (h i hi).2.1 _ _ hz,
    fun x => sum_mem fun i hi => (h i hi).2.2 _⟩

def homS {a b : ℕ} (A : Submodule (𝓞 E) (Sp E a)) (B : Submodule (𝓞 E) (Sp E b)) : Set (HomE E a b) := {x | ∀ y ∈ A, x y ∈ B}

theorem fnModAt_iff {a b : ℕ} (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) :
    FnModAt P N N' Φ ↔ Good P (homS (localization₂ P.asIdeal N) (localization₂ P.asIdeal N')) Φ := by
  have h : ∀ x : HomE E a b, x ∈ homAt {P} N N' ↔ x ∈ homS (localization₂ P.asIdeal N) (localization₂ P.asIdeal N') := fun x =>
    ⟨fun h => h P (Finset.mem_singleton_self P), fun h Q hQ => by rw [Finset.mem_singleton.1 hQ]; exact h⟩
  simp only [FnModAt, Good, h]

end Good

section Lat

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem mem_sclLat {N : ℕ} {e : ℕ → ℤ} {v : Sp E N} :
    v ∈ LocE.sclLat P (qOf P) N e ↔ ∀ l : Fin N, IntAt P (((qOf P : E) ^ e l.1)⁻¹ * v l) := by
  unfold LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt]
  rfl

theorem mem_homS_sclLat {N' N : ℕ} {e' e : ℕ → ℤ} {x : HomE E N' N} :
    x ∈ homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e) ↔
      ∀ (l : Fin N) (l' : Fin N'), IntAt P (x (Pi.single l' 1) l * (qOf P : E) ^ (e' l'.1 - e l.1)) := by
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  constructor
  · intro h l l'
    have h1 : ((qOf P : E) ^ e' l'.1) • (Pi.single l' 1 : Sp E N') ∈ LocE.sclLat P (qOf P) N' e' := by
      refine mem_sclLat.2 fun j => ?_
      by_cases hj : j = l'
      · subst hj
        simpa [inv_mul_cancel₀ (zpow_ne_zero _ hq)] using intAt_one
      · simpa [hj] using intAt_zero
    have h2 := mem_sclLat.1 (h _ h1) l
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
    convert h2 using 1
    rw [zpow_sub₀ hq]
    ring
  · intro h y hy
    refine mem_sclLat.2 fun l => ?_
    rw [apply_eq_sum, Finset.mul_sum]
    refine intAt_sum _ fun j _ => ?_
    convert (mem_sclLat.1 hy j).mul (h l j) using 1
    rw [zpow_sub₀ hq]
    have := zpow_ne_zero (e' j.1) hq
    field_simp

omit [NumberField E] [StarRing E] in
theorem eN_eq {N i : ℕ} (h : i < N) : Loc.eN E N i = Pi.single ⟨i, h⟩ 1 := by
  funext l
  simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

omit [NumberField E] [StarRing E] in
theorem eN_of_not {N i : ℕ} (h : ¬ i < N) : Loc.eN E N i = 0 := by
  funext l
  have := l.2
  simp only [Loc.eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem entB_int {n' c' n c : ℕ} (k₀ : ℕ) {ex' ex : ℕ → ℕ} {x : HomE E (n' + c') (n + c)}
    (h : x ∈ homS (LocE.lamY P (qOf P) n' c' ex') (LocE.lamY P (qOf P) n c ex)) (p p' : ℕ) :
    IntAt P (LocE.entB (qOf P) k₀ c' n' c n ex' ex x p p') := by
  unfold LocE.entB Loc.atN
  split_ifs with h1
  · by_cases h2 : LocE.fIdx k₀ c' n' p' < n' + c'
    · rw [eN_eq h2]
      exact mem_homS_sclLat.1 h ⟨_, h1⟩ ⟨_, h2⟩
    · rw [eN_of_not h2]
      simpa using intAt_zero
  · simpa using intAt_zero

theorem fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) :
    LocE.fPos k₀ c n l < n + c ∧ LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l := by
  unfold LocE.fIdx LocE.fPos
  split_ifs <;> omega

theorem homS_of_entB {n' c' n c k₀ : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n) {ex' ex : ℕ → ℕ} {x : HomE E (n' + c') (n + c)}
    (h : ∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB (qOf P) k₀ c' n' c n ex' ex x p p')) :
    x ∈ homS (LocE.lamY P (qOf P) n' c' ex') (LocE.lamY P (qOf P) n c ex) := by
  refine mem_homS_sclLat.2 fun l l' => ?_
  obtain ⟨h1, h2⟩ := fIdx_fPos hk l.2
  obtain ⟨h1', h2'⟩ := fIdx_fPos hk' l'.2
  have := h _ _ h1 h1'
  unfold LocE.entB Loc.atN at this
  rw [h2, h2', dif_pos l.2, eN_eq l'.2] at this
  exact this

omit [NumberField E] [StarRing E] in
theorem entB_add_smul {N' N : ℕ} (q k₀ c' n' c n : ℕ) (ex' ex : ℕ → ℕ) (x z : HomE E N' N) (s : E) :
    LocE.entB q k₀ c' n' c n ex' ex (x + s • z) =
      fun p p' => LocE.entB q k₀ c' n' c n ex' ex x p p' + s * LocE.entB q k₀ c' n' c n ex' ex z p p' := by
  funext p p'
  unfold LocE.entB Loc.atN
  split_ifs
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

theorem intAt_det_of_homS {N : ℕ} {e : ℕ → ℤ} {x : HomE E N N}
    (h : x ∈ homS (LocE.sclLat P (qOf P) N e) (LocE.sclLat P (qOf P) N e)) : IntAt P (LinearMap.det x) := by
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have h1 := (det_int (A := Matrix.of fun l l' : Fin N => ((qOf P : E) ^ e l.1)⁻¹ *
      (Matrix.of fun l l' : Fin N => (qOf P : E) ^ e l'.1 * LinearMap.toMatrix' x l l') l l') fun l l' => by
    convert mem_homS_sclLat.1 h l l' using 1
    simp only [Matrix.of_apply, LinearMap.toMatrix'_apply]
    rw [zpow_sub₀ hq]
    ring).1
  rw [Matrix.det_mul_column, Matrix.det_mul_row, Finset.prod_inv_distrib, ← mul_assoc,
    inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq), one_mul, LinearMap.det_toMatrix'] at h1
  exact h1

theorem isUnit_det_of_stab {N : ℕ} {e : ℕ → ℤ} {g : Sp E N ≃ₗ[E] Sp E N} (h : g ∈ stabL E N (LocE.sclLat P (qOf P) N e)) :
    IsUnit (redP P ((LinearEquiv.det g : Eˣ) : E)) := by
  have h1 : ∀ g ∈ stabL E N (LocE.sclLat P (qOf P) N e), IntAt P ((LinearEquiv.det g : Eˣ) : E) := fun g hg => by
    rw [LinearEquiv.coe_det]
    exact intAt_det_of_homS fun y hy => (hg y).2 hy
  have h2 := reduction_mul (h1 g h) (h1 g⁻¹ (inv_mem h))
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, reduction_one₂] at h2
  exact IsUnit.of_mul_eq_one _ h2.symm

end Lat

theorem ne_of_ite {α : Type} [Zero α] {p : Prop} {_ : Decidable p} {a : α} (h : (if p then a else 0) ≠ 0) : p := by
  by_contra hp
  exact h (if_neg hp)

theorem ite_eq_ite_zero {α : Type} [Zero α] {p q : Prop} {_ : Decidable p} {_ : Decidable q} {a b : α} (h : p ↔ q)
    (h' : q → a = b) : (if p then a else 0) = if q then b else 0 := by
  by_cases hq : q
  · rw [if_pos hq, if_pos (h.2 hq), h' hq]
  · rw [if_neg hq, if_neg (fun hp => hq (h.1 hp))]

section Data

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
  (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

omit [StarRing E] in
theorem blocks_congr {r t j : ℕ} {M Z : ℕ → ℕ → E} (hM : ∀ p p', p < r + j * t → p' < r + j * t → IntAt P (M p p'))
    (hZ : ∀ p p', IntAt P (Z p p')) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t =>
        M (r + i * t + s.1) (r + i * t + s'.1) + (qOf P : E) * Z (r + i * t + s.1) (r + i * t + s'.1))) =
      ∏ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) := by
  refine Finset.prod_congr rfl fun i hi => unitV_congr _ (redP_det_add_q (fun s s' => ?_) fun _ _ => hZ _ _)
  have h1 : ∀ s : Fin t, r + i * t + s.1 < r + j * t := fun s => by
    have := Finset.mem_range.1 hi
    have := s.2
    nlinarith
  exact hM _ _ (h1 s) (h1 s')

omit [StarRing E] in
theorem lamGv_congr {r t j : ℕ} {M Z : ℕ → ℕ → E} (hM : ∀ p p', p < r + j * t → p' < r + j * t → IntAt P (M p p'))
    (hZ : ∀ p p', IntAt P (Z p p')) :
    LocE.lamGv ψ₀ χ r t j (fun p p' => M p p' + (qOf P : E) * Z p p') = LocE.lamGv ψ₀ χ r t j M := by
  unfold LocE.lamGv
  rw [blocks_congr χ hM hZ, Finset.sum_add_distrib, ← Finset.mul_sum, redP_add_q (intAt_sum _ fun _ _ => hZ _ _)]

omit [StarRing E] in
theorem lamGvS_congr {k₀ r t j : ℕ} {M Z : ℕ → ℕ → E} (hM : ∀ p p', p < r + j * t → p' < r + j * t → IntAt P (M p p'))
    (hZ : ∀ p p', IntAt P (Z p p')) :
    LocE.lamGvS ψ₀ χ k₀ r t j (fun p p' => M p p' + (qOf P : E) * Z p p') = LocE.lamGvS ψ₀ χ k₀ r t j M := by
  unfold LocE.lamGvS
  rw [blocks_congr χ hM hZ, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    add_add_add_comm, ← mul_add, redP_add_q ((intAt_sum _ fun _ _ => hZ _ _).add (intAt_sum _ fun _ _ => hZ _ _))]

theorem good_PhiG {k₀ r t j c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n) (ha : r + (j - 1) * t = n' + c') (hab : n' + c' ≤ n + c) :
    Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1))
      (LocE.PhiG (qOf P) ψ₀ χ false k₀ r t j c' n' c n) := by
  refine ⟨fun x hx => ?_, fun x z hz => ?_, fun x => ?_⟩
  · unfold LocE.PhiG at hx
    dsimp only at hx
    exact homS_of_entB hk' hk fun p p' h h' => (ne_of_ite hx).1 p p' h (by omega)
  · have hZ := entB_int k₀ hz
    unfold LocE.PhiG
    dsimp only
    rw [entB_add_smul]
    generalize LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) z = Z at hZ
    generalize LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x = M
    have e1 := fun a p p' => intAt_add_q (a := a) (hZ p p')
    have e2 := fun a p p' => intAt_add_q_div (a := a) (hZ p p')
    have e3 := fun a p p' => redP_add_q (a := a) (hZ p p')
    refine ite_eq_ite_zero (by simp only [e1, e2, e3]) fun h => ?_
    · have hM := fun p p' (h1 : p < r + (j - 1) * t) (h2 : p' < r + (j - 1) * t) => h.1 p p' (by omega) h2
      rw [lamGv_congr ψ₀ χ hM hZ, unitV_congr _ (redP_det_add_q (fun s s' => hM _ _ s.2 s'.2) fun _ _ => hZ _ _)]
  · unfold LocE.PhiG LocE.lamGv
    dsimp only
    split_ifs
    · exact mul_mem (mul_mem (addChar_mem _ _) (prod_mem fun _ _ => unitV_mem _ _)) (unitV_inv_mem _ _)
    · exact zero_mem _

theorem good_PhiGS {k₀ rS r t j c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n) (ha : r + (j - 1) * t = n' + c')
    (hab : n' + c' ≤ n + c) :
    Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1))
      (LocE.PhiGS (qOf P) ψ₀ χ k₀ rS r t j c' n' c n) := by
  refine ⟨fun x hx => ?_, fun x z hz => ?_, fun x => ?_⟩
  · unfold LocE.PhiGS at hx
    dsimp only at hx
    exact homS_of_entB hk' hk fun p p' h h' => (ne_of_ite hx).1 p p' h (by omega)
  · have hZ := entB_int k₀ hz
    unfold LocE.PhiGS
    dsimp only
    rw [entB_add_smul]
    generalize LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) z = Z at hZ
    generalize LocE.entB (qOf P) k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x = M
    have e1 := fun a p p' => intAt_add_q (a := a) (hZ p p')
    have e2 := fun a p p' => intAt_add_q_div (a := a) (hZ p p')
    have e3 := fun a p p' => redP_add_q (a := a) (hZ p p')
    refine ite_eq_ite_zero (by simp only [e1, e2, e3]) fun h => ?_
    · have hM := fun p p' (h1 : p < r + (j - 1) * t) (h2 : p' < r + (j - 1) * t) => h.1 p p' (by omega) h2
      rw [lamGvS_congr ψ₀ χ hM hZ, unitV_congr _ (redP_det_add_q (fun s s' => hM _ _ s.2 s'.2) fun _ _ => hZ _ _)]
  · unfold LocE.PhiGS LocE.lamGvS
    dsimp only
    split_ifs
    · exact mul_mem (mul_mem (addChar_mem _ _) (prod_mem fun _ _ => unitV_mem _ _)) (unitV_inv_mem _ _)
    · exact zero_mem _

theorem good_om {N' N : ℕ} {e' : ℕ → ℤ} {B : Submodule (𝓞 E) (Sp E N)} {Φ : HomE E N' N → K}
    (h : Good P (homS (LocE.sclLat P (qOf P) N' e') B) Φ) (cq sq : K) (χ₀ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {g : Sp E N' ≃ₗ[E] Sp E N'} (hg : g ∈ stabL E N' (LocE.sclLat P (qOf P) N' e')) :
    Good P (homS (LocE.sclLat P (qOf P) N' e') B)
      (Loc.om (LocE.locChar (qOf P) cq χ₀) (LocE.vP P (qOf P)) sq g 1 Φ) := by
  have hu := isUnit_det_of_stab hg
  have h1 : IsUnit (redP P ((LinearEquiv.det (1 : Sp E N ≃ₗ[E] Sp E N) : Eˣ) : E)) := by
    rw [map_one, Units.val_one, reduction_one₂]
    exact isUnit_one
  unfold Loc.om
  rw [locChar_unit _ _ hu, locChar_unit _ _ h1, vP_unit hu, vP_unit h1]
  refine Good.const_mul (h.comp (H' := homS (LocE.sclLat P (qOf P) N' e') B) (fun x => (1 : Sp E N ≃ₗ[E] Sp E N).symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap)
    (fun x z => ?_) fun w => ⟨fun hw y hy => hw _ ((hg y).2 hy), fun hw y hy => ?_⟩) ?_
  · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
  · have := hw (g.symm y) ((hg _).1 (by simpa using hy))
    rw [← g.apply_symm_apply y]
    exact this
  · simp only [neg_zero, zero_mul, zpow_zero, mul_one]
    exact mul_mem (unitV_mem _ _) (unitV_inv_mem _ _)

theorem lamY_zero {n : ℕ} (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  ext v
  unfold LocE.lamY
  rw [mem_sclLat]
  refine Iff.trans (forall_congr' fun l => ?_) mem_stdAt.symm
  have : l.1 < n := l.2
  simp [LocE.scE, this]

theorem mem_lamY_one {n : ℕ} {v : Sp E (n + 1)} : v ∈ LocE.lamY P (qOf P) n 1 (fun i => i + 1) ↔
    LinearMap.funLeft E E (Fin.castAdd 1) v ∈ stdAt E n P ∧ IntAt P ((qOf P : E)⁻¹ * v (Fin.last n)) := by
  unfold LocE.lamY
  rw [mem_sclLat, Fin.forall_fin_succ', mem_stdAt]
  refine and_congr (forall_congr' fun l => ?_) ?_
  · simp [LocE.scE, LinearMap.funLeft_apply]
    rfl
  · simp [LocE.scE]

omit [NumberField E] [StarRing E] in
theorem joinCol_apply {n' n : ℕ} (x₀ : HomE E n' n) (y : Sp E n) (v : Sp E (n' + 1)) :
    joinCol (c' := 1) (c := 0) x₀ y v = x₀ (LinearMap.funLeft E E (Fin.castAdd 1) v) + v (Fin.last n') • y := by
  funext l
  have : l.1 < n := l.2
  simp [joinCol, Loc.inX, atNL, this]
  exact Or.inl rfl

omit [NumberField E] [StarRing E] in
theorem funLeft_inX {n c : ℕ} (w : Sp E n) : LinearMap.funLeft E E (Fin.castAdd c) (Loc.inX E n c w) = w := by
  funext l
  simp [Loc.inX, LinearMap.funLeft_apply]

omit [NumberField E] [StarRing E] in
theorem inX_last {n : ℕ} (w : Sp E n) : Loc.inX E n 1 w (Fin.last n) = 0 := by
  simp [Loc.inX]

theorem joinCol_mem {n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0) (x₀ : HomE E n' n) (y : Sp E n) :
    joinCol (c' := c') (c := c) x₀ y ∈
        homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) ↔
      x₀ ∈ homS (stdAt E n' P) (stdAt E n P) ∧ (qOf P : E) • y ∈ stdAt E n P := by
  subst hc' hc
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  rw [lamY_zero]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, ?_⟩
    · have := h (Loc.inX E n' 1 w) (mem_lamY_one.2 ⟨by rwa [funLeft_inX], by rw [inX_last, mul_zero]; exact intAt_zero⟩)
      rw [joinCol_apply, funLeft_inX, inX_last, zero_smul] at this
      exact (add_zero (x₀ w)) ▸ this
    · have e : LinearMap.funLeft E E (Fin.castAdd 1) (Pi.single (Fin.last n') (qOf P : E) : Sp E (n' + 1)) = 0 := by
        funext l
        exact Pi.single_eq_of_ne (Fin.castSucc_ne_last l) _
      have := h (Pi.single (Fin.last n') (qOf P : E)) (mem_lamY_one.2 ⟨by rw [e]; exact zero_mem _, by
        rw [Pi.single_eq_same, inv_mul_cancel₀ hq]; exact intAt_one⟩)
      rwa [joinCol_apply, e, map_zero, zero_add, Pi.single_eq_same] at this
  · rintro ⟨h1, h2⟩ v hv
    obtain ⟨h3, h4⟩ := mem_lamY_one.1 hv
    rw [joinCol_apply]
    refine add_mem (h1 _ h3) ?_
    have := smul_mem_locP h4 h2
    rwa [smul_smul, mul_right_comm, inv_mul_cancel₀ hq, one_mul] at this

omit [NumberField E] [StarRing E] in
theorem joinCol_restr {n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0) (x : HomE E (n' + c') (n + c)) :
    joinCol (restrX x) (colX x) = x := by
  subst hc' hc
  refine LinearMap.ext fun v => ?_
  have e : v = Loc.inX E n' 1 (LinearMap.funLeft E E (Fin.castAdd 1) v) + v (Fin.last n') • Loc.eN E (n' + 1) n' := by
    funext l
    refine Fin.lastCases ?_ (fun j => ?_) l
    · simp [Loc.inX, Loc.eN]
    · simp [Loc.inX, Loc.eN, j.2.ne, LinearMap.funLeft_apply]
      rfl
  rw [joinCol_apply]
  conv_rhs => rw [e, map_add, map_smul]
  rfl

omit [NumberField E] [StarRing E] in
theorem joinCol_add {n' c' n c : ℕ} (x₀ z₀ : HomE E n' n) (y l : Sp E n) (s : E) :
    joinCol (c' := c') (c := c) (x₀ + s • z₀) (y + s • l) = joinCol x₀ y + s • joinCol z₀ l := by
  refine LinearMap.ext fun v => ?_
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    map_add, map_smul, smul_add]
  rw [smul_comm s]
  abel

theorem finite_classes (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    {a : Sp E n ⧸ stdAt E n P | ∃ y, (qOf P : E) • y ∈ stdAt E n P ∧ Submodule.Quotient.mk y = a}.Finite := by
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hq' : ((qOf P : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hq (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((qOf P : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hq')
  refine (Set.finite_range fun t : Fin n → 𝓞 E ⧸ Ideal.span {((qOf P : ℕ) : 𝓞 E)} =>
    (Submodule.Quotient.mk (fun i => algebraMap (𝓞 E) E (t i).out / (qOf P : E)) : Sp E n ⧸ stdAt E n P)).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  choose r hr using fun i => exists_int_congr (mem_stdAt.1 hy i)
  refine ⟨fun i => Ideal.Quotient.mk _ (r i), (Submodule.Quotient.eq _).2 (mem_stdAt.2 fun i => ?_)⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1
    (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {((qOf P : ℕ) : 𝓞 E)}) (r i))))
  have hc' := congrArg (algebraMap (𝓞 E) E) hc
  simp only [map_mul, map_natCast, map_sub] at hc'
  convert intAt_sub (IntAt.coe P c) (hr i) using 1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination -hc'

theorem exists_split {V : Type} {n : ℕ} (F : V → Sp E n → K) (h1 : ∀ x y, F x y ≠ 0 → (qOf P : E) • y ∈ stdAt E n P)
    (h2 : ∀ x y z, z ∈ stdAt E n P → F x (y + z) = F x y) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → Sp E n) (f : ι → Sp E n → K), (∀ i, ColFn P (f i)) ∧
      ∀ x y, F x y = ∑ i, F x (a i) * f i y := by
  classical
  have := (finite_classes P n).fintype
  let T := {a : Sp E n ⧸ stdAt E n P | ∃ y, (qOf P : E) • y ∈ stdAt E n P ∧ Submodule.Quotient.mk y = a}
  choose a ha hmk using fun i : T => i.2
  refine ⟨T, this, a, fun i y => if y - a i ∈ stdAt E n P then 1 else 0, fun i => colFn_indicator P _ (ha i), fun x y => ?_⟩
  by_cases hy : (qOf P : E) • y ∈ stdAt E n P
  · have key : ∀ i : T, y - a i ∈ stdAt E n P ↔ i = ⟨Submodule.Quotient.mk y, y, hy, rfl⟩ := fun i => by
      rw [← Submodule.Quotient.eq, hmk, Subtype.ext_iff, eq_comm]
    rw [Finset.sum_eq_single ⟨Submodule.Quotient.mk y, y, hy, rfl⟩]
    · dsimp only
      rw [if_pos ((key _).2 rfl), mul_one, ← h2 x (a _) _ ((key _).2 rfl), add_sub_cancel]
    · intro i _ hi
      dsimp only
      rw [if_neg (fun h => hi ((key i).1 h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [of_not_not fun h => hy (h1 x y h), Finset.sum_eq_zero]
    intro i _
    exact mul_eq_zero_of_right _ (of_not_not fun h => hy ((colFn_indicator (K := K) P _ (ha i)).1 y h))

theorem inDual_iff {n : ℕ} (ξ : Sp E n →ₗ[E] E) : InDual P ξ ↔ ∀ i, IntAt P (ξ (Pi.single i 1)) := by
  refine ⟨fun h i => h _ (single_mem_stdAt i), fun h y hy => ?_⟩
  have e : y = ∑ i, y i • (Pi.single i 1 : Sp E n) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e, map_sum]
  refine intAt_sum _ fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact (mem_stdAt.1 hy i).mul (h i)

end Data

end GlobalTheory.LastSteps
