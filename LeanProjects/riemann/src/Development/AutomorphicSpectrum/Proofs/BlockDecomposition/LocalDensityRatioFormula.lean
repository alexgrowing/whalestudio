import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide

set_option maxSynthPendingDepth 1

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.Rg.Base1
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RatioBase

variable {F : Type} [Field F] [NumberField F]

section Core

attribute [-instance] HeckeCharacterZeroLocus.SiegelWeilU.measAF

def Ge (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) (s : Fv F v) : Prop :=
  s ≠ 0 ∧ Valued.v s ≤ ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

open Classical in
theorem rv_eq (v : HeightOneSpectrum (𝓞 F)) (e : ℝ) (s : Fv F v) :
    rv v e s = ∑' i : ℕ, if Ge v i s then e ^ i else 0 := by
  unfold rv Ge
  refine tsum_congr fun i => ?_
  by_cases h : s ≠ 0 ∧ Valued.v s ≤ ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem ge_iff (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) (s : Fv F v) :
    Ge v i s ↔ s ≠ 0 ∧ Valued.v s ≤ WithZero.exp (-(i : ℤ)) := Iff.rfl

theorem ge_mono {v : HeightOneSpectrum (𝓞 F)} {i j : ℕ} {s : Fv F v} (hij : i ≤ j) (h : Ge v j s) : Ge v i s := by
  rw [ge_iff] at h ⊢
  refine ⟨h.1, h.2.trans ?_⟩
  rw [WithZero.exp_le_exp]
  omega

theorem ge_congr {v : HeightOneSpectrum (𝓞 F)} {i : ℕ} {s s' : Fv F v} (h : Valued.v s = Valued.v s') :
    Ge v i s ↔ Ge v i s' := by
  rw [ge_iff, ge_iff, h]
  have : s ≠ 0 ↔ s' ≠ 0 := by
    rw [← (Valued.v : Valuation (Fv F v) _).ne_zero_iff, ← (Valued.v : Valuation (Fv F v) _).ne_zero_iff (x := s'), h]
  rw [this]

theorem exists_not_ge {v : HeightOneSpectrum (𝓞 F)} (s : Fv F v) : ∃ N : ℕ, ∀ i, N < i → ¬ Ge v i s := by
  by_cases hs : s = 0
  · exact ⟨0, fun i _ h => h.1 hs⟩
  have h0 : Valued.v s ≠ 0 := (Valued.v : Valuation (Fv F v) _).ne_zero_iff.2 hs
  refine ⟨(-(Valued.v s).log).toNat, fun i hi h => ?_⟩
  have h2 := ((ge_iff v i s).1 h).2
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at h2
  have := Int.self_le_toNat (-(Valued.v s).log)
  omega

open Classical in
theorem summable_ge (v : HeightOneSpectrum (𝓞 F)) (e : ℝ) (s : Fv F v) :
    Summable fun i : ℕ => if Ge v i s then e ^ i else 0 := by
  obtain ⟨N, hN⟩ := exists_not_ge s
  refine summable_of_finite_support ((Set.finite_Iic N).subset fun i hi => ?_)
  by_contra h
  exact hi (if_neg (hN i (not_le.1 h)))

open Classical in

theorem rv_form {v : HeightOneSpectrum (𝓞 F)} (s : Fv F v) :
    (¬ Ge v 0 s ∧ ∀ e, rv v e s = 0) ∨
      ∃ n : ℕ, (∀ i, Ge v i s ↔ i ≤ n) ∧ ∀ e, rv v e s = ∑ i ∈ Finset.range (n + 1), e ^ i := by
  by_cases h0 : Ge v 0 s
  · right
    have hex : ∃ i, ¬ Ge v i s := by
      obtain ⟨N, hN⟩ := exists_not_ge s
      exact ⟨N + 1, hN _ (Nat.lt_succ_self N)⟩
    have hm : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · exact absurd (h ▸ Nat.find_spec hex) (not_not.2 h0)
      · exact h
    have key : ∀ i, Ge v i s ↔ i ≤ Nat.find hex - 1 := by
      intro i
      constructor
      · intro h
        by_contra hc
        exact Nat.find_spec hex (ge_mono (by omega) h)
      · intro h
        exact not_not.1 (Nat.find_min hex (by omega))
    refine ⟨Nat.find hex - 1, key, fun e => ?_⟩
    rw [rv_eq, tsum_eq_sum (s := Finset.range (Nat.find hex - 1 + 1))]
    · refine Finset.sum_congr rfl fun i hi => if_pos ((key i).2 (by simpa [Nat.lt_succ_iff] using hi))
    · intro i hi
      refine if_neg fun h => hi ?_
      simpa [Nat.lt_succ_iff] using (key i).1 h
  · left
    refine ⟨h0, fun e => ?_⟩
    rw [rv_eq]
    have : ∀ i, ¬ Ge v i s := fun i h => h0 (ge_mono (Nat.zero_le i) h)
    simp [this]

theorem sum_neg_one (m : ℕ) : (∑ i ∈ Finset.range m, (-1 : ℝ) ^ i = 0 ∧ Even m) ∨
    (∑ i ∈ Finset.range m, (-1 : ℝ) ^ i = 1 ∧ Odd m) := by
  induction m with
  | zero => left; simp
  | succ m ih =>
    rcases ih with ⟨h, hm⟩ | ⟨h, hm⟩
    · right
      rw [Finset.sum_range_succ, h, hm.neg_one_pow]
      exact ⟨by norm_num, hm.add_one⟩
    · left
      rw [Finset.sum_range_succ, h, hm.neg_one_pow]
      exact ⟨by norm_num, hm.add_one⟩

theorem sum_bounds {e : ℝ} (he : e = 0 ∨ e = 1 ∨ e = -1) (n : ℕ) :
    0 ≤ ∑ i ∈ Finset.range (n + 1), e ^ i ∧ ∑ i ∈ Finset.range (n + 1), e ^ i ≤ ∑ i ∈ Finset.range (n + 1), (1 : ℝ) ^ i := by
  have hn : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  rcases he with rfl | rfl | rfl
  · have h1 : ∑ i ∈ Finset.range (n + 1), (0 : ℝ) ^ i = 1 := by
      rw [Finset.sum_range_succ']
      simp
    rw [h1]
    simpa using hn
  · simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ⟨by positivity, le_refl _⟩
  · have h1 : ∑ i ∈ Finset.range (n + 1), (1 : ℝ) ^ i = n + 1 := by simp
    rw [h1]
    rcases sum_neg_one (n + 1) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact ⟨le_refl _, by linarith⟩
    · exact ⟨by norm_num, hn⟩

theorem rv_nonneg {v : HeightOneSpectrum (𝓞 F)} {e : ℝ} (he : e = 0 ∨ e = 1 ∨ e = -1) (s : Fv F v) : 0 ≤ rv v e s := by
  rcases rv_form s with ⟨-, h⟩ | ⟨n, -, h⟩
  · rw [h]
  · rw [h]; exact (sum_bounds he n).1

theorem rv_le {v : HeightOneSpectrum (𝓞 F)} {e : ℝ} (he : e = 0 ∨ e = 1 ∨ e = -1) (s : Fv F v) : rv v e s ≤ rv v 1 s := by
  rcases rv_form s with ⟨-, h⟩ | ⟨n, -, h⟩
  · rw [h, h]
  · rw [h, h]; exact (sum_bounds he n).2

theorem rv_unit {v : HeightOneSpectrum (𝓞 F)} (e : ℝ) {s : Fv F v} (hs : Valued.v s = 1) : rv v e s = 1 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have h0 : Ge v 0 s := by
    rw [ge_iff]
    refine ⟨hs0, ?_⟩
    rw [hs]
    simp
  have h1 : ¬ Ge v 1 s := by
    intro h
    have := ((ge_iff v 1 s).1 h).2
    rw [hs, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    norm_num at this
  rcases rv_form s with ⟨h, -⟩ | ⟨n, hn, h⟩
  · exact absurd h0 h
  · have : n = 0 := by
      by_contra hc
      exact h1 ((hn 1).2 (by omega))
    subst this
    rw [h]
    simp

theorem rv_congr {v : HeightOneSpectrum (𝓞 F)} (e : ℝ) {s s' : Fv F v} (h : Valued.v s = Valued.v s') :
    rv v e s = rv v e s' := by
  classical
  rw [rv_eq, rv_eq]
  refine tsum_congr fun i => ?_
  simp only [ge_congr (i := i) h]

open Classical in
theorem rv_zero (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) : rv v 0 s = if Ge v 0 s then 1 else 0 := by
  rcases rv_form s with ⟨h, h'⟩ | ⟨n, hn, h'⟩
  · rw [h', if_neg h]
  · rw [h', if_pos ((hn 0).2 (Nat.zero_le n)), Finset.sum_range_succ']
    simp

theorem ge_shift {v : HeightOneSpectrum (𝓞 F)} {u : (Fv F v)ˣ} (hu : Valued.v (u : Fv F v) = WithZero.exp (1 : ℤ))
    (i : ℕ) (s : Fv F v) : Ge v (i + 1) s ↔ Ge v i ((u : Fv F v) * s) := by
  rw [ge_iff, ge_iff, map_mul, hu]
  have h1 : (u : Fv F v) * s ≠ 0 ↔ s ≠ 0 := by simp
  rw [h1]
  have h2 : WithZero.exp (-(i : ℤ)) = WithZero.exp (1 : ℤ) * WithZero.exp (-((i + 1 : ℕ) : ℤ)) := by
    rw [← WithZero.exp_add]
    congr 1
    push_cast
    ring
  rw [h2, mul_le_mul_iff_right₀ (WithZero.exp_pos)]

open Classical in
theorem rv_rec {v : HeightOneSpectrum (𝓞 F)} {u : (Fv F v)ˣ} (hu : Valued.v (u : Fv F v) = WithZero.exp (1 : ℤ))
    (e : ℝ) (s : Fv F v) : rv v e s = rv v 0 s + e * rv v e ((u : Fv F v) * s) := by
  rw [rv_eq v e s, (summable_ge v e s).tsum_eq_zero_add, rv_zero, rv_eq v e, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun i => ?_
  by_cases h : Ge v (i + 1) s
  · rw [if_pos h, if_pos ((ge_shift hu i s).1 h)]
    ring
  · rw [if_neg h, if_neg (fun h' => h ((ge_shift hu i s).2 h'))]
    ring

theorem ge_pow {v : HeightOneSpectrum (𝓞 F)} {u : (Fv F v)ˣ} (hu : Valued.v (u : Fv F v) = WithZero.exp (1 : ℤ))
    (k : ℕ) (s : Fv F v) : Ge v k s ↔ Ge v 0 ((((u ^ k : (Fv F v)ˣ)) : Fv F v) * s) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [ge_shift hu, ih, pow_succ, Units.val_mul, mul_assoc]

open Classical in

theorem rv_one_series {v : HeightOneSpectrum (𝓞 F)} {u : (Fv F v)ˣ} (hu : Valued.v (u : Fv F v) = WithZero.exp (1 : ℤ))
    (s : Fv F v) : rv v 1 s = ∑' k : ℕ, rv v 0 ((((u ^ k : (Fv F v)ˣ)) : Fv F v) * s) := by
  rw [rv_eq]
  refine tsum_congr fun k => ?_
  rw [rv_zero]
  by_cases h : Ge v k s
  · rw [if_pos h, if_pos ((ge_pow hu k s).1 h), one_pow]
  · rw [if_neg h, if_neg fun h' => h ((ge_pow hu k s).2 h')]

open Classical in
theorem summable_rv_shift {v : HeightOneSpectrum (𝓞 F)} {u : (Fv F v)ˣ} (hu : Valued.v (u : Fv F v) = WithZero.exp (1 : ℤ))
    (s : Fv F v) : Summable fun k : ℕ => rv v 0 ((((u ^ k : (Fv F v)ˣ)) : Fv F v) * s) := by
  refine (summable_ge v 1 s).congr fun k => ?_
  rw [rv_zero]
  by_cases h : Ge v k s
  · rw [if_pos h, if_pos ((ge_pow hu k s).1 h), one_pow]
  · rw [if_neg h, if_neg fun h' => h ((ge_pow hu k s).2 h')]

theorem exists_inv_uniformizer (v : HeightOneSpectrum (𝓞 F)) :
    ∃ u : (Fv F v)ˣ, Valued.v (u : Fv F v) = WithZero.exp (1 : ℤ) ∧ Valued.v ((u⁻¹ : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hr : Valued.v (algebraMap F (Fv F v) π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π).trans hπ
  have h0 : algebraMap F (Fv F v) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hr
    exact WithZero.exp_ne_zero hr.symm
  refine ⟨(Units.mk0 _ h0)⁻¹, ?_, ?_⟩
  · rw [Units.val_inv_eq_inv_val, map_inv₀, Units.val_mk0, hr, ← WithZero.exp_neg]
    simp
  · simpa using hr

def Good (w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) : Prop :=
  ∀ v, (∀ s s', Valued.v s = Valued.v s' → w v s = w v s') ∧ (∀ s, Valued.v s = 1 → w v s = 1) ∧ (∀ s, 0 ≤ w v s) ∧
    ∀ s, w v s ≤ rv v 1 s

theorem good_rv {e : HeightOneSpectrum (𝓞 F) → ℝ} (he : ∀ v, e v = 0 ∨ e v = 1 ∨ e v = -1) :
    Good fun v => rv v (e v) :=
  fun v => ⟨fun _ _ h => rv_congr _ h, fun _ h => rv_unit _ h, fun _ => rv_nonneg (he v) _, fun _ => rv_le (he v) _⟩

theorem val_eq_one_of_mul {v : HeightOneSpectrum (𝓞 F)} {a b : Fv F v} (hab : a * b = 1)
    (ha : a ∈ v.adicCompletionIntegers F) (hb : b ∈ v.adicCompletionIntegers F) : Valued.v a = 1 := by
  have ha' : Valued.v a ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 ha
  have hb' : Valued.v b ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 hb
  have h1 : Valued.v a * Valued.v b = 1 := by rw [← map_mul, hab, map_one]
  refine le_antisymm ha' ?_
  calc (1 : _) = Valued.v a * Valued.v b := h1.symm
    _ ≤ Valued.v a * 1 := mul_le_mul_right hb' _
    _ = Valued.v a := mul_one _

theorem eventually_val_eq_one (a : (AF F)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v ((a : AF F).2 v) = 1 := by
  filter_upwards [(a : AF F).2.2, ((a⁻¹ : (AF F)ˣ) : AF F).2.2] with v h1 h2
  exact val_eq_one_of_mul (IdeleGroup.finite_mul_inv a v) h1 h2

theorem continuous_of_inv {X : Type*} [TopologicalSpace X] (f : (AF F)ˣ → X)
    (h : ∀ a u, u ∈ IdeleGroup.standardOpenSubgroup F → f (a * u) = f a) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hU : (fun y => x⁻¹ * y) ⁻¹' (IdeleGroup.standardOpenSubgroup F : Set (IdeleGroup F)) ∈ 𝓝 x :=
    ((IdeleGroup.isOpen_standardOpenSubgroup F).preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp [(IdeleGroup.standardOpenSubgroup F).one_mem])
  refine (continuousAt_const (y := f x)).congr ?_
  filter_upwards [hU] with y hy
  rw [← mul_inv_cancel_left x y, h x _ hy]

theorem val_mul_std (a u : (AF F)ˣ) (hu : u ∈ IdeleGroup.standardOpenSubgroup F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (((a * u : (AF F)ˣ) : AF F).2 v) = Valued.v ((a : AF F).2 v) := by
  have h := (IdeleGroup.mem_standardOpenSubgroup F).1 hu v
  have h1 := val_eq_one_of_mul (IdeleGroup.finite_mul_inv u v) h.1 h.2
  rw [Units.val_mul, IdeleGroup.adele_snd_mul_apply, map_mul, h1, mul_one]

theorem continuous_pure (S : Finset (HeightOneSpectrum (𝓞 F))) {G : Ainf F → ℝ}
    {g w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ} (hG : Continuous G) (hg : ∀ v ∈ S, Continuous (g v)) (hw : Good w) :
    Continuous (PositivityTheory.Rg.Base1.pure S G g w) := by
  have c0 : Continuous fun a : (AF F)ˣ => (a : AF F) := Units.continuous_val
  have c1 : Continuous fun a : (AF F)ˣ => (a : AF F).1 := continuous_fst.comp c0
  have c2 : Continuous fun a : (AF F)ˣ => (a : AF F).2 := continuous_snd.comp c0
  unfold PositivityTheory.Rg.Base1.pure
  refine ENNReal.continuous_ofReal.comp ?_
  refine ((hG.comp c1).mul ?_).mul ?_
  · refine continuous_finset_prod _ fun v hv => (hg v hv).comp ?_
    exact (RestrictedProduct.continuous_eval v).comp c2
  · refine continuous_of_inv _ fun a u hu => finprod_congr fun x => ?_
    exact (hw x.1).1 _ _ (val_mul_std a u hu x.1)

abbrev Off (S : Finset (HeightOneSpectrum (𝓞 F))) := {v : HeightOneSpectrum (𝓞 F) // v ∉ S}

def rest (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ)
    (x₀ : Off S) (a : (AF F)ˣ) : ℝ :=
  G (a : AF F).1 * (∏ v ∈ S, g v ((a : AF F).2 v)) * ∏ᶠ (x : Off S) (_ : x ≠ x₀), w x.1 ((a : AF F).2 x.1)

theorem finite_mulSupport_off {w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ} (hw : Good w) (a : (AF F)ˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (Function.mulSupport fun x : Off S => w x.1 ((a : AF F).2 x.1)).Finite := by
  have h := eventually_cofinite.1 (eventually_val_eq_one a)
  refine (h.preimage (Subtype.val_injective.injOn)).subset fun x hx => ?_
  intro h1
  exact hx ((hw x.1).2.1 _ h1)

theorem pure_eq {S : Finset (HeightOneSpectrum (𝓞 F))} {G : Ainf F → ℝ} {g w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ}
    (hw : Good w) (x₀ : Off S) (a : (AF F)ˣ) :
    PositivityTheory.Rg.Base1.pure S G g w a = ENNReal.ofReal (rest S G g w x₀ a * w x₀.1 ((a : AF F).2 x₀.1)) := by
  unfold PositivityTheory.Rg.Base1.pure rest
  rw [← mul_finprod_cond_ne x₀ (finite_mulSupport_off hw a S)]
  congr 1
  ring

theorem rest_nonneg {S : Finset (HeightOneSpectrum (𝓞 F))} {G : Ainf F → ℝ} {g w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ}
    (hG : ∀ y, 0 ≤ G y) (hg : ∀ v y, 0 ≤ g v y) (hw : Good w) (x₀ : Off S) (a : (AF F)ˣ) : 0 ≤ rest S G g w x₀ a :=
  mul_nonneg (mul_nonneg (hG _) (Finset.prod_nonneg fun v _ => hg v _))
    (finprod_nonneg fun x => finprod_nonneg fun _ => (hw x.1).2.2.1 _)

theorem rest_congr {S : Finset (HeightOneSpectrum (𝓞 F))} {G : Ainf F → ℝ} {g w w' : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ}
    (x₀ : Off S) (h : ∀ x : Off S, x ≠ x₀ → w x.1 = w' x.1) (a : (AF F)ˣ) : rest S G g w x₀ a = rest S G g w' x₀ a := by
  unfold rest
  congr 1
  refine finprod_congr fun x => finprod_congr fun hx => ?_
  rw [h x hx]

abbrev emb (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ) : (AF F)ˣ := IdeleGroup.finiteEmbedding v u

theorem emb_fst (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ) (a : (AF F)ˣ) :
    ((emb v u * a : (AF F)ˣ) : AF F).1 = (a : AF F).1 :=
  one_mul (a : AF F).1

theorem emb_snd_self (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ) (a : (AF F)ˣ) :
    ((emb v u * a : (AF F)ˣ) : AF F).2 v = (u : Fv F v) * (a : AF F).2 v := by
  rw [Units.val_mul, IdeleGroup.adele_snd_mul_apply, IdeleGroup.coe_finiteEmbedding]
  simp

theorem emb_snd_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (u : (Fv F v)ˣ) (a : (AF F)ˣ) :
    ((emb v u * a : (AF F)ˣ) : AF F).2 w = (a : AF F).2 w := by
  rw [Units.val_mul, IdeleGroup.adele_snd_mul_apply, IdeleGroup.coe_finiteEmbedding]
  simp [IdeleGroup.finiteAdeleSingle_apply_of_ne h]

theorem rest_emb {S : Finset (HeightOneSpectrum (𝓞 F))} {G : Ainf F → ℝ} {g w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ}
    (x₀ : Off S) (u : (Fv F x₀.1)ˣ) (a : (AF F)ˣ) : rest S G g w x₀ (emb x₀.1 u * a) = rest S G g w x₀ a := by
  unfold rest
  have h1 : ∏ v ∈ S, g v (((emb x₀.1 u * a : (AF F)ˣ) : AF F).2 v) = ∏ v ∈ S, g v ((a : AF F).2 v) := by
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [emb_snd_ne (fun h => x₀.2 (by rw [← h]; exact hv))]
  have h2 : ∏ᶠ (x : Off S) (_ : x ≠ x₀), w x.1 (((emb x₀.1 u * a : (AF F)ˣ) : AF F).2 x.1) =
      ∏ᶠ (x : Off S) (_ : x ≠ x₀), w x.1 ((a : AF F).2 x.1) := by
    refine finprod_congr fun x => finprod_congr fun hx => ?_
    rw [emb_snd_ne (fun h => hx (Subtype.ext h))]
  rw [emb_fst, h1, h2]

theorem md_mul (a b : (AF F)ˣ) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_pos (a : (AF F)ˣ) : 0 < md a := (IdeleGroup.ideleModule F a).2

theorem md_one : md (1 : (AF F)ˣ) = 1 := by
  simp [md, map_one]

theorem continuous_md : Continuous (md (F := F)) :=
  continuous_subtype_val.comp IdeleGroup.continuous_ideleModule

theorem md_emb {v : HeightOneSpectrum (𝓞 F)} {u : (Fv F v)ˣ}
    (hu : Valued.v ((u⁻¹ : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ)) : md (emb v u) = (Ideal.absNorm v.asIdeal : ℝ) := by
  have h1 : md (emb v u⁻¹) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := ideleModule_finiteEmbedding_of_uniformizer hu
  have h2 : md (emb v u) * md (emb v u⁻¹) = 1 := by
    rw [← md_mul, emb, emb, ← map_mul, mul_inv_cancel, map_one, md_one]
  have h3 : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast (one_lt_absNorm_asIdeal v).trans' Nat.zero_lt_one
  rw [h1] at h2
  field_simp at h2
  exact h2

theorem zi_shift (f : (AF F)ˣ → ℝ≥0∞) (c : (AF F)ˣ) (s : ℝ) :
    zi (fun a => f (c * a)) s = ENNReal.ofReal (md c ^ (-s)) * zi f s := by
  have h : ∀ a, f (c * a) * ENNReal.ofReal (md a ^ s) =
      ENNReal.ofReal (md c ^ (-s)) * (f (c * a) * ENNReal.ofReal (md (c * a) ^ s)) := by
    intro a
    have h1 : md (c * a) ^ s = md c ^ s * md a ^ s := by
      rw [md_mul, Real.mul_rpow (md_pos c).le (md_pos a).le]
    have h2 : ENNReal.ofReal (md c ^ (-s)) * ENNReal.ofReal (md c ^ s) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (md_pos c).le _), ← Real.rpow_add (md_pos c)]
      simp
    rw [h1, ENNReal.ofReal_mul (Real.rpow_nonneg (md_pos c).le _)]
    calc f (c * a) * ENNReal.ofReal (md a ^ s)
        = (ENNReal.ofReal (md c ^ (-s)) * ENNReal.ofReal (md c ^ s)) * (f (c * a) * ENNReal.ofReal (md a ^ s)) := by
          rw [h2, one_mul]
      _ = _ := by ring
  unfold zi
  simp_rw [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact lintegral_mul_left_eq_self (fun a => f a * ENNReal.ofReal (md a ^ s)) c

section Step

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {G : Ainf F → ℝ} {g w W : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ}

theorem measurable_md_rpow (s : ℝ) : Measurable fun a : (AF F)ˣ => ENNReal.ofReal (md a ^ s) :=
  ENNReal.measurable_ofReal.comp (continuous_md.measurable.pow_const s)

theorem md_pow (a : (AF F)ˣ) (k : ℕ) : md (a ^ k) = md a ^ k := by
  induction k with
  | zero => simp [md_one]
  | succ k ih => rw [pow_succ, md_mul, ih, pow_succ]

theorem step_neg (hG : Continuous G) (hG0 : ∀ y, 0 ≤ G y) (hg : ∀ v ∈ S, Continuous (g v)) (hg0 : ∀ v y, 0 ≤ g v y)
    (hw : Good w) (hW : Good W) (x₀ : Off S) (h0 : w x₀.1 = rv x₀.1 0) (h1 : W x₀.1 = rv x₀.1 (-1))
    (hne : ∀ x : Off S, x ≠ x₀ → w x.1 = W x.1) (s : ℝ) :
    zi (PositivityTheory.Rg.Base1.pure S G g w) s =
      ENNReal.ofReal (1 + (Ideal.absNorm x₀.1.asIdeal : ℝ) ^ (-s)) * zi (PositivityTheory.Rg.Base1.pure S G g W) s := by
  obtain ⟨u, hu, hu'⟩ := exists_inv_uniformizer x₀.1
  have hq : (0 : ℝ) ≤ (Ideal.absNorm x₀.1.asIdeal : ℝ) ^ (-s) := by positivity
  have key : ∀ a, PositivityTheory.Rg.Base1.pure S G g w a =
      PositivityTheory.Rg.Base1.pure S G g W a + PositivityTheory.Rg.Base1.pure S G g W (emb x₀.1 u * a) := by
    intro a
    have hR := rest_nonneg hG0 hg0 hW x₀ a
    rw [pure_eq hw x₀ a, pure_eq hW x₀ a, pure_eq hW x₀ (emb x₀.1 u * a), rest_emb, emb_snd_self, rest_congr x₀ hne, h0, h1,
      ← ENNReal.ofReal_add (mul_nonneg hR (rv_nonneg (by simp) _)) (mul_nonneg hR (rv_nonneg (by simp) _)), ← mul_add]
    congr 2
    have := rv_rec hu (-1) ((a : AF F).2 x₀.1)
    linarith
  have hz : zi (PositivityTheory.Rg.Base1.pure S G g w) s =
      zi (PositivityTheory.Rg.Base1.pure S G g W) s + zi (fun a => PositivityTheory.Rg.Base1.pure S G g W (emb x₀.1 u * a)) s := by
    unfold zi
    have hm : Measurable fun a => PositivityTheory.Rg.Base1.pure S G g W a * ENNReal.ofReal (md a ^ s) :=
      ((continuous_pure S hG hg hW).measurable).mul (measurable_md_rpow s)
    refine Eq.trans ?_ (lintegral_add_left hm _)
    refine lintegral_congr fun a => ?_
    rw [key a, add_mul]
  rw [hz, zi_shift, md_emb hu', ENNReal.ofReal_add zero_le_one hq, ENNReal.ofReal_one, add_mul, one_mul]

theorem step_pos (hG : Continuous G) (hG0 : ∀ y, 0 ≤ G y) (hg : ∀ v ∈ S, Continuous (g v)) (hg0 : ∀ v y, 0 ≤ g v y)
    (hw : Good w) (hW : Good W) (x₀ : Off S) (h0 : w x₀.1 = rv x₀.1 0) (h1 : W x₀.1 = rv x₀.1 1)
    (hne : ∀ x : Off S, x ≠ x₀ → w x.1 = W x.1) (s : ℝ) :
    zi (PositivityTheory.Rg.Base1.pure S G g W) s =
      (∑' k : ℕ, ENNReal.ofReal ((Ideal.absNorm x₀.1.asIdeal : ℝ) ^ (-s)) ^ k) * zi (PositivityTheory.Rg.Base1.pure S G g w) s := by
  obtain ⟨u, hu, hu'⟩ := exists_inv_uniformizer x₀.1
  have hcw := continuous_pure S hG hg hw
  have key : ∀ a, PositivityTheory.Rg.Base1.pure S G g W a = ∑' k : ℕ, PositivityTheory.Rg.Base1.pure S G g w (emb x₀.1 (u ^ k) * a) := by
    intro a
    have hR := rest_nonneg hG0 hg0 hw x₀ a
    have hk : ∀ k : ℕ, PositivityTheory.Rg.Base1.pure S G g w (emb x₀.1 (u ^ k) * a) =
        ENNReal.ofReal (rest S G g w x₀ a * rv x₀.1 0 ((((u ^ k : (Fv F x₀.1)ˣ)) : Fv F x₀.1) * (a : AF F).2 x₀.1)) := by
      intro k
      rw [pure_eq hw x₀, rest_emb, emb_snd_self, h0]
    simp_rw [hk]
    rw [pure_eq hW x₀, ← rest_congr x₀ hne, h1, rv_one_series hu, ← tsum_mul_left,
      ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hR (rv_nonneg (by simp) _)) ((summable_rv_shift hu _).mul_left _)]
  have hz : zi (PositivityTheory.Rg.Base1.pure S G g W) s = ∑' k : ℕ, zi (fun a => PositivityTheory.Rg.Base1.pure S G g w (emb x₀.1 (u ^ k) * a)) s := by
    unfold zi
    have hm : ∀ k : ℕ, AEMeasurable (fun a => PositivityTheory.Rg.Base1.pure S G g w (emb x₀.1 (u ^ k) * a) * ENNReal.ofReal (md a ^ s))
        (ideleMeasure F) := fun k =>
      (Measurable.mul (hcw.comp (continuous_const.mul continuous_id)).measurable (measurable_md_rpow s)).aemeasurable
    refine Eq.trans ?_ (lintegral_tsum hm)
    refine lintegral_congr fun a => ?_
    rw [key a, ENNReal.tsum_mul_right]
  rw [hz]
  simp_rw [zi_shift]
  rw [ENNReal.tsum_mul_right]
  congr 1
  refine tsum_congr fun k => ?_
  have hq0 : (0 : ℝ) ≤ (Ideal.absNorm x₀.1.asIdeal : ℝ) := Nat.cast_nonneg _
  rw [emb, map_pow, md_pow, ← emb, md_emb hu', ← ENNReal.ofReal_pow (Real.rpow_nonneg hq0 _), ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hq0, ← Real.rpow_mul hq0, mul_comm]

theorem one_lt_q (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast one_lt_absNorm_asIdeal v

theorem q_lt_one (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 0 < s) : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (one_lt_q v) (by linarith)

theorem step (hG : Continuous G) (hG0 : ∀ y, 0 ≤ G y) (hg : ∀ v ∈ S, Continuous (g v)) (hg0 : ∀ v y, 0 ≤ g v y)
    (hw : Good w) (hW : Good W) (x₀ : Off S) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (h0 : w x₀.1 = rv x₀.1 0) (h1 : W x₀.1 = rv x₀.1 ε)
    (hne : ∀ x : Off S, x ≠ x₀ → w x.1 = W x.1) {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (1 - ε * (Ideal.absNorm x₀.1.asIdeal : ℝ) ^ (-s)) * zi (PositivityTheory.Rg.Base1.pure S G g W) s =
      zi (PositivityTheory.Rg.Base1.pure S G g w) s := by
  rcases hε with rfl | rfl
  · have hx := q_lt_one x₀.1 hs
    have hq : (0 : ℝ) ≤ (Ideal.absNorm x₀.1.asIdeal : ℝ) ^ (-s) := by positivity
    have hr : ENNReal.ofReal ((Ideal.absNorm x₀.1.asIdeal : ℝ) ^ (-s)) < 1 := ENNReal.ofReal_lt_one.2 hx
    rw [step_pos hG hG0 hg hg0 hw hW x₀ h0 h1 hne s, ENNReal.tsum_geometric, one_mul, ENNReal.ofReal_sub 1 hq,
      ENNReal.ofReal_one, ← mul_assoc, ENNReal.mul_inv_cancel (tsub_pos_of_lt hr).ne' (by simp), one_mul]
  · rw [step_neg hG hG0 hg hg0 hw hW x₀ h0 h1 hne s]
    congr 2
    ring

end Step

section Limit

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {G : Ainf F → ℝ} {g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ}
  {e : HeightOneSpectrum (𝓞 F) → ℝ}

open Classical in

def wT (e : HeightOneSpectrum (𝓞 F) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (T : Finset (Off S))
    (v : HeightOneSpectrum (𝓞 F)) : Fv F v → ℝ :=
  if ∃ hv : v ∉ S, (⟨v, hv⟩ : Off S) ∈ T then rv v (e v) else rv v 0

theorem wT_mem {T : Finset (Off S)} {x : Off S} (h : x ∈ T) : wT e S T x.1 = rv x.1 (e x.1) :=
  if_pos ⟨x.2, h⟩

theorem wT_not {T : Finset (Off S)} {x : Off S} (h : x ∉ T) : wT e S T x.1 = rv x.1 0 :=
  if_neg fun ⟨_, h'⟩ => h h'

theorem wT_empty (v : HeightOneSpectrum (𝓞 F)) : wT e S ∅ v = rv v 0 :=
  if_neg fun ⟨_, h'⟩ => by simp at h'

theorem good_wT (he : ∀ v, e v = 1 ∨ e v = -1) (T : Finset (Off S)) : Good (wT e S T) := by
  intro v
  unfold wT
  split_ifs
  · exact good_rv (e := e) (fun v => Or.inr (he v)) v
  · exact good_rv (e := fun _ => 0) (fun _ => Or.inl rfl) v

theorem factor_nonneg (v : HeightOneSpectrum (𝓞 F)) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {s : ℝ} (hs : 0 < s) :
    0 ≤ 1 - ε * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := by
  have hx := q_lt_one v hs
  have hq : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := by positivity
  rcases hε with rfl | rfl <;> linarith

theorem zi_finite (hG : Continuous G) (hG0 : ∀ y, 0 ≤ G y) (hg : ∀ v ∈ S, Continuous (g v)) (hg0 : ∀ v y, 0 ≤ g v y)
    (he : ∀ v, e v = 1 ∨ e v = -1) {s : ℝ} (hs : 0 < s) (T : Finset (Off S)) :
    ENNReal.ofReal (∏ x ∈ T, (1 - e x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s))) *
        zi (PositivityTheory.Rg.Base1.pure S G g (wT e S T)) s = zi (PositivityTheory.Rg.Base1.pure S G g (wT e S ∅)) s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    have hst := step (S := S) (G := G) (g := g) (w := wT e S T) (W := wT e S (insert x T)) hG hG0 hg hg0
      (good_wT he T) (good_wT he _) x (he x.1) (wT_not hx) (wT_mem (Finset.mem_insert_self x T))
      (fun y hy => by
        by_cases hyT : y ∈ T
        · rw [wT_mem hyT, wT_mem (Finset.mem_insert_of_mem hyT)]
        · rw [wT_not hyT, wT_not (fun h => hyT ((Finset.mem_insert.1 h).resolve_left hy))]) hs
    rw [Finset.prod_insert hx, ENNReal.ofReal_mul (factor_nonneg x.1 (he x.1) hs), mul_comm (ENNReal.ofReal _),
      mul_assoc, hst, ih]

theorem pure_congr {w w' : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ} (a : (AF F)ˣ)
    (h : ∀ x : Off S, w x.1 ((a : AF F).2 x.1) = w' x.1 ((a : AF F).2 x.1)) :
    PositivityTheory.Rg.Base1.pure S G g w a = PositivityTheory.Rg.Base1.pure S G g w' a := by
  unfold PositivityTheory.Rg.Base1.pure
  rw [finprod_congr h]

theorem pure_le {w : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ} (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y)
    (hw : Good w) (a : (AF F)ˣ) :
    PositivityTheory.Rg.Base1.pure S G g w a ≤ PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 1) a := by
  classical
  have h1 : Good fun v : HeightOneSpectrum (𝓞 F) => rv v 1 := good_rv (e := fun _ => 1) fun _ => Or.inr (Or.inl rfl)
  unfold PositivityTheory.Rg.Base1.pure
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hG0 _) (Finset.prod_nonneg fun v _ => hg0 v _)))
  set U := (finite_mulSupport_off hw a S).toFinset ∪ (finite_mulSupport_off h1 a S).toFinset with hU
  rw [finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun x hx => by simp [hU, Set.Finite.mem_toFinset] at hx ⊢; exact Or.inl hx),
    finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun x hx => by simp [hU, Set.Finite.mem_toFinset] at hx ⊢; exact Or.inr hx)]
  exact Finset.prod_le_prod (fun x _ => (hw x.1).2.2.1 _) (fun x _ => (hw x.1).2.2.2 _)

theorem eventually_pure_eq (he : ∀ v, e v = 1 ∨ e v = -1) (a : (AF F)ˣ) :
    ∀ᶠ T : Finset (Off S) in atTop, PositivityTheory.Rg.Base1.pure S G g (wT e S T) a = PositivityTheory.Rg.Base1.pure S G g (fun v => rv v (e v)) a := by
  have h := eventually_cofinite.1 (eventually_val_eq_one a)
  have h' : {x : Off S | ¬ Valued.v ((a : AF F).2 x.1) = 1}.Finite := h.preimage Subtype.val_injective.injOn
  filter_upwards [eventually_ge_atTop h'.toFinset] with T hT
  refine pure_congr a fun x => ?_
  by_cases hx : x ∈ T
  · rw [wT_mem hx]
  · have hv : Valued.v ((a : AF F).2 x.1) = 1 := by
      by_contra hc
      exact hx (hT (h'.mem_toFinset.2 hc))
    rw [wT_not hx, rv_unit _ hv, rv_unit _ hv]

theorem exp_le_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.exp (-(2 * x)) ≤ 1 - x := by
  have h := Real.add_one_le_exp (2 * x)
  have hp : 0 < Real.exp (-(2 * x)) := Real.exp_pos _
  have hm : Real.exp (2 * x) * Real.exp (-(2 * x)) = 1 := by rw [← Real.exp_add]; simp
  have h2 : 1 ≤ (1 - x) * Real.exp (2 * x) := by nlinarith
  calc Real.exp (-(2 * x)) = 1 * Real.exp (-(2 * x)) := (one_mul _).symm
    _ ≤ ((1 - x) * Real.exp (2 * x)) * Real.exp (-(2 * x)) := mul_le_mul_of_nonneg_right h2 hp.le
    _ = 1 - x := by rw [mul_assoc, hm, mul_one]

theorem q_le_half (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 1 < s) : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm_asIdeal v
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

theorem summable_off (S : Finset (HeightOneSpectrum (𝓞 F))) {s : ℝ} (hs : 1 < s) :
    Summable fun x : Off S => (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s) :=
  (summable_absNorm_rpow_neg (L := F) hs).comp_injective Subtype.val_injective

theorem countable_off (S : Finset (HeightOneSpectrum (𝓞 F))) : Countable (Off S) := by
  have h := (summable_off S (s := 2) (by norm_num)).countable_support
  have hu : Function.support (fun x : Off S => (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-(2 : ℝ))) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by linarith [one_lt_q x.1]) _).ne'
  rw [hu] at h
  exact Set.countable_univ_iff.1 h

theorem zi_one_ne_top (hG : Continuous G) (hG0 : ∀ y, 0 ≤ G y) (hg : ∀ v ∈ S, Continuous (g v)) (hg0 : ∀ v y, 0 ≤ g v y)
    {s : ℝ} (hs : 1 < s) (hfin : zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) s ≠ ⊤) :
    zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 1) s ≠ ⊤ := by
  have hs0 : 0 < s := by linarith
  have he1 : ∀ v : HeightOneSpectrum (𝓞 F), ((fun _ => 1 : HeightOneSpectrum (𝓞 F) → ℝ) v) = 1 ∨ ((fun _ => 1 : HeightOneSpectrum (𝓞 F) → ℝ) v) = -1 :=
    fun _ => Or.inl rfl
  have := countable_off S
  set tq := ∑' x : Off S, (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s) with htq
  set p := Real.exp (-(2 * tq)) with hp
  have hp0 : 0 < p := Real.exp_pos _
  have hZ0 : wT (fun _ => 1) S ∅ = fun v : HeightOneSpectrum (𝓞 F) => rv v 0 := funext fun v => wT_empty v
  have hbound : ∀ T : Finset (Off S), zi (PositivityTheory.Rg.Base1.pure S G g (wT (fun _ => 1) S T)) s ≤
      (ENNReal.ofReal p)⁻¹ * zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) s := by
    intro T
    have h := zi_finite (S := S) (G := G) (g := g) (e := fun _ => 1) hG hG0 hg hg0 he1 hs0 T
    rw [hZ0] at h
    have hle : p ≤ ∏ x ∈ T, (1 - (fun _ => (1 : ℝ)) x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s)) := by
      have h1 : Real.exp (-(2 * ∑ x ∈ T, (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s))) ≤
          ∏ x ∈ T, (1 - (fun _ => (1 : ℝ)) x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s)) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
        refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun x _ => ?_
        simp only [one_mul]
        exact exp_le_one_sub (by positivity) (q_le_half x.1 hs)
      refine le_trans ?_ h1
      refine Real.exp_le_exp.2 ?_
      have := (summable_off S hs).sum_le_tsum T (fun x _ => by positivity)
      linarith
    have hc : ENNReal.ofReal p ≤ ENNReal.ofReal (∏ x ∈ T, (1 - (fun _ => (1 : ℝ)) x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s))) :=
      ENNReal.ofReal_le_ofReal hle
    have hp1 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    calc zi (PositivityTheory.Rg.Base1.pure S G g (wT (fun _ => 1) S T)) s
        = (ENNReal.ofReal p)⁻¹ * (ENNReal.ofReal p * zi (PositivityTheory.Rg.Base1.pure S G g (wT (fun _ => 1) S T)) s) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hp1 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal p)⁻¹ * (ENNReal.ofReal (∏ x ∈ T, (1 - (fun _ => (1 : ℝ)) x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s))) *
            zi (PositivityTheory.Rg.Base1.pure S G g (wT (fun _ => 1) S T)) s) := by gcongr
      _ = _ := by rw [h]
  obtain ⟨u, hu⟩ := exists_seq_tendsto (atTop : Filter (Finset (Off S)))
  have hlim : ∀ a, Filter.liminf (fun n => PositivityTheory.Rg.Base1.pure S G g (wT (fun _ => 1) S (u n)) a * ENNReal.ofReal (md a ^ s)) atTop =
      PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 1) a * ENNReal.ofReal (md a ^ s) := by
    intro a
    refine Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)
    filter_upwards [hu.eventually (eventually_pure_eq (S := S) (G := G) (g := g) (e := fun _ => 1) he1 a)] with n hn
    rw [hn]
  have hfat : ∫⁻ a, Filter.liminf (fun n => PositivityTheory.Rg.Base1.pure S G g (wT (fun _ => 1) S (u n)) a * ENNReal.ofReal (md a ^ s)) atTop ∂(ideleMeasure F) ≤
      Filter.liminf (fun n => ∫⁻ a, PositivityTheory.Rg.Base1.pure S G g (wT (fun _ => 1) S (u n)) a * ENNReal.ofReal (md a ^ s) ∂(ideleMeasure F)) atTop :=
    lintegral_liminf_le (fun n => (continuous_pure S hG hg (good_wT he1 _)).measurable.mul (measurable_md_rpow s))
  simp_rw [hlim] at hfat
  have hle : zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 1) s ≤
      (ENNReal.ofReal p)⁻¹ * zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) s :=
    hfat.trans (Filter.liminf_le_of_frequently_le' (Eventually.of_forall fun n => hbound (u n)).frequently)
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ?_ hfin) hle
  simpa using hp0

theorem euler (hG : Continuous G) (hG0 : ∀ y, 0 ≤ G y) (hg : ∀ v ∈ S, Continuous (g v)) (hg0 : ∀ v y, 0 ≤ g v y)
    (he : ∀ v, e v = 1 ∨ e v = -1) {s : ℝ} (hs : 1 < s) (hfin : zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) s ≠ ⊤) :
    ENNReal.ofReal (∏' v : {v // v ∉ S}, (1 - e v.1 * (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s))) *
        zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v (e v)) s = zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) s := by
  have hs0 : 0 < s := by linarith
  have := countable_off S
  have he' : ∀ v, e v = 0 ∨ e v = 1 ∨ e v = -1 := fun v => Or.inr (he v)
  have h1 : Good fun v : HeightOneSpectrum (𝓞 F) => rv v 1 := good_rv (e := fun _ => 1) fun _ => Or.inr (Or.inl rfl)
  have hZ0 : wT e S ∅ = fun v : HeightOneSpectrum (𝓞 F) => rv v 0 := funext fun v => wT_empty v
  have hb := zi_one_ne_top hG hG0 hg hg0 hs hfin

  have hT : Tendsto (fun T : Finset (Off S) => zi (PositivityTheory.Rg.Base1.pure S G g (wT e S T)) s) atTop
      (𝓝 (zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v (e v)) s)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun a => PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 1) a * ENNReal.ofReal (md a ^ s))
      (Eventually.of_forall fun T => (continuous_pure S hG hg (good_wT he T)).measurable.mul (measurable_md_rpow s))
      (Eventually.of_forall fun T => Eventually.of_forall fun a => ?_) hb (Eventually.of_forall fun a => ?_)
    · exact mul_le_mul_left (pure_le hG0 hg0 (good_wT he T) a) _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_pure_eq (S := S) (G := G) (g := g) he a] with T hT
      rw [hT]

  have hsum : Summable fun x : Off S => -(e x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s)) := by
    refine Summable.of_norm_bounded (summable_off S hs) fun x => ?_
    rw [norm_neg, norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s))]
    rcases he x.1 with h | h <;> simp [h]
  have hmul : Multipliable fun x : Off S => 1 - e x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s) := by
    have := Real.multipliable_one_add_of_summable hsum
    simpa [sub_eq_add_neg] using this
  have hP : Tendsto (fun T : Finset (Off S) => ENNReal.ofReal (∏ x ∈ T, (1 - e x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s)))) atTop
      (𝓝 (ENNReal.ofReal (∏' x : Off S, (1 - e x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s))))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hmul.hasProd
  have hne : zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v (e v)) s ≠ ⊤ := by
    refine ne_top_of_le_ne_top hb (lintegral_mono fun a => ?_)
    exact mul_le_mul_left (pure_le hG0 hg0 (good_rv he') a) _
  have hprod := ENNReal.Tendsto.mul hP (Or.inr hne) hT (Or.inr ENNReal.ofReal_ne_top)
  have hconst : (fun T : Finset (Off S) => ENNReal.ofReal (∏ x ∈ T, (1 - e x.1 * (Ideal.absNorm x.1.asIdeal : ℝ) ^ (-s))) *
      zi (PositivityTheory.Rg.Base1.pure S G g (wT e S T)) s) = fun _ => zi (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) s := by
    funext T
    rw [zi_finite hG hG0 hg hg0 he hs0 T, hZ0]
  rw [hconst] at hprod
  exact tendsto_nhds_unique hprod tendsto_const_nhds

theorem measurable_pure_found (hG : Continuous G) (hg : ∀ v ∈ S, Continuous (g v)) (he : ∀ v, e v = 1 ∨ e v = -1) :
    Measurable (PositivityTheory.Rg.Base1.pure S G g fun v => rv v (e v)) :=
  (continuous_pure S hG hg (good_rv fun v => Or.inr (he v))).measurable

end Limit

end Core

theorem ratio : Ratio := by
  intro F _ _ S G g e hG hG0 hg0 hg he
  refine ⟨?_, fun s hs hfin => euler hG hG0 hg hg0 he hs hfin⟩
  have h : (measAF : MeasurableSpace (AF F)) = GroundTheory.Global.measurableSpace_adeleRing F :=
    (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm
  rw [h]
  exact measurable_pure_found hG hg he

end GlobalTheory.CompanionTheory.RatioBase

end
