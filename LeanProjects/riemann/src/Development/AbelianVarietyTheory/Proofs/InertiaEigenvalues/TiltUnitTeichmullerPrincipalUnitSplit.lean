import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisEqZeroOfForallDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiltRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU.TeichSplit

variable {l : ℕ} [Fact l.Prime]

def nrm (y : Per.Fl l) : ℝ := ‖((y.untilt : Per.OC l) : ℂ_[l])‖

lemma nrm_mul (y z : Per.Fl l) : nrm (y * z) = nrm y * nrm z := by
  simp only [nrm, map_mul]
  push_cast
  exact norm_mul _ _

lemma nrm_one : nrm (1 : Per.Fl l) = 1 := by
  simp [nrm]

lemma nrm_pow (y : Per.Fl l) (n : ℕ) : nrm (y ^ n) = nrm y ^ n := by
  simp only [nrm, map_pow]
  push_cast
  exact norm_pow _ _

lemma nrm_nonneg (y : Per.Fl l) : 0 ≤ nrm y := norm_nonneg _

lemma nrm_le_one (y : Per.Fl l) : nrm y ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 (y.untilt).2

lemma nrm_add (y z : Per.Fl l) : nrm (y + z) ≤ max (nrm y) (nrm z) :=
  (GlobalTheory.TiltAbs.untilt_ultrametric_definite l y z).1

lemma eq_zero_of_nrm (y : Per.Fl l) (h : nrm y = 0) : y = 0 := by
  refine (GlobalTheory.TiltAbs.untilt_ultrametric_definite l y y).2 ?_
  have : ((y.untilt : Per.OC l) : ℂ_[l]) = 0 := norm_eq_zero.1 h
  exact Subtype.ext this

lemma nrm_neg_one : nrm (-1 : Per.Fl l) = 1 := by
  have h : nrm (-1 : Per.Fl l) ^ 2 = 1 := by
    rw [← nrm_pow]; simp [nrm_one]
  exact (pow_eq_one_iff_of_nonneg (nrm_nonneg _) (by norm_num)).1 h

lemma nrm_neg (y : Per.Fl l) : nrm (-y) = nrm y := by
  rw [neg_eq_neg_one_mul, nrm_mul, nrm_neg_one, one_mul]

lemma nrm_sub_tri (a b c : Per.Fl l) : nrm (a - c) ≤ max (nrm (a - b)) (nrm (b - c)) := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [this]; exact nrm_add _ _

lemma norm_l_pos : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero

lemma nrm_sub_le (y z : Per.Fl l) :
    nrm (y - z) ≤ max ‖((y.untilt : Per.OC l) : ℂ_[l]) - ((z.untilt : Per.OC l) : ℂ_[l])‖
      ‖((l : ℕ) : ℂ_[l])‖ := by
  obtain ⟨t, ht⟩ := GlobalTheory.TiltAbs.untilt_add (y - z) z
  rw [sub_add_cancel] at ht
  have h : (((y - z).untilt : Per.OC l) : ℂ_[l]) =
      (((y.untilt : Per.OC l) : ℂ_[l]) - ((z.untilt : Per.OC l) : ℂ_[l])) +
        (-((l : ℕ) : ℂ_[l]) * ((t : Per.OC l) : ℂ_[l])) := by
    rw [ht]; push_cast; ring
  unfold nrm
  rw [h]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl ?_)
  rw [norm_mul, norm_neg]
  exact mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one t)

private lemma exists_pow_between_pt {r s c : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hs : s ≤ 1) (hc0 : 0 < c)
    (hc1 : c < 1) : ∃ n k : ℕ, r ^ n < c ^ k ∧ c ^ k < s ^ n := by
  have hs0 : 0 < s := lt_of_le_of_lt hr hrs
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc0 ((div_lt_one hs0).2 hrs)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one (pow_pos hs0 n) (pow_le_one₀ hs0.le hs) hc0 hc1
  refine ⟨n, k + 1, ?_, hk1⟩
  rw [div_pow, div_lt_iff₀ (pow_pos hs0 n)] at hn
  calc r ^ n < c * s ^ n := hn
    _ ≤ c * c ^ k := mul_le_mul_of_nonneg_left hk2 hc0.le
    _ = c ^ (k + 1) := by ring

private lemma norm_map_mono_pt (f : Per.OC l →+* Per.OC l) (a b : Per.OC l)
    (h : ‖(a : ℂ_[l])‖ ≤ ‖(b : ℂ_[l])‖) : ‖((f a : Per.OC l) : ℂ_[l])‖ ≤ ‖((f b : Per.OC l) : ℂ_[l])‖ := by
  have hd : ∃ t : Per.OC l, a = b * t := by
    by_cases hb : (b : ℂ_[l]) = 0
    · rw [hb, norm_zero] at h
      have ha : (a : ℂ_[l]) = 0 := norm_le_zero_iff.1 h
      exact ⟨0, by rw [mul_zero]; exact Subtype.ext ha⟩
    · refine ⟨⟨(a : ℂ_[l]) / (b : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
      · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
      · push_cast
        rw [mul_div_cancel₀ _ hb]
  obtain ⟨t, rfl⟩ := hd
  rw [map_mul]
  push_cast
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one _)

private lemma norm_map_pt (f : Per.OC l →+* Per.OC l) (y : Per.OC l) :
    ‖((f y : Per.OC l) : ℂ_[l])‖ = ‖(y : ℂ_[l])‖ := by
  have hlt := GlobalTheory.TiltAbs.norm_l_lt (l := l)
  have e (z : Per.OC l) (n : ℕ) : ‖((z ^ n : Per.OC l) : ℂ_[l])‖ = ‖(z : ℂ_[l])‖ ^ n := by
    push_cast; exact norm_pow _ _
  have el : ‖((((l : ℕ) : Per.OC l)) : ℂ_[l])‖ = ‖((l : ℕ) : ℂ_[l])‖ := by
    push_cast; rfl
  rcases lt_trichotomy ‖((f y : Per.OC l) : ℂ_[l])‖ ‖(y : ℂ_[l])‖ with h | h | h
  · obtain ⟨n, k, h1, h2⟩ := exists_pow_between_pt (norm_nonneg _) h (GlobalTheory.TiltAbs.norm_le_one y)
      (norm_l_pos (l := l)) hlt
    have h3 := norm_map_mono_pt f (((l : ℕ) : Per.OC l) ^ k) (y ^ n) (by rw [e, e, el]; exact h2.le)
    rw [map_pow, map_pow, map_natCast, e, e, el] at h3
    exact absurd h1 (not_lt.2 h3)
  · exact h
  · obtain ⟨n, k, h1, h2⟩ := exists_pow_between_pt (norm_nonneg _) h (GlobalTheory.TiltAbs.norm_le_one (f y))
      (norm_l_pos (l := l)) hlt
    have h3 := norm_map_mono_pt f (y ^ n) (((l : ℕ) : Per.OC l) ^ k) (by rw [e, e, el]; exact h1.le)
    rw [map_pow, map_pow, map_natCast, e, e, el] at h3
    exact absurd h2 (not_lt.2 h3)

lemma nrm_σF (g : Per.Gq l) (y : Per.Fl l) : nrm (Per.σF g y) = nrm y := by
  unfold nrm
  rw [GlobalTheory.RingBasics.untilt_σF]
  exact norm_map_pt (Per.σO g) _

end GlobalTheory.LogU.TeichSplit

namespace GlobalTheory.LogU.TeichSplit
variable {l : ℕ} [Fact l.Prime]

lemma nrm_eq_one_of_isUnit {x : Per.Fl l} (hx : IsUnit x) : nrm x = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h := congrArg nrm hy
  rw [nrm_mul, nrm_one] at h
  nlinarith [nrm_le_one x, nrm_le_one y, nrm_nonneg x, nrm_nonneg y]

lemma eq_zero_of_pow_eq_self {d : Per.Fl l} {q : ℕ} (hq : 2 ≤ q) (hd : d ^ q = d) (h : nrm d < 1) :
    d = 0 := by
  refine eq_zero_of_nrm d ?_
  have h1 : nrm d ^ q = nrm d := by rw [← nrm_pow, hd]
  by_contra hne
  have hpos : 0 < nrm d := lt_of_le_of_ne (nrm_nonneg d) (Ne.symm hne)
  have h2 : nrm d ^ (q - 1) = 1 := by
    have : nrm d ^ (q - 1) * nrm d = 1 * nrm d := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), h1, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have := (pow_eq_one_iff_of_nonneg (nrm_nonneg d) (by omega)).1 h2
  linarith

lemma inJ_of_nrm {y : Per.Fl l} (h : nrm (y - 1) ≤ ‖((l : ℕ) : ℂ_[l])‖) : InJ (Per.tm y - 1) := by
  obtain ⟨t, ht⟩ := GlobalTheory.TiltAbs.untilt_add (y - 1) 1
  rw [sub_add_cancel, map_one] at ht
  have hmem : (y - 1).untilt ∈ (Ideal.span {((l : ℕ) : Per.OC l)}) ^ 1 := by
    rw [GlobalTheory.RingBasics.mem_span_pow_OC, pow_one]; exact h
  rw [pow_one, Ideal.mem_span_singleton'] at hmem
  obtain ⟨s, hs⟩ := hmem
  refine ⟨s + t, ?_⟩
  rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller, ht, ← hs]
  ring

end GlobalTheory.LogU.TeichSplit

open GlobalTheory.LogU.TeichSplit in

theorem GlobalTheory.LogU.teich_split : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Fl l), IsUnit x → ∃ (ω x₁ : Per.Fl l) (N : ℕ), x = ω * x₁ ∧ GlobalTheory.LogU.InJ (Per.tm (x₁ ^ (l ^ N)) - 1) ∧ ∀ (g : Per.Gq l) (e : Per.Fl l), e.untilt = 1 → Per.σF g x = x * e → Per.σF g ω = ω := by
  intro l _ x hx
  have hl : l.Prime := Fact.out
  have hlt := GlobalTheory.TiltAbs.norm_l_lt (l := l)
  have hN1 : nrm x = 1 := nrm_eq_one_of_isUnit hx

  obtain ⟨α, hα⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
    (((x.untilt : Per.OC l) : ℂ_[l])) one_pos
  rw [dist_eq_norm] at hα
  have hαn : ‖α‖ = 1 := by
    rw [← PadicComplex.norm_extends]
    have hx1 : ‖((x.untilt : Per.OC l) : ℂ_[l])‖ = 1 := hN1
    have a1 : ‖((α : PadicAlgCl l) : ℂ_[l])‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (((x.untilt : Per.OC l) : ℂ_[l]))
        (((α : PadicAlgCl l) : ℂ_[l]) - ((x.untilt : Per.OC l) : ℂ_[l]))
      rw [add_sub_cancel, norm_sub_rev] at this
      exact this.trans (max_le hx1.le hα.le)
    have a2 := IsUltrametricDist.norm_add_le_max (((α : PadicAlgCl l) : ℂ_[l]))
        (((x.untilt : Per.OC l) : ℂ_[l]) - ((α : PadicAlgCl l) : ℂ_[l]))
    rw [add_sub_cancel, hx1] at a2
    refine le_antisymm a1 ?_
    rcases le_max_iff.1 a2 with h | h
    · exact h
    · exact absurd h (not_le.2 hα)
  obtain ⟨ζ, m, hm, hζ, hαζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar α hαn
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  obtain ⟨ω, hωm, hωζ⟩ := GlobalTheory.MemLoc.exists_tilt_root_of_unity l ζ m hm0 hm hζ

  have hxω : nrm (x - ω) < 1 := by
    refine lt_of_le_of_lt (nrm_sub_le x ω) (max_lt ?_ hlt)
    rw [hωζ]
    have e1 : ((x.untilt : Per.OC l) : ℂ_[l]) - ((ζ : Om l) : ℂ_[l]) =
        (((x.untilt : Per.OC l) : ℂ_[l]) - ((α : PadicAlgCl l) : ℂ_[l])) +
          (((α - ζ : PadicAlgCl l)) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_sub]; ring
    rw [e1]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hα ?_)
    rw [PadicComplex.norm_extends]; exact hαζ
  set x₁ := x * ω ^ (m - 1) with hx₁
  have hωω : ω * ω ^ (m - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hm0, hωm]
  have hx1 : nrm (x₁ - 1) < 1 := by
    have : x₁ - 1 = ω ^ (m - 1) * (x - ω) := by
      rw [hx₁, ← hωω]; ring
    rw [this, nrm_mul]
    calc nrm (ω ^ (m - 1)) * nrm (x - ω) ≤ 1 * nrm (x - ω) :=
          mul_le_mul_of_nonneg_right (nrm_le_one _) (nrm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hxω

  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (norm_l_pos (l := l)) hx1
  refine ⟨ω, x₁, k, ?_, ?_, ?_⟩
  · rw [hx₁, ← mul_assoc, mul_comm ω x, mul_assoc, hωω, mul_one]
  · refine inJ_of_nrm ?_
    have e2 : x₁ ^ l ^ k - 1 = (x₁ - 1) ^ l ^ k := by
      rw [sub_pow_char_pow, one_pow]
    rw [e2, nrm_pow]
    refine le_trans (pow_le_pow_of_le_one (nrm_nonneg _) (nrm_le_one _)
      (Nat.lt_pow_self hl.one_lt).le) hk.le
  · intro g e he hgx
    have f0 : 0 < Nat.totient m := Nat.totient_pos.2 hm0
    have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
    have hmod : l ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
    have hq1 : 1 ≤ l ^ Nat.totient m := Nat.one_le_pow _ _ hl.pos
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hq1).1 hmod.symm
    have hωq : ω ^ l ^ Nat.totient m = ω := by
      rw [← Nat.sub_add_cancel hq1, pow_succ, hc, pow_mul, hωm, one_pow, one_mul]
    have hq2 : 2 ≤ l ^ Nat.totient m :=
      le_trans hl.two_le (Nat.le_self_pow f0.ne' l)
    rw [← sub_eq_zero]
    refine eq_zero_of_pow_eq_self hq2 ?_ ?_
    · rw [sub_pow_char_pow, ← map_pow, hωq]
    · have he1 : nrm (e - 1) < 1 := by
        refine lt_of_le_of_lt (nrm_sub_le e 1) (max_lt ?_ hlt)
        rw [he, map_one, sub_self, norm_zero]; exact zero_lt_one
      have h1 : nrm (Per.σF g ω - Per.σF g x) < 1 := by
        rw [← map_sub, nrm_σF, ← neg_sub, nrm_neg]; exact hxω
      have h2 : nrm (Per.σF g x - x) < 1 := by
        have : Per.σF g x - x = x * (e - 1) := by rw [hgx]; ring
        rw [this, nrm_mul, hN1, one_mul]; exact he1
      refine lt_of_le_of_lt (nrm_sub_tri _ (Per.σF g x) _) (max_lt h1 ?_)
      exact lt_of_le_of_lt (nrm_sub_tri _ x _) (max_lt h2 hxω)

example : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Fl l), IsUnit x → ∃ (ω x₁ : Per.Fl l) (N : ℕ), x = ω * x₁ ∧ GlobalTheory.LogU.InJ (Per.tm (x₁ ^ (l ^ N)) - 1) ∧ ∀ (g : Per.Gq l) (e : Per.Fl l), e.untilt = 1 → Per.σF g x = x * e → Per.σF g ω = ω := GlobalTheory.LogU.teich_split
