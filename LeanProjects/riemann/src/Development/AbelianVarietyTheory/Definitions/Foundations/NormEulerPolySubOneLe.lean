import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow

noncomputable section

namespace GlobalTheory.LFun

open NumberField IsDedekindDomain
open Formalism.L2.Host (HChar aboveF)

section Factor

def eulerPoly (B : Multiset ℂˣ) (x : ℂ) : ℂ := (B.map fun b : ℂˣ => 1 - (b : ℂ) * x).prod

def eulerFac (B : Multiset ℂˣ) (x : ℂ) : ℂ := (eulerPoly B x)⁻¹

@[simp] theorem eulerPoly_zero (x : ℂ) : eulerPoly 0 x = 1 := rfl
@[simp] theorem eulerFac_zero (x : ℂ) : eulerFac 0 x = 1 := by simp [eulerFac]

theorem eulerPoly_cons (b : ℂˣ) (B : Multiset ℂˣ) (x : ℂ) :
    eulerPoly (b ::ₘ B) x = (1 - (b : ℂ) * x) * eulerPoly B x := by simp [eulerPoly]

@[simp] theorem eulerFac_singleton (b : ℂˣ) (x : ℂ) : eulerFac {b} x = (1 - (b : ℂ) * x)⁻¹ := by
  simp [eulerFac, eulerPoly]

theorem eulerPoly_add (A B : Multiset ℂˣ) (x : ℂ) : eulerPoly (A + B) x = eulerPoly A x * eulerPoly B x := by
  simp [eulerPoly]

theorem eulerFac_add (A B : Multiset ℂˣ) (x : ℂ) : eulerFac (A + B) x = eulerFac A x * eulerFac B x := by
  simp [eulerFac, eulerPoly_add, mul_comm]

theorem eulerFac_eq_prod (B : Multiset ℂˣ) (x : ℂ) :
    eulerFac B x = (B.map fun b : ℂˣ => (1 - (b : ℂ) * x)⁻¹).prod := by
  rw [eulerFac, eulerPoly, Multiset.prod_map_inv]

theorem eulerFac_map {ι : Type} (s : Finset ι) (α : ι → ℂˣ) (x : ℂ) :
    eulerFac (s.val.map α) x = ∏ i ∈ s, (1 - (α i : ℂ) * x)⁻¹ := by
  rw [eulerFac_eq_prod, Multiset.map_map]; rfl

theorem eulerFac_map_mul (z : ℂˣ) (B : Multiset ℂˣ) (x : ℂ) :
    eulerFac (B.map (z * ·)) x = eulerFac B ((z : ℂ) * x) := by
  simp only [eulerFac, eulerPoly, Multiset.map_map, Function.comp_def, Units.val_mul]
  congr 3
  funext b
  ring

theorem eulerPoly_ne_zero {B : Multiset ℂˣ} {x : ℂ} (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ < 1) : eulerPoly B x ≠ 0 := by
  refine Multiset.prod_ne_zero fun h0 => ?_
  obtain ⟨b, hb, e⟩ := Multiset.mem_map.1 h0
  have := h b hb
  rw [← sub_eq_zero.1 e] at this
  simp at this

theorem norm_eulerPoly_sub_one_le {B : Multiset ℂˣ} {x : ℂ} {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ ≤ y) : ‖eulerPoly B x - 1‖ ≤ (2 ^ B.card - 1) * y := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih =>
    have h1 := ih fun c hc => h c (Multiset.mem_cons_of_mem hc)
    have h2 := h b (Multiset.mem_cons_self _ _)
    have h3 : (1 : ℝ) ≤ 2 ^ B.card := one_le_pow₀ one_le_two
    have h4 : ‖eulerPoly B x‖ ≤ 2 ^ B.card := by
      have := norm_add_le (eulerPoly B x - 1) 1
      rw [sub_add_cancel, norm_one] at this
      nlinarith
    have e : eulerPoly (b ::ₘ B) x - 1 = (eulerPoly B x - 1) - (b : ℂ) * x * eulerPoly B x := by
      rw [eulerPoly_cons]; ring
    have h5 : ‖(b : ℂ) * x * eulerPoly B x‖ ≤ y * 2 ^ B.card := by
      rw [norm_mul]; exact mul_le_mul h2 h4 (norm_nonneg _) hy0
    rw [e, Multiset.card_cons, pow_succ]
    refine (norm_sub_le _ _).trans ?_
    nlinarith

end Factor

section Product

variable {K : Type} [Field K] [NumberField K]

def npow (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) : ℂ := ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ z

theorem one_lt_absNorm (w : HeightOneSpectrum (𝓞 K)) : 1 < Ideal.absNorm w.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm w

theorem npow_ne_zero (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) : npow w z ≠ 0 := fun h =>
  (one_lt_absNorm w).ne_bot (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h).1)

theorem npow_add (w : HeightOneSpectrum (𝓞 K)) (y z : ℂ) : npow w (y + z) = npow w y * npow w z :=
  Complex.cpow_add _ _ (by exact_mod_cast (one_lt_absNorm w).ne_bot)

theorem norm_npow (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) :
    ‖npow w z‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ z.re :=
  Complex.norm_natCast_cpow_of_pos (one_lt_absNorm w).bot_lt z

def npowU (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) : ℂˣ := Units.mk0 (npow w z) (npow_ne_zero w z)

@[simp] theorem coe_npowU (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) : (npowU w z : ℂ) = npow w z := rfl

variable (K) in

abbrev Fam : Type := HeightOneSpectrum (𝓞 K) → Multiset ℂˣ

def locL (c : Fam K) (w : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ := eulerFac (c w) (npow w (-s))

def eulerProd (T : Set (HeightOneSpectrum (𝓞 K))) (c : Fam K) (s : ℂ) : ℂ :=
  ∏' w : {w // w ∉ T}, locL c w s

def Converges (T : Set (HeightOneSpectrum (𝓞 K))) (c : Fam K) (s : ℂ) : Prop :=
  (∀ w ∉ T, eulerPoly (c w) (npow w (-s)) ≠ 0) ∧
    Summable fun w : {w // w ∉ T} => ‖eulerPoly (c w) (npow w.1 (-s)) - 1‖

def Bounded (T : Set (HeightOneSpectrum (𝓞 K))) (c : Fam K) (r : ℕ) (κ : ℝ) : Prop :=
  ∀ w ∉ T, (c w).card ≤ r ∧ ∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ κ

def twist (c : Fam K) (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : Fam K := fun w => (c w).map (z w * ·)

def seg (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ) : Multiset ℂˣ :=
  (Finset.range t).val.map fun i : ℕ => x * npowU w (((t : ℂ) - 1) / 2 - i)

def segFam (z : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : Fam K := fun w => seg w (z w) t

variable {T : Set (HeightOneSpectrum (𝓞 K))} {c c' : Fam K} {s : ℂ}

theorem locL_add (c c' : Fam K) (w : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    locL (c + c') w s = locL c w s * locL c' w s := eulerFac_add _ _ _

theorem locL_twist (c : Fam K) (z : HeightOneSpectrum (𝓞 K) → ℂˣ) (w : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    locL (twist c z) w s = ((c w).map fun b : ℂˣ => (1 - (b : ℂ) * (z w : ℂ) * npow w (-s))⁻¹).prod := by
  rw [locL, twist, eulerFac_map_mul, eulerFac_eq_prod]
  simp only [mul_assoc]

@[simp] theorem twist_one (c : Fam K) : twist c 1 = c := by funext w; simp [twist]

theorem twist_twist (c : Fam K) (y z : HeightOneSpectrum (𝓞 K) → ℂˣ) : twist (twist c y) z = twist c (z * y) := by
  funext w; simp [twist, mul_assoc]

theorem twist_add (c c' : Fam K) (z : HeightOneSpectrum (𝓞 K) → ℂˣ) :
    twist (c + c') z = twist c z + twist c' z := by funext w; simp [twist]

theorem twist_segFam (y z : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : twist (segFam y t) z = segFam (z * y) t := by
  funext w; simp [twist, segFam, seg, mul_assoc]

@[simp] theorem card_seg (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) (t : ℕ) : (seg w x t).card = t := by simp [seg]

theorem locL_segFam (z : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) (w : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    locL (segFam z t) w s = ∏ i ∈ Finset.range t, locL (fun u => {z u}) w (s - ((t : ℂ) - 1) / 2 + i) := by
  rw [locL, segFam, seg, eulerFac_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [locL, eulerFac_singleton, Units.val_mul, coe_npowU, mul_assoc, ← npow_add]
  congr 4
  ring

theorem locL_segFam' (z : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) (w : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    locL (segFam z t) w s = ∏ i ∈ Finset.range t, locL (fun u => {z u}) w (s + ((t : ℂ) - 1) / 2 - i) := by
  rw [locL_segFam, ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  congr 1
  push_cast
  ring

theorem Converges.hasProd_and_ne_zero (h : Converges T c s) :
    HasProd (fun w : {w // w ∉ T} => locL c w s) (eulerProd T c s) ∧ eulerProd T c s ≠ 0 := by
  have h1 := multipliable_one_add_of_summable h.2
  have h2 := tprod_one_add_ne_zero_of_summable (f := fun w : {w // w ∉ T} => eulerPoly (c w) (npow w.1 (-s)) - 1)
    (fun w => by simpa using h.1 w w.2) h.2
  simp only [add_sub_cancel] at h1 h2
  have h3 : HasProd (fun w : {w // w ∉ T} => locL c w s) _ := h1.hasProd.inv₀ h2
  refine ⟨h3.multipliable.hasProd, ?_⟩
  rw [eulerProd, h3.tprod_eq]
  exact inv_ne_zero h2

theorem Converges.hasProd (h : Converges T c s) :
    HasProd (fun w : {w // w ∉ T} => locL c w s) (eulerProd T c s) := h.hasProd_and_ne_zero.1

theorem Converges.multipliable (h : Converges T c s) : Multipliable fun w : {w // w ∉ T} => locL c w s :=
  h.hasProd.multipliable

theorem Converges.ne_zero (h : Converges T c s) : eulerProd T c s ≠ 0 := h.hasProd_and_ne_zero.2

theorem eulerProd_add (h : Converges T c s) (h' : Converges T c' s) :
    eulerProd T (c + c') s = eulerProd T c s * eulerProd T c' s := by
  have := h.hasProd.mul h'.hasProd
  simp only [← locL_add] at this
  exact this.tprod_eq

theorem eulerProd_congr (h : ∀ w ∉ T, c w = c' w) (s : ℂ) : eulerProd T c s = eulerProd T c' s :=
  tprod_congr fun w => by rw [locL, locL, h w w.2]

theorem Converges.congr (h : Converges T c s) (e : ∀ w ∉ T, c w = c' w) : Converges T c' s :=
  ⟨fun w hw => e w hw ▸ h.1 w hw, h.2.congr fun w => by rw [e w w.2]⟩

theorem Converges.eulerProd_eq_inv (h : Converges T c s) :
    eulerProd T c s = (∏' w : {w // w ∉ T}, eulerPoly (c w) (npow w.1 (-s)))⁻¹ := by
  have h1 := multipliable_one_add_of_summable h.2
  have h2 := tprod_one_add_ne_zero_of_summable (f := fun w : {w // w ∉ T} => eulerPoly (c w) (npow w.1 (-s)) - 1)
    (fun w => by simpa using h.1 w w.2) h.2
  simp only [add_sub_cancel] at h1 h2
  exact (h1.hasProd.inv₀ h2).tprod_eq

theorem Bounded.norm_le {r : ℕ} {κ σ : ℝ} (h : Bounded T c r κ) (hs : σ ≤ s.re) {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ∉ T) {b : ℂˣ} (hb : b ∈ c w) :
    ‖(b : ℂ) * npow w (-s)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-(σ - κ)) := by
  have hN : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm w
  rw [norm_mul, norm_npow, neg_sub, sub_eq_add_neg, Real.rpow_add (by linarith)]
  exact mul_le_mul ((h w hw).2 b hb) (Real.rpow_le_rpow_of_exponent_le hN.le (by simpa using hs)) (by positivity)
    (by positivity)

theorem Bounded.norm_eulerPoly_le {r : ℕ} {κ σ : ℝ} (h : Bounded T c r κ) (hσ : κ ≤ σ) (hs : σ ≤ s.re)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ T) :
    ‖eulerPoly (c w) (npow w (-s)) - 1‖ ≤ 2 ^ r * ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-(σ - κ)) := by
  refine (norm_eulerPoly_sub_one_le (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (one_lt_absNorm w).le) (by linarith)) fun b hb => h.norm_le hs hw hb).trans ?_
  have : (2 : ℝ) ^ (c w).card ≤ 2 ^ r := pow_le_pow_right₀ one_le_two (h w hw).1
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem summable_rpow (T : Set (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun w : {w // w ∉ T} => ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 σ hσ).2.subtype {w | w ∉ T}

theorem Bounded.converges {r : ℕ} {κ : ℝ} (h : Bounded T c r κ) (hs : κ + 1 < s.re) : Converges T c s :=
  ⟨fun w hw => eulerPoly_ne_zero fun _ hb => (h.norm_le le_rfl hw hb).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith)),
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => h.norm_eulerPoly_le (by linarith) le_rfl w.2)
      ((summable_rpow T (σ := s.re - κ) (by linarith)).mul_left (2 ^ r))⟩

theorem differentiable_eulerPoly (B : Multiset ℂˣ) (w : HeightOneSpectrum (𝓞 K)) :
    Differentiable ℂ fun s => eulerPoly B (npow w (-s)) := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih =>
    simp only [eulerPoly_cons]
    refine ((differentiable_const _).sub ((differentiable_const _).mul ?_)).mul ih
    exact differentiable_neg.const_cpow (Or.inl (by exact_mod_cast (one_lt_absNorm w).ne_bot))

theorem Bounded.differentiableOn {r : ℕ} {κ : ℝ} (h : Bounded T c r κ) :
    DifferentiableOn ℂ (eulerProd T c) {s | κ + 1 < s.re} := by
  intro s hs
  obtain ⟨σ, h1, h2⟩ := exists_between (show κ + 1 < s.re from hs)
  have ho : IsOpen {z : ℂ | σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h3 := ((summable_rpow T (σ := σ - κ) (by linarith)).mul_left (2 ^ r)).hasProdLocallyUniformlyOn_one_add
    (f := fun (w : {w // w ∉ T}) z => eulerPoly (c w) (npow w.1 (-z)) - 1) ho
    (Filter.Eventually.of_forall fun w z hz => h.norm_eulerPoly_le (by linarith) (le_of_lt hz) w.2)
    fun w => ((differentiable_eulerPoly _ _).sub_const 1).continuous.continuousOn
  simp only [add_sub_cancel] at h3
  have h4 := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.1 h3).differentiableOn
    (Filter.Eventually.of_forall fun t =>
      (Differentiable.fun_finsetProd fun w _ => differentiable_eulerPoly _ _).differentiableOn) ho
  have h5 : DifferentiableOn ℂ (eulerProd T c) {z | σ < z.re} :=
    (h4.inv fun z hz h0 => (h.converges (h1.trans hz)).ne_zero (by
      rw [(h.converges (h1.trans hz)).eulerProd_eq_inv, h0, inv_zero])).congr
      fun z hz => (h.converges (h1.trans hz)).eulerProd_eq_inv
  exact (h5.differentiableAt (ho.mem_nhds h2)).differentiableWithinAt

theorem Bounded.twist {r : ℕ} {κ : ℝ} (h : Bounded T c r κ) {z : HeightOneSpectrum (𝓞 K) → ℂˣ}
    (hz : ∀ w ∉ T, ‖(z w : ℂ)‖ = 1) : Bounded T (twist c z) r κ := fun w hw =>
  ⟨by simpa [LFun.twist] using (h w hw).1, fun b hb => by
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    simpa [hz w hw] using (h w hw).2 a ha⟩

theorem Bounded.add {r r' : ℕ} {κ : ℝ} (h : Bounded T c r κ) (h' : Bounded T c' r' κ) :
    Bounded T (c + c') (r + r') κ := fun w hw =>
  ⟨by simpa using add_le_add (h w hw).1 (h' w hw).1, fun b hb =>
    (Multiset.mem_add.1 hb).elim ((h w hw).2 b) ((h' w hw).2 b)⟩

def IsCont (T : Set (HeightOneSpectrum (𝓞 K))) (c : Fam K) (σ : ℝ) (Λ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Λ {s | σ < s.re} ∧ ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → Converges T c s ∧ Λ s = eulerProd T c s

def IsMerCont (T : Set (HeightOneSpectrum (𝓞 K))) (c : Fam K) (σ : ℝ) (Λ : ℂ → ℂ) : Prop :=
  MeromorphicOn Λ {s | σ < s.re} ∧ ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → Converges T c s ∧ Λ s = eulerProd T c s

theorem IsCont.unique {σ : ℝ} {Λ Λ' : ℂ → ℂ} (h : IsCont T c σ Λ) (h' : IsCont T c σ Λ') :
    Set.EqOn Λ Λ' {s | σ < s.re} := by
  obtain ⟨h1, a, h2⟩ := h
  obtain ⟨h1', a', h2'⟩ := h'
  have ho : ∀ x : ℝ, IsOpen {s : ℂ | x < s.re} := fun x => isOpen_lt continuous_const Complex.continuous_re
  refine (h1.analyticOnNhd (ho σ)).eqOn_of_preconnected_of_eventuallyEq (h1'.analyticOnNhd (ho σ))
    (convex_halfSpace_re_gt σ).isPreconnected (z₀ := ((max σ (max a a') + 1 : ℝ) : ℂ))
    (show σ < max σ (max a a') + 1 from (le_max_left _ _).trans_lt (lt_add_one _)) ?_
  filter_upwards [(ho (max σ (max a a'))).mem_nhds (lt_add_one (max σ (max a a')))] with s hs
  simp only [Set.mem_setOf_eq, max_lt_iff] at hs
  rw [(h2 s hs.2.1).2, (h2' s hs.2.2).2]

end Product

section Hecke

variable {K : Type} [Field K] [NumberField K]

open Classical in

def heckeFam (χ : HChar K) : Fam K := fun w => if χ.UnrAt w then {χ.val w} else 0

def heckeL (T : Set (HeightOneSpectrum (𝓞 K))) (χ : HChar K) (s : ℂ) : ℂ := eulerProd T (heckeFam χ) s

def zetaOff (T : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ := eulerProd T (fun _ => {1}) s

theorem heckeFam_of_unrAt {χ : HChar K} {w : HeightOneSpectrum (𝓞 K)} (h : χ.UnrAt w) :
    heckeFam χ w = {χ.val w} := if_pos h

theorem heckeFam_of_not_unrAt {χ : HChar K} {w : HeightOneSpectrum (𝓞 K)} (h : ¬ χ.UnrAt w) :
    heckeFam χ w = 0 := if_neg h

theorem locL_heckeFam (χ : HChar K) (w : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    locL (heckeFam χ) w s = GlobalTheory.CMVal.eulerFactor χ s w := by
  unfold locL heckeFam GlobalTheory.CMVal.eulerFactor
  split_ifs <;> simp [npow]

theorem heckeFam_one : heckeFam (1 : HChar K) = fun _ => {1} :=
  funext fun _ => heckeFam_of_unrAt fun _ _ => rfl

theorem heckeL_one (T : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : heckeL T 1 s = zetaOff T s := by
  rw [heckeL, heckeFam_one, zetaOff]

theorem bounded_heckeFam (T : Set (HeightOneSpectrum (𝓞 K))) {χ : HChar K} (h : χ.IsUnitary) :
    Bounded T (heckeFam χ) 1 0 := fun w _ => by
  unfold heckeFam
  split_ifs
  · refine ⟨by simp, fun b hb => ?_⟩
    rw [Multiset.mem_singleton.1 hb, Real.rpow_zero]
    exact (h _).le
  · simp

theorem converges_heckeFam (T : Set (HeightOneSpectrum (𝓞 K))) {χ : HChar K} (h : χ.IsUnitary) {s : ℂ}
    (hs : 1 < s.re) : Converges T (heckeFam χ) s := (bounded_heckeFam T h).converges (by simpa using hs)

theorem converges_zeta (T : Set (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    Converges T (fun _ => {1}) s := by
  rw [← heckeFam_one]
  exact converges_heckeFam T (fun _ => by simp) hs

end Hecke

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (E) in

def above (S : Set (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 E)) := {w | w.under (𝓞 F) ∈ S}

theorem mem_aboveF {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} :
    w ∈ aboveF (L := E) F v ↔ w.under (𝓞 F) = v := by simp [aboveF]

def Lv (c : Fam E) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ := ∏ w ∈ aboveF (L := E) F v, locL c w s

def LS (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (s : ℂ) : ℂ := eulerProd (above E S) c s

def LvTw (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  Lv (twist c m⁻¹) v s

def LSTw (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (s : ℂ) : ℂ :=
  LS S (twist c m⁻¹) s

theorem LvTw_eq (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    LvTw c m v s = ∏ w ∈ aboveF (L := E) F v,
      ((c w).map fun b : ℂˣ => (1 - (b : ℂ) * (m w : ℂ)⁻¹ * npow w (-s))⁻¹).prod := by
  simp [LvTw, Lv, locL_twist]

theorem Lv_add (c c' : Fam E) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : Lv (c + c') v s = Lv c v s * Lv c' v s := by
  simp [Lv, locL_add, Finset.prod_mul_distrib]

theorem hasProd_Lv {S : Set (HeightOneSpectrum (𝓞 F))} {c : Fam E} {s : ℂ} (h : Converges (above E S) c s) :
    HasProd (fun v : {v // v ∉ S} => Lv c v.1 s) (LS S c s) := by
  let f : {w // w ∉ above E S} → {v // v ∉ S} := fun w => ⟨w.1.under (𝓞 F), w.2⟩
  have h1 := (Equiv.sigmaFiberEquiv f).hasProd_iff.2 h.hasProd
  refine h1.sigma fun v => ?_
  let e : {w // w ∈ aboveF (L := E) F v.1} ≃ {w // f w = v} :=
    { toFun := fun w => ⟨⟨w.1, fun hw : w.1.under (𝓞 F) ∈ S => v.2 (mem_aboveF.1 w.2 ▸ hw)⟩,
        Subtype.ext (mem_aboveF.1 w.2)⟩
      invFun := fun w => ⟨w.1.1, mem_aboveF.2 (congrArg Subtype.val w.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.hasProd_iff.1 (Finset.hasProd (aboveF (L := E) F v.1) fun w => locL c w s)

theorem LvTw_inert (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) {v : HeightOneSpectrum (𝓞 F)}
    {w : HeightOneSpectrum (𝓞 E)} (hv : ∀ u, u.under (𝓞 F) = v ↔ u = w)
    (hq : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2) (s : ℂ) :
    LvTw c m v s = eulerFac (c w) ((m w : ℂ)⁻¹ * npow v (-(2 * s))) := by
  have e : aboveF (L := E) F v = {w} := by ext u; simp [mem_aboveF, hv]
  have e2 : npow w (-s) = npow v (-(2 * s)) := by
    rw [show -(2 * s) = -s + -s by ring, npow_add, npow, hq, pow_two, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    rfl
  rw [LvTw, Lv, e, Finset.prod_singleton, locL, twist, eulerFac_map_mul, e2]
  simp

open Formalism.MainNotions.SchurIrreducible

variable (E) in
open Classical in

def etaU (v : HeightOneSpectrum (𝓞 F)) : ℂˣ := if IsSplit (E := E) v then 1 else -1

theorem etaU_sq (v : HeightOneSpectrum (𝓞 F)) : etaU E v ^ 2 = 1 := by
  unfold etaU; split_ifs <;> simp

variable (E) in
open Classical in

def etaFam (k : ℕ) : Fam F := fun v => if IsUnram (E := E) v ∨ Even k then {etaU E v ^ k} else 0

variable (E) in

def etaL (S : Set (HeightOneSpectrum (𝓞 F))) (k : ℕ) (s : ℂ) : ℂ := eulerProd S (etaFam E k) s

theorem etaFam_of_unram {v : HeightOneSpectrum (𝓞 F)} (h : IsUnram (E := E) v) (k : ℕ) :
    etaFam E k v = {etaU E v ^ k} := if_pos (Or.inl h)

theorem etaFam_add_two_mul (k j : ℕ) : etaFam (F := F) E (k + 2 * j) = etaFam E k := by
  funext v
  have : Even (k + 2 * j) ↔ Even k := by simp [Nat.even_add]
  rw [etaFam, etaFam, pow_add, pow_mul, etaU_sq, one_pow, mul_one]
  by_cases h : IsUnram (E := E) v ∨ Even k
  · rw [if_pos h, if_pos ((or_congr_right this).2 h)]
  · rw [if_neg h, if_neg (mt (or_congr_right this).1 h)]

theorem bounded_etaFam (S : Set (HeightOneSpectrum (𝓞 F))) (k : ℕ) : Bounded S (etaFam E k) 1 0 := fun v _ => by
  unfold etaFam
  split_ifs
  · refine ⟨by simp, fun b hb => ?_⟩
    rw [Multiset.mem_singleton.1 hb, Real.rpow_zero]
    unfold etaU
    split_ifs <;> simp
  · simp

theorem converges_etaFam (S : Set (HeightOneSpectrum (𝓞 F))) (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Converges S (etaFam E k) s := (bounded_etaFam S k).converges (by simpa using hs)

variable (E) in

def dv (a b : ℕ) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  ∏ i ∈ Finset.range a, locL (etaFam E (b + i)) v (2 * s + a - i)

variable (E) in

def dSfun (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) (s : ℂ) : ℂ := ∏' v : {v // v ∉ S}, dv E a b v.1 s

variable (E) in

def dS (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) : ℂ := dSfun E S a b (((b : ℂ) - a) / 2)

theorem dv_center (a t : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    dv E a (a + t) v ((t : ℂ) / 2) = ∏ k ∈ Finset.Icc (t + 1) (t + a), locL (etaFam E k) v k := by
  rw [dv, ← Finset.prod_range_reflect, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range,
    show t + a + 1 - (t + 1) = a by omega]
  refine Finset.prod_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  rw [show a + t + (a - 1 - i) = t + 1 + i + 2 * (a - 1 - i) by omega, etaFam_add_two_mul,
    Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  congr 1
  push_cast
  ring

theorem hasProd_dv (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasProd (fun v : {v // v ∉ S} => dv E a b v.1 s) (∏ i ∈ Finset.range a, etaL E S (b + i) (2 * s + a - i)) := by
  refine hasProd_prod fun i hi => (converges_etaFam S _ ?_).hasProd
  have : (i : ℝ) + 1 ≤ a := by exact_mod_cast Finset.mem_range.1 hi
  simp
  linarith

theorem dSfun_eq (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    dSfun E S a b s = ∏ i ∈ Finset.range a, etaL E S (b + i) (2 * s + a - i) := (hasProd_dv S a b hs).tprod_eq

theorem dS_eq (S : Set (HeightOneSpectrum (𝓞 F))) (a : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    dS E S a (a + t) = ∏ k ∈ Finset.Icc (t + 1) (t + a), etaL E S k k ∧ dS E S a (a + t) ≠ 0 := by
  have hc : ∀ k ∈ Finset.Icc (t + 1) (t + a), Converges S (etaFam E k) k := fun k hk =>
    converges_etaFam S k (by
      have := (Finset.mem_Icc.1 hk).1
      rw [Complex.natCast_re]
      exact_mod_cast (by omega : 1 < k))
  have e : dS E S a (a + t) = ∏ k ∈ Finset.Icc (t + 1) (t + a), etaL E S k k := by
    rw [dS, dSfun, show (((a + t : ℕ) : ℂ) - a) / 2 = (t : ℂ) / 2 by push_cast; ring]
    simp only [dv_center]
    exact (hasProd_prod fun k hk => (hc k hk).hasProd).tprod_eq
  exact ⟨e, e ▸ Finset.prod_ne_zero_iff.2 fun k hk => (hc k hk).ne_zero⟩

end Ext

example : eulerFac {Units.mk0 2 two_ne_zero, (Units.mk0 2 two_ne_zero)⁻¹} (1 / 4) = 16 / 7 := by
  simp [eulerFac, eulerPoly]; norm_num

example {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : ℂˣ) : seg w x 1 = {x} := by
  have : npowU w 0 = 1 := Units.ext (by simp [npow])
  simp [seg, this]

example {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    ¬ Converges (K := K) ∅ (fun _ => {1}) 0 := fun h => h.1 w (by simp) (by simp [eulerPoly, npow])

end GlobalTheory.LFun

end
