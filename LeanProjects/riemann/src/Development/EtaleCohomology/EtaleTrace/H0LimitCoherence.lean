import Development.EtaleCohomology.EtaleTrace.TorsionH0PointAndSections

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.H0LimitCoherence
open LateralTheory.EtaleTrace

variable (l : ℕ) [Fact l.Prime]

def Coh : Subring (∀ m : ℕ, ZMod (l ^ m)) where
  carrier := {x | ∀ a b (h : a ≤ b), ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ a)) (x b) = x a}
  one_mem' a b h := map_one _
  mul_mem' {u v} hu hv a b h := by simp only [Pi.mul_apply, map_mul]; rw [hu a b h, hv a b h]
  zero_mem' a b h := map_zero _
  add_mem' {u v} hu hv a b h := by simp only [Pi.add_apply, map_add]; rw [hu a b h, hv a b h]
  neg_mem' {u} hu a b h := by simp only [Pi.neg_apply, map_neg]; rw [hu a b h]

def toZl : Coh l →+* ℤ_[l] :=
  PadicInt.lift (f := fun a => (Pi.evalRingHom (fun m : ℕ => ZMod (l ^ m)) a).comp (Coh l).subtype)
    (fun a b h => RingHom.ext fun x => x.2 a b h)

theorem toZModPow_toZl (x : Coh l) (m : ℕ) : PadicInt.toZModPow m (toZl l x) = x.1 m :=
  RingHom.congr_fun (PadicInt.lift_spec _ m) x

theorem coh_of_succ (x : ∀ m : ℕ, ZMod (l ^ m))
    (h : ∀ m, ZMod.castHom (pow_dvd_pow l (Nat.le_succ m)) (ZMod (l ^ m)) (x (m + 1)) = x m) : x ∈ Coh l := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => simp [ZMod.castHom_apply, ZMod.cast_id']
  | succ n hn ih => rw [← ih, ← h n, ← RingHom.comp_apply, ZMod.castHom_comp]

theorem tensor_form {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (z : ℚ_[l] ⊗[ℤ_[l]] M) :
    ∃ (b : ℤ_[l]) (x : M), b ≠ 0 ∧ z = ((b : ℚ_[l]))⁻¹ ⊗ₜ x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q m =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) q
    refine ⟨b, a • m, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    try simp [div_eq_mul_inv, mul_comm]
  | add z z' ih ih' =>
    obtain ⟨b, x, hb, rfl⟩ := ih
    obtain ⟨b', x', hb', rfl⟩ := ih'
    have h1 : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
    have h2 : (b' : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
    refine ⟨b * b', b' • x + b • x', mul_ne_zero hb hb', ?_⟩
    rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def]
    congr 2 <;> simp <;> field_simp

variable {l}

abbrev lv {E : Spc} {n i : ℤ} (x : Hl l E n i) (j : ℕ) : Ht (l ^ j) E n i := x.1 j

theorem rep_of {E : Spc} (ω : Hl l E 0 0)
    (hgen : ∀ j (z : Ht (l ^ j) E 0 0), ∃ a : ℕ, z = a • lv ω j)
    (hord : ∀ j (a : ℕ), a • lv ω j = 0 → l ^ j ∣ a) :
    (∀ x : Hl l E 0 0, ∃ c : ℤ_[l], x = c • ω) ∧ ∀ c : ℤ_[l], c • ω = 0 → c = 0 := by
  have key : ∀ j (s s' : ZMod (l ^ j)), s • lv ω j = s' • lv ω j → s = s' := by
    intro j s s' h
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have h0 : (s - s').val • lv ω j = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val, sub_smul, h, sub_self]
    obtain ⟨t, ht⟩ := hord j _ h0
    have : (((s - s').val : ℕ) : ZMod (l ^ j)) = 0 := by rw [ht, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [ZMod.natCast_zmod_val] at this
    exact sub_eq_zero.1 this
  have gen : ∀ j (z : Ht (l ^ j) E 0 0), ∃ s : ZMod (l ^ j), z = s • lv ω j := by
    intro j z
    obtain ⟨a, ha⟩ := hgen j z
    exact ⟨a, by rw [Nat.cast_smul_eq_nsmul]; exact ha⟩
  have redω : ∀ j (s : ZMod (l ^ (j + 1))), red (l ^ (j + 1)) (l ^ j) E 0 0 (s • lv ω (j + 1)) =
      (ZMod.castHom (pow_dvd_pow l (Nat.le_succ j)) (ZMod (l ^ j)) s) • lv ω j := by
    intro j s
    haveI : NeZero (l ^ (j + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    conv_lhs => rw [← ZMod.natCast_zmod_val s, Nat.cast_smul_eq_nsmul]
    rw [map_nsmul, ZMod.castHom_apply, ZMod.cast_eq_val, Nat.cast_smul_eq_nsmul]
    exact congrArg (s.val • ·) (ω.2 j)
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · choose s hs using fun j => gen j (lv x j)
    have hc : s ∈ Coh l := coh_of_succ l s fun j => key j _ _ (by
      rw [← redω, ← hs (j + 1), ← hs j]; exact x.2 j)
    refine ⟨toZl l ⟨s, hc⟩, Subtype.ext (funext fun j => ?_)⟩
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    change lv x j = (toZl l ⟨s, hc⟩) • (ω.1 j : HtL l j E 0 0)
    rw [HtL.smul_eq l j j le_rfl, toZModPow_toZl]
    change lv x j = (s j).val • lv ω j
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val]
    exact hs j
  · refine PadicInt.ext_of_toZModPow.mp fun j => ?_
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [map_zero]
    refine key j _ _ ?_
    have h1 : (c • ω).1 j = (0 : Hl l E 0 0).1 j := by rw [hc]
    change c • (ω.1 j : HtL l j E 0 0) = 0 at h1
    rw [HtL.smul_eq l j j le_rfl] at h1
    change (PadicInt.toZModPow j c).val • lv ω j = 0 at h1
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val] at h1
    rw [h1, zero_smul]

end LateralTheory.EtaleTrace.H0LimitCoherence

namespace LateralTheory.EtaleTrace

end LateralTheory.EtaleTrace
