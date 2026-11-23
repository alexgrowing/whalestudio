import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn)

noncomputable section

section ResidueMap

variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω] {K : Type} {ι : K → Type}
  (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [hp : p.IsPrime]

open IndefiniteRowSideFullHecke.Kleiman2 (ResField residue resImage)

instance resField.isFractionRing : IsFractionRing (chartRingOver S y c ⧸ p) (ResField S y c p) :=
  inferInstanceAs (IsFractionRing (chartRingOver S y c ⧸ p) (FractionRing (chartRingOver S y c ⧸ p)))

omit hp in
theorem coe_ne_zero_of_notMem {b : (chartRingOver S y c)} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := Subtype.ext h
  rw [this]
  exact p.zero_mem

theorem mem_locIn_chart_iff {u : Ω} : u ∈ locIn (chartRingOver S y c) p ↔ ∃ a b : (chartRingOver S y c), b ∉ p ∧ u = (a : Ω) / b := by
  constructor
  · intro hu
    induction hu using Subring.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, 1, Ideal.one_notMem p, by simp⟩
    | one => exact ⟨1, 1, Ideal.one_notMem p, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      obtain ⟨a', b', hb', rfl⟩ := hy
      refine ⟨a * b' + b * a', b * b', hp.mul_notMem hb hb', ?_⟩
      rw [div_add_div _ _ (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')]
      simp
    | neg x _ hx =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      exact ⟨-a, b, hb, by simp [neg_div]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, hb, rfl⟩ := hx
      obtain ⟨a', b', hb', rfl⟩ := hy
      exact ⟨a * a', b * b', hp.mul_notMem hb hb', by simp [div_mul_div_comm]⟩
  · intro h
    exact Subring.subset_closure h

def resq (a : (chartRingOver S y c)) : ResField S y c p :=
  algebraMap (chartRingOver S y c ⧸ p) (ResField S y c p) (Ideal.Quotient.mk p a)

theorem resq_eq_zero_iff (a : (chartRingOver S y c)) : resq y c p a = 0 ↔ a ∈ p := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, resq]
  constructor
  · intro h
    exact IsFractionRing.injective (chartRingOver S y c ⧸ p) (ResField S y c p) (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

theorem resq_ne_zero {b : (chartRingOver S y c)} (hb : b ∉ p) : resq y c p b ≠ 0 :=
  fun h => hb ((resq_eq_zero_iff y c p b).mp h)

theorem resq_mul (a b : (chartRingOver S y c)) : resq y c p (a * b) = resq y c p a * resq y c p b := by
  simp [resq, map_mul]

theorem resq_add (a b : (chartRingOver S y c)) : resq y c p (a + b) = resq y c p a + resq y c p b := by
  simp [resq, map_add]

theorem resq_div_eq {a b a' b' : (chartRingOver S y c)} (hb : b ∉ p) (hb' : b' ∉ p) (h : (a : Ω) / b = (a' : Ω) / b') :
    resq y c p a / resq y c p b = resq y c p a' / resq y c p b' := by
  rw [div_eq_div_iff (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')] at h
  have h' : a * b' = a' * b := Subtype.ext (by simpa using h)
  rw [div_eq_div_iff (resq_ne_zero y c p hb) (resq_ne_zero y c p hb'), ← resq_mul, ← resq_mul, h']

theorem exists_rep (u : locIn (chartRingOver S y c) p) : ∃ a b : (chartRingOver S y c), b ∉ p ∧ (u : Ω) = (a : Ω) / b :=
  (mem_locIn_chart_iff y c p).mp u.2

def resFun (u : locIn (chartRingOver S y c) p) : ResField S y c p :=
  resq y c p (exists_rep y c p u).choose / resq y c p (exists_rep y c p u).choose_spec.choose

theorem resFun_eq (u : locIn (chartRingOver S y c) p) {a b : (chartRingOver S y c)} (hb : b ∉ p) (hu : (u : Ω) = a / b) :
    resFun y c p u = resq y c p a / resq y c p b := by
  obtain ⟨hb0, hu0⟩ := (exists_rep y c p u).choose_spec.choose_spec
  exact resq_div_eq y c p hb0 hb (hu0.symm.trans hu)

def resMap : locIn (chartRingOver S y c) p →+* ResField S y c p where
  toFun := resFun y c p
  map_one' := by
    rw [resFun_eq y c p 1 (a := 1) (b := 1) (Ideal.one_notMem p) (by simp)]
    simp [resq]
  map_mul' u v := by
    obtain ⟨a, b, hb, hu⟩ := exists_rep y c p u
    obtain ⟨a', b', hb', hv⟩ := exists_rep y c p v
    rw [resFun_eq y c p u hb hu, resFun_eq y c p v hb' hv,
      resFun_eq y c p (u * v) (a := a * a') (b := b * b') (hp.mul_notMem hb hb')
        (by simp [hu, hv, div_mul_div_comm]), resq_mul, resq_mul, div_mul_div_comm]
  map_zero' := by
    rw [resFun_eq y c p 0 (a := 0) (b := 1) (Ideal.one_notMem p) (by simp)]
    simp [resq]
  map_add' u v := by
    obtain ⟨a, b, hb, hu⟩ := exists_rep y c p u
    obtain ⟨a', b', hb', hv⟩ := exists_rep y c p v
    rw [resFun_eq y c p u hb hu, resFun_eq y c p v hb' hv,
      resFun_eq y c p (u + v) (a := a * b' + b * a') (b := b * b') (hp.mul_notMem hb hb') (by
        rw [Subring.coe_add, hu, hv,
          div_add_div _ _ (coe_ne_zero_of_notMem y c p hb) (coe_ne_zero_of_notMem y c p hb')]
        simp),
      div_add_div _ _ (resq_ne_zero y c p hb) (resq_ne_zero y c p hb'), resq_add, resq_mul, resq_mul, resq_mul]

theorem resMap_eq (u : locIn (chartRingOver S y c) p) {a b : (chartRingOver S y c)} (hb : b ∉ p) (hu : (u : Ω) = a / b) :
    resMap y c p u = resq y c p a / resq y c p b :=
  resFun_eq y c p u hb hu

theorem resMap_of_mem (a : (chartRingOver S y c)) (h : (a : Ω) ∈ locIn (chartRingOver S y c) p) : resMap y c p ⟨a, h⟩ = resq y c p a := by
  rw [resMap_eq y c p _ (a := a) (b := 1) (Ideal.one_notMem p) (by simp)]
  simp [resq]

theorem resMap_surjective : Function.Surjective (resMap y c p) := by
  intro z
  obtain ⟨x0, y0, hy0, rfl⟩ := IsFractionRing.div_surjective (A := chartRingOver S y c ⧸ p) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x0
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y0
  have hb : b ∉ p := by
    intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h
    rw [h] at hy0
    have : Nontrivial (chartRingOver S y c ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
    exact zero_notMem_nonZeroDivisors hy0
  refine ⟨⟨(a : Ω) / b, (mem_locIn_chart_iff y c p).mpr ⟨a, b, hb, rfl⟩⟩, ?_⟩
  rw [resMap_eq y c p _ hb rfl]
  rfl

theorem resMap_eq_zero_iff (u : locIn (chartRingOver S y c) p) : resMap y c p u = 0 ↔ ¬ IsUnit u := by
  obtain ⟨a, b, hb, hu⟩ := exists_rep y c p u
  constructor
  · intro h hu'
    exact (hu'.map (resMap y c p)).ne_zero h
  · intro h
    by_contra h0
    apply h
    rw [resMap_eq y c p u hb hu] at h0
    have ha : a ∉ p := fun ha => h0 (by rw [(resq_eq_zero_iff y c p a).mpr ha, zero_div])
    have ha0 := coe_ne_zero_of_notMem y c p ha
    have hb0 := coe_ne_zero_of_notMem y c p hb
    refine IsUnit.of_mul_eq_one ⟨(b : Ω) / a, (mem_locIn_chart_iff y c p).mpr ⟨b, a, ha, rfl⟩⟩ ?_
    apply Subtype.ext
    rw [Subring.coe_mul, hu, Subring.coe_one, div_mul_div_comm, mul_comm (a : Ω),
      div_self (mul_ne_zero hb0 ha0)]

theorem residue_of_mem (a : chartRingOver S y c) : residue S y c p a = resq y c p a := by
  unfold residue resq
  rw [dif_pos a.2]

theorem resMap_algebraMap (s : S) (h : algebraMap S Ω s ∈ locIn (chartRingOver S y c) p) :
    resMap y c p ⟨algebraMap S Ω s, h⟩ = algebraMap S (ResField S y c p) s := by
  have h' : ((algebraMap S (chartRingOver S y c) s : chartRingOver S y c) : Ω) ∈ locIn (chartRingOver S y c) p := h
  rw [show (⟨algebraMap S Ω s, h⟩ : locIn (chartRingOver S y c) p) = ⟨_, h'⟩ from rfl, resMap_of_mem, resq]
  rfl

theorem resImage_eq (z : Subring Ω) (hz : z ≤ locIn (chartRingOver S y c) p) :
    resImage S y c p z = {v | ∃ u : locIn (chartRingOver S y c) p, (u : Ω) ∈ z ∧ v = resMap y c p u} := by
  ext v
  constructor
  · rintro ⟨a, b, hb, habz, rfl⟩
    exact ⟨⟨_, hz habz⟩, habz, (resMap_eq y c p _ hb rfl).symm⟩
  · rintro ⟨u, huz, rfl⟩
    obtain ⟨a, b, hb, hu⟩ := exists_rep y c p u
    exact ⟨a, b, hb, hu ▸ huz, resMap_eq y c p u hb hu⟩

end ResidueMap

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
