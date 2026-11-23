import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNormOneOfPair
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem algebraMap_conjO (r : 𝓞 K) :
    algebraMap (𝓞 K) K (conjO K r) = star (algebraMap (𝓞 K) K r) := rfl

theorem conjO_conjO (r : 𝓞 K) : conjO K (conjO K r) = r :=
  _root_.Formalism.HermitianLattices.Ext.L3.conjO_conjO r

theorem mem_conjIdeal_iff (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    r ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p ↔ conjO K r ∈ p := by
  rw [conjIdeal_eq_comap, Ideal.mem_comap]

theorem conjIdeal_isPrime {p : Ideal (𝓞 K)} (hp : p.IsPrime) :
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p).IsPrime := by
  rw [conjIdeal_eq_comap]
  exact Ideal.comap_isPrime (conjO K) p

theorem hcompl_eq_closure (p : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) p = Submonoid.closure {s : 𝓞 K | s ∉ p ∧ conjO K s ∉ p} := by
  unfold Formalism.HermitianLatticesTheory.hcompl
  congr 1
  ext s
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 _ (algebraMap_conjO s)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    have : t = conjO K s := RingOfIntegers.ext ht
    rwa [this]

theorem mem_hcompl_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (s : 𝓞 K) :
    s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ↔ s ∉ p ∧ s ∉ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
  rw [hcompl_eq_closure, mem_conjIdeal_iff]
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one =>
      have h1 : (1 : 𝓞 K) ∉ p := (Ideal.ne_top_iff_one p).mp hp.ne_top
      exact ⟨h1, by rwa [map_one]⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · exact (hp.mem_or_mem h).elim ihx.1 ihy.1
      · rw [map_mul] at h
        exact (hp.mem_or_mem h).elim ihx.2 ihy.2
  · intro hs
    exact Submonoid.subset_closure hs

theorem conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    conjO K s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  rw [hcompl_eq_closure] at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    apply Submonoid.subset_closure
    exact ⟨hx.2, by rw [conjO_conjO]; exact hx.1⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_mem ihx ihy

theorem algebraMap_ne_zero_of_mem_hcompl {p : Ideal (𝓞 K)} (hp : p.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h0
  have hs0 : s = 0 := RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm)
  exact ((mem_hcompl_iff hp s).mp hs).1 (hs0 ▸ p.zero_mem)

theorem mem_locR_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) :
    a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ↔
      ∃ r : 𝓞 K, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
        a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by
  rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
  constructor
  · rintro ⟨s, hs, h1⟩
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp h1
    refine ⟨r, s, hs, ?_⟩
    rw [eq_div_iff (algebraMap_ne_zero_of_mem_hcompl hp hs), hr, mul_comm]
  · rintro ⟨r, s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [mul_div_cancel₀ _ (algebraMap_ne_zero_of_mem_hcompl hp hs)]
    exact Formalism.HermitianLatticesTheory.locDual_alg_mem r

def locRing (p : Ideal (𝓞 K)) : Subring K where
  carrier := {a | a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p}
  mul_mem' := by
    intro a b ha hb
    change a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at ha
    change b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p at hb
    change a * b ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR] at ha hb ⊢
    obtain ⟨s, hs, h1⟩ := ha
    obtain ⟨t, ht, h2⟩ := hb
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have e : algebraMap (𝓞 K) K (s * t) * (a * b) =
        (algebraMap (𝓞 K) K s * a) * (algebraMap (𝓞 K) K t * b) := by
      rw [map_mul]; ring
    rw [e]
    exact Formalism.HermitianLatticesTheory.locDual_one_mul h1 h2
  one_mem' := by
    change (1 : K) ∈ Formalism.HermitianLatticesTheory.locR (K := K) p
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, by rw [map_one, mul_one]; exact Submodule.one_le.mp le_rfl⟩
  add_mem' := fun ha hb => (Formalism.HermitianLatticesTheory.locR (K := K) p).add_mem ha hb
  zero_mem' := (Formalism.HermitianLatticesTheory.locR (K := K) p).zero_mem
  neg_mem' := fun ha => (Formalism.HermitianLatticesTheory.locR (K := K) p).neg_mem ha

theorem mem_locRing (p : Ideal (𝓞 K)) (a : K) :
    a ∈ locRing p ↔ a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := Iff.rfl

theorem algebraMap_mem_locRing (p : Ideal (𝓞 K)) (r : 𝓞 K) :
    algebraMap (𝓞 K) K r ∈ locRing p := by
  rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR]
  exact ⟨1, one_mem _, by rw [map_one, one_mul]; exact Formalism.HermitianLatticesTheory.locDual_alg_mem r⟩

theorem frac_locRing (p : Ideal (𝓞 K)) (a : K) : ∃ t ∈ locRing p, t ≠ 0 ∧ t * a ∈ locRing p := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) a
  refine ⟨algebraMap (𝓞 K) K s, algebraMap_mem_locRing p _, ?_, ?_⟩
  · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  · rw [mul_comm]
    change a * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K r at hrs
    rw [hrs]
    exact algebraMap_mem_locRing p r

theorem star_mem_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) :
    star a ∈ locRing p := by
  rw [mem_locRing, mem_locR_iff hp] at ha ⊢
  obtain ⟨r, s, hs, rfl⟩ := ha
  refine ⟨conjO K r, conjO K s, conjO_mem_hcompl hs, ?_⟩
  rw [algebraMap_conjO, algebraMap_conjO, star_div₀]

theorem isUnitIn_div_iff {p : Ideal (𝓞 K)} (hp : p.IsPrime) (r : 𝓞 K) {s : 𝓞 K}
    (hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p) :
    IsUnitIn (locRing p) (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) ↔
      r ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  constructor
  · rintro ⟨h0, -, hinv⟩
    have hr0 : algebraMap (𝓞 K) K r ≠ 0 := fun h => h0 (by rw [h, zero_div])
    rw [mem_locRing, Formalism.HermitianLatticesTheory.locDual_mem_locR] at hinv
    obtain ⟨u, hu, h1⟩ := hinv
    obtain ⟨v, hv⟩ := Submodule.mem_one.mp h1
    have e : u * s = v * r := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 K) K (u * s) = algebraMap (𝓞 K) K (v * r)
      rw [map_mul, map_mul, hv, inv_div]
      field_simp
    have hus := (mem_hcompl_iff hp _).mp (mul_mem hu hs)
    rw [e] at hus
    rw [mem_hcompl_iff hp]
    exact ⟨fun h => hus.1 (p.mul_mem_left v h), fun h => hus.2 (Ideal.mul_mem_left _ v h)⟩
  · intro hr
    have hr0 := algebraMap_ne_zero_of_mem_hcompl hp hr
    refine ⟨div_ne_zero hr0 hs0, ?_, ?_⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨r, s, hs, rfl⟩
    · rw [mem_locRing, mem_locR_iff hp]
      exact ⟨s, r, hr, inv_div _ _⟩

theorem unram_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    ∃ θ ∈ locRing p, IsUnitIn (locRing p) (θ - star θ) := by
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hp
  refine ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_locRing p θ, ?_⟩
  have hmem : θ - conjO K θ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    rw [mem_hcompl_iff hp.isPrime, mem_conjIdeal_iff]
    refine ⟨hθ, fun h => hθ ?_⟩
    rw [map_sub, conjO_conjO] at h
    have := p.neg_mem h
    rwa [neg_sub] at this
  have h := (isUnitIn_div_iff hp.isPrime (θ - conjO K θ)
    (one_mem (Formalism.HermitianLatticesTheory.hcompl (K := K) p))).mpr hmem
  rwa [map_one, div_one, map_sub, algebraMap_conjO] at h

end Formalism.HermitianLattices.Ext.L3.WA
