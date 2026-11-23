import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowSubMem

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.PlaceDataValuations

private theorem int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
    A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem isUnit_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : Ow w) :
    IsUnit a ↔ w.valuation E (a : E) = 1 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    have h1 : w.valuation E (a : E) * w.valuation E (b : E) = 1 := by
      rw [← map_mul]
      have : ((a : E) * (b : E)) = 1 := congrArg Subtype.val hb
      rw [this, map_one]
    have ha : w.valuation E (a : E) ≤ 1 := a.2
    have hb' : w.valuation E (b : E) ≤ 1 := b.2
    refine le_antisymm ha (not_lt.1 fun hlt => ?_)
    have := mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt hb'
    rw [h1] at this
    exact lt_irrefl _ this
  · intro h
    have h0 : (a : E) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h
      exact zero_ne_one h
    have hi : w.valuation E (a : E)⁻¹ ≤ 1 := by
      rw [map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one (⟨(a : E)⁻¹, hi⟩ : Ow w) (Subtype.ext (mul_inv_cancel₀ h0))

private theorem mem_max_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : Ow w) :
    a ∈ IsLocalRing.maximalIdeal (Ow w) ↔ w.valuation E (a : E) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  have ha : w.valuation E (a : E) ≤ 1 := a.2
  exact ⟨fun h => lt_of_le_of_ne ha h, fun h => h.ne⟩

private theorem pow_sub_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    x ^ Ideal.absNorm w.asIdeal - x ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk67.pow_sub_mem w x

end UpperTheory.Gal.Mod.PlaceDataValuations

open UpperTheory.Gal.Mod.PlaceDataValuations in
theorem UpperTheory.Gal.Mod.placeData :
    PlaceData := by
  intro E Ω _ _ _ _ _ w A hA
  have hle : ∀ y : 𝓞 E, A.valuation (algebraMap E Ω (y : E)) ≤ 1 := fun y =>
    int_le A (y.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom)
  have h1 : ∀ y : 𝓞 E, y ∉ w.asIdeal → A.valuation (algebraMap E Ω (y : E)) = 1 := fun y hy =>
    le_antisymm (hle y) (not_lt.1 fun hh => hy ((hA y).1 hh))
  have key : ∀ x : E, w.valuation E x ≤ 1 → ∃ c s : 𝓞 E, s ∉ w.asIdeal ∧ x * (s : E) = (c : E) := by
    intro x hx
    obtain ⟨c, s, hs⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨c, s, s.2, hs⟩
  have hval : ∀ (x : E) (c s : 𝓞 E), s ∉ w.asIdeal → x * (s : E) = (c : E) →
      A.valuation (algebraMap E Ω x) = A.valuation (algebraMap E Ω (c : E)) := by
    intro x c s hs he
    rw [← he, map_mul, map_mul, h1 s hs, mul_one]
  have hws : ∀ s : 𝓞 E, s ∉ w.asIdeal → w.valuation E (s : E) = 1 := fun s hs =>
    w.valuation_eq_one_iff_notMem.2 hs
  have hwm : ∀ c : 𝓞 E, c ∈ w.asIdeal → w.valuation E (c : E) < 1 := fun c hc =>
    (w.valuation_lt_one_iff_mem c).2 hc
  let ι : 𝓞 E →+* Ow w :=
    { toFun := fun x => ⟨(x : E), w.valuation_le_one x⟩
      map_one' := Subtype.ext (map_one (algebraMap (𝓞 E) E))
      map_mul' := fun a b => Subtype.ext (map_mul (algebraMap (𝓞 E) E) a b)
      map_zero' := Subtype.ext (map_zero (algebraMap (𝓞 E) E))
      map_add' := fun a b => Subtype.ext (map_add (algebraMap (𝓞 E) E) a b) }
  have hιm : ∀ c : 𝓞 E, c ∈ w.asIdeal → IsLocalRing.residue (Ow w) (ι c) = 0 := fun c hc =>
    (IsLocalRing.residue_eq_zero_iff _).2 ((mem_max_iff w _).2 (hwm c hc))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨c, s, hs, he⟩ := key _ a.2
    have : A.valuation (algebraMap E Ω (algebraMap (Ow w) E a)) ≤ 1 := by
      rw [hval (algebraMap (Ow w) E a) c s hs he]
      exact hle c
    exact (A.valuation_le_one_iff _).1 this
  · intro a ha
    obtain ⟨c, s, hs, he⟩ := key _ a.2
    rw [hval (algebraMap (Ow w) E a) c s hs he]
    refine (hA c).2 ?_
    have h2 : w.valuation E (a : E) < 1 := (mem_max_iff w a).1 ha
    have h3 : w.valuation E (c : E) < 1 := by
      rw [← he, map_mul, hws s hs, mul_one]
      exact h2
    exact (w.valuation_lt_one_iff_mem c).1 h3
  · intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨c, s, hs, he⟩ := key _ b.2
    obtain ⟨s', i, hi, hs'⟩ := w.isMaximal.exists_inv hs
    have hb : IsLocalRing.residue (Ow w) b = IsLocalRing.residue (Ow w) (ι (s' * c)) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
      have h2 : ((b - ι (s' * c) : Ow w) : E) * (s : E) = ((c * i : 𝓞 E) : E) := by
        have h3 : ((ι (s' * c) : Ow w) : E) = (s' : E) * (c : E) := by
          simp [ι]
        have h4 : (s' : E) * (s : E) + (i : E) = 1 := by
          exact_mod_cast congrArg (algebraMap (𝓞 E) E) hs'
        have h5 : (b : E) * (s : E) = (c : E) := he
        push_cast
        rw [h3, sub_mul, h5]
        linear_combination (-(c : E)) * h4
      have h6 := hwm _ (w.asIdeal.mul_mem_left c hi)
      rw [← h2, map_mul, hws s hs, mul_one] at h6
      exact h6
    rw [hb, ← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, ← map_sub]
    exact hιm _ (pow_sub_mem w _)
  · rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro m hm
    simpa using h1 (m : 𝓞 E) hm
  · intro m hm hu
    have h2 := (isUnit_iff w (m : Ow w)).1 hu
    have hc : ((m : Ow w) : E) = ((m : 𝓞 E) : E) := by simp
    rw [hc] at h2
    exact (hwm _ hm).ne h2
  · intro s hs
    exact ⟨fun v hv => (apply_mem_iff_of_mem_Dec hs.1 v).2 hv,
      fun v hv => hs.2 v ((A.valuation_le_one_iff v).2 hv)⟩
  · intro q σ hσ
    exact ⟨fun v hv => (apply_mem_iff_of_mem_Dec hσ.1 v).2 hv,
      fun v hv => hσ.2 v ((A.valuation_le_one_iff v).2 hv)⟩
