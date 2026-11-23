import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open UpperTheory.Gal.Int.Geo

private theorem unit_aux {A : Type} [CommRing A] {m c t t' s : A} (hm : m = c * t) (ht : t * t' = 1)
    (hs : m * s = 1) : c = 1 * (m * t') ∧ (m * t') * (t * s) = 1 := by
  constructor
  · rw [_root_.one_mul, hm, _root_.mul_assoc, ht, _root_.mul_one]
  · calc (m * t') * (t * s) = (m * s) * (t * t') := by ring
      _ = 1 := by rw [hs, ht, _root_.one_mul]

theorem UpperTheory.trace_unit_of_pullback_multiplier :
    TrBack → MultUnit → TrUnit := by
  intro hB hM p _ D G L R _ _ gb h X s N' N o' o ψ hT hh
  obtain ⟨ψ', -, e₁, e₂⟩ := hB p D G L R gb h X s N' N o' o ψ hT 1 (Nat.coprime_one_left p)
    (fun v hv => ⟨L.actG h⁻¹ v, integ_of_mem (inv_mem hh) v hv, by
      rw [one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩)
  have hiso : CategoryTheory.IsIso ψ := ⟨ψ', e₁.trans (pow_one _), e₂.trans (pow_one _)⟩
  refine ⟨hiso, ?_⟩
  obtain ⟨-, -, -, ⟨c, hc, hP, t, t', ht, ht', htt, hm⟩, -⟩ := hT
  obtain ⟨hu, hfix⟩ := hM p D G L
  obtain ⟨s', hi, hs, hs1⟩ := hu h hh
  obtain ⟨a₁, a₂⟩ := unit_aux hm htt hs1
  have hint : ∀ {a b : GlobalTheory.LKTrip.AfP p}, GlobalTheory.LKGeo.IsIntAf a → GlobalTheory.LKGeo.IsIntAf b → GlobalTheory.LKGeo.IsIntAf (a * b) := fun ha hb v => by
    rw [map_mul]; exact mul_mem (ha v) (hb v)
  have hc1 : c = 1 := hfix c 1 _ _ hc (Nat.coprime_one_left p) (hint hi ht') (hint ht hs) a₂
    (by rw [Nat.cast_one]; exact a₁)
  subst hc1
  exact hP
