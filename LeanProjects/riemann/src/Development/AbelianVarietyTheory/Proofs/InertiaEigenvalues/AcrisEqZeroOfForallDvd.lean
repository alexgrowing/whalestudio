import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPower
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

def InJ (w : Per.Ainf l) : Prop := ∃ c : Per.OC l, Per.θ l w = (l : Per.OC l) * c

def IsLogJ (w : Per.Ainf l) (y : Per.Acris l) : Prop :=
  ∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ s : Per.Acris0 l,
    ((n.factorial : ℕ) : Per.AinfP l) * (s : Per.AinfP l) =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) w) ^ (k + 1) ∧
    ∃ z : Per.Acris l, y - algebraMap (Per.Acris0 l) (Per.Acris l) s = ((l : ℕ) : Per.Acris l) ^ r * z

theorem isLogJ_zero : IsLogJ (0 : Per.Ainf l) 0 := fun _ => ⟨0, fun _ _ => ⟨0, by simp, 0, by simp⟩⟩

private theorem acris_eq_zero_of_forall_dvd (x : Per.Acris l)
    (h : ∀ r : ℕ, ∃ z : Per.Acris l, x = ((l : ℕ) : Per.Acris l) ^ r * z) : x = 0 := by
  refine IsHausdorff.haus (I := Ideal.span {((l : ℕ) : Per.Acris l)})
    (GlobalTheory.MemLoc.acris_basic l).1.toIsHausdorff x fun r => ?_
  obtain ⟨z, hz⟩ := h r
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

theorem isLogJ_unique {w : Per.Ainf l} {y y' : Per.Acris l} (h : IsLogJ w y) (h' : IsLogJ w y') :
    y = y' := by
  rw [← sub_eq_zero]
  refine acris_eq_zero_of_forall_dvd (y - y') fun r => ?_
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  obtain ⟨s, hs, z, hz⟩ := hN (max N N') (le_max_left _ _)
  obtain ⟨s', hs', z', hz'⟩ := hN' (max N N') (le_max_right _ _)
  have : s = s' := Subtype.ext
    ((GlobalTheory.RingBasics.isUnit_nat l _ (Nat.factorial_ne_zero _)).mul_left_cancel (hs.trans hs'.symm))
  subst this
  have key : y - y' = ((l : ℕ) : Per.Acris l) ^ r * (z - z') := by linear_combination hz - hz'
  exact ⟨z - z', key⟩

theorem isLogJ_extends {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) {w : Per.Ainf l} {y : Per.Acris l}
    (hy : IsLogJ w y) : IsLogJ (f w) (F y) := by
  intro r
  obtain ⟨N, hN⟩ := hy r
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs, z, hz⟩ := hN n hn
  refine ⟨⟨Per.extP f s, hf.mem _ s.2⟩, ?_, F z, ?_⟩
  · have := congrArg (Per.extP f) hs
    simpa only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, GlobalTheory.RingBasics.awayMap_algebraMap₂] using this
  · have := congrArg F hz
    rw [map_sub, map_mul, map_pow, map_natCast, hf.env] at this
    exact this

theorem inJ_mu {e : Per.Fl l} (he : e.untilt = 1) : InJ (mu e) :=
  ⟨0, by rw [Model.theta_mu, he, sub_self, mul_zero]⟩

theorem inJ_pow {e : Per.Fl l} (h : InJ (Per.tm e - 1)) (m : ℕ) : InJ (Per.tm (e ^ m) - 1) := by
  obtain ⟨c, hc⟩ := h
  have hθ : Per.θ l (Per.tm e) - 1 = (l : Per.OC l) * c := by rw [← hc, map_sub, map_one]
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (Per.θ l (Per.tm e)) 1 m
  refine ⟨c * d, ?_⟩
  have e1 : Per.tm (e ^ m) = Per.tm e ^ m := map_pow (WittVector.teichmuller l) e m
  rw [e1, map_sub, map_one, map_pow, ← one_pow m, hd, hθ, mul_assoc]

end GlobalTheory.LogU
