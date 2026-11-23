import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.PeriodLowerBounds

noncomputable section

namespace GlobalTheory.Survey.PeriodBoundOfPlaceBound

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.PeriodLowerBounds
open scoped BigOperators

theorem vAdd_unit (D : D7) (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal) :
    vAdd (D.plEq w) (s : D.what₂.LL) = 0 := by
  have h1 : (D.plEq w).valuation D.what₂.LL (s : D.what₂.LL) = 1 := by
    have := (D.plEq w).valuation_of_algebraMap (K := D.what₂.LL) s
    rw [show (s : D.what₂.LL) = algebraMap (𝓞 D.what₂.LL) D.what₂.LL s from rfl, this]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
  unfold vAdd
  rw [h1]; simp

theorem exists_place (D : D7) (p : ℕ) (hp : p.Prime) : ∃ w : D.what₂.places.Pl, D.what₂.places.resChar w = p := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 D.what₂.LL) := by
    intro h
    have : IsUnit (algebraMap ℤ (𝓞 D.what₂.LL) (p : ℤ)) := by simpa using h
    have h2 := Int.isUnit_iff.1 (isUnit_of_map_unit (algebraMap ℤ (𝓞 D.what₂.LL)) _ this)
    have := hp.two_le
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 D.what₂.LL)}) (by
    rwa [Ne, Ideal.span_singleton_eq_top])
  have hpM : ((p : ℕ) : 𝓞 D.what₂.LL) ∈ M := hle (Ideal.subset_span rfl)
  have hne : M ≠ ⊥ := by
    rintro rfl
    have : ((p : ℕ) : 𝓞 D.what₂.LL) = 0 := hpM
    exact hp.ne_zero (by exact_mod_cast this)
  let v : HeightOneSpectrum (𝓞 D.what₂.LL) := ⟨M, hM.isPrime, hne⟩
  refine ⟨D.plEq.symm v, ?_⟩
  set w := D.plEq.symm v with hw
  have hv : D.plEq w = v := by simp [hw]
  by_contra hq
  have hq' := D.what₂.places.resChar_prime w
  have hnot : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal := by
    rw [hv]
    intro hin
    have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq' hp).2 hq)
    obtain ⟨a, b, hab⟩ := hc
    apply hM.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 D.what₂.LL) = (a : 𝓞 D.what₂.LL) * (D.what₂.places.resChar w : ℕ) + (b : 𝓞 D.what₂.LL) * (p : ℕ) := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.what₂.LL) hab.symm
    rw [this]
    exact M.add_mem (M.mul_mem_left _ hin) (M.mul_mem_left _ hpM)
  have h0 := vAdd_unit D w _ hnot
  have h1 := D.what₂.places.val_resChar w
  rw [D.val_eq w _ (Nat.cast_ne_zero.2 hq'.ne_zero)] at h1
  have h2 : vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℕ) := by
    exact_mod_cast h1
  have h3 : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    simp
  rw [h3, h2] at h0
  have := D.what₂.places.ramIdx_pos w
  omega

end GlobalTheory.Survey.PeriodBoundOfPlaceBound

end
