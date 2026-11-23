import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TwoSumsCondition
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF altF)

variable {p : ℕ} [hp : Fact p.Prime]

theorem sx_dual_even {n' : ℕ} (B : OmBasis p n') (i i' : Fin (n' / 2)) :
    ∑ r, (sigW p)^[2 * i.val] (B.omS r) * (sigW p)^[2 * i'.val] (B.om r) = if i = i' then 1 else 0 := by
  classical
  have hAB : (Matrix.of fun (r j : Fin (n' / 2)) => (sigW p)^[2 * j.val] (B.om r)) *
      (Matrix.of fun (j r' : Fin (n' / 2)) => (sigW p)^[2 * j.val] (B.omS r')) = 1 := by
    refine Matrix.ext fun r r' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply, ← B.dual r r']
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.of_apply, Matrix.of_apply, iterate_map_mul]
  have hBA := mul_eq_one_comm.mp hAB
  have h := congrFun (congrFun hBA i) i'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa using h

theorem sx_dual {n' : ℕ} (B : OmBasis p n') (hev : Even n') (a b : Fin n') (hab : a.val % 2 = b.val % 2) :
    ∑ r, (sigW p)^[a.val] (B.omS r) * (sigW p)^[b.val] (B.om r) = if a = b then 1 else 0 := by
  classical
  obtain ⟨k, hk⟩ := hev
  have ha := a.isLt
  have hb := b.isLt
  let i : Fin (n' / 2) := ⟨a.val / 2, by omega⟩
  let i' : Fin (n' / 2) := ⟨b.val / 2, by omega⟩
  have hE := sx_dual_even B i i'
  have hii : (i = i') ↔ (a = b) := by
    simp only [i, i', Fin.ext_iff]
    constructor
    · intro h
      omega
    · intro h
      rw [h]
  rcases Nat.mod_two_eq_zero_or_one a.val with h0 | h1
  · have e1 : (sigW p)^[a.val] = (sigW p)^[2 * i.val] := by
      congr 1
      show a.val = 2 * (a.val / 2)
      omega
    have e2 : (sigW p)^[b.val] = (sigW p)^[2 * i'.val] := by
      congr 1
      show b.val = 2 * (b.val / 2)
      omega
    rw [e1, e2, hE]
    by_cases h : a = b
    · rw [if_pos h, if_pos (hii.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hii.mp h'))]
  · have e1 : (sigW p)^[a.val] = (sigW p) ∘ (sigW p)^[2 * i.val] := by
      rw [← Function.iterate_succ']
      congr 1
      show a.val = 2 * (a.val / 2) + 1
      omega
    have e2 : (sigW p)^[b.val] = (sigW p) ∘ (sigW p)^[2 * i'.val] := by
      rw [← Function.iterate_succ']
      congr 1
      show b.val = 2 * (b.val / 2) + 1
      omega
    rw [e1, e2]
    simp only [Function.comp_apply]
    have hsig : ∑ r, sigW p ((sigW p)^[2 * i.val] (B.omS r)) * sigW p ((sigW p)^[2 * i'.val] (B.om r)) =
        sigW p (∑ r, (sigW p)^[2 * i.val] (B.omS r) * (sigW p)^[2 * i'.val] (B.om r)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun r _ => (map_mul _ _ _).symm
    rw [hsig, hE]
    by_cases h : a = b
    · rw [if_pos h, if_pos (hii.mpr h), map_one]
    · rw [if_neg h, if_neg (fun h' => h (hii.mp h')), map_zero]

theorem sx_iter_posAdd {n' : ℕ} (x : WW p) (hx : (sigW p)^[n'] x = x) (s : Fin n') (e : ℕ) :
    (sigW p)^[(posAdd s e).val] x = (sigW p)^[s.val + e] x := by
  exact Function.IsPeriodicPt.iterate_mod_apply hx (s.val + e)

theorem frobenius_congruence_witt (a : WW p) : ∃ y : WW p, sigW p a = a ^ p + p * y := by
  obtain ⟨y, hy⟩ := Formalism.InvariantFactorPaths.G7.WModel.frob_sub_pow p a
  exact ⟨y, by unfold sigW; linear_combination hy⟩

theorem sx_lift {ι K' : Type} [Field K'] {R : Subring K'} {f : MvPowerSeries ι K'} (hf : IntR R f) :
    ∃ f0 : MvPowerSeries ι R, MvPowerSeries.map R.subtype f0 = f := by
  refine ⟨fun m => ⟨MvPowerSeries.coeff m f, hf m⟩, ?_⟩
  ext m
  rfl

theorem sx_sum_pow {A α : Type} [CommRing A] (s : Finset α) (x : α → A) :
    ∃ r : A, (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + (p : A) * r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [zero_pow hp.out.ne_zero]⟩
  | insert a s ha ih =>
    obtain ⟨r1, hr1⟩ := ih
    obtain ⟨r2, hr2⟩ := exists_add_pow_prime_eq hp.out (x a) (∑ i ∈ s, x i)
    refine ⟨r1 + x a * (∑ i ∈ s, x i) * r2, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr2, hr1]
    ring

theorem sx_frob_sum {ι α K' : Type} [Field K'] (R : Subring K') (s : Finset α) (x : α → MvPowerSeries ι K')
    (hx : ∀ i ∈ s, IntR R (x i)) :
    ∃ Y, IntR R Y ∧ (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + MvPowerSeries.C (p : K') * Y := by
  classical
  have hlift : ∀ i ∈ s, ∃ f0 : MvPowerSeries ι R, MvPowerSeries.map R.subtype f0 = x i :=
    fun i hi => sx_lift (hx i hi)
  choose y hy using hlift
  let y' : α → MvPowerSeries ι R := fun i => if h : i ∈ s then y i h else 0
  obtain ⟨r, hr⟩ := sx_sum_pow (p := p) s y'
  refine ⟨MvPowerSeries.map R.subtype r, fun n => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n r).2
  · have hsum : ∀ i ∈ s, MvPowerSeries.map R.subtype (y' i) = x i := fun i hi => by
      simp only [y', dif_pos hi]
      exact hy i hi
    have h2 := congrArg (MvPowerSeries.map R.subtype) hr
    simp only [map_pow, map_sum, map_add, map_mul, map_natCast] at h2
    have e3 : ∑ i ∈ s, (MvPowerSeries.map R.subtype (y' i)) ^ p = ∑ i ∈ s, x i ^ p :=
      Finset.sum_congr rfl fun i hi => by rw [hsum i hi]
    rw [Finset.sum_congr rfl hsum, e3] at h2
    rw [h2, map_natCast]

end Formalism.MainNotions.FormalGroupSystem.Pf
