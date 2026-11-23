import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AtPiEqRescale

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF expSum eq_of_low Gser)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

section ExpFormal

variable {K : Type} [Field K]

theorem th_expK_zero {ι : Type} : expK (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_expK, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h

theorem th_subst_expSum {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries σ K) (M : ℕ) : MvPowerSeries.subst a (expSum f M) = expSum (MvPowerSeries.subst a f) M := by
  rw [expSum, expSum, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]

theorem th_subst_expK {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (expK f) = expK (MvPowerSeries.subst a f) := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hsf : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 hf
  refine eq_of_low fun M => ?_
  have h1 := Formalism.DworkPowerSeriesWeights.low_subst_of_low ha0 (low_expK_sub hf M)
  have h2 := low_expK_sub hsf M
  have e : MvPowerSeries.subst a (expK f) - expK (MvPowerSeries.subst a f) =
      MvPowerSeries.subst a (expK f - expSum f M) -
        (expK (MvPowerSeries.subst a f) - expSum (MvPowerSeries.subst a f) M) := by
    rw [← th_subst_expSum ha, ← MvPowerSeries.coe_substAlgHom ha, map_sub]
    ring
  rw [e]
  exact low_sub h1 h2

theorem th_map_expK {ι K2 : Type} [Field K2] (φ : K →+* K2) (f : MvPowerSeries ι K) :
    MvPowerSeries.map φ (expK f) = expK (MvPowerSeries.map φ f) := by
  ext n
  rw [MvPowerSeries.coeff_map, coeff_expK, coeff_expK, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_inv₀, map_natCast, ← map_pow, MvPowerSeries.coeff_map]

end ExpFormal

section Param

variable (p : ℕ) [hp : Fact p.Prime]

def E0 {ι : Type} (f : MvPowerSeries ι (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ ∃ h : MvPowerSeries ι (WW p), MvPowerSeries.constantCoeff h = 0 ∧
    expK f = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) h

theorem integralExp_zero {ι : Type} : E0 p (0 : MvPowerSeries ι (K0 p)) := by
  refine ⟨map_zero _, 0, map_zero _, ?_⟩
  rw [th_expK_zero, map_zero, add_zero]

theorem integralExp_add {ι : Type} {f g : MvPowerSeries ι (K0 p)} (hf : E0 p f) (hg : E0 p g) : E0 p (f + g) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  obtain ⟨hg0, h', hh0', hge⟩ := hg
  refine ⟨by rw [map_add, hf0, hg0, add_zero], h + h' + h * h', by simp [hh0, hh0'], ?_⟩
  rw [expK_add hf0 hg0, hfe, hge, map_add, map_add, map_mul]
  ring

theorem integralExp_sum {ι α : Type} (s : Finset α) (f : α → MvPowerSeries ι (K0 p)) (h : ∀ a ∈ s, E0 p (f a)) :
    E0 p (∑ a ∈ s, f a) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact integralExp_zero p
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact integralExp_add p (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

def ren {κ σ R : Type} [CommRing R] (φ : κ → σ) (f : MvPowerSeries κ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ R)) f

theorem integralExp_rename {κ σ : Type} [Finite κ] (φ : κ → σ) {f : MvPowerSeries κ (K0 p)} (hf : E0 p f) :
    E0 p (ren φ f) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  have hXK : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have hXW : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have haW : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXW
  have haK : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXK
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero haK hXK hf0, ren φ h,
    MvPowerSeries.constantCoeff_subst_eq_zero haW hXW hh0, ?_⟩
  unfold ren
  rw [← th_subst_expK _ hXK hf0, hfe, ← MvPowerSeries.coe_substAlgHom haK, map_add, map_one,
    MvPowerSeries.coe_substAlgHom haK, MvPowerSeries.map_subst haW]
  simp only [MvPowerSeries.map_X]

theorem exp_neg_integral {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : E0 p f) :
    ∃ w : MvPowerSeries ι (WW p), expK (-f) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  refine ⟨MvPowerSeries.invOfUnit (1 + h) 1, ?_⟩
  have hinv : (1 + h) * MvPowerSeries.invOfUnit (1 + h) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by simp [hh0])
  have hneg : expK (-f) * expK f = 1 := by
    rw [← expK_add (by simp [hf0]) hf0, neg_add_cancel, th_expK_zero]
  calc expK (-f) = expK (-f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        ((1 + h) * MvPowerSeries.invOfUnit (1 + h) 1) := by rw [hinv, map_one, mul_one]
    _ = (expK (-f) * expK f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        (MvPowerSeries.invOfUnit (1 + h) 1) := by
      rw [hfe, map_mul, map_add, map_one]
      ring
    _ = _ := by rw [hneg, one_mul]

end Param

end Formalism.MainNotions.FormalGroupSystem.Pf
