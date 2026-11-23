import Formalism.GaussJetBounds.FrameJetEval

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds MvPowerSeries

namespace Transfer

section Maps

variable {F K : Type} [Field F] [Field K] (φ : F →+* K) {d : ℕ}

theorem map_substZero (s : ZMod d) : map φ (s0 (K := F) s) = s0 s := by
  simp [s0]
theorem map_substOne (s : ZMod d) : map φ (s1 (K := F) s) = s1 s := by
  unfold s1
  split_ifs <;> simp
theorem map_substTwo (s : ZMod d) : map φ (s2 (K := F) s) = s2 s := by
  unfold s2
  split_ifs <;> simp
theorem map_substOne' (s : ZMod d) : map φ (s1' (K := F) s) = s1' s := by
  unfold s1'
  split_ifs <;> simp
theorem map_substTwo' (s : ZMod d) : map φ (s2' (K := F) s) = s2' s := by
  unfold s2'
  split_ifs <;> simp

theorem constantCoeff_substZero (s : ZMod d) : constantCoeff (s0 (K := F) s) = 0 := by
  simp [s0]
theorem constantCoeff_substOne (s : ZMod d) : constantCoeff (s1 (K := F) s) = 0 := by
  unfold s1
  split_ifs <;> simp
theorem constantCoeff_substTwo (s : ZMod d) : constantCoeff (s2 (K := F) s) = 0 := by
  unfold s2
  split_ifs <;> simp
theorem constantCoeff_substOne' (s : ZMod d) : constantCoeff (s1' (K := F) s) = 0 := by
  unfold s1'
  split_ifs <;> simp
theorem constantCoeff_substTwo' (s : ZMod d) : constantCoeff (s2' (K := F) s) = 0 := by
  unfold s2'
  split_ifs <;> simp

theorem map_torus (l : ℕ) (ζ : F) (s : ZMod d) :
    map φ (torus l ζ s) = torus l (φ ζ) s := by
  simp [torus]

theorem cc_torus (l : ℕ) (ζ : F) (s : ZMod d) : constantCoeff (torus l ζ s) = 0 := by
  simp [torus]

theorem map_letterLog (l : ℕ) (x : V2 d) :
    map φ (letterLog (K := F) l x) = letterLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (letterLog (K := F) l x n) = letterLog (K := K) l x n
  simp only [letterLog]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

theorem cc_letterLog (l : ℕ) (x : V2 d) : constantCoeff (letterLog (K := F) l x) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change letterLog (K := F) l x 0 = 0
  simp only [letterLog]
  refine Finset.sum_eq_zero fun e he => ?_
  have he0 : e = 0 := by simpa using he
  subst he0
  rw [if_neg]
  intro h
  have h1 := Finsupp.single_eq_zero.mp h.symm
  simp at h1

theorem map_entLog {N0 N1 : ℕ} (l : ℕ) (x : ZV d N0 N1) :
    map φ (entLog (K := F) l x) = entLog l x := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (entLog (K := F) l x n) = entLog (K := K) l x n
  simp only [entLog]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

variable [NeZero d]

theorem map_defectOne (be : MvPowerSeries (ZMod d) F) : map φ (de1 be) = de1 (map φ be) := by
  have hs : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.map φ (MvPowerSeries.subst a be) =
        MvPowerSeries.subst (fun s => MvPowerSeries.map φ (a s)) (MvPowerSeries.map φ be) :=
    fun a ha => MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) be
  unfold de1
  rw [map_sub, map_sub, hs s1 constantCoeff_substOne, hs s0 constantCoeff_substZero, hs s2 constantCoeff_substTwo]
  simp only [map_substOne, map_substZero, map_substTwo]

theorem map_defectTwo (be : MvPowerSeries (ZMod d) F) : map φ (de2 be) = de2 (map φ be) := by
  have hs : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.map φ (MvPowerSeries.subst a be) =
        MvPowerSeries.subst (fun s => MvPowerSeries.map φ (a s)) (MvPowerSeries.map φ be) :=
    fun a ha => MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) be
  unfold de2
  rw [map_sub, map_sub, hs s1' constantCoeff_substOne', hs s0 constantCoeff_substZero, hs s2' constantCoeff_substTwo']
  simp only [map_substOne', map_substZero, map_substTwo']

theorem constantCoeff_defectOne {be : MvPowerSeries (ZMod d) F} (h : constantCoeff be = 0) :
    constantCoeff (de1 be) = 0 := by
  have hz : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a be) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha h
  unfold de1
  rw [map_sub, map_sub, hz s1 constantCoeff_substOne, hz s0 constantCoeff_substZero, hz s2 constantCoeff_substTwo]
  simp

theorem constantCoeff_defectTwo {be : MvPowerSeries (ZMod d) F} (h : constantCoeff be = 0) :
    constantCoeff (de2 be) = 0 := by
  have hz : ∀ (a : ZMod d → MvPowerSeries (V2 d) F), (∀ s, MvPowerSeries.constantCoeff (a s) = 0) →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst a be) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha h
  unfold de2
  rw [map_sub, map_sub, hz s1' constantCoeff_substOne', hz s0 constantCoeff_substZero, hz s2' constantCoeff_substTwo']
  simp

theorem cc_of_noLow {be : MvPowerSeries (ZMod d) F} (h : NoLowBidegree be) :
    constantCoeff be = 0 := by
  by_contra hc
  have h0 := (h 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])).1
  simp [degE] at h0

end Maps

section Normed

variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)

theorem map_mvExp {ι : Type} {f : MvPowerSeries ι F} (h : constantCoeff f = 0) :
    map φ (mvExp f) = mvExp (map φ f) := by
  unfold mvExp
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h), PowerSeries.map_exp]

theorem integral_map (hφ : ∀ z, ‖φ z‖ = ‖z‖) {ι : Type} {U : MvPowerSeries ι F}
    (h : Integral U) : Integral (map φ U) := by
  intro n
  rw [MvPowerSeries.coeff_map, hφ]
  exact h n

theorem map_logExp {d : ℕ} [NeZero d] (l : ℕ) {f : MvPowerSeries (V2 d) F}
    (h : constantCoeff f = 0) :
    map φ (subst (letterLog (K := F) l) (mvExp f)) =
      subst (letterLog (K := K) l) (mvExp (map φ f)) := by
  have hL : ∀ x : V2 d, MvPowerSeries.constantCoeff (letterLog (K := F) l x) = 0 := cc_letterLog l
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hL), map_mvExp φ h]
  congr 1
  funext x
  exact map_letterLog φ l x

end Normed

end Transfer

open Transfer in
theorem admissibleTransfer : TransferB := by
  intro F K _ _ _ _ φ hφ l d N0 N1 _ K0 ζ be
  refine ⟨?_, ?_, ?_, fun U hU => integral_map φ hφ hU⟩
  · intro hU a ha ha0
    obtain ⟨b, hb, rfl⟩ := Subfield.mem_map.mp ha
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at ha0
    obtain ⟨k, hk⟩ := hU b hb hb0
    exact ⟨k, by rw [hφ, hk, ← map_natCast φ l, hφ]⟩
  · rintro ⟨h1, h2, h3, ⟨h4, h5⟩, ⟨h6, h7⟩⟩
    have hcc : MvPowerSeries.constantCoeff be = 0 := cc_of_noLow h3
    have E1 : MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de1 (MvPowerSeries.map φ be))) =
        MvPowerSeries.map φ (MvPowerSeries.subst (letterLog (K := F) l) (mvExp (de1 be))) := by
      rw [← map_defectOne, map_logExp φ l (constantCoeff_defectOne hcc)]
    have E2 : MvPowerSeries.subst (letterLog (K := K) l) (mvExp (de2 (MvPowerSeries.map φ be))) =
        MvPowerSeries.map φ (MvPowerSeries.subst (letterLog (K := F) l) (mvExp (de2 be))) := by
      rw [← map_defectTwo, map_logExp φ l (constantCoeff_defectTwo hcc)]
    have hcm : ∀ G : MvPowerSeries (V2 d) F,
        MvPowerSeries.constantCoeff (MvPowerSeries.map φ G) = φ (MvPowerSeries.constantCoeff G) := by
      intro G
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    refine ⟨fun n => ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [MvPowerSeries.coeff_map]
      exact Subfield.mem_map.mpr ⟨_, h1 n, rfl⟩
    · have ht : ∀ s : ZMod d, MvPowerSeries.constantCoeff (torus l ζ s) = 0 := fun s => cc_torus l ζ s
      have := congrArg (MvPowerSeries.map φ) h2
      rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ht)] at this
      simpa only [map_torus] using this
    · intro n hn
      rw [MvPowerSeries.coeff_map] at hn
      exact h3 n (fun h0 => hn (by rw [h0, map_zero]))
    · rw [E1]
      exact integral_map φ hφ h4
    · rw [E1, hcm, h5, map_one]
    · rw [E2]
      exact integral_map φ hφ h6
    · rw [E2, hcm, h7, map_one]
  · intro g hg hgs
    refine ⟨fun y => ?_, fun y => ?_⟩
    · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg y, map_zero]
    · have := congrArg (MvPowerSeries.map φ) (hgs y)
      rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg), map_entLog,
        MvPowerSeries.map_X] at this
      exact this

end Formalism.DworkPowerSeriesWeights
