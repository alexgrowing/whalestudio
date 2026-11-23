import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.SchPhiOneApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SchSharp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CFCoreA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Sch

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

omit [NormedAddCommGroup M] [InnerProductSpace ℂ M] in

theorem two_lt_of_gap {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ} (hbig : 2 * (n : ℝ) < h) : 2 < h := by
  have hab : a ≠ b := fun e => hε (by rw [e])
  have ha := a.isLt
  have hb := b.isLt
  have hv : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  linarith

theorem khw_eq_zero_sharp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) (h2 : 2 < h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b)
    {T : Submodule ℂ M} (hTf : FiniteDimensional ℂ T) (hTk : IsKStableSub ε E T)
    (hTc : ∀ v ∈ T, casimir E v = (casVal lam : ℂ) • v) {y : M} (hyT : y ∈ T)
    (hy : IsKHWVec ε E (lowK ε lam - root a b) y) : y = 0 := by
  by_contra hy0
  have hle := kLowSpan_le (E := E) hTk hyT
  have hfin : FiniteDimensional ℂ (kLowSpan ε E y) := Submodule.finiteDimensional_of_le hle
  exact sch_sharp hmono hh h2 hE hU hab hε (kLowSpan_kIrrHW hE hU hy hy0 hfin)
    (fun v hv => hTc v (hle hv))

theorem phi_one_Wm (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) : phi E 1 x = 0 := by
  by_contra hne
  have := finiteDimensional_ncV (ε := ε) hV.1 1
  have hfdW : FiniteDimensional ℂ (Wm ε E V) := Submodule.finiteDimensional_of_le Wm_le_ncV
  have hWst : IsKStableSub ε (bAct E 1) (Wm ε E V) := Wm_kStable hE hU hV
  set T : Submodule ℂ M := (Wm ε E V).map (phi E 1) with hTdef
  have hfdT : FiniteDimensional ℂ T := inferInstance
  have hTst : IsKStableSub ε E T := by
    intro a b hab v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
    rw [← phi_bAct hE 1 hab y]
    exact Submodule.mem_map_of_mem (hWst a b hab y hy)
  have hTne : T ≠ ⊥ := by
    intro hT
    have : phi E 1 x ∈ T := Submodule.mem_map_of_mem hx
    rw [hT, Submodule.mem_bot] at this
    exact hne this
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  obtain ⟨y, hyT, hy0, μ, hyμ⟩ := exists_khw hE hKU hfdT hTst hTne
  obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hyT
  obtain ⟨x1, hx1, -, hkhw, hfx⟩ := lift_khw (A := bAct E 1) (bAct_isKUnitary hU 1) (phi E 1)
    (fun a b hab z => phi_bAct hE 1 hab z) hfdW hWst hx₀ hyμ
  have hx10 : x1 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hfx
    exact hy0 hfx.symm
  obtain ⟨a, b, hab, hε, hμ⟩ := Wm_khw hE hU hV hmono hh hbig hx1 hx10 hkhw
  have hTc : ∀ v ∈ T, casimir E v = (casVal lam : ℂ) • v := by
    intro v hv
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.1 hv
    exact casimir_genSub hE hc _ (layer_le_genSub (ε := ε) 1 (phi_mem_layer (Wm_le_ncV hx')))
  rw [hμ] at hyμ
  exact hy0 (khw_eq_zero_sharp hE hU hmono hh (two_lt_of_gap hε hbig) hab hε hfdT hTst hTc hyT hyμ)

theorem phi_Wm_last (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} {F : Big n (k + 1) M}
    (hF : ∀ κ, slice (Fin.last k) κ F ∈ Wm ε E V) : phi E (k + 1) F = 0 := by
  have key : ∀ init : Fin k → Fin n × Fin n,
      ∑ p : Fin n × Fin n, E p.1 p.2 (F (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n)) = 0 := by
    intro init
    rcases isEmpty_or_nonempty (Fin n × Fin n) with h0 | hne
    · simp [Finset.univ_eq_empty]
    · obtain ⟨p0⟩ := hne
      have := phi_one_Wm hE hU hV hc hmono hh hbig (hF (Fin.snoc init p0))
      rw [sch_phi_one_apply] at this
      simpa only [sch_slice_apply, Fin.update_snoc_last] using this
  unfold phi
  rw [LinearMap.sum_apply, ← (Fin.snocEquiv (fun _ => Fin n × Fin n)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero (fun init _ => ?_)
  have hs : ∀ p, (Fin.snocEquiv (fun _ => Fin n × Fin n)) (p, init) =
      (Fin.snoc init p : Fin (k + 1) → Fin n × Fin n) := fun p => rfl
  simp only [hs, LinearMap.comp_apply, sch_coord_apply, sch_word_snoc, Module.End.mul_apply]
  rw [← map_sum, key, map_zero]

theorem phi_Wm_position (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} (i : Fin (k + 1)) {F : Big n (k + 1) M} (hF0 : F ∈ ncV ε V (k + 1))
    (hF : ∀ κ, slice i κ F ∈ Wm ε E V) : phi E (k + 1) F ∈ layer ε E V k := by
  set σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap i (Fin.last k) with hσ
  have hperm : ∀ κ, slice (Fin.last k) κ (permute σ F) = slice i (κ ∘ σ) F := by
    intro κ
    unfold slice
    congr 1
    funext ι
    rw [sch_permute_apply, Function.update_comp_equiv, hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have h0 : phi E (k + 1) (permute σ F) = 0 :=
    phi_Wm_last hE hU hV hc hmono hh hbig (fun κ => by rw [hperm]; exact hF _)
  have hs := phi_permute_sub_mem hE hV.2.1 σ hF0
  rwa [h0, sub_zero] at hs

end Sch

end ReciprocityTheory.ChartRestriction.DS.G2
