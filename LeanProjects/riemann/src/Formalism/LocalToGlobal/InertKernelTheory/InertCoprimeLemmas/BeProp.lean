import Formalism.LocalToGlobal.InertKernelTheory.StatementBe
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSv
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWHolds

noncomputable section

namespace Formalism.L2.KerInert

open MvPowerSeries Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend Formalism.MainNotions.J

section Witt

variable {p : ℕ} [hp : Fact p.Prime]

theorem sig_teich (y : kb p) :
    Formalism.MainNotions.FormalGroupSystem.sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p) := by
  ext n
  show (WittVector.frobenius (WittVector.teichmuller p y)).coeff n = _
  rw [WittVector.coeff_frobenius_charP]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  · rw [WittVector.teichmuller_coeff_pos p y n hn, WittVector.teichmuller_coeff_pos p _ n hn,
      zero_pow hp.out.ne_zero]

def pairHom (p : ℕ) [Fact p.Prime] : WW p →+* ℂ_[p] × ℂ_[p] :=
  RingHom.prod (wToC p) ((wToC p).comp (Formalism.MainNotions.FormalGroupSystem.sigW p))

def gensP (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)}

theorem teich_mem {y : kb p} (hy : y ^ (p ^ 2) = y) :
    pairHom p (WittVector.teichmuller p y) ∈ Subring.closure (gensP p) := by
  by_cases h0 : y = 0
  · rw [h0, WittVector.teichmuller_zero, map_zero]
    exact zero_mem _
  · apply Subring.subset_closure
    refine ⟨wToC p (WittVector.teichmuller p y), ?_, ?_⟩
    · have h1 : y ^ (p ^ 2 - 1) * y = 1 * y := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos), hy, one_mul]
      have h2 : y ^ (p ^ 2 - 1) = 1 := mul_right_cancel₀ h0 h1
      rw [← map_pow, ← map_pow, h2, map_one, map_one]
    · show (wToC p (WittVector.teichmuller p y), wToC p (Formalism.MainNotions.FormalGroupSystem.sigW p (WittVector.teichmuller p y))) = _
      rw [sig_teich, map_pow, map_pow]

theorem coeff_fix {α : WW p} (hα : (Formalism.MainNotions.FormalGroupSystem.sigW p)^[2] α = α) (i : ℕ) :
    α.coeff i ^ (p ^ 2) = α.coeff i := by
  have h2 : Formalism.MainNotions.FormalGroupSystem.sigW p (Formalism.MainNotions.FormalGroupSystem.sigW p α) = α := hα
  have h3 := congrArg (fun x : WW p => x.coeff i) h2
  have e : ∀ x : WW p, (Formalism.MainNotions.FormalGroupSystem.sigW p x).coeff i = x.coeff i ^ p := fun x =>
    WittVector.coeff_frobenius_charP (p := p) x i
  rw [e, e, ← pow_mul, ← sq] at h3
  exact h3

theorem pair_mem_W2pair {α : WW p} (hα : (Formalism.MainNotions.FormalGroupSystem.sigW p)^[2] α = α) :
    (wToC p α, wToC p (Formalism.MainNotions.FormalGroupSystem.sigW p α)) ∈ W2pair p := by
  show pairHom p α ∈ closure (Subring.closure (gensP p) : Set (ℂ_[p] × ℂ_[p]))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (r_lt_one p)
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff α n
  set S := ∑ i ∈ Finset.Iic n, WittVector.teichmuller p
    (((_root_.frobeniusEquiv (kb p) p).symm ^ i) (α.coeff i)) * (p : WW p) ^ i with hS
  refine ⟨pairHom p S, ?_, ?_⟩
  · rw [hS, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_mul, map_pow, map_natCast]
    refine Subring.mul_mem _ (teich_mem ?_) (Subring.pow_mem _ (natCast_mem _ p) i)
    rw [← map_pow, coeff_fix hα]
  · rw [dist_eq_norm, ← map_sub, hc, Prod.norm_def]
    have h1 : ‖wToC p ((p : WW p) ^ (n + 1) * c)‖ ≤ ((p : ℝ)⁻¹) ^ (n + 1) := norm_wToC_pow_mul p (n + 1) c
    have h2 : ‖wToC p (Formalism.MainNotions.FormalGroupSystem.sigW p ((p : WW p) ^ (n + 1) * c))‖ ≤ ((p : ℝ)⁻¹) ^ (n + 1) := by
      rw [map_mul, map_pow, map_natCast]
      exact norm_wToC_pow_mul p (n + 1) _
    have h3 : ((p : ℝ)⁻¹) ^ (n + 1) ≤ ((p : ℝ)⁻¹) ^ n :=
      pow_le_pow_of_le_one (r_nonneg p) (r_lt_one p).le (Nat.le_succ n)
    exact lt_of_le_of_lt (max_le (h1.trans h3) (h2.trans h3)) hn

theorem okp_of (D : Formalism.BasicNotions.D7) (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (h2 : p ≠ 2) (hin : InertK D p) {α : WW p}
    (hα : (Formalism.MainNotions.FormalGroupSystem.sigW p)^[2] α = α) : (wToC p α, wToC p (Formalism.MainNotions.FormalGroupSystem.sigW p α)) ∈ OKp D lam := by
  rw [Formalism.MainNotions.Ext.okpInert_holds D p lam h2 hin]
  exact pair_mem_W2pair hα

end Witt

section Be

variable {p : ℕ} [hp : Fact p.Prime]

theorem integralMv_of_integralW {σ : Type*} {F : MvPowerSeries σ ℂ_[p]} (h : IntegralW F) : Formalism.MainNotions.TaylorLogMetric.IntegralMv F := by
  intro n
  obtain ⟨w, hw⟩ := (mem_Wp_iff p _).1 (h n)
  show ‖_‖ ≤ 1
  rw [← hw]
  exact norm_wToC_le p w

theorem be_props_at (D : Formalism.BasicNotions.D7) (g : G1 p) (hLT : LTIso g) (hOk : g.Ok) (h2 : p ≠ 2) (hin : InertK D p)
    (hM : ModelOverW g.lam g.abelian₂ g.C) (hB : BeWAt D g) :
    (∀ n : Fin 2 →₀ ℕ, coeff n (beLT hLT) ≠ 0 → 1 ≤ n 0 ∧ 1 ≤ n 1) ∧
    Formalism.MainNotions.FormalGroupSystem.Simeq p (Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) -
              Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0) (MvPowerSeries.X 2) -
              Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 1) (MvPowerSeries.X 2))
      (0 : MvPowerSeries (Fin 3) (K0 p)) ∧
    Formalism.MainNotions.FormalGroupSystem.Simeq p (Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0) (MvPowerSeries.X 1 + MvPowerSeries.X 2) -
              Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0) (MvPowerSeries.X 1) -
              Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0) (MvPowerSeries.X 2))
      (0 : MvPowerSeries (Fin 3) (K0 p)) ∧
    ∀ α : WW p, (Formalism.MainNotions.FormalGroupSystem.sigW p)^[2] α = α →
      Formalism.MainNotions.FormalGroupSystem.Simeq p
        (Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (C (algebraMap (WW p) (K0 p) α) * MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X 1))
        (Formalism.MainNotions.FormalGroupSystem.sub2 p (beLT hLT) (MvPowerSeries.X 0)
          (C (algebraMap (WW p) (K0 p) (Formalism.MainNotions.FormalGroupSystem.sigW p α)) * MvPowerSeries.X 1)) := by
  have hex : PowerSeries.constantCoeff g.ex = 0 := hOk.2.2.1
  have hinv : PowerSeries.subst g.ex g.l = PowerSeries.X := hOk.2.2.2
  set ep : ℂ_[p] := wToC p (epOf hLT : WW p) with hep
  have hep0 : ep ≠ 0 := wToC_unit_ne _
  have hrat : BeRat g ep := by
    rw [hep, ← witt_fraction_to_Cp_algebraMap]
    exact beRat_of g hex hB.1 (exRat_of g hOk hM) _
  set i0 : K0 p →+* ℂ_[p] := (k0ToC p).comp (algebraMap (K0 p) (K0 p)) with hi0
  have hi0' : i0 = k0ToC p := by rw [hi0, Algebra.algebraMap_self, RingHom.comp_id]
  have hi0W : ∀ x : WW p, i0 (algebraMap (WW p) (K0 p) x) = wToC p x := by
    intro x
    rw [hi0', witt_fraction_to_Cp_algebraMap]
  have htie : subst ![C ep * g.lg (MvPowerSeries.X (0 : Fin 2)), C ep * g.lg (MvPowerSeries.X (1 : Fin 2))]
      (map i0 (beLT hLT)) = g.be (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) := by
    rw [hi0']
    exact be_tie hOk hep0 hrat
  have hlog : PowerSeries.subst
      (PowerSeries.map ((k0ToC p).comp ((algebraMap (K0 p) (K0 p)).comp (algebraMap (WW p) (K0 p)))) (thOf hLT))
      (PowerSeries.map ((k0ToC p).comp (algebraMap (K0 p) (K0 p))) (Formalism.MainNotions.FormalGroupSystem.logF p)) = PowerSeries.C ep * g.l := by
    have e1 : (k0ToC p).comp ((algebraMap (K0 p) (K0 p)).comp (algebraMap (WW p) (K0 p))) = wToC p := by
      rw [Algebra.algebraMap_self, RingHom.id_comp]
      exact wToC_eq
    have e2 : (k0ToC p).comp (algebraMap (K0 p) (K0 p)) = k0ToC p := by
      rw [Algebra.algebraMap_self, RingHom.comp_id]
    rw [e1, e2]
    exact thOf_log hLT
  have hab := be_ab g i0 (beLT hLT) ep hep0 hex hinv htie
  have hbe : constantCoeff (beLT hLT) = 0 := by
    by_contra h0
    have := (hab 0 (by rwa [coeff_zero_eq_constantCoeff_apply])).1
    simp at this
  have hs3 := hs_dg (ι := Fin 3) (cc_Cl g ep)
  have hs2' := hs_dg (ι := Fin 2) (cc_Cl g ep)
  have lX3 := fun i : Fin 3 => logOf_X g i0 ep i
  have lX2 := fun i : Fin 2 => logOf_X g i0 ep i
  let Oc : Subring (K0 p) := (algebraMap (WW p) (K0 p)).range
  have witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) (K0 p) (algebraMap (WW p) (K0 p) x) ∈ Oc := by
    intro x
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    exact ⟨x, rfl⟩
  have iC_int : ∀ x : K0 p, x ∈ Oc ↔ ‖k0ToC p x‖ ≤ 1 := by
    intro x
    rw [norm_k0ToC_le_iff]
    rfl
  have sim := fun (ι : Type) => simeq_of (ι := ι) (K0 p) Oc witt_mem_integers_Cp (k0ToC p) iC_int (thOf hLT) (thOf_zero hLT)
    (thOf_unit hLT) _ hlog
  refine ⟨hab, ?_, ?_, ?_⟩
  · have l01 := logOf_add g i0 ep hex hinv (lX3 0) (lX3 1)
    refine sim (Fin 3) _ _ ?_ ?_
    · rw [sub_zero, map_sub, map_sub, constantCoeff_sub2_eq_zero (beLT hLT) hbe l01.1 (lX3 2).1, constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 0).1 (lX3 2).1,
        constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 1).1 (lX3 2).1]
      simp
    · rw [sub_zero, map_sub, map_sub, subst_sub hs3, subst_sub hs3, subtraction_formal_group_log g i0 (beLT hLT) _ hex htie l01 (lX3 2),
        subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 0) (lX3 2), subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 1) (lX3 2), sub_sub]
      exact integralMv_of_integralW hB.2.1.2
  · have l12 := logOf_add g i0 ep hex hinv (lX3 1) (lX3 2)
    refine sim (Fin 3) _ _ ?_ ?_
    · rw [sub_zero, map_sub, map_sub, constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 0).1 l12.1, constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 0).1 (lX3 1).1,
        constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX3 0).1 (lX3 2).1]
      simp
    · rw [sub_zero, map_sub, map_sub, subst_sub hs3, subst_sub hs3, subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 0) l12,
        subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 0) (lX3 1), subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX3 0) (lX3 2), sub_sub]
      exact integralMv_of_integralW hB.2.2.1.2
  · intro α hα
    have la := logOf_mul g i0 ep hex hinv (algebraMap (WW p) (K0 p) α) (lX2 0)
    have lb := logOf_mul g i0 ep hex hinv (algebraMap (WW p) (K0 p) (Formalism.MainNotions.FormalGroupSystem.sigW p α)) (lX2 1)
    refine sim (Fin 2) _ _ ?_ ?_
    · rw [map_sub, constantCoeff_sub2_eq_zero (beLT hLT) hbe la.1 (lX2 1).1, constantCoeff_sub2_eq_zero (beLT hLT) hbe (lX2 0).1 lb.1, sub_zero]
    · rw [map_sub, subst_sub hs2', subtraction_formal_group_log g i0 (beLT hLT) _ hex htie la (lX2 1),
        subtraction_formal_group_log g i0 (beLT hLT) _ hex htie (lX2 0) lb]
      have hok := okp_of D g.lam h2 hin hα
      rw [← hi0W, ← hi0W] at hok
      exact integralMv_of_integralW (hB.2.2.2 _ hok).2

theorem beProp_of_ok (D : Formalism.BasicNotions.D7) (g : G1 p) (hLT : LTIso g) (hOk : g.Ok) (h2 : p ≠ 2) (hin : InertK D p)
    (hM : ModelOverW g.lam g.abelian₂ g.C) (hB : BeWAt D g) : Formalism.MainNotions.FormalGroupSystem.BeProp p (beLT hLT) := by
  obtain ⟨h1, h2', h3, h4⟩ := be_props_at D g hLT hOk h2 hin hM hB
  refine ⟨h1, h2', h3, ?_⟩
  intro α hα
  exact h4 α hα

end Be

theorem beta_property_of_weight : BePropOfBeW := by
  intro D cc δ p _ g hLT hAt h5 hin hM hB
  exact beProp_of_ok D g hLT hAt.2.2.2.2 (by omega) hin hM hB

theorem admissible_second_at_place : Adm2cAt := by
  intro D cc δ p _ g hLT hAt h5 hin hM hB X Y hY
  show Formalism.MainNotions.FormalGroupSystem.BeProp p Y.be
  rw [hY]
  exact beta_property_of_weight D cc δ p g hLT hAt h5 hin hM hB

theorem beProp_of_beW {D : Formalism.BasicNotions.D7} (hW : beW D) {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ} {p : ℕ}
    [Fact p.Prime] {g : G1 p} (hLT : LTIso g) (hAt : At D cc δ g) (h5 : 5 ≤ p) (hin : InertK D p)
    (hM : ModelOverW g.lam g.abelian₂ g.C) : Formalism.MainNotions.FormalGroupSystem.BeProp p (beLT hLT) :=
  beta_property_of_weight D cc δ p g hLT hAt h5 hin hM (hW p cc δ g hAt h5 hin hM)

end Formalism.L2.KerInert
