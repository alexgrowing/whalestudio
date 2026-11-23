import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.WAniso

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section D7

open PI.UnitaryGroupMassFormula.BetaLUniq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem positive_weight_holds : PosW := by
  intro D T' F' τ w hT' hw hwX
  by_contra hneg
  push_neg at hneg
  classical
  have hτ : ∀ a : D.host.E, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have hTE : ((T' : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hT'.ne'
  have hsymm : ∀ x y : (hS D).V, (hS D).hT y x = star ((hS D).hT x y) := by
    intro x y
    rw [← (hS D).herm.eq x y, starRingEnd_apply]
  have horth := (mem_orth (hS D)).1 hw
  have hez : ∀ a, (hS D).hT (F'.fl.e a) F'.fl.z = 0 := F'.fl.z_orth
  have hze : ∀ a, (hS D).hT F'.fl.z (F'.fl.e a) = 0 := by
    intro a; rw [hsymm, hez, star_zero]
  have hXz : ∀ x ∈ Xsp F', (hS D).hT x F'.fl.z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hez a
    | zero => simp
    | add y y' _ _ h1 h2 => simp [h1, h2]
    | smul c y _ h1 => simp [h1]
  have hzX : ∀ x ∈ Xsp F', (hS D).hT F'.fl.z x = 0 := by
    intro x hx; rw [hsymm, hXz x hx, star_zero]
  have hzz : (hS D).hT F'.fl.z F'.fl.z = -((T' : ℕ) : D.host.E) := F'.fl.z_norm
  have he_mem : ∀ a, F'.fl.e a ∈ Xplus F' := fun a =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hz_mem : F'.fl.z ∈ Xplus F' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hew : ∀ a, (hS D).hT (F'.fl.e a) w = 0 := fun a => horth _ (he_mem a)
  have hzw : (hS D).hT F'.fl.z w = 0 := horth _ hz_mem
  have hwe : ∀ a, (hS D).hT w (F'.fl.e a) = 0 := by intro a; rw [hsymm, hew, star_zero]
  have hwz : (hS D).hT w F'.fl.z = 0 := by rw [hsymm, hzw, star_zero]
  have hzX' : F'.fl.z ∉ Submodule.span D.host.E (Set.range F'.fl.e) := by
    intro h
    have := hXz _ h
    rw [hzz] at this
    exact hTE (neg_eq_zero.1 this)
  have hwX' : w ∉ Submodule.span D.host.E
      (Set.range (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V)) := by
    intro h
    have hle : Submodule.span D.host.E
        (Set.range (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V)) ≤
        Xsp F' ⊔ Submodule.span D.host.E {F'.fl.z} := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      | cast a =>
        simp only [Fin.snoc_castSucc]
        exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hle h)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have h0 : (hS D).hT F'.fl.z (x + c • F'.fl.z) = 0 := by rw [hxy]; exact hzw
    rw [map_add, hzX x hx, map_smul, hzz, zero_add, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.1 h0 with h' | h'
      · exact h'
      · exact absurd (neg_eq_zero.1 h') hTE
    apply hwX
    rw [← hxy, hc, zero_smul, add_zero]
    exact hx
  let u : Fin (D.R.rS + 1 + 1) → (hS D).V :=
    Fin.snoc (Fin.snoc F'.fl.e F'.fl.z : Fin (D.R.rS + 1) → (hS D).V) w
  have hu : LinearIndependent D.host.E u :=
    linearIndependent_finSnoc.2 ⟨linearIndependent_finSnoc.2 ⟨F'.fl.e_indep, hzX'⟩, hwX'⟩
  have hsig : Formalism.UG.HasSignature (((hS D).gram).map τ) (D.R.k + D.R.rS) (D.R.rS + 1) := by
    have h := D.sp.Y_sig 0 τ
    rw [D.sp.baseSpace_signature_eq τ] at h
    exact h
  obtain ⟨hcard, Q, hQ⟩ := wa_sig_data _ _ _ hsig
  have hdim := wa_neg_dim (((hS D).gram).map τ) Q hQ hcard (fun k => wa_cv (hS D) τ (u k))
    (fun x hx => wa_indep u hu x hx) (by
      intro x
      rw [wa_comb hτ x u]
      simp only [Fin.sum_univ_castSucc, u, Fin.snoc_castSucc, Fin.snoc_last, F'.fl.e_iso, hez, hze, hew,
        hwe, hzw, hwz, hzz, map_zero, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
      have h1 : ∀ c : ℂ, starRingEnd ℂ c * c = (Complex.normSq c : ℂ) := by
        intro c; rw [mul_comm]; exact Complex.mul_conj c
      rw [h1, h1, map_neg, map_natCast]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
        Complex.neg_im, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, mul_zero]
      have := Complex.normSq_nonneg (x (Fin.castSucc (Fin.last D.R.rS)))
      have := Complex.normSq_nonneg (x (Fin.last (D.R.rS + 1)))
      have : (0 : ℝ) ≤ (T' : ℝ) := Nat.cast_nonneg _
      nlinarith)
  omega

end D7

end PI.UnitaryGroupMassFormula.BetaModX
