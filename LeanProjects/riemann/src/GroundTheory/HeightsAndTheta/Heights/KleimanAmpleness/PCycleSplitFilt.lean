import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CycleSplitFiltStepSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotGraded
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplit
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFilt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem CycleSplit.Filt.telescope : ∀ {n : ℕ} (a : Fin (n + 1) → ℤ) (b : Fin n → ℤ),
    (∀ l : Fin n, a l.castSucc = a l.succ + b l) → a 0 = a (Fin.last n) + ∑ l, b l
  | 0, a, b, _ => by simp
  | n + 1, a, b, h => by
    have ih := CycleSplit.Filt.telescope (fun m => a m.castSucc) (fun l => b l.castSucc)
      (fun l => by
        have := h l.castSucc
        simpa only [Fin.succ_castSucc] using this)
    have hl := h (Fin.last n)
    rw [Fin.succ_last] at hl
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_zero] at ih
    linarith

open SectionCount.Drop.Filt in

theorem CycleSplit.Filt.proof (hS : CycleSplit.Filt.Step.Statement.{u, w}) :
    CycleSplit.Filt.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x 𝔪 h𝔪 J hJhom hJx hJ𝔪

  have hkill : ∀ p ∈ primeOf (S := S) x, ∀ m : Poly S N ⧸ J, p • m = 0 := by
    intro p hp m
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Ideal.Quotient.mk J (p * m) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right m (hJx hp))
  obtain ⟨⟨Fl⟩, hcount⟩ := PrimeFiltration.Exists.proof.{u, u, w} S Ω N x (Poly S N ⧸ J)
    (quotGraded J hJhom) (finite_quot J) hkill
  rw [Ideal.annihilator_quotient] at hcount
  have hann : ∀ l, J ≤ Fl.prime l := fun l => by
    have := Fl.ann_le l; rwa [Ideal.annihilator_quotient] at this

  have hlift : ∀ l : Fin Fl.n, ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      Ideal.Quotient.mk J g = Fl.gen l := by
    intro l
    obtain ⟨g, hg, hgm⟩ := mem_quotGraded_piece.mp (Fl.gen_mem l)
    by_cases h0 : 0 ≤ Fl.deg l
    · refine ⟨g, (Fl.deg l).toNat, isHomogeneous_of_isWeightedHomogeneous_one ?_, hgm⟩
      rwa [Int.toNat_of_nonneg h0]
    · refine ⟨0, 0, isHomogeneous_zero _ _ _, ?_⟩
      have hg0 : g = 0 := by
        ext m
        by_contra hne
        have h1 := hg hne
        rw [weight_one_int] at h1
        omega
      rw [← hgm, hg0]
  choose g eK hgH hgm using hlift

  let Jk : Fin (Fl.n + 1) → Ideal (Poly S N) := fun l => (Fl.step l).comap J.mkQ
  have hJ0 : Jk 0 = J := by
    simp only [Jk, Fl.step_zero, Submodule.comap_bot, Submodule.ker_mkQ]
  have hJlast : Jk (Fin.last _) = ⊤ := by
    simp only [Jk, Fl.step_last, Submodule.comap_top]
  have hmkQ : ∀ (c : Poly S N) (l : Fin Fl.n), J.mkQ (c * g l) = c • Fl.gen l := by
    intro c l
    rw [← hgm l]
    rfl
  have hJsucc : ∀ l : Fin Fl.n, Jk l.succ = Jk l.castSucc ⊔ Ideal.span {g l} := by
    intro l
    ext f
    simp only [Jk, Fl.step_succ, Submodule.mem_comap]
    constructor
    · intro hf
      obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have h1 : f - c * g l ∈ (Fl.step l.castSucc).comap J.mkQ := by
        rw [Submodule.mem_comap, map_sub, hmkQ, ← hay, add_sub_cancel_right]
        exact ha
      have h2 := Submodule.add_mem_sup h1 (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self (g l)))
      rwa [sub_add_cancel] at h2
    · intro hf
      obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      rw [map_add, hmkQ]
      exact Submodule.add_mem_sup ha (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hJkp : ∀ (l : Fin Fl.n) (f : Poly S N), f ∈ Fl.prime l ↔ f * g l ∈ Jk l.castSucc := by
    intro l f
    rw [Fl.mem_prime, ← hgm l]
    exact Iff.rfl
  have hJk_ge : ∀ l, J ≤ Jk l := fun l f hf => by
    simp only [Jk, Submodule.mem_comap, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero J).mpr hf, zero_mem]
  have hJk_hom : ∀ l, ∀ f ∈ Jk l, ∀ d : ℕ, homogeneousComponent d f ∈ Jk l := by
    intro l
    induction l using Fin.induction with
    | zero => rw [hJ0]; exact hJhom
    | succ l ih =>
      rw [hJsucc l]
      exact hom_sup ih (hom_span fun g' hg' => ⟨eK l, by rw [Set.mem_singleton_iff.mp hg']; exact hgH l⟩)
  refine ⟨Fl.n, Fl.prime, fun l => -((eK l : ℕ) : ℤ),
    fun l => ⟨Fl.isPrime l, Fl.isHomogeneous l, hann l⟩, fun G _ hG => hcount Fl G hG, fun Q => ?_⟩

  have hstep : ∀ l : Fin Fl.n, ∀ᶠ c : ℕ in atTop,
      restrLen (Jk l.castSucc) (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (Jk l.succ) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen (Fl.prime l) (Q.twist (twistSys S x ((c : ℤ) - (eK l : ℕ)))) := by
    intro l
    rw [hJsucc l]
    exact hS S Ω N x 𝔪 h𝔪 (Jk l.castSucc) (Fl.prime l) (g l) (eK l) (hJk_hom _)
      (hJx.trans (hJk_ge _)) (hJ𝔪.trans (hJk_ge _)) (hgH l) (Fl.isHomogeneous l) (hJkp l) Q
  filter_upwards [Filter.eventually_all.mpr hstep] with c hc
  have htel := CycleSplit.Filt.telescope
    (fun m => restrLen (Jk m) (Q.twist (twistSys S x (c : ℤ))))
    (fun l => restrLen (Fl.prime l) (Q.twist (twistSys S x ((c : ℤ) - (eK l : ℕ))))) hc
  simp only [hJ0, hJlast, restrLen_of_irrelevant ⊤ (fun i => Submodule.mem_top), zero_add] at htel
  rw [htel]
  simp only [sub_eq_add_neg]

end GroundTheory.Heights₂.Heights.Kleiman
