import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QDivBdQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeComparisonOnPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLogSumAndPrimeBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CovHt.Link

theorem abs_lgOf_rootSym_false_sub_ind_le : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (B : ℝ) (x : DV.Rt D.what₂.Tau N) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (Φ.C k).Y), |lgOf (Φ.C k) (rootSym S.Dw (fun _ => false) none (DV.tauEmb D x.1) x.2) v e y - lgOf (Φ.C k) (rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D x.1) x.2) v e y| ≤ htLog κ B v := by
  intro D A N j S κ s Φ k B x v e y
  have hind : ArIn.ind (∅ : Finset ℕ) = fun _ => false := funext fun q => by simp [ArIn.ind]
  have h := GlobalTheory.LatHt.abs_lgOf_rootSym_sub_le (Φ.C k) (DV.tauEmb D x.1) x.2 (Pad.setB κ B) v e y
  rw [hind, abs_sub_comm] at h
  refine h.trans ?_
  have hpr : ∀ p ∈ Pad.setB κ B, p.Prime := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact (Finset.mem_filter.1 h).2
    · exact Nat.prime_of_mem_primeFactors h
  have hterm : ∀ p ∈ Pad.setB κ B,
      0 ≤ -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p :=
    fun p hp => mul_nonneg (neg_log_adicAbv_natCast_nonneg _ p v) (htEx_nonneg' _ p (hpr p hp))
  split_ifs with hT
  · have hp := hpr _ hT
    have hlp : 0 < Real.log (resP v) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hp1 : (1 : ℝ) < (resP v : ℝ) := by exact_mod_cast hp.one_lt
    have ha := neg_log_adicAbv_natCast_nonneg D.what₂.LL (resP v) v
    have hvd : 0 ≤ vDiff D.host.E (resP v) := by unfold vDiff; positivity
    rw [← map_natCast (algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL)), e.w_alg]
    have key : |-Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (resP v : D.what₂.LL)) / Real.log (resP v)| *
        LatHt.jump D.host.E (resP v) ≤
        -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (resP v : D.what₂.LL)) * htEx D.host.E (resP v) := by
      rw [abs_of_nonneg (div_nonneg ha hlp.le)]
      have e1 : -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (resP v : D.what₂.LL)) / Real.log (resP v) *
          LatHt.jump D.host.E (resP v) =
          -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (resP v : D.what₂.LL)) *
            (1 / ((resP v : ℝ) - 1) + vDiff D.host.E (resP v)) := by
        unfold LatHt.jump
        field_simp
      rw [e1]
      refine mul_le_mul_of_nonneg_left ?_ ha
      unfold htEx
      have : vDiff D.host.E (resP v) = (padicValNat (resP v) (discr D.host.E).natAbs : ℝ) /
          (Module.finrank ℚ D.host.E : ℝ) := rfl
      rw [← this]
      linarith
    exact key.trans (Finset.single_le_sum (f := fun p : ℕ =>
      -Real.log (NumberField.HeightOneSpectrum.adicAbv D.what₂.LL v (p : D.what₂.LL)) * htEx D.host.E p) hterm hT)
  · exact Finset.sum_nonneg hterm

end GlobalTheory.CovHt.Link
