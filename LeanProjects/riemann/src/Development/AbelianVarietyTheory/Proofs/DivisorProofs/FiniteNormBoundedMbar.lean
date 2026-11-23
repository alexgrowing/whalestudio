import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QDivBdQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLogSumAndPrimeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRootSymbolDifferenceHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedFiniteNormAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormLeExpWeightGapStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link

theorem sum_abs_wtR (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (L : CmList A) (u : AllWt.Weight S.Dw) :
    ∑ z : DV.Rt D.what₂.Tau N, |wtR L u z.1 z.2| = l1 u := by
  rw [Fintype.sum_prod_type, l1, ← L.ψ.sum_comp]
  refine Finset.sum_congr rfl fun t _ => ?_
  exact (finCongr S.rank_eq.symm).sum_comp (fun i => |(u (L.ψ t) i : ℝ)|)

theorem finN_le_nrmFin_mbarOf : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (k : s.Comp), ∃ cX : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ, (Function.support cX).Finite ∧ ∀ r : ℚ, 0 < r → ∀ τ : ℕ, 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR L u) r k).secs τ, ∀ v e y, finN Φ k (τ • u) v e y f ≤ (mbarOf P B (wtR L u) r k).nrmFin v τ f e y * Real.exp (τ * (r * cX v + htLog κ B v * l1 u)) := by
  intro hP hH D A N j S κ s Φ L x P B u k
  obtain ⟨c, hc, hcb⟩ := GlobalTheory.T.bounded_finite_norm_almost_all hP hH D A N j S κ s Φ x P k
  obtain ⟨hL1, -, hL3⟩ := GlobalTheory.T.height_log_sum_and_prime_bound D A κ B
  set dS : ℝ := ∑ z : DV.Rt D.what₂.Tau N, |P.dir z.1 z.2| with hdS
  refine ⟨fun v => c v + htLog κ B v * dS, (hc.union hL1).subset fun v hv => ?_, ?_⟩
  · by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    exact hv (by simp [h.1, h.2])
  intro r hr τ hτ f hf v e y
  have h3 := GlobalTheory.T.finite_norm_le_exp_weight_gap D A N j S κ s Φ L x P B u r hr k τ hτ f hf v e y
  refine h3.trans ?_
  set M := mbarOf P B (wtR L u) r k
  have hr' : (0 : ℝ) < r := Rat.cast_pos.2 hr
  have hτ' : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
  have hM : 0 ≤ M.nrmFin v τ f e y := mul_nonneg (Real.rpow_nonneg (e.w.nonneg _) _) (Real.exp_pos _).le
  have hQ0 : 0 ≤ (bdQ P k).nrmFin v 1 1 e y := mul_nonneg (Real.rpow_nonneg (e.w.nonneg _) _) (Real.exp_pos _).le
  have hH0 : 0 ≤ htLog κ B v := (hL3 v).1
  have hQ : (bdQ P k).nrmFin v 1 1 e y ^ ((τ : ℝ) * r) ≤ Real.exp (τ * (r * c v)) := by
    refine (Real.rpow_le_rpow hQ0 (hcb v e y) (mul_nonneg hτ' hr'.le)).trans_eq ?_
    rw [← Real.exp_mul]
    ring_nf
  have hS : ∑ z : DV.Rt D.what₂.Tau N, |wtR L u z.1 z.2 - r * P.dir z.1 z.2| *
      |lgOf (Φ.C k) (rootSym S.Dw (fun _ => false) none (DV.tauEmb D z.1) z.2) v e y -
        lgOf (Φ.C k) (rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D z.1) z.2) v e y| ≤
      htLog κ B v * (l1 u + r * dS) := by
    calc _ ≤ ∑ z : DV.Rt D.what₂.Tau N, (|wtR L u z.1 z.2| + r * |P.dir z.1 z.2|) * htLog κ B v := by
          refine Finset.sum_le_sum fun z _ => mul_le_mul ?_ (GlobalTheory.T.log_root_symbol_difference_height D A N j S κ s Φ k B z v e y) (abs_nonneg _)
            (by positivity)
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_pos hr']
      _ = htLog κ B v * (l1 u + r * dS) := by
          rw [← sum_abs_wtR D A N j S L u, hdS, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
  calc M.nrmFin v τ f e y * Real.exp (τ * _) * (bdQ P k).nrmFin v 1 1 e y ^ ((τ : ℝ) * r)
      ≤ M.nrmFin v τ f e y * Real.exp (τ * (htLog κ B v * (l1 u + r * dS))) * Real.exp (τ * (r * c v)) := by
        gcongr
    _ = M.nrmFin v τ f e y * Real.exp (τ * (r * (c v + htLog κ B v * dS) + htLog κ B v * l1 u)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

end GlobalTheory.CovHt.Link
