import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlaggedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingEverywhereOfRegularAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyBundleMapSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleMapSmoothMetricsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverInducesDualLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFamilySignsDimensionCountStatement
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TwoLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat

theorem ramModelDR : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
    GlobalTheory.EigWholeDR.RamModelDR := by
  intro hP hH hR D O hO R hR2 c _ M L m Ψ hL hΨ
  obtain ⟨B, _, q, E, E', h, h', u, hq, hn, H, H', hu, hB⟩ := GlobalTheory.T.arithmetic_variety_bundle_map_setup hP hH hR D O hO R hR2 c
  obtain ⟨V, Y, _, π, ρ, w, fl, fl', hY, hρ, hfl, hc, h₁, h₂⟩ :=
    GlobalTheory.T.arithmetic_bundle_map_smooth_metrics hP hH hR D O hO R hR2 c B q E E' h h' H H' u hq hn hu hB
  obtain ⟨ix, sg, n, e, Q, hn1, hne, hsg, hfam, hQ, hQ0, hhom, halg⟩ := GlobalTheory.T.eigen_family_signs_dimension_count D O
  have hdim : (O.var c).dim = n + 1 + e := (O.dim_eq c).trans hne.symm
  have hV := GlobalTheory.T.vanishing_everywhere_of_regular_alteration hP hR (GlobalTheory.T.vanishing_on_regular_flagged hP) _ B Y V.X q π ρ V.p w n e (hn1 ▸ hq) (hdim ▸ hY) (hdim ▸ hρ) _ E E' _ h h' H H' u
    hu trivial fl hfl fl' hc
  let x : Letter O.S.Dw ⊕ Letter O.S.Dw → HermLB V.p := Sum.elim
    (fun z => (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)).pull ρ w)
    fun z => VMetric.grLB (fl' z.1) z.2 (((H' z.1).pull π rfl).pull ρ w)
  obtain ⟨Φ, hΦ⟩ := ((hP.p4.arExists _ V.X V.p _ V.ar).2 _ x).1
  let L' : EigWhole.Var O → HermLB V.p := fun i => if sg i = 1 then x (ix i) else (x (ix i)).dual
  have hΦ' := ((hP.p4.arIso _ V.X V.p _ V.ar).2 _ x Φ hΦ).2.2 _ L' (fun i => Pi.single (ix i) (sg i)) fun i => by
    refine HermLB.icls_eq_iff.1 ?_
    rw [icls_comb, Finset.sum_eq_single (ix i) (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp),
      Pi.single_eq_same]
    rcases hsg i with e₁ | e₁
    · simp only [L', e₁, if_true, one_smul]
    · simp only [L', e₁, neg_smul, one_smul]
      rw [if_neg (by norm_num), HermLB.icls_dual]
  have hind : ∀ i, V.Induces (adlOf (O.Φ.C c) (O.met.hm c) (EigWhole.fam O ∅ R i)) (L' i) 1 := fun i => by
    have key (st) (hst : V.Induces (lineAdl O R c st 1) (x (ix i)) 1) : V.Induces (lineAdl O R c st (sg i)) (L' i) 1 := by
      rcases hsg i with e₁ | e₁
      · simpa only [L', e₁, if_true] using hst
      · simp only [L', e₁]
        rw [if_neg (by norm_num)]
        exact GlobalTheory.T.cover_induces_dual_line_bundle D O hO R c V st _ hst
    rcases hfam R i with ⟨z, hz, e₁⟩ | ⟨z, k, hz, hk, e₁⟩
    · rw [e₁]
      exact key _ (by rw [hz]; exact h₁ z)
    · rw [e₁]
      exact key _ (by rw [hz]; exact h₂ k z hk)
  have hcmp := GlobalTheory.CoverModelTop.top_eq hP.p4 hH.deg (O.var c) (Equiv.refl _) _ (fun _ => rfl) M L m Ψ hL hΨ V L' _
    hind hΦ'
  obtain ⟨I, _, a, b, hs⟩ := FlagCmp.exists_sum_pow hhom
  have h0 := hV Φ (hdim ▸ hΦ) Q hQ hQ0
  have hA : (fun j : EigWhole.Var O => lin fun i => (((Pi.single (ix j) (sg j) : _ → ℤ) i : ℤ) : ℝ)) =
      fun i => (C (sg i : ℝ) * X (ix i) : MvPolynomial (Letter O.S.Dw ⊕ Letter O.S.Dw) ℝ) := funext fun j => by
    rw [lin, Finset.sum_eq_single (ix j) (fun i _ hi => by rw [Pi.single_eq_of_ne hi]; simp) (by simp), Pi.single_eq_same]
  rw [← halg, ← hA, ← hs] at h0
  have hc₀ : (((m : ℕ) : ℝ) ^ ((O.var c).dim + 1) * (Module.finrank ℚ D.what₂.LL : ℝ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 m.ne_zero)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  rw [← hs, ← div_eq_zero_iff.trans (or_iff_left hc₀), map_sum, Finset.sum_div, ← zero_div V.ν, ← h0, map_sum, map_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hcmp (b j)
  rw [hdim] at this ⊢
  rw [map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc, mul_div_assoc, this]
  rfl

end GlobalTheory.TwoLat

end
