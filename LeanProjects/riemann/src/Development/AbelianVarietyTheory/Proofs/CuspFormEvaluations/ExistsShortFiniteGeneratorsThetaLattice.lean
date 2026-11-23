import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupBoundsLeGeneratorConstantMulSizeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsReducedIntegralBasisHarmonicPolynomialsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevelStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRulesLinearAndLevelCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormThetaGeneratorLeStatement

noncomputable section

namespace GlobalTheory.ThetaFamily

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem span_eq_spanIn {D : D7} {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]
    (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j)) (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) {ι : Type}
    (g : ι → cutR C j w) (hg : ∀ i, (g i : R j) ∈ s)
    (hs : ∀ f ∈ s, f ∈ AddSubgroup.closure (Set.range fun i => (g i : R j))) :
    Submodule.span (𝓞 K) (Set.range g) = spanIn C j w s := by
  unfold spanIn
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (hg i)
  · intro x hx
    have hx' : (x : R j) ∈ Submodule.span (𝓞 K) s := hx
    let F : cutR C j w →ₗ[𝓞 K] R j := (cutR C j w).subtype.restrictScalars (𝓞 K)
    have hsub : Submodule.span (𝓞 K) s ≤ (Submodule.span (𝓞 K) (Set.range g)).map F := by
      rw [Submodule.span_le]
      intro f hf
      have hcl : AddSubgroup.closure (Set.range fun i => (g i : R j)) ≤
          ((Submodule.span (𝓞 K) (Set.range g)).map F).toAddSubgroup := by
        rw [AddSubgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨g i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
      exact hcl (hs f hf)
    obtain ⟨y, hy, hyx⟩ := hsub hx'
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']

theorem exists_family (hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hn : IsNab Xo c nab) (ht : ThValTot Xo c nab) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {R : ℕ}
    (b : Fin R → MvPolynomial (LtN Dw n) c.F) (hb : ∀ i, b i ∈ harmA (Dw := Dw) c a n)
    (hgen : ∀ P ∈ harmA (Dw := Dw) c a n, ∃ z : Fin R → ℤ, P = ∑ i, (z i : c.F) • b i) :
    ∃ g : (Fin n → LevQ Dw l) × Fin R → Rul Xo c,
      (∀ p, IsThRule Xo c nab (fun k => levRep (p.1 k)) (b p.2) (g p)) ∧
      ∀ f ∈ thGen Xo c nab a n, f ∈ AddSubgroup.closure (Set.range g) := by
  have hex : ∀ p : (Fin n → LevQ Dw l) × Fin R,
      ∃ f : Rul Xo c, IsThRule Xo c nab (fun k => levRep (p.1 k)) (b p.2) f := fun p =>
    (existsUnique_thRule Xo c nab ht (fun k => levRep (p.1 k)) (hb p.2)).exists
  choose g hg using hex
  refine ⟨g, hg, ?_⟩
  rintro f ⟨x, P, hP, hf⟩
  obtain ⟨hlin, hmod⟩ := GlobalTheory.T.theta_rules_linear_and_level_congruence hci E H Dw l Xo c nab hn a n
  set q : Fin n → LevQ Dw l := fun k => Submodule.Quotient.mk (x k) with hq
  have hrep : ∀ k, x k - levRep (q k) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro k
    have h1 : Submodule.Quotient.mk (levRep (q k)) = q k := by
      unfold levRep
      exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ (q k))
    rw [← Submodule.Quotient.eq, h1]
  have hf' : IsThRule Xo c nab (fun k => levRep (q k)) P f := hmod x _ P f hrep hf
  obtain ⟨z, hz⟩ := hgen P hP
  have hsum : f = ∑ i, ((z i : ℤ) : c.F) • g (q, i) := by
    refine hlin (fun k => levRep (q k)) R (fun i => ((z i : ℤ) : c.F)) b f (fun i => g (q, i)) hb ?_ ?_ ?_
    · rw [← hz]; exact hP
    · rw [← hz]; exact hf'
    · intro i; exact hg (q, i)
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (q, i))) _

theorem log_rdE (D : D7) : Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) = lrd D := by
  have hf : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by
    first
    | exact_mod_cast Formalism.MainNotions.Gaps.LevGap.finrank_hostE_eq D.host
    | exact_mod_cast Formalism.MainNotions.StandardLattice.finrank_host D
  have hd : (NumberField.discr D.host.E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero D.host.E
  unfold lrd ReciprocityTheory.ChartRestriction.G.FD.rdE ReciprocityTheory.ChartRestriction.G.FD.dE
  rw [Real.log_rpow (abs_pos.mpr hd), hf]
  ring

theorem absA_eq {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) : absA w = (WeightAlgebra.DF w : ℝ) := by
  unfold absA WeightAlgebra.DF WeightAlgebra.degP
  push_cast
  rfl

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem theta_family : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) => ∃ (N : ℕ) (w0 : Fin N → B.Cusp j w), Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll w ∧ N ≤ (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ B.KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n)) ∧ ∀ k σ, Real.log (B.supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ B.KO) + Real.log |((NumberField.discr B.KO : ℤ) : ℝ)| / Module.finrank ℚ B.KO + 2) (recB h.toLawsCore) (recPJ h j hj) := by
  intro hci D T h hG large₂ j hj w hpg hL hr hlast
  beta_reduce

  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    first
    | exact Formalism.MainNotions.Gaps.LevGap.finrank_hostE_eq D.host
    | exact Formalism.MainNotions.StandardLattice.finrank_host D
  have hfd : ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg
    omega
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.toLawsCore.toLawsM.pins.2.1.1
  have hk := D.R.m_add_three_le_k
  obtain ⟨hj1, hj2⟩ := id hj
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    have h4 := h.toLawsCore.toLawsM.pins.2.2.2 j hj
    unfold IsDatW at h4
    rw [h4.1, h4.2.1]
    simp only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]
    omega
  have hr1 : 1 ≤ D.R.r := by
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  have hnpos : 0 < w.n := by omega
  have hDF : Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w := ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
  have hLP : Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlast
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hnabex, -, htot, hcusp, -, -⟩ := id h
  obtain ⟨inst, hn⟩ := hnabex j hj
  obtain ⟨-, hlrd, -, -, hlf, -, -, hlDF, hln⟩ := id hpg

  have hrd : Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) ≤ 2 * large₂.sc.L := by
    rw [log_rdE]; exact hlrd
  have hfd' : Real.log (ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E) ≤ 2 * large₂.sc.L := by
    rw [hfd]; exact hlf
  have hDFr : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ WeightAlgebra.DF w := by exact_mod_cast hDF
  have hDF' : Real.log (1 + Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)) ≤ 2 * large₂.sc.L := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hlDF
    linarith
  obtain ⟨R, b, hb, hgen, hR, hl1⟩ := GlobalTheory.T.exists_reduced_integral_basis_harmonicPolynomials D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c w.n
    (by rw [hpq]; exact hr) (wtA w) large₂.sc.L hL hrd hfd' hDF' hln

  obtain ⟨g, hgr, hgcl⟩ := exists_family hci (T.Q.Xo j) T.Q.c (T.nab j) hn (htot j hj) (wtA w) w.n b hb hgen
  have hmem : ∀ f, f ∈ T.th j w ↔ ∃ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
      P ∈ harmA T.Q.c (wtA w) w.n ∧ IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f := fun f => Iff.rfl
  have hth : ∀ p, g p ∈ T.th j w := fun p => (hmem _).2 ⟨fun k => levRep (p.1 k), b p.2, hb p.2, hgr p⟩
  have hcut : ∀ p, g p ∈ cutR T.C j w := by
    intro p
    unfold cutR
    rw [Submodule.mem_inf, Submodule.mem_iInf]
    exact ⟨hcusp j hj (wtA w) w.n (dom_wtA w) hLP (g p) (hth p), fun hn' => absurd hj hn'⟩
  have : Finite (LevQ (T.Q.Dw j) T.Q.l) := (GlobalTheory.T.card_lattice_quotient_half_level D.host.E T.Q.H (T.Q.Dw j) T.Q.l).1
  let e := Finite.equivFin ((Fin w.n → LevQ (T.Q.Dw j) T.Q.l) × Fin R)
  let w0 : Fin (Nat.card ((Fin w.n → LevQ (T.Q.Dw j) T.Q.l) × Fin R)) → ↥(cutR T.C j w) :=
    fun k => ⟨g (e.symm k), hcut (e.symm k)⟩
  refine ⟨_, (w0 : Fin _ → (recB h.toLawsCore).Cusp j w), ?_, ?_, ?_⟩
  ·
    have h2 : Set.range (fun k => ((w0 k : cutR T.C j w) : T.R j)) = Set.range g :=
      e.symm.surjective.range_comp g
    have hsp := span_eq_spanIn T.C j w (T.th j w) w0 (fun k => hth (e.symm k))
      (fun f hf => by rw [h2]; exact hgcl f ((hmem f).1 hf))
    exact hsp
  ·
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_fin,
      (GlobalTheory.T.card_lattice_quotient_half_level D.host.E T.Q.H (T.Q.Dw j) T.Q.l).2, hM, hfd, hpq, ← pow_mul]
    rw [hfd, hpq] at hR
    refine Nat.mul_le_mul le_rfl (le_trans hR (Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by omega) _)))
  ·
    intro k σ
    have hs : (recB h.toLawsCore).supN j w σ (w0 k) = T.Ns j w σ (g (e.symm k)) := by
      dsimp only [recB, mkB]
      unfold cutN
      rw [if_pos hj]
    rw [hs]
    have hexp := hl1 (e.symm k).2 σ
    simp only [hfd, hpq] at hexp
    have hlg : 0 ≤ Real.log (Module.finrank ℚ T.Q.c.F) := Real.log_natCast_nonneg _
    have hld : 0 ≤ Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F := by
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply Real.log_nonneg
      have : (1 : ℤ) ≤ |NumberField.discr T.Q.c.F| := Int.one_le_abs (NumberField.discr_ne_zero _)
      exact_mod_cast this
    have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
    have hA : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ absA w := by rw [absA_eq]; exact hDFr
    have hrL : (0 : ℝ) ≤ 140 * (D.R.r : ℝ) * large₂.sc.L := by positivity
    have hAm := mul_le_mul_of_nonneg_left hA hrL
    have hfrnL : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L := by positivity
    have hDF0 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) := Nat.cast_nonneg _
    have hℓ : (0 : ℝ) ≤ 140 * ((D.R.r : ℕ) : ℝ) * large₂.sc.L * (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) +
        2 * (D.R.f : ℝ) * ((D.R.r : ℕ) : ℝ) * (w.n : ℝ) * large₂.sc.L + 4 * Real.log (Module.finrank ℚ T.Q.c.F) +
        Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F := by
      have : (0 : ℝ) ≤ 140 * ((D.R.r : ℕ) : ℝ) * large₂.sc.L * (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) := by positivity
      linarith
    have key := GlobalTheory.T.log_supNorm_thetaGenerator_le hci D T h hG large₂ j hj w hpg hL hr hLP (fun i => levRep ((e.symm k).1 i)) (b (e.symm k).2)
      (hb _) (g (e.symm k)) (hgr _) σ _ hℓ hexp
    have h30 := (GlobalTheory.T.supBounds_le_generatorConstant_mul_size D (recB h.toLawsCore) large₂ j w 0 hL hnpos).1
    show Real.log (T.Ns j w σ (g (e.symm k))) ≤ 400 * Zb D large₂ * w.size + 3 * (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L +
      5 * Real.log (Module.finrank ℚ T.Q.c.F) + Real.log |((NumberField.discr T.Q.c.F : ℤ) : ℝ)| / Module.finrank ℚ T.Q.c.F + 2
    nlinarith [key, h30, hAm, hfrnL, hlg, hld]

end GlobalTheory.ThetaFamily
