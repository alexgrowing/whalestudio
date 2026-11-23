import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRCuspCsdb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.UnitOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Thin
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DeterminantOneCharacters.DeterminantOneConditionHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemma
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem sum_inf_zero {a : ℕ} (ρ : CuspSub E a) (hn : GlobalTheory.DiscSpec.IsNormalised ρ) :
    ∑ τ : E →+* ℂ, ((CG.mk ρ).infChar τ).sum = 0 := by
  have := Submodule.nontrivial_iff_ne_bot.2 ρ.ne_bot
  obtain ⟨x, hx⟩ := exists_ne (0 : ρ.V)
  obtain ⟨g₀, hg₀⟩ : ∃ g, (x : Sm E a).1 g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (Subtype.ext (Subtype.ext (funext hcon)))
  have hlie : lie E a (oneL E a) (x : Sm E a) = (∑ τ : E →+* ℂ, ((CG.mk ρ).infChar τ).sum) • (x : Sm E a) := by
    rw [GlobalTheory.T.lie_central_element_trace E a, LinearMap.sum_apply,
      Finset.sum_congr rfl fun τ _ => GlobalTheory.T.trace_operator_eigenvalue_sum E a ρ τ _ (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) τ) x x.2,
      ← Finset.sum_smul]
  refine GlobalTheory.CompanionTheory.TotalTrace.eq_zero_of_exp_mul_eq_one fun t => ?_
  have h1 := GlobalTheory.T.central_eigen_exponential E a _ _ hlie t g₀
  rw [hn _ x.2 t g₀] at h1
  exact mul_right_cancel₀ hg₀ (by rw [one_mul]; exact h1.symm)

private theorem im_sum_of_const (m : Multiset ℂ) (c : ℝ) (h : ∀ x ∈ m, x.im = c) : m.sum.im = m.card * c := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    rw [Multiset.sum_cons, Complex.add_im, h x (Multiset.mem_cons_self x m),
      ih fun y hy => h y (Multiset.mem_cons_of_mem hy), Multiset.card_cons]
    push_cast
    ring

private theorem log_norm_prod (B : Multiset ℂˣ) :
    Real.log ‖((B.prod : ℂˣ) : ℂ)‖ = (B.map fun α : ℂˣ => Real.log ‖(α : ℂ)‖).sum := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons α B ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons, Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 α.ne_zero) (norm_ne_zero_iff.2 (Units.ne_zero _)), ih]

private theorem twist_zero (hA : AbsInf) {a n : ℕ} (ha : 1 ≤ a) (ρ : CuspSub E a) (hn : GlobalTheory.DiscSpec.IsNormalised ρ) (z : ℂ)
    (hR : ∀ τ, ∀ y ∈ ((CG.mk ρ).twist (Model.absC E z)).infChar τ, ∃ k : ℤ, y = (k : ℂ) + ((n : ℂ) - 1) / 2)
    (w : HeightOneSpectrum (𝓞 E)) (b : Multiset ℂˣ) (hb : ((CG.mk ρ).twist (Model.absC E z)).HasSat w b)
    (hbd : ∀ α ∈ b, (Ideal.absNorm w.asIdeal : ℝ) ^ (-(1 / 2) : ℝ) < ‖(α : ℂ)‖ ∧
      ‖(α : ℂ)‖ < (Ideal.absNorm w.asIdeal : ℝ) ^ (1 / 2 : ℝ)) : z = 0 := by
  have hI : ∀ τ, ((CG.mk ρ).twist (Model.absC E z)).infChar τ = ((CG.mk ρ).infChar τ).map (· + z) :=
    fun τ => (hA E a (CG.mk ρ) z τ).1
  have hcard : ∀ τ, ((CG.mk ρ).infChar τ).card = a := fun τ =>
    (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) τ).1

  have him : ∀ τ, ∀ x ∈ (CG.mk ρ).infChar τ, (x + z).im = 0 := fun τ x hx => by
    obtain ⟨k, hk⟩ := hR τ (x + z) (by rw [hI]; exact Multiset.mem_map_of_mem _ hx)
    rw [hk]
    simp
  have hzim : z.im = 0 := by
    have h0 := congrArg Complex.im (sum_inf_zero ρ hn)
    rw [Complex.im_sum, Finset.sum_congr rfl fun τ _ => im_sum_of_const ((CG.mk ρ).infChar τ) (-z.im) fun x hx => by
      have := him τ x hx
      rw [Complex.add_im] at this
      linarith] at h0
    simp only [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Complex.zero_im] at h0
    have hc : (Fintype.card (E →+* ℂ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have ha' : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have := (mul_eq_zero.1 h0).resolve_left hc
    have := (mul_eq_zero.1 this).resolve_left ha'
    linarith

  obtain ⟨M, hM⟩ : ∃ M : ℤ, 2 * z = (M : ℂ) := by
    obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hcard τ₀]; omega : 0 < ((CG.mk ρ).infChar τ₀).card)
    have hconj := PositivityTheory.Rg.BcB.F.Rig.B.infChar_conj ρ hn τ₀ _ _ (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) τ₀)
      (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) (ComplexEmbedding.conjugate τ₀))
    have hxim : x.im = 0 := by
      have := him τ₀ x hx
      rw [Complex.add_im, hzim] at this
      linarith
    have hxc : (starRingEnd ℂ) x = x := Complex.conj_eq_iff_im.2 hxim
    obtain ⟨k₁, hk₁⟩ := hR τ₀ (x + z) (by rw [hI]; exact Multiset.mem_map_of_mem _ hx)
    obtain ⟨k₂, hk₂⟩ := hR (ComplexEmbedding.conjugate τ₀) (-x + z) (by
      rw [hI, hconj, Multiset.map_map]
      refine Multiset.mem_map.2 ⟨x, hx, ?_⟩
      simp [hxc])
    refine ⟨k₁ + k₂ + n - 1, ?_⟩
    push_cast
    linear_combination hk₁ + hk₂

  have hq1 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast DiscreteGroups.T1.G.one_lt_absNorm w
  have hq0 : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by linarith
  have hlq : 0 < Real.log (Ideal.absNorm w.asIdeal : ℝ) := Real.log_pos hq1
  have hS := PositivityTheory.RgJS.satake_twist_holds E a _ (Model.absC E (-z)) w b (PositivityTheory.Rg.Rs.StrStepB.absC_unrAt (-z) w) hb
  rw [← CG.twist_mul, ← PositivityTheory.Rg.Rs.StrStepB.absC_add, add_neg_cancel, PositivityTheory.Rg.Rs.StrStepB.absC_zero, CG.twist_one] at hS
  have hu : (CG.mk ρ).IsUnitary := (CG.isUnitary_mk ρ).2 (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn)
  have hd := PositivityTheory.RgJS.determinant_one_condition_holds E a (CG.mk ρ) w _ hu hS
  have hbc : b.card = a := hb.card
  set q : ℝ := (Ideal.absNorm w.asIdeal : ℝ) with hq
  set r : ℝ := (M : ℝ) / 2 with hr
  have hzr : z = (r : ℂ) := by
    rw [hr]
    push_cast
    linear_combination hM / 2
  have hprod : (((b.map (· * (Model.absC E (-z)).val w)).prod : ℂˣ) : ℂ) =
      ((b.prod : ℂˣ) : ℂ) * (((Model.absC E (-z)).val w : ℂˣ) : ℂ) ^ a := by
    rw [Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const', Multiset.prod_replicate, hbc]
    simp
  have hv : ‖(((Model.absC E (-z)).val w : ℂˣ) : ℂ)‖ = q ^ r := by
    have := DiscreteGroups.T1.G.norm_absC_val (E := E) (-r) w
    rw [neg_neg] at this
    rw [hzr, ← Complex.ofReal_neg]
    exact this
  rw [hprod, norm_mul, norm_pow, hv] at hd
  have hpos : q ^ r ≠ 0 := (Real.rpow_pos_of_pos hq0 r).ne'
  have hl := congrArg Real.log hd
  rw [Real.log_mul (norm_ne_zero_iff.2 (Units.ne_zero _)) (pow_ne_zero _ hpos), Real.log_pow, Real.log_rpow hq0,
    Real.log_one, log_norm_prod] at hl
  have hb0 : b ≠ 0 := fun h => by
    rw [h, Multiset.card_zero] at hbc
    omega
  have hlo : (b.map fun _ : ℂˣ => -(Real.log q / 2)).sum < (b.map fun α : ℂˣ => Real.log ‖(α : ℂ)‖).sum := by
    refine Multiset.sum_lt_sum_of_nonempty hb0 fun α hα => ?_
    have h1 := Real.log_lt_log (Real.rpow_pos_of_pos hq0 _) (hbd α hα).1
    rw [Real.log_rpow hq0] at h1
    linarith
  have hhi : (b.map fun α : ℂˣ => Real.log ‖(α : ℂ)‖).sum < (b.map fun _ : ℂˣ => Real.log q / 2).sum := by
    refine Multiset.sum_lt_sum_of_nonempty hb0 fun α hα => ?_
    have h1 := Real.log_lt_log (norm_pos_iff.2 α.ne_zero) (hbd α hα).2
    rw [Real.log_rpow hq0] at h1
    linarith
  rw [Multiset.map_const', Multiset.sum_replicate, hbc, nsmul_eq_mul] at hlo hhi
  have hP : 0 < (a : ℝ) * Real.log q := mul_pos (by exact_mod_cast ha) hlq
  have h1 : r < 1 / 2 := by
    refine lt_of_mul_lt_mul_left ?_ hP.le
    nlinarith
  have h2 : -(1 / 2) < r := by
    refine lt_of_mul_lt_mul_left ?_ hP.le
    nlinarith
  have hM0 : M = 0 := by
    have h3 : (M : ℝ) < 1 := by rw [hr] at h1; linarith
    have h4 : (-1 : ℝ) < M := by rw [hr] at h2; linarith
    have h5 : M < 1 := by exact_mod_cast h3
    have h6 : -1 < M := by exact_mod_cast h4
    omega
  rw [hM0] at hM
  simpa using hM

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.partNorm :
    AbsInf → PartNorm := by
  intro hA E _ _ _ n hn π hd D hR hs i
  obtain ⟨w, hsp, B, ⟨b, hb, rfl⟩, hB⟩ : ∃ w : UpperTheory.V.Cj.S.Pl E, IsSplitAt w ∧ ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B := by
    have hinf := (UpperTheory.V.Z.Tf.GOne.thin E).2
    have hfin := Filter.eventually_cofinite.1 hs
    obtain ⟨w, hw, hw'⟩ := (hinf.diff hfin).nonempty
    have h : ¬ ¬ (IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B) := hw'
    exact ⟨w, hw, (not_not.1 h) hw⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CuspSub E (D.N i), CG.mk ρ = D.P i := Quotient.exists_rep (D.P i)
  obtain ⟨s, hs'⟩ := GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised E (D.N i) (D.pos i) ρ fun τ =>
    ⟨_, GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk ρ) τ⟩
  have hP : D.P i = (CG.mk (ρ.twist (Model.absC E s))).twist (Model.absC E (-s)) := by
    rw [← hρ, ← CG.twist_mk, ← CG.twist_mul, ← PositivityTheory.Rg.Rs.StrStepB.absC_add, add_neg_cancel,
      PositivityTheory.Rg.Rs.StrStepB.absC_zero, CG.twist_one]
  have hu := UpperTheory.V.Z.Tf.GOne.unitOf E n hn π hd
  have hz : -s = 0 := by
    refine twist_zero (n := n) hA (D.pos i) (ρ.twist (Model.absC E s)) hs' (-s) (fun τ y hy => ?_) w (b i) (hP ▸ hb i)
      fun α hα => PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound E n (CG.mk π) hu w _ hB α
        (Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hα⟩)
    rw [← hP] at hy
    obtain ⟨lam, hlam⟩ := hR τ
    have hy' : y ∈ infOfWeight lam := by
      rw [← hlam]
      exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hy⟩
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hy'
    refine ⟨lam.w k - (k : ℕ), ?_⟩
    push_cast
    ring
  have hs0 : s = 0 := neg_eq_zero.1 hz
  refine ⟨ρ.twist (Model.absC E s), ?_, hs', GlobalTheory.SpehPair.isUnitary_of_isNormalised hs'⟩
  rw [← hρ, hs0, PositivityTheory.Rg.Rs.StrStepB.absC_zero, CuspSub.twist_one]
