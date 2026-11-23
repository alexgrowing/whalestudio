import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WithZeroLeOneEqExp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CongrLoc

private lemma exists_integer_mul_eq_of_valuation_le (D : D7) (q : PlF D) (x y : D.host.F) (hy : y ≠ 0)
    (h : q.valuation D.host.F x ≤ q.valuation D.host.F y) :
    ∃ β ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp),
      (D.s.atP q).ιF x = (D.s.atP q).ιF y * β := by
  have hle : (D.s.atP q).ιF x ≤ᵥ (D.s.atP q).ιF y := ((D.s.atP q).val x y).2 h
  have hv := (Valuation.vle_iff_le (ValuativeRel.valuation (D.s.atP q).Fp)).1 hle
  have hy' : (D.s.atP q).ιF y ≠ 0 := (map_ne_zero _).2 hy
  have hpos : 0 < ValuativeRel.valuation (D.s.atP q).Fp ((D.s.atP q).ιF y) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy')
  refine ⟨(D.s.atP q).ιF x / (D.s.atP q).ιF y, ?_, ?_⟩
  · rw [Valuation.mem_integer_iff, map_div₀]
    exact (div_le_one₀ hpos).2 hv
  · field_simp

private lemma algebraMap_mem_O_of_mem_integer' (D : D7) (q : PlF D) (w : (D.s.atP q).Fp)
    (hw : w ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp)) :
    algebraMap (D.s.atP q).Fp (D.s.atP q).Ep w ∈ (D.s.atP q).O := by
  rw [(D.s.atP q).O_def]
  exact isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp))
    (x := (⟨w, hw⟩ : Valuation.integer (ValuativeRel.valuation (D.s.atP q).Fp)))

private lemma exists_smul_sub_eq_gS_mul_mem_O (D : D7) (p : PlF D) (f : (D.s.atP p).Fp) (e : D.host.E) :
    ∃ b : D.host.E, ∃ o ∈ (D.s.atP p).O,
      f • (D.s.atP p).ιE e - (D.s.atP p).ιE b = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  classical
  have := (D.s.atP p).char0
  have := (D.s.atP p).lf
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Pf.StabIntSh.gS_ne
  have hgN : (gS D : ℕ) ≠ 0 := by
    intro h
    apply hg0
    simp [h]
  have halg : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).mpr inferInstance
  obtain ⟨d, hd0, hdint⟩ := (halg.isAlgebraic e).exists_integral_multiple

  set u : (D.s.atP p).Fp := ((gS D : ℕ) : (D.s.atP p).Fp) * ((d : ℤ) : (D.s.atP p).Fp) with hu
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)
  have hvu : ValuativeRel.valuation (D.s.atP p).Fp u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hnhds : {z : (D.s.atP p).Fp | ValuativeRel.valuation (D.s.atP p).Fp (z - f) <
      ((Units.mk0 _ hvu : (ValuativeRel.ValueGroupWithZero (D.s.atP p).Fp)ˣ) : ValuativeRel.ValueGroupWithZero (D.s.atP p).Fp)} ∈ nhds f :=
    (IsValuativeTopology.mem_nhds_iff').2 ⟨Units.mk0 _ hvu, subset_rfl⟩
  obtain ⟨a, ha⟩ := (D.s.atP p).dense.mem_nhds hnhds
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at ha

  have hβ : ValuativeRel.valuation (D.s.atP p).Fp ((f - (D.s.atP p).ιF a) / u) ≤ 1 := by
    rw [map_div₀, ← Valuation.map_neg, neg_sub]
    exact (div_le_one₀ (zero_lt_iff.2 hvu)).2 ha.le
  refine ⟨algebraMap D.host.F D.host.E a * e,
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((f - (D.s.atP p).ιF a) / u) * (D.s.atP p).ιE ((d : ℤ) • e),
    mul_mem (algebraMap_mem_O_of_mem_integer' D p _ ((Valuation.mem_integer_iff _ _).2 hβ))
      (Formalism.L2.SG.Pf.StabIntSh.lg_iota_int p ⟨(d : ℤ) • e, hdint⟩), ?_⟩
  rw [map_mul, (D.s.atP p).compat, zsmul_eq_mul, map_mul, map_intCast, map_natCast, Algebra.smul_def]
  have hsplit : f = (f - (D.s.atP p).ιF a) / u * u + (D.s.atP p).ιF a := by
    field_simp
    ring
  conv_lhs => rw [hsplit]
  rw [hu]
  simp only [map_add, map_mul, map_natCast, map_intCast]
  ring

private lemma exists_pow_mul_finset_sum_mem_subring (D : D7) (p : PlF D) (x : (D.s.atP p).Ep) :
    ∃ b : D.host.E, ∃ o ∈ (D.s.atP p).O,
      x - (D.s.atP p).ιE b = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  classical
  have hx : x ∈ Submodule.span (D.s.atP p).Fp (Set.range (D.s.atP p).ιE) := by
    rw [(D.s.atP p).span]
    exact Submodule.mem_top
  obtain ⟨w, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hx
  rw [Finsupp.sum]
  induction w.support using Finset.induction_on with
  | empty => exact ⟨0, 0, zero_mem _, by simp⟩
  | insert i s hi ih =>
    obtain ⟨b₁, o₁, ho₁, h₁⟩ := ih
    obtain ⟨b₂, o₂, ho₂, h₂⟩ := exists_smul_sub_eq_gS_mul_mem_O D p (w i) i
    refine ⟨b₂ + b₁, o₂ + o₁, add_mem ho₂ ho₁, ?_⟩
    rw [Finset.sum_insert hi, map_add, mul_add, ← h₁, ← h₂]
    ring

private lemma exists_intValuation_sub_one_le_and_le_elsewhere (D : D7) (p : PlF D) (r : 𝓞 D.host.F) (hr : r ≠ 0) :
    ∃ t : 𝓞 D.host.F, p.intValuation (t - 1) ≤ p.intValuation r ∧
      ∀ q : PlF D, q ≠ p → q.intValuation t ≤ q.intValuation r := by
  classical
  have hfin : {q : PlF D | r ∈ q.asIdeal}.Finite := by
    have hI : Ideal.span {r} ≠ 0 := by
      simpa [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
    refine (Ideal.finite_factors hI).subset ?_
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq ⊢
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert p hfin.toFinset)
    (fun q : PlF D => q.asIdeal) (fun q => multiplicity q.asIdeal (Ideal.span {r}))
    (fun q _ => q.prime) (fun q _ q' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun q => if (q : PlF D) = p then 1 else 0)
  refine ⟨y, ?_, ?_⟩
  · have h := hy p (Finset.mem_insert_self _ _)
    simp only [if_true] at h
    rw [p.intValuation_eq_exp_neg_multiplicity hr]
    exact (p.intValuation_le_pow_iff_mem _ _).2 h
  · intro q hq
    by_cases hqs : r ∈ q.asIdeal
    · have h := hy q (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hqs))
      simp only [hq, if_false, sub_zero] at h
      rw [q.intValuation_eq_exp_neg_multiplicity hr]
      exact (q.intValuation_le_pow_iff_mem _ _).2 h
    · rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hqs]
      exact q.intValuation_le_one _

theorem exists_int_congr_gS : ∀ (D : D7) (p : PlF D) (c : (D.s.atP p).Ep), c ∈ (D.s.atP p).O → ∃ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - c = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) ∧ ∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p c hc
  classical
  have hg0 : ((gS D : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Pf.StabIntSh.gS_ne
  have hgN : (gS D : ℕ) ≠ 0 := by
    intro h
    apply hg0
    simp [h]

  obtain ⟨b₀, o₀, ho₀, h₀⟩ := exists_pow_mul_finset_sum_mem_subring D p c
  have halg : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).mpr inferInstance
  obtain ⟨d, hd0, hdint⟩ := (halg.isAlgebraic b₀).exists_integral_multiple
  set r : 𝓞 D.host.F := ((gS D : ℕ) : 𝓞 D.host.F) * ((d : ℤ) : 𝓞 D.host.F) with hr
  have hr0 : r ≠ 0 := mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)

  obtain ⟨t, ht₁, ht₂⟩ := exists_intValuation_sub_one_le_and_le_elsewhere D p r hr0
  set a : D.host.E := algebraMap D.host.F D.host.E (t : D.host.F) * b₀ with ha
  have hιa : ∀ q : PlF D, (D.s.atP q).ιE a =
      algebraMap (D.s.atP q).Fp (D.s.atP q).Ep ((D.s.atP q).ιF (t : D.host.F)) * (D.s.atP q).ιE b₀ := by
    intro q
    rw [ha, map_mul, (D.s.atP q).compat]
  have hG : ∀ q : PlF D, (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) ∈ (D.s.atP q).O := by
    intro q
    rw [map_natCast]
    exact natCast_mem _ _
  have hb₀ : (D.s.atP p).ιE b₀ ∈ (D.s.atP p).O := by
    have : (D.s.atP p).ιE b₀ = c - (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o₀ := by
      rw [← h₀]; ring
    rw [this]
    exact sub_mem hc (mul_mem (hG p) ho₀)
  have hdb : ∀ q : PlF D, (D.s.atP q).ιE ((d : ℤ) • b₀) ∈ (D.s.atP q).O :=
    fun q => Formalism.L2.SG.Pf.StabIntSh.lg_iota_int q ⟨(d : ℤ) • b₀, hdint⟩

  have hp : ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE a - c = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
    have hle : p.valuation D.host.F ((t : D.host.F) - 1) ≤ p.valuation D.host.F ((gS D : ℕ) : D.host.F) := by
      have e1 : ((t : D.host.F) - 1) = algebraMap (𝓞 D.host.F) D.host.F (t - 1) := by simp
      have e2 : ((gS D : ℕ) : D.host.F) = algebraMap (𝓞 D.host.F) D.host.F ((gS D : ℕ) : 𝓞 D.host.F) := by simp
      rw [e1, e2, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      refine ht₁.trans ?_
      rw [hr, map_mul]
      exact mul_le_of_le_one_right' (p.intValuation_le_one _)
    obtain ⟨β, hβ, hβe⟩ := exists_integer_mul_eq_of_valuation_le D p _ _ (by exact_mod_cast hgN) hle
    refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep β * (D.s.atP p).ιE b₀ - o₀,
      sub_mem (mul_mem (algebraMap_mem_O_of_mem_integer' D p β hβ) hb₀) ho₀, ?_⟩
    have ht : (D.s.atP p).ιF (t : D.host.F) = (D.s.atP p).ιF ((gS D : ℕ) : D.host.F) * β + 1 := by
      rw [← hβe, map_sub, map_one]; ring
    rw [hιa p, ht, map_add, map_mul, map_one, map_natCast, map_natCast, map_natCast]
    have : c = (D.s.atP p).ιE b₀ + ((gS D : ℕ) : (D.s.atP p).Ep) * o₀ := by
      rw [← map_natCast (D.s.atP p).ιE, ← h₀]; ring
    rw [this]
    ring

  have hq : ∀ q : PlF D, q ≠ p →
      ∃ o ∈ (D.s.atP q).O, (D.s.atP q).ιE a = (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) * o := by
    intro q hqp
    have hle : q.valuation D.host.F (t : D.host.F) ≤
        q.valuation D.host.F (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) := by
      have e1 : (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F r := by
        simp [hr]
      rw [e1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact ht₂ q hqp
    have hne : (((gS D : ℕ) : D.host.F) * ((d : ℤ) : D.host.F)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hgN) (by exact_mod_cast hd0)
    obtain ⟨β, hβ, hβe⟩ := exists_integer_mul_eq_of_valuation_le D q _ _ hne hle
    refine ⟨algebraMap (D.s.atP q).Fp (D.s.atP q).Ep β * (D.s.atP q).ιE ((d : ℤ) • b₀),
      mul_mem (algebraMap_mem_O_of_mem_integer' D q β hβ) (hdb q), ?_⟩
    rw [hιa q, hβe, zsmul_eq_mul]
    simp only [map_mul, map_intCast, map_natCast]
    ring

  have hloc : ∀ q : PlF D, (D.s.atP q).ιE a ∈ (D.s.atP q).O := by
    intro q
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨o, ho, he⟩ := hp
      have : (D.s.atP q).ιE a = c + (D.s.atP q).ιE ((gS D : ℕ) : D.host.E) * o := by
        rw [← he]; ring
      rw [this]
      exact add_mem hc (mul_mem (hG q) ho)
    · obtain ⟨o, ho, he⟩ := hq q hqp
      rw [he]
      exact mul_mem (hG q) ho
  have hint : IsIntegral ℤ a := Formalism.L2.SG.Pf.StabIntSh.lg_int_of_loc a hloc
  exact ⟨⟨a, hint⟩, hp, hq⟩

end GlobalTheory.CongrLoc
