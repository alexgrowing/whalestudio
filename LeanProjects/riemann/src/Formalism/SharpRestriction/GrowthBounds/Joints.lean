import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename
import Formalism.SharpRestriction.GrowthBounds.FlipOneThree
import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
import Formalism.SharpRestriction.GrowthBounds.ColumnSystems
import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.GrowthBounds.ConclusionA2
import Formalism.SharpRestriction.GrowthBounds.ProjectionLemmaBaseLevel
import Formalism.SharpRestriction.GrowthBounds.DefsInst
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.TopChoiceBounds
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop

noncomputable section

open Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

theorem degree_bound_gives_symbol_space (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) :
    Formalism.MainNotions.SelectionLemmas.TensorColumnFamily D := h

theorem reducibility_gives_symbol_space (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D) :
    Formalism.MainNotions.SelectionLemmas.BranchingColumnFamily D := h

theorem third_degree_bound_gives_symbol_space (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) :
    Formalism.MainNotions.SelectionLemmas.GlobalSectionsSchur D := h

theorem first_isotypic_gives_symbol_space (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.RotatedSumBound D) :
    Formalism.MainNotions.SelectionLemmas.BracketPolynomialSpan D := h

theorem third_isotypic_gives_symbol_space (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ConclusionB3 D) :
    Formalism.MainNotions.SelectionLemmas.GradedLatticeStable D := h

theorem integral_invariants_gives_counts (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D) :
    Formalism.MainNotions.tableLineDegreeFive.adm11 D := h

theorem invariant_projection_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.InvariantProjectionField D) :
    Formalism.MainNotions.tableLineDegreeFive.adm7 D := h

theorem invariant_denominator_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.NablaDeltaComparisonField D) :
    Formalism.MainNotions.tableLineDegreeFive.adm8 D := h

theorem integral_invariants_give_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.IsotypicProjectorTheoremField D) :
    Formalism.MainNotions.tableLineDegreeFive.adm9 D := h

theorem corollary_denominator_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.TranslateCorollaryField D) :
    Formalism.MainNotions.tableLineDegreeFive.adm10 D := h

theorem reducibility_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D) :
    Formalism.MainNotions.tableLineDegreeFive.adm12 D := h

theorem support_lemma_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ConclusionE D) :
    Formalism.MainNotions.tableLineDegreeFive.adm21 D := h

theorem second_decomposition_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D) :
    Formalism.MainNotions.tableLineDegreeFive.adm23 D := h

theorem lattice_index_gives_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.DerivativeLemma D) :
    Formalism.MainNotions.tableLineDegreeFive.FrobeniusExpansionCongruence D := h

theorem rank_degree_bounds_give_orbit_count (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg) :
    Formalism.MainNotions.tableLineDegreeFive.adm26 D CLa Ck Crk Cdeg := h

theorem first_degree_bound_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.AutomorphicSideConclusion D) :
    Formalism.MainNotions.tableLineDegreeFive.adm13 D := h

theorem degree_bound_gives_multiplicity (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) :
    Formalism.MainNotions.tableLineDegreeFive.adm14 D := h

theorem third_degree_bound_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) :
    Formalism.MainNotions.tableLineDegreeFive.adm15 D := h

theorem first_isotypic_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.RotatedSumBound D) :
    Formalism.MainNotions.tableLineDegreeFive.adm16 D := h

theorem second_isotypic_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.PathWeightComponents D) :
    Formalism.MainNotions.tableLineDegreeFive.adm17 D := h

theorem third_isotypic_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ConclusionB3 D) :
    Formalism.MainNotions.tableLineDegreeFive.adm18 D := h

theorem corollary_base_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.CoefficientDependence D) :
    Formalism.MainNotions.tableLineDegreeFive.adm19 D := h

theorem corollary_zero_gives_orbit_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.CanonicalTranslateJetIdentity D) :
    Formalism.MainNotions.tableLineDegreeFive.adm20 D := h

theorem invariant_denominator_gives_exponent_data (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.NablaDeltaComparisonField D) :
    Formalism.MainNotions.flipOneThree.GenericProjectionCriterion D := h

theorem integral_invariants_give_exponent_data (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.IsotypicProjectorTheoremField D ∧ Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D) :
    Formalism.MainNotions.flipOneThree.ColumnFamilyClosure D := h

theorem degree_bounds_give_exponent_data (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.AutomorphicSideConclusion D ∧ Formalism.MainNotions.CovariantDegrees.HyperplaneRank D ∧ Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) :
    Formalism.MainNotions.flipOneThree.GlobalSectionsSchur D := h

theorem reducibility_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D) :
    Formalism.MainNotions.ColumnSystems.ArchimedeanSignatureMatching D := h

theorem first_degree_bound_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.AutomorphicSideConclusion D) :
    Formalism.MainNotions.ColumnSystems.adm5 D := h

theorem third_degree_bound_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) :
    Formalism.MainNotions.ColumnSystems.adm6 D := h

theorem first_isotypic_gives_statement (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.RotatedSumBound D) :
    Formalism.MainNotions.ColumnSystems.adm7 D := h

theorem second_isotypic_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.PathWeightComponents D) :
    Formalism.MainNotions.ColumnSystems.adm8 D := h

theorem isotypic_bound_gives_statement (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ConclusionB3 D) :
    Formalism.MainNotions.ColumnSystems.adm9 D := h

theorem corollary_base_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.CoefficientDependence D) :
    Formalism.MainNotions.ColumnSystems.adm10 D := h

theorem corollary_gives_lattice_count (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.CanonicalTranslateJetIdentity D) :
    Formalism.MainNotions.ColumnSystems.adm11 D := h

theorem second_decomposition_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D) :
    Formalism.MainNotions.ColumnSystems.adm13 D := h

theorem lattice_index_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.DerivativeLemma D) :
    Formalism.MainNotions.ColumnSystems.adm14 D := h

theorem second_degree_bound_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) :
    Formalism.MainNotions.ColumnSystems.adm15 D := h

theorem corollary_zero_gives_counting_input (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.CanonicalTranslateJetIdentity D) :
    Formalism.MainNotions.ColumnSystems.adm20 D := h

theorem invariant_projection_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.InvariantProjectionField D) :
    Formalism.MainNotions.SourceCleaning.InvariantProjectionLemma D := h

theorem invariant_denominator_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.NablaDeltaComparisonField D) :
    Formalism.MainNotions.SourceCleaning.NablaDeltaComparison D := h

theorem integral_invariants_give_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.IsotypicProjectorTheoremField D) :
    Formalism.MainNotions.SourceCleaning.IsotypicProjectorTheorem D := h

theorem corollary_denominator_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.TranslateCorollaryField D) :
    Formalism.MainNotions.SourceCleaning.TranslateCorollary D := h

theorem integral_corollary_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D) :
    Formalism.MainNotions.SourceCleaning.FilteredProjectorCorollary D := h

theorem reducibility_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D) :
    Formalism.MainNotions.SourceCleaning.ValuationLemma D := h

theorem first_degree_bound_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.AutomorphicSideConclusion D) :
    Formalism.MainNotions.SourceCleaning.ValuationsOfProducts D := h

theorem second_degree_bound_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) :
    Formalism.MainNotions.SourceCleaning.PathColumnBasis D := h

theorem third_degree_bound_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) :
    Formalism.MainNotions.SourceCleaning.StandardMonomialSpanBis D := h

theorem first_isotypic_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.RotatedSumBound D) :
    Formalism.MainNotions.SourceCleaning.PathPairCorrespondence D := h

theorem second_isotypic_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.PathWeightComponents D) :
    Formalism.MainNotions.SourceCleaning.admB2 D := h

theorem third_isotypic_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ConclusionB3 D) :
    Formalism.MainNotions.SourceCleaning.admB3 D := h

theorem corollary_base_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.CoefficientDependence D) :
    Formalism.MainNotions.SourceCleaning.CoefficientDependenceLemma D := h

theorem corollary_zero_gives_localiser_hypothesis (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.CanonicalTranslateJetIdentity D) :
    Formalism.MainNotions.SourceCleaning.CoefficientValuationLemma D := h

theorem support_lemma_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.ConclusionE D) :
    Formalism.MainNotions.SourceCleaning.LargePrimeLengthVanishing D := h

theorem multiplicity_decomposition_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.UnitFunctionExpansion D) :
    Formalism.MainNotions.SourceCleaning.CharpolyCoeffsLemmaFamily D := h

theorem second_decomposition_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D) :
    Formalism.MainNotions.SourceCleaning.SpanQuotientLemma D := h

theorem lattice_index_gives_localiser (D : Formalism.BasicNotions.D7)  (h : Formalism.MainNotions.CovariantDegrees.DerivativeLemma D) :
    Formalism.MainNotions.SourceCleaning.DividedDerivativeLemma D := h

theorem rank_degree_bounds_give_localiser (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg) :
    Formalism.MainNotions.SourceCleaning.admG2 D CLa Ck Crk Cdeg := h

theorem integral_form_exponent_le_ceil (p a r n : ℕ) (hn : n + 1 ≤ r) (l : ℕ) (hl : l ≤ 8 * a) :
    N0 (n + 1) * deF p (n + 1) l ≤ ⌈Formalism.MainNotions.flipOneThree.kappaOneExponent p a r⌉₊ := by
  have hN0 : N0 (n + 1) ≤ r ^ 2 := by
    unfold N0
    calc (n + 1) * (n + 1 - 1) / 2 ≤ (n + 1) * (n + 1 - 1) := Nat.div_le_self _ _
      _ ≤ r * r := Nat.mul_le_mul hn (by omega)
      _ = r ^ 2 := (sq r).symm
  have hde : deF p (n + 1) l ≤ Nat.log p (8 * a + r) := by
    unfold deF
    exact Nat.log_mono_right (by omega)
  have hlog : (Nat.log p (8 * a + r) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + r) := by
    have := Real.natLog_le_logb (8 * a + r) p
    push_cast at this
    exact this
  have h1 : ((N0 (n + 1) * deF p (n + 1) l : ℕ) : ℝ) ≤ Formalism.MainNotions.flipOneThree.kappaOneExponent p a r := by
    unfold Formalism.MainNotions.flipOneThree.kappaOneExponent Formalism.MainNotions.flipOneThree.lgA
    have hA : ((N0 (n + 1) : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast hN0
    have hB : ((deF p (n + 1) l : ℕ) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + r) :=
      (Nat.cast_le.mpr hde).trans hlog
    have hB0 : (0 : ℝ) ≤ ((deF p (n + 1) l : ℕ) : ℝ) := Nat.cast_nonneg _
    push_cast
    nlinarith [sq_nonneg (r : ℝ)]
  exact_mod_cast h1.trans (Nat.le_ceil _)

theorem mq_top_of_irr {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n : ℕ} [NeZero n]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) (hirr : IsIrrHW E lam v)
    (M : Submodule O V) (hM : UZLattice (O := O) E M) (hv : v ∈ M) : MQ (K := KK O) M = ⊤ := by
  have hE : ∀ a b, ∀ y ∈ MQ (K := KK O) M, E a b y ∈ MQ (K := KK O) M := by
    intro a b y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      apply Submodule.subset_span
      by_cases hab : a = b
      · subst hab
        have hg : binomE E a 1 ∈ UZgens E := Or.inr ⟨a, 1, rfl⟩
        have := hM.1 _ hg x hx
        simpa [binomE] using this
      · have hg : divPowE E a b 1 ∈ UZgens E := Or.inl ⟨a, b, 1, hab, rfl⟩
        have := hM.1 _ hg x hx
        simpa [divPowE] using this
    | zero => simp
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
  have hU : ∀ u ∈ Umon E, ∀ y ∈ MQ (K := KK O) M, u y ∈ MQ (K := KK O) M := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu =>
      obtain ⟨⟨a, b⟩, rfl⟩ := hu
      exact hE a b
    | one => intro y hy; simpa using hy
    | mul u w _ _ hu hw => intro y hy; simpa using hu _ (hw y hy)
  rw [eq_top_iff, ← hirr.2.2.2]
  apply Submodule.span_le.mpr
  rintro x ⟨u, hu, rfl⟩
  exact hU u hu v (Submodule.subset_span hv)

theorem weight_condition_of_integral_form (D : Formalism.BasicNotions.D7) (X : Formalism.MainNotions.flipOneThree.Inst) (h : Formalism.MainNotions.CovariantDegrees.NablaDeltaComparisonField D) :
    Formalism.MainNotions.flipOneThree.adm2 D X := by
  intro n V _ _ _ _ E lam v hn _ hirr hl
  obtain ⟨hA, hB⟩ := h X.p X.L.n' X.O X.setting X.instance_ring_standard (n + 1) lam V E v hirr
  refine ⟨fun x hx => ?_, fun M hM hv hwt => ?_⟩
  · have hx' := hA x hx
    have hle := integral_form_exponent_le_ceil X.p X.L.a X.r n hn (ellWt lam) hl
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    have : ((X.p : KK X.O) ^ ⌈Formalism.MainNotions.flipOneThree.kappaOneExponent X.p X.L.a X.r⌉₊) • x =
        ((X.p : X.O) ^ k) • (((X.p : X.O) ^ (N0 (n + 1) * deF X.p (n + 1) (ellWt lam))) • x) := by
      rw [hk, smul_smul, ← pow_add, add_comm, ← algebraMap_smul (KK X.O) (((X.p : X.O)) ^ _ )]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ hx'
  · apply hB M hM (mq_top_of_irr E lam v hirr M hM hv)
    intro x
    constructor
    · rintro ⟨hxM, hxw⟩
      exact hwt x hxM hxw
    · rintro ⟨c, rfl⟩
      refine ⟨M.smul_mem c hv, ?_⟩
      rw [← algebraMap_smul (KK X.O) c v]
      exact Submodule.smul_mem _ _ hirr.2.2.1.2.1

def PolIsoDecomp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι),
    ∃ e : (Fin r → ℤ) → Module.End K (MvPolynomial (ι × Fin r) K),
      (∀ mu, IsIsoProj (glOps K r LL S) mu (e mu)) ∧
      ∀ G : MvPolynomial (ι × Fin r) K, ∃ T : Finset (Fin r → ℤ),
        G = ∑ mu ∈ T, e mu G ∧ ∀ mu, e mu G ∈ isoSub (glOps K r LL S) mu

theorem isotypic_multiplicity_of_reducibility (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D) (hdec : PolIsoDecomp) :
    Formalism.MainNotions.PlaneGramData.adm1 D := by
  intro p O _ _ _ _ _ r _ ι _ LL S
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨hV1, hV2⟩ := hV
  refine ⟨fun F G => ⟨(hV1 (KK O) ι LL r S).1 F G, (hV1 (KK O) ι LL r S).2.1 F G⟩, fun d th => ?_⟩
  obtain ⟨e, he, hsum⟩ := hdec (KK O) ι LL r S
  have h2 := (hV2 (KK O) ι LL r S e he).1
  ext G
  constructor
  · rintro ⟨hP, hA⟩
    refine ⟨?_, hP⟩
    have hA' : ((th : ℤ) : WithTop ℤ) ≤ valS LL S G := hA
    have hmu := (h2 G th).1 hA'
    obtain ⟨T, hGT, hmem⟩ := hsum G
    change G ∈ (⨆ (ν : Fin r → ℤ) (_ : th ≤ ν (lastIdx r)), isoSub (Formalism.MainNotions.PlaneGramData.glE (KK O) LL S) ν)
    rw [hGT]
    refine Submodule.sum_mem _ fun mu _ => ?_
    by_cases h0 : e mu G = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem (hmu mu h0) (hmem mu))
  · rintro ⟨hI, hP⟩
    refine ⟨hP, ?_⟩
    change ((th : ℤ) : WithTop ℤ) ≤ valS LL S G
    refine (h2 G th).2 fun mu hne => ?_
    by_contra hth
    apply hne
    have hle : (⨆ (ν : Fin r → ℤ) (_ : th ≤ ν (lastIdx r)), isoSub (Formalism.MainNotions.PlaneGramData.glE (KK O) LL S) ν) ≤
        LinearMap.ker (e mu) := by
      refine iSup_le fun ν => iSup_le fun hν => fun x hx => ?_
      have hne' : ν ≠ mu := fun h => hth (h ▸ hν)
      exact (he mu).2 ν hne' x hx
    exact hle hI

open Formalism.MainNotions.G MvPolynomial

theorem glCoord_nontrivial (R : Type) [Field R] (n : ℕ) : Nontrivial (GLCoord R n) := by
  have hx : (genMat R n).det ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin n) R
  exact (IsLocalization.injective (GLCoord R n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx)).nontrivial

theorem valS_one (R : Type) [Field R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι) :
    valS LL S (1 : MvPolynomial (ι × Fin n) R) = 0 := by
  have := glCoord_nontrivial R n
  unfold valS sDegs
  rw [map_one]
  simp

theorem divDer_zero {R : Type} [CommSemiring R] {σ : Type} (F : MvPolynomial σ R) : divDer 0 F = F := by
  unfold divDer
  simp only [zero_le, if_true, tsub_zero, Finsupp.prod_zero_index, Nat.cast_one, mul_one]
  exact (MvPolynomial.as_sum F).symm

theorem valuation_of_letters_clauses (D : Formalism.BasicNotions.D7) (hL : Formalism.MainNotions.CovariantDegrees.DerivativeValuationBound D) (K : Type) [Field K] (ι : Type) [Fintype ι]
    (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι) :
    (∀ (i : ι) (a : Fin r),
      (LL.vec i = true → Formalism.MainNotions.PlaneGramData.geZ (valS LL S (X (i, a) : MvPolynomial (ι × Fin r) K)) 0) ∧
      (LL.vec i = false → Formalism.MainNotions.PlaneGramData.geZ (valS LL S (X (i, a) : MvPolynomial (ι × Fin r) K)) (-1))) ∧
    (∀ (i : ι) (be : Fin r → ℕ) (F : MvPolynomial (ι × Fin r) K),
      (LL.vec i = true →
        valS LL S F ≤ valS LL S (divDer (Formalism.MainNotions.PlaneGramData.atLetter i be) F) + (((∑ a, be a : ℕ) : ℤ) : WithTop ℤ)) ∧
      (LL.vec i = false → valS LL S F ≤ valS LL S (divDer (Formalism.MainNotions.PlaneGramData.atLetter i be) F))) := by
  classical
  refine ⟨fun i a => ?_, fun i be F => ?_⟩
  · have h := (hL K ι LL r S 1 (Finsupp.single (i, a) 1) 0).2.2.1
    rw [valS_one, divDer_zero, mul_one, ← MvPolynomial.X] at h
    have hv0 : Formalism.MainNotions.CovariantDegrees.vecDeg LL S (0 : ι × Fin r →₀ ℕ) = 0 := by simp [Formalism.MainNotions.CovariantDegrees.vecDeg]
    have hc : Formalism.MainNotions.CovariantDegrees.covDeg LL S (Finsupp.single (i, a) 1) =
        if i ∈ S ∧ LL.vec i = false then 1 else 0 := by
      simp [Formalism.MainNotions.CovariantDegrees.covDeg]
    rw [hv0, hc] at h
    refine ⟨fun hvec k hk => ?_, fun _ k hk => ?_⟩
    · rw [hk] at h
      have : ¬ (i ∈ S ∧ LL.vec i = false) := fun h' => by simp [hvec] at h'
      rw [if_neg this] at h
      simp at h
      exact_mod_cast h
    · rw [hk] at h
      split_ifs at h
      · have : (0 : WithTop ℤ) ≤ ((k + 1 : ℤ) : WithTop ℤ) := by simpa using h
        have : (0 : ℤ) ≤ k + 1 := by exact_mod_cast this
        have : (-1 : ℤ) ≤ k := by linarith
        exact_mod_cast this
      · have : (0 : ℤ) ≤ k := by simpa using h
        have : (-1 : ℤ) ≤ k := by linarith
        exact_mod_cast this
  · have h := (hL K ι LL r S F 0 (Formalism.MainNotions.PlaneGramData.atLetter i be)).2.2.1
    rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_mul] at h
    have hc0 : Formalism.MainNotions.CovariantDegrees.covDeg LL S (0 : ι × Fin r →₀ ℕ) = 0 := by simp [Formalism.MainNotions.CovariantDegrees.covDeg]
    rw [hc0, zero_add] at h
    have hsupp : ∀ v ∈ (Formalism.MainNotions.PlaneGramData.atLetter i be).support, v.1 = i := by
      intro v hv
      unfold Formalism.MainNotions.PlaneGramData.atLetter at hv
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hv)
      have := Finsupp.support_single_subset ha
      simp at this
      rw [this]
    refine ⟨fun _ => le_trans h ?_, fun hvec => ?_⟩
    · gcongr
      have hle : Formalism.MainNotions.CovariantDegrees.vecDeg LL S (Formalism.MainNotions.PlaneGramData.atLetter i be) ≤
          (Formalism.MainNotions.PlaneGramData.atLetter i be).sum (fun _ k => k) := by
        unfold Formalism.MainNotions.CovariantDegrees.vecDeg Finsupp.sum
        exact Finset.sum_le_sum fun v _ => by split_ifs <;> simp
      have hs : (Formalism.MainNotions.PlaneGramData.atLetter i be).sum (fun _ k => k) = ∑ a, be a := by
        unfold Formalism.MainNotions.PlaneGramData.atLetter
        rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finsupp.sum_single_index rfl
      exact_mod_cast hle.trans hs.le
    · have hz : Formalism.MainNotions.CovariantDegrees.vecDeg LL S (Formalism.MainNotions.PlaneGramData.atLetter i be) = 0 := by
        unfold Formalism.MainNotions.CovariantDegrees.vecDeg
        refine Finset.sum_eq_zero fun v hv => ?_
        rw [hsupp v hv, hvec]; simp
      rw [hz] at h
      simpa using h

open Formalism.MainNotions.G Formalism.BasicNotions

theorem LPprime_mono_kappa {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf]
    [Algebra O Kf] {p n' : ℕ} {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {w : O} {m : ℕ} {r : ℕ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {t D : ℕ} {κ κ' : ℝ} {cStar : ℕ} (hk : κ ≤ κ')
    (h : LPprime (W := W) p n' ι σ w r lam0 t D κ cStar) : LPprime (W := W) p n' ι σ w r lam0 t D κ' cStar := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun L hL => ?_⟩
  obtain ⟨M, e, F, he, hF, hsc, n, hn, hg⟩ := h2 L hL
  refine ⟨M, e, F, he, hF, hsc, n, ?_, hg⟩
  have h0 : (0 : ℝ) ≤ (dimV Kf lam0 : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem LPprime_min_one {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf]
    [Algebra O Kf] {p n' : ℕ} {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {w : O} {m r : ℕ} {lam0 : Fin n' → Fin (m + 1) → ℤ}
    {t Dd : ℕ} {κ : ℝ} {cStar : ℕ} (h : LPprime (W := W) p n' ι σ w r lam0 t Dd κ cStar) :
    LPprime (W := W) p n' ι σ w r lam0 t Dd (min 1 κ) cStar := by
  rcases le_total κ 1 with hk | hk
  · rwa [min_eq_right hk]
  · obtain ⟨h1, h2⟩ := h
    refine ⟨h1, fun L hL => ?_⟩
    obtain ⟨M, e, F, he, hF, hsc, n, _, hg⟩ := h2 L hL
    refine ⟨M, e, F, he, hF, hsc, n, ?_, hg⟩
    rw [min_eq_left hk, sub_self, zero_mul]
    exact Nat.cast_nonneg _

theorem type_two_hypothesis_of_counts (D : D7) (L : SizeData₂ D) (K : Consts) (C : ℝ) (hC0 : 0 ≤ C)
    (hCk : C ≤ K.kII) (hCt : C ≤ K.tII) (hCL : C ≤ K.La) (hCD : C ≤ K.DII) (hCs : C ≤ K.szII)
    (hCk' : C ≤ K.kII') (hc : 0 ≤ cG L) (ha : 1 ≤ L.sc.a - cG L)
    (h : Formalism.MainNotions.tableLineDegreeFive.aux₃ D C) : Formalism.MainNotions.AuxBlock8.adm6 D L K := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS TT hGood hL12 hL2u hG3 hNp hp0 a b hwin hwt lam0 hbase hdom
    h13 hr2 hN1 hrY hpL h256 hk hkLa hsize
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hxA : 0 < L.sc.x ^ Scale.A := Real.rpow_pos_of_pos hx0 _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hapos : 0 < L.sc.a - cG L := by linarith
  have hlog' : 0 ≤ Real.log (L.sc.a - cG L) := Real.log_nonneg ha
  have hloga : Real.log (L.sc.a - cG L) ≤ Real.log L.sc.a := Real.log_le_log hapos (by linarith)
  have hlogb' : 0 ≤ Real.logb p (L.sc.a - cG L) := Real.logb_nonneg hp1 ha
  have hlogb : Real.logb p (L.sc.a - cG L) ≤ Real.logb p L.sc.a :=
    Real.logb_le_logb_of_le hp1 hapos (by linarith)
  have hlogbA : 0 ≤ Real.logb p L.sc.a := hlogb'.trans hlogb
  have hcpp : (⌊cG L⌋₊ : ℝ) ≤ cG L := Nat.floor_le hc
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hkge : 1 ≤ D.R.k := by omega
  have hk1 : D.R.k - 1 + 1 = D.R.k := by omega
  have hkR : ((D.R.k - 1 + 1 : ℕ) : ℝ) = (D.R.k : ℝ) := by rw [hk1]
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast hkge
  have hrK : rG L.sc - 1 = KG L.sc := by simp [rG]
  have hN1e : N1 L.sc = orbitWindowCount (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x := rfl
  have hcard : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have hNp0 : (0 : ℝ) ≤ NplusF L.sc n' := hcard.trans hNp
  have hr0 : (0 : ℝ) ≤ (rG L.sc : ℝ) := Nat.cast_nonneg _
  have hLaC : 0 ≤ Formalism.MainNotions.tableLineDegreeFive.La C (N1 L.sc) (L.sc.a - cG L) := by
    unfold Formalism.MainNotions.tableLineDegreeFive.La; exact mul_nonneg (mul_nonneg hC0 (by positivity)) hlog'
  have hLaCK : Formalism.MainNotions.tableLineDegreeFive.La C (N1 L.sc) (L.sc.a - cG L) ≤ La K L.sc := by
    unfold Formalism.MainNotions.tableLineDegreeFive.La La
    exact mul_le_mul (mul_le_mul_of_nonneg_right hCL (by positivity)) hloga hlog'
      (mul_nonneg (hC0.trans hCL) (by positivity))

  have hOrb : Formalism.MainNotions.tableLineDegreeFive.OrbitHyp n' TT (rG L.sc) (L1 D L.sc p) (L2 D L.sc) L.sc.delta1 (hG L.sc) L.sc.x := by
    refine ⟨?_, hL12, hL2u, hG3⟩
    rw [hrK]; exact hGood
  have hc0nn : 0 ≤ c0num L := by unfold c0num; linarith [hb'.le, hc]
  have hWt : Formalism.MainNotions.tableLineDegreeFive.WeightHyp TT a b ⌊cG L⌋₊ ⌊c0num L⌋₊ (L.sc.a - cG L) lam0 := by
    refine ⟨hbase, hdom, fun s hs => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hwt s hs
    have h3' : b s + 2 * (⌊cG L⌋₊ : ℤ) ≤ (⌊c0num L⌋₊ : ℤ) := by
      rw [Int.natCast_floor_eq_floor hc0nn]
      exact Int.le_floor.2 (by push_cast; exact h3)
    refine ⟨h1, h2, ?_, h3'⟩
    have hb := (Finset.mem_Icc.mp (hwin s hs).2).1
    have : (0 : ℤ) < ⌈L.sc.b'⌉ := Int.ceil_pos.mpr hb'
    omega
  have hLa : Formalism.MainNotions.tableLineDegreeFive.La C (orbitWindowCount (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x) (L.sc.a - cG L) ≤
      ((D.R.k - 1 + 1 : ℕ) : ℝ) := by
    rw [hkR, ← hN1e]
    refine le_trans ?_ hkLa
    unfold Formalism.MainNotions.tableLineDegreeFive.La
    exact mul_le_mul (mul_le_mul_of_nonneg_right hCk' (by positivity)) hloga hlog'
      (mul_nonneg (hC0.trans hCk') (by positivity))
  have hN1r : orbitWindowCount (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x + 2 * rG L.sc ≤ (D.R.k - 1 + 1) - rG L.sc := by
    rw [hk1, ← hN1e]; omega
  have h256' : 256 * ((D.R.k - 1 + 1 : ℕ) : ℝ) ^ 2 * (TT.card : ℝ) * (L.sc.x ^ Scale.A) ^ 2 ≤
      (p : ℝ) ^ ((L1 D L.sc p : ℤ) - 1) := by
    rw [hkR]; exact h256.trans hpL
  have hDII : (0 : ℝ) ≤ K.DII := hC0.trans hCD
  have hDp : C * (TT.card : ℝ) * ((D.R.k - 1 + 1 : ℕ) : ℝ) ^ 2 * Real.logb p (L.sc.a - cG L) ≤
      (DIIf K L p n' : ℝ) := by
    rw [hkR]
    refine le_trans ?_ (Nat.le_ceil _)
    have hsum : ((D.R.k : ℝ)) ^ 2 ≤ (N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2 := by
      have : (0 : ℝ) ≤ (N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 := by positivity
      linarith
    have h1 : C * (TT.card : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p (L.sc.a - cG L) ≤
        K.DII * NplusF L.sc n' * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) * Real.logb p L.sc.a := by
      apply mul_le_mul _ hlogb hlogb' (by positivity)
      apply mul_le_mul (mul_le_mul hCD hNp hcard hDII) hsum (by positivity) (mul_nonneg hDII hNp0)
    have h2 : (0 : ℝ) ≤ 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L := by positivity
    have h3 : (0 : ℝ) ≤ (rG L.sc : ℝ) * NplusF L.sc n' * c0num L := by
      exact mul_nonneg (mul_nonneg hr0 hNp0) hc0nn
    linarith
  have hSize : C * ((D.R.k - 1 + 1 : ℕ) : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * (TT.card : ℝ) *
      ((p : ℝ) ^ goodG' (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x) ^ 5 *
      (((8 * (DIIf K L p n' + 1) : ℕ) : ℝ) + ((rG L.sc : ℝ) * TT.card * (⌊c0num L⌋₊ : ℝ) +
        2 * (rG L.sc : ℝ) * n' * (⌊cG L⌋₊ : ℝ))) * L.sc.x ^ Scale.A ≤ L.sc.a - cG L := by
    rw [hkR]
    refine le_trans ?_ hsize
    have hB : (((8 * (DIIf K L p n' + 1) : ℕ) : ℝ) + ((rG L.sc : ℝ) * TT.card * (⌊c0num L⌋₊ : ℝ) +
        2 * (rG L.sc : ℝ) * n' * (⌊cG L⌋₊ : ℝ))) ≤
        (8 * ((DIIf K L p n' : ℝ) + 1)) + ((rG L.sc : ℝ) * (TT.card : ℝ) * c0num L +
          2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L) := by
      push_cast
      have : 2 * (rG L.sc : ℝ) * n' * (⌊cG L⌋₊ : ℝ) ≤ 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L :=
        mul_le_mul_of_nonneg_left hcpp (by positivity)
      have : (rG L.sc : ℝ) * TT.card * (⌊c0num L⌋₊ : ℝ) ≤ (rG L.sc : ℝ) * (TT.card : ℝ) * c0num L :=
        mul_le_mul_of_nonneg_left (Nat.floor_le hc0nn) (by positivity)
      linarith
    have hA : (0 : ℝ) ≤ (D.R.k : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * (TT.card : ℝ) * Qp L.sc p ^ 5 := by
      unfold Qp; positivity
    have hB0 : (0 : ℝ) ≤ (((8 * (DIIf K L p n' + 1) : ℕ) : ℝ) + ((rG L.sc : ℝ) * TT.card * (⌊c0num L⌋₊ : ℝ) +
        2 * (rG L.sc : ℝ) * n' * (⌊cG L⌋₊ : ℝ))) := by positivity
    have e1 : C * (D.R.k : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * (TT.card : ℝ) *
        ((p : ℝ) ^ goodG' (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x) ^ 5 = C * ((D.R.k : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * (TT.card : ℝ) * Qp L.sc p ^ 5) := by
      unfold Qp Gp; ring
    have e2 : K.szII * (D.R.k : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * (TT.card : ℝ) * Qp L.sc p ^ 5 =
        K.szII * ((D.R.k : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * (TT.card : ℝ) * Qp L.sc p ^ 5) := by ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_right _ hxA.le
    exact mul_le_mul (mul_le_mul_of_nonneg_right hCs hA) hB hB0 (mul_nonneg (hC0.trans hCs) hA)
  have key := h p W Qq O Kf ι σ j w n' (D.R.k - 1) (rG L.sc) TT (L1 D L.sc p) (L2 D L.sc) L.sc.delta1 (hG L.sc)
    L.sc.x lam0 a b (L.sc.a - cG L) (L.sc.x ^ Scale.A) ⌊cG L⌋₊ ⌊c0num L⌋₊ (DIIf K L p n') (8 * (DIIf K L p n' + 1))
    hS h13 hr2 hOrb hN1 hWt hrY hLa hN1r h256' hDp le_rfl hSize

  have hT : Formalism.MainNotions.tableLineDegreeFive.tBound C p (rG L.sc) TT.card (orbitWindowCount (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x) (L1 D L.sc p)
      (goodG' (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x) n' (D.R.k - 1 + 1) ⌊cG L⌋₊ ⌊c0num L⌋₊ (L.sc.a - cG L) ≤
      ((⌈tIIf K L p n' TT.card⌉₊ : ℕ) : ℝ) := by
    refine le_trans ?_ (Nat.le_ceil _)
    unfold Formalism.MainNotions.tableLineDegreeFive.tBound tIIf
    rw [hkR, ← hN1e]
    have hpk : (0 : ℝ) < (p : ℝ) * (D.R.k : ℝ) := mul_pos hp0 hk0
    have hz : (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) = (p : ℝ) ^ (-(L1 D L.sc p : ℤ)) := by
      rw [← Real.rpow_intCast]; push_cast; ring_nf
    have hzpos : (0 : ℝ) ≤ (p : ℝ) ^ (-(L1 D L.sc p : ℤ)) := zpow_nonneg hp0.le _
    have i1 : Formalism.MainNotions.tableLineDegreeFive.La C (N1 L.sc) (L.sc.a - cG L) * (L.sc.a - cG L) / ((p : ℝ) * D.R.k) ≤
        La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) :=
      div_le_div_of_nonneg_right (mul_le_mul hLaCK (by linarith) hapos.le (hLaC.trans hLaCK)) hpk.le
    have i2 : (L.sc.a - cG L) * (p : ℝ) ^ (-(L1 D L.sc p : ℤ)) ≤ L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) := by
      rw [hz]; exact mul_le_mul_of_nonneg_right (by linarith) hzpos
    have hin0 : 0 ≤ Formalism.MainNotions.tableLineDegreeFive.La C (N1 L.sc) (L.sc.a - cG L) * (L.sc.a - cG L) / ((p : ℝ) * D.R.k) +
        (L.sc.a - cG L) * (p : ℝ) ^ (-(L1 D L.sc p : ℤ)) + (⌊c0num L⌋₊ : ℝ) +
        (D.R.k : ℝ) * (p : ℝ) ^ goodG' (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x := by
      have : 0 ≤ Formalism.MainNotions.tableLineDegreeFive.La C (N1 L.sc) (L.sc.a - cG L) * (L.sc.a - cG L) / ((p : ℝ) * D.R.k) :=
        div_nonneg (mul_nonneg hLaC hapos.le) hpk.le
      have : 0 ≤ (L.sc.a - cG L) * (p : ℝ) ^ (-(L1 D L.sc p : ℤ)) := mul_nonneg hapos.le hzpos
      positivity
    have hin : Formalism.MainNotions.tableLineDegreeFive.La C (N1 L.sc) (L.sc.a - cG L) * (L.sc.a - cG L) / ((p : ℝ) * D.R.k) +
        (L.sc.a - cG L) * (p : ℝ) ^ (-(L1 D L.sc p : ℤ)) + (⌊c0num L⌋₊ : ℝ) +
        (D.R.k : ℝ) * (p : ℝ) ^ goodG' (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x ≤
        La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + L.sc.a * (p : ℝ) ^ (-(L1 D L.sc p : ℝ)) + c0num L +
        (D.R.k : ℝ) * Qp L.sc p := by
      unfold Qp Gp; linarith [Nat.floor_le hc0nn]
    have hC' : C * (rG L.sc : ℝ) * (TT.card : ℝ) ≤ K.tII * (rG L.sc : ℝ) * (TT.card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCt hr0) hcard
    have hlast : 2 * (rG L.sc : ℝ) * (n' : ℝ) * (⌊cG L⌋₊ : ℝ) ≤ 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L :=
      mul_le_mul_of_nonneg_left hcpp (by positivity)
    have := mul_le_mul hC' hin hin0 (mul_nonneg (mul_nonneg (hC0.trans hCt) hr0) hcard)
    linarith
  have hκ : min 1 (C * (TT.card : ℝ) * (rG L.sc : ℝ) ^ 2 * ((D.R.k - 1 + 1 : ℕ) : ℝ) / L.sc.x ^ Scale.A) ≤
      kapIIf K L TT.card := by
    unfold kapIIf
    rw [hkR, Real.rpow_neg hx0.le, div_eq_mul_inv]
    apply min_le_min le_rfl
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hxA.le)
    have : (0 : ℝ) ≤ (TT.card : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) := by positivity
    have e1 : C * (TT.card : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) = C * ((TT.card : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ)) := by ring
    have e2 : K.kII * (TT.card : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ) = K.kII * ((TT.card : ℝ) * (rG L.sc : ℝ) ^ 2 * (D.R.k : ℝ)) := by ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right hCk this
  exact LPprime_mono_kappa hκ (LPprime_min_one (key _ hT))

theorem valuation_clauses_of_lattice_index (D : Formalism.BasicNotions.D7) (hL : Formalism.MainNotions.CovariantDegrees.DerivativeValuationBound D) : Formalism.MainNotions.PlaneGramData.WittOrbitTheorem D :=
  fun _ O _ _ _ _ _ r _ ι _ LL S => valuation_of_letters_clauses D hL (KK O) ι LL r S

theorem isotypic_coefficient_of_degree_bound (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) : Formalism.MainNotions.PlaneGramData.adm3a D := by
  intro p O _ _ _ _ _ N r _ LL d
  exact h O N r LL d

theorem third_degree_bound_gives_span_clause (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) : Formalism.MainNotions.PlaneGramData.adm3b D := by
  intro p O _ _ _ _ hS N r _ LL d
  obtain ⟨⟨S⟩, n', hR⟩ := hS
  have : Fact p.Prime := ⟨hR.prime⟩
  refine ⟨fun th M => (h p O S N r LL d th M).1, fun P I hI i => ?_⟩
  have hA := (h p O S N r LL d (fun i => P.mu i.succ (lastIdx r)) (fun i => P.mu i.succ 0)).1
  have hmem : Psi O P.mu I ∈ (Submodule.span O {G | ∃ P' : PPath r N LL d, ∃ I' : ℤ → Finset (Fin r), IsSt P'.mu I' ∧
      (∀ i : Fin N, P.mu i.succ (lastIdx r) ≤ P'.mu i.succ (lastIdx r) ∧ P'.mu i.succ 0 ≤ P.mu i.succ 0) ∧
      G = Psi O P'.mu I'} : Set _) :=
    Submodule.subset_span ⟨P, I, hI, fun i => ⟨le_rfl, le_rfl⟩, rfl⟩
  unfold Formalism.MainNotions.CovariantDegrees.A3at at hA
  rw [← hA] at hmem
  exact (hmem.2 i).1

theorem extended_hypothesis_of_window {C0 CYb Cde Ck CD Cb Cc : ℝ} {X : Formalism.MainNotions.flipOneThree.Inst} (h : Formalism.MainNotions.flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    {aT' : Fin X.L.n' → ℕ} (hw : X.InWinA aT') : Formalism.MainNotions.ColumnSystems.HIext C0 CYb Cde Ck CD Cb (X.LA aT') := by
  obtain ⟨h0, _, _, hxa, _, hxb, _⟩ := h
  have hJ : (X.LA aT').J0 C0 = X.L.J0 C0 := rfl
  refine ⟨h0, fun s hs => ?_, fun s hs => ?_⟩
  · obtain ⟨h1, h2⟩ := hw.1 s hs
    refine ⟨h1, ?_⟩
    rw [hJ]
    linarith
  · obtain ⟨h1, h2⟩ := hw.2 s hs
    refine ⟨h1, ?_⟩
    rw [hJ]
    linarith

theorem residue_bound_of_extension (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : Formalism.MainNotions.flipOneThree.Inst)
    (h : Formalism.MainNotions.ColumnSystems.RootMultiplicityTwo D C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : Formalism.MainNotions.flipOneThree.adm11 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X := by
  intro hHI aT' hw m hm0 hm rz ry hd
  haveI : NeZero (X.LA aT').m := ⟨X.hm⟩
  letI := X.ringW
  letI := X.domW
  letI := X.dvrW
  letI := X.fieldQ
  letI := X.algW
  letI := X.ring
  letI := X.dom
  letI := X.dvr
  letI := X.fieldK
  letI := X.algO
  exact h (X.LA aT') X.W X.Qq X.O X.Kf X.ι X.σ X.jO X.w X.std (extended_hypothesis_of_window hHI hw) hHI.2.1 X.j m hm0 hm rz ry hd

theorem fourth_extension_gives_ratio_bound (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (X : Formalism.MainNotions.flipOneThree.Inst)
    (h : Formalism.MainNotions.ColumnSystems.ExtendedDigitRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : Formalism.MainNotions.flipOneThree.adm10 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc X := by
  intro hHI aT' hw j rz ry hd
  haveI : NeZero (X.LA aT').m := ⟨X.hm⟩
  letI := X.ringW
  letI := X.domW
  letI := X.dvrW
  letI := X.fieldQ
  letI := X.algW
  letI := X.ring
  letI := X.dom
  letI := X.dvr
  letI := X.fieldK
  letI := X.algO
  exact h (X.LA aT') X.W X.Qq X.O X.Kf X.ι X.σ X.jO X.w X.std (extended_hypothesis_of_window hHI hw) hHI.2.1 j rz ry hd

section P13B
open Formalism.MainNotions.flipOneThree

def orbitLocalData (p n' m : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb : ℝ) (a : ℕ) (b' bl bu : ℝ) (ccl Dp cStar : ℕ)
    (aT bT : Fin n' → ℕ) (c : ℕ) : Formalism.MainNotions.ColumnSystems.Loc :=
  { p := p, n' := n', m := m, TT := TT, aT := aT, bT := bT, a := a, b' := b', Y := Y, Yb := Yb, N1 := N₁, G' := G',
    bl := bl, bh := bu, ccl := ccl, DLP := Dp, cs := cStar, c := c }

theorem type_one_hypothesis_to_local {C₀ CH : ℝ} {p n' m : ℕ} {TT : Finset (Fin n')} {G' N₁ : ℕ} {Y Yb : ℝ} {a : ℕ} {b' bl bu : ℝ}
    {ccl Dp cStar : ℕ} (aT bT : Fin n' → ℕ) (c : ℕ)
    (h : HypI C₀ CH p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar) :
    Formalism.MainNotions.ColumnSystems.WindowHypotheses C₀ CH CH CH CH CH (orbitLocalData p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24⟩ := h
  have h23' : (8 : ℝ) * ((Dp : ℝ) + 1) ≤ (cStar : ℝ) := by exact_mod_cast h23
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    Nat.cast_nonneg _, h21, h22, h23', h24⟩

theorem alternative_extension_gives_bound (D : Formalism.BasicNotions.D7) (C₀ CH CE1 CE2 Ct Cc : ℝ)
    (h : Formalism.MainNotions.ColumnSystems.ExtendedOrderBound D C₀ CH CH CH CH CH CE1 CE2 Ct Cc) : ColumnFamilyLowerSet D C₀ CH CE1 CE2 Ct Cc := by
  intro p n' m _ TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c hp h5 h2 he hH hW hc bs hk
  exact h (orbitLocalData p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c) ⟨hp, h5, h2, he⟩
    ⟨type_one_hypothesis_to_local aT bT c hH, hW⟩ hc bs hk

theorem kappa_share_of_extension_bounds (D : Formalism.BasicNotions.D7) (C₀ CH CE1 CE2 Ckap Cc Cs : ℝ)
    (h : Formalism.MainNotions.ColumnSystems.ExtendedModelRank D C₀ CH CH CH CH CH CE1 CE2 Ckap Cc)
    (h2 : ∀ X : Formalism.MainNotions.ColumnSystems.Loc, Formalism.MainNotions.ColumnSystems.D1num X → Formalism.MainNotions.ColumnSystems.HIext C₀ CH CH CH CH CH X → Formalism.MainNotions.ColumnSystems.CBound Cc X →
      ∀ mm : ℝ, 0 ≤ mm → mm ≤ X.b' / (X.k * X.Q * X.Y) →
        kappaMarginBound Ckap X.N X.k X.Q mm X.N1 X.b' X.Y (X.E0 C₀ CE1 CE2) X.a (X.La C₀) ≤ Cs * X.N * X.N1 / X.Y) :
    admB3 D C₀ CH CE1 CE2 Ckap Cc Cs := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m hm TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c hS hH hW hc mm h0 h1
  exact ⟨@h (orbitLocalData p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c) hm W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS
      ⟨type_one_hypothesis_to_local aT bT c hH, hW⟩ hc mm h0,
    h2 (orbitLocalData p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c) ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
      ⟨type_one_hypothesis_to_local aT bT c hH, hW⟩ hc mm h0 h1⟩

theorem depth_bound_of_extension (D : Formalism.BasicNotions.D7) (C₀ CH CA CE1 CE2 Cm Ckap Ct Cc : ℝ)
    (h : Formalism.MainNotions.ColumnSystems.HerrExtensionClass D C₀ CH CH CH CH CH CE1 CE2 Cm Ckap Ct Cc)
    (hk : ∀ (X : Formalism.MainNotions.ColumnSystems.Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O],
      Formalism.MainNotions.ColumnSystems.HIext C₀ CH CH CH CH CH X →
      Formalism.MainNotions.ColumnSystems.DjHyp O C₀ CE1 CE2 Cm X (fun _ => depthD CA X.p X.a X.TT.card X.N1 X.m X.Y)
        (fun j => Formalism.MainNotions.G.kapT O X.p X.m (X.seg C₀ CE1 CE2 j) (X.m0 Cm) (depthD CA X.p X.a X.TT.card X.N1 X.m X.Y)
          (segATop X.TT X.aT j) (segAPlus X.TT X.aT j))) :
    admB2 D C₀ CH CA CE1 CE2 Cm Ckap Ct Cc := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m hm TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c hS hH hW hcb hc e he
  have hX : Formalism.MainNotions.ColumnSystems.HIext C₀ CH CH CH CH CH (orbitLocalData p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c) :=
    ⟨type_one_hypothesis_to_local aT bT c hH, hW⟩
  have hs : (∑ _j : Fin (numSeg TT), depthD CA p a TT.card N₁ m Y) = (numSeg TT : ℝ) * DjI CA p m TT N₁ Y a := by
    simp [DjI]
  have := @h (orbitLocalData p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c) hm W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS hX hcb _ _
    (@hk (orbitLocalData p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar aT bT c) hm O _ _ _ hX)
    (by
      show 4 * ((∑ _j : Fin (numSeg TT), depthD CA p a TT.card N₁ m Y) + 4 * kap0I p m TT a) < (c : ℝ)
      rw [hs]; exact hc) e he
  have h' : RhoGE p (beHH (m := m) p TT aT bT)
      (CCe p ι σ w TT aT bT ⌊t0I C₀ Ct p m TT G' N₁ a b' c aT bT⌋₊ c e)
      (CCe' p ι σ w TT aT bT ⌊t0I C₀ Ct p m TT G' N₁ a b' c aT bT⌋₊ c e)
      ((∑ _j : Fin (numSeg TT), depthD CA p a TT.card N₁ m Y) + 4 * kap0I p m TT a)
      ((1 - kapPI C₀ CE1 CE2 Cm Ckap p m TT G' N₁ Y a b' c -
          ∑ jj, kapTI O C₀ CA CE1 CE2 Cm p n' m TT G' N₁ Y a b' c aT bT jj) *
        (dimHH (m := m) Kf TT aT bT : ℝ) / gaussianNumber (p ^ n') (m + 1)) := this
  rw [hs] at h'
  exact h'

theorem bad_share_bound_of_extension (D : Formalism.BasicNotions.D7) (C₀ CH CA CE1 CE2 Cc : ℝ)
    (h : ∀ X : Formalism.MainNotions.flipOneThree.Inst, Conclusion1 D C₀ CH CH CH CH CH CE1 CE2 Cc CA X) : PathPairCorrespondence D C₀ CH CA CE1 CE2 Cc := h

example (X : Formalism.MainNotions.flipOneThree.Inst) (C₀ CA CE1 CE2 Cm : ℝ) (aT : Fin X.L.n' → ℕ) :
    kapTI X.O C₀ CA CE1 CE2 Cm X.L.p X.L.n' X.L.m X.L.TT X.L.G' X.L.N1 X.L.Y X.L.a X.L.b' X.L.c aT X.L.bT X.j =
      Formalism.MainNotions.G.kapT X.O X.p X.r (X.S C₀ CE1 CE2) (X.L.m0 Cm) (depthD CA X.p X.L.a X.Nt X.N₁ X.r X.L.Y)
        (segATop X.L.TT aT X.j) (segAPlus X.L.TT aT X.j) := rfl

end P13B

theorem kap_margin (Ck N k Q m0 mm N1 b' Y E0 a La Cs : ℝ) (hCk : 0 ≤ Ck) (hN : 0 ≤ N) (hk : 0 < k) (hQ : 0 < Q)
    (hb : 0 < b') (hY : 0 < Y) (hN1 : 1 ≤ N1) (hm0 : 0 ≤ m0) (hmm : mm ≤ b' / (k * Q * Y))
    (h0 : kappaMarginBound Ck N k Q m0 N1 b' Y E0 a La ≤ Cs * N * N1 / Y) :
    kappaMarginBound Ck N k Q mm N1 b' Y E0 a La ≤ (Cs + Ck) * N * N1 / Y := by
  unfold kappaMarginBound at *
  have hCN : 0 ≤ Ck * N := mul_nonneg hCk hN
  have h1 : k * Q * mm / b' ≤ 1 / Y := by
    rw [div_le_div_iff₀ hb hY]
    have := (le_div_iff₀ (by positivity)).mp hmm
    nlinarith
  have h2 : k * Q * (mm + N1 * k) / b' ≤ k * Q * (m0 + N1 * k) / b' + 1 / Y := by
    have e1 : k * Q * (mm + N1 * k) / b' = k * Q * mm / b' + k * Q * (N1 * k) / b' := by ring
    have e2 : k * Q * (m0 + N1 * k) / b' = k * Q * m0 / b' + k * Q * (N1 * k) / b' := by ring
    have : 0 ≤ k * Q * m0 / b' := by positivity
    linarith
  have key : Ck * N * (Real.exp (-La / 8) + k * Q * (mm + N1 * k) / b' + 1 / Y + k * E0 / a) ≤
      Ck * N * (Real.exp (-La / 8) + k * Q * (m0 + N1 * k) / b' + 1 / Y + k * E0 / a) + Ck * N / Y := by
    have := mul_le_mul_of_nonneg_left h2 hCN
    calc _ = Ck * N * (Real.exp (-La / 8) + 1 / Y + k * E0 / a) + Ck * N * (k * Q * (mm + N1 * k) / b') := by
          ring
      _ ≤ Ck * N * (Real.exp (-La / 8) + 1 / Y + k * E0 / a) +
            Ck * N * (k * Q * (m0 + N1 * k) / b' + 1 / Y) := by linarith
      _ = _ := by ring
  have h3 : Ck * N / Y ≤ Ck * N * N1 / Y :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_right hCN hN1) hY.le
  calc _ ≤ _ := key
    _ ≤ Cs * N * N1 / Y + Ck * N * N1 / Y := add_le_add h0 h3
    _ = (Cs + Ck) * N * N1 / Y := by ring

theorem loc_kap_facts (C0 CYb Cde Ck CD Cb Cm : ℝ) (X : Formalism.MainNotions.ColumnSystems.Loc) (hCm : 0 ≤ Cm) (hD : Formalism.MainNotions.ColumnSystems.D1num X)
    (hX : Formalism.MainNotions.ColumnSystems.WindowHypotheses C0 CYb Cde Ck CD Cb X) :
    0 ≤ X.N ∧ 0 < X.k ∧ 0 < X.Q ∧ 0 < X.b' ∧ 0 < X.Y ∧ 1 ≤ (X.N1 : ℝ) ∧ 0 ≤ X.m0 Cm := by
  obtain ⟨hY, -, -, -, -, hN1, -, -, hb, -⟩ := hX
  have hp : (0 : ℝ) < X.p := by exact_mod_cast hD.1.pos
  have hk : 0 < X.k := by unfold Formalism.MainNotions.ColumnSystems.Loc.k; positivity
  have hQ : 0 < X.Q := by unfold Formalism.MainNotions.ColumnSystems.Loc.Q; positivity
  have hN1' : (1 : ℝ) ≤ (X.N1 : ℝ) := by exact_mod_cast hN1
  refine ⟨by unfold Formalism.MainNotions.ColumnSystems.Loc.N; positivity, hk, hQ, hb, by linarith, hN1', ?_⟩
  unfold Formalism.MainNotions.ColumnSystems.Loc.m0 m0G4 m1G4
  have : (0 : ℝ) ≤ (X.c : ℝ) := Nat.cast_nonneg _
  have h1 : 0 ≤ Cm * X.k * (X.N1 : ℝ) * X.Q * (X.c : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCm hk.le) (by linarith)) hQ.le) this
  linarith

theorem kappa_share_bound_of_extension (D : Formalism.BasicNotions.D7) (C₀ CH CE1 CE2 Cm Ckap Cc Cs : ℝ) (hCk : 0 ≤ Ckap) (hCm : 0 ≤ Cm)
    (h : Formalism.MainNotions.ColumnSystems.ExtendedModelRank D C₀ CH CH CH CH CH CE1 CE2 Ckap Cc)
    (h2 : Formalism.MainNotions.ColumnSystems.ExtendedKappaBound D C₀ CH CH CH CH CH CE1 CE2 Cm Ckap Cc Cs) :
    Formalism.MainNotions.flipOneThree.admB3 D C₀ CH CE1 CE2 Ckap Cc (Cs + Ckap) :=
  kappa_share_of_extension_bounds D C₀ CH CE1 CE2 Ckap Cc (Cs + Ckap) h (fun X hD hX hc mm _ h1 => by
    obtain ⟨hN, hk, hQ, hb, hY, hN1, hm0⟩ := loc_kap_facts C₀ CH CH CH CH CH Cm X hCm hD hX.1
    exact kap_margin Ckap X.N X.k X.Q (X.m0 Cm) mm X.N1 X.b' X.Y (X.E0 C₀ CE1 CE2) X.a (X.La C₀) Cs hCk hN hk hQ
      hb hY hN1 hm0 h1 (h2 X hD hX hc))

theorem extension_gives_ratio_bound (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs : ℝ) (X : Formalism.MainNotions.flipOneThree.Inst)
    (hCk : 0 ≤ Ckap) (hCm : 0 ≤ Cm) (h : Formalism.MainNotions.ColumnSystems.ExtendedModelRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc)
    (h2 : Formalism.MainNotions.ColumnSystems.ExtendedKappaBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs) :
    Formalism.MainNotions.flipOneThree.adm9 D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc (Cs + Ckap) X :=
  fun hH aT' hw m h0 =>
    ⟨h (X.LA aT') X.W X.Qq X.O X.Kf X.ι X.σ X.jO X.w X.std (extended_hypothesis_of_window hH hw) hH.2.1 m h0, fun hm => by
      have hD : Formalism.MainNotions.ColumnSystems.D1num (X.LA aT') :=
        ⟨X.std.1.prime, X.std.1.five_le, X.std.1.two_le, X.std.1.even⟩
      have hX := extended_hypothesis_of_window hH hw
      obtain ⟨hN, hk, hQ, hb, hY, hN1, hm0⟩ := loc_kap_facts C0 CYb Cde Ck CD Cb Cm (X.LA aT') hCm hD hX.1
      exact kap_margin Ckap _ _ _ ((X.LA aT').m0 Cm) m _ _ _ _ _ _ Cs hCk hN hk hQ hb hY hN1 hm0 hm
        (h2 (X.LA aT') hD hX hH.2.1)⟩

theorem goodSub_bot {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {V : Type*}
    [AddCommGroup V] [Module O V] [NoZeroSMulDivisors O V] (be : V → V → KK O) (L : Submodule O V) (D : ℝ) :
    GoodSub p be L ⊥ D := by
  refine ⟨⟨bot_le, fun c x hc _ hx => ?_⟩, fun u hu => ?_⟩
  · rw [Submodule.mem_bot] at hx ⊢
    exact (smul_eq_zero.mp hx).resolve_left hc
  · exfalso
    obtain ⟨hu0, hu1⟩ := hu
    rw [Submodule.mem_bot] at hu0
    exact not_isUnit_zero (hu1 0 0 (Submodule.zero_mem _) (by rw [hu0, smul_zero]))

theorem badShare_spec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) {V : Type*}
    [AddCommGroup V] [Module O V] [NoZeroSMulDivisors O V] (be : V → V → KK O) (L : Submodule O V) (D : ℝ) :
    0 ≤ badShare p be L D ∧ GoodShare p be L D (badShare p be L D) := by
  classical
  have h0S : 0 ∈ {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n} :=
    ⟨⊥, goodSub_bot p be L D, finrank_bot O V⟩
  by_cases hr0 : Module.finrank O L = 0
  · have hb : badShare p be L D = 0 := by simp [badShare, hr0]
    rw [hb]
    exact ⟨le_rfl, ⊥, goodSub_bot p be L D, by simp [hr0]⟩
  · have hbdd : ∀ n ∈ {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n},
        n ≤ Module.finrank O L := by
      rintro n ⟨L₁, hL₁, rfl⟩
      have h1 := LinearMap.rank_le_of_injective (Submodule.inclusion hL₁.1.1) (Submodule.inclusion_injective _)
      have h2 : Module.rank O L < Cardinal.aleph0 := (Cardinal.toNat_ne_zero.mp hr0).2
      exact Cardinal.toNat_le_toNat h1 h2
    have hmem := Nat.sSup_mem ⟨0, h0S⟩ ⟨_, hbdd⟩
    have hle := hbdd _ hmem
    have hb : badShare p be L D = ((Module.finrank O L : ℝ) -
        ((sSup {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n} : ℕ) : ℝ)) /
          (Module.finrank O L : ℝ) := by
      simp only [badShare, hr0, if_false]
    have hrpos : (0 : ℝ) < Module.finrank O L := by exact_mod_cast Nat.pos_of_ne_zero hr0
    have hle' : ((sSup {n : ℕ | ∃ L₁ : Submodule O V, GoodSub p be L L₁ D ∧ Module.finrank O L₁ = n} : ℕ) : ℝ)
        ≤ Module.finrank O L := by exact_mod_cast hle
    obtain ⟨L₁, hL₁, hn⟩ := hmem
    refine ⟨?_, L₁, hL₁, ?_⟩
    · rw [hb]
      exact div_nonneg (by linarith) hrpos.le
    · rw [hb, ← hn]
      have e : (1 - ((Module.finrank O L : ℝ) - (Module.finrank O L₁ : ℝ)) / (Module.finrank O L : ℝ)) *
          (Module.finrank O L : ℝ) = (Module.finrank O L₁ : ℝ) := by
        field_simp
        ring
      exact e.le

theorem noZeroSMul_mvPoly (O : Type*) [CommRing O] [IsDomain O] (σ : Type*) :
    NoZeroSMulDivisors O (MvPolynomial σ (KK O)) := by
  refine ⟨fun {c x} h => ?_⟩
  rw [Algebra.smul_def, mul_eq_zero] at h
  rcases h with h | h
  · left
    rw [IsScalarTower.algebraMap_eq O (KK O) (MvPolynomial σ (KK O)), RingHom.comp_apply,
      MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_zero, IsFractionRing.to_map_eq_zero_iff] at h
    exact h
  · exact Or.inr h

theorem depthD_nonneg (CA : ℝ) (hCA : 0 ≤ CA) (p a Nt N₁ r : ℕ) (Y : ℝ) (hp : 1 < p) (hr : 1 ≤ r) :
    0 ≤ Formalism.MainNotions.flipOneThree.depthD CA p a Nt N₁ r Y := by
  unfold Formalism.MainNotions.flipOneThree.depthD Formalism.MainNotions.flipOneThree.lgA Formalism.MainNotions.flipOneThree.kappaZeroExponent
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hlp : 0 < Real.log p := Real.log_pos hp'
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : 0 ≤ Real.logb p (8 * a + r) := by
    apply Real.logb_nonneg hp'
    nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
  have h2 : 0 ≤ Real.logb p a := div_nonneg (Real.log_natCast_nonneg a) hlp.le
  exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCA (sq_nonneg Y)) (by positivity))
    (by positivity)) (by linarith)) (mul_nonneg (by norm_num) (mul_nonneg (by positivity) h2))

theorem bad_share_of_extension_proposition (D : Formalism.BasicNotions.D7) (C₀ CH CA CE1 CE2 Cm Ckap Ct Cc : ℝ) (hCA : 0 ≤ CA)
    (h : Formalism.MainNotions.ColumnSystems.HerrExtensionClass D C₀ CH CH CH CH CH CE1 CE2 Cm Ckap Ct Cc) :
    Formalism.MainNotions.flipOneThree.admB2 D C₀ CH CA CE1 CE2 Cm Ckap Ct Cc := by
  refine depth_bound_of_extension D C₀ CH CA CE1 CE2 Cm Ckap Ct Cc h ?_
  intro X _ O _ _ _ hX j
  have hY := hX.1.1
  have hkp := hX.1.2.1
  have hm : 1 ≤ X.m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne X.m)
  have hp : 1 < X.p := by
    have hk : (2 : ℝ) ≤ X.k := by
      unfold Formalism.MainNotions.ColumnSystems.Loc.k; have : (1 : ℝ) ≤ (X.m : ℝ) := by exact_mod_cast hm
      linarith
    have hk2 : (4 : ℝ) ≤ X.k ^ 2 := by nlinarith
    have hY2 : (1 : ℝ) ≤ X.Y ^ 2 := by nlinarith
    have : (4 : ℝ) ≤ (X.p : ℝ) := by
      have := mul_le_mul hk2 hY2 (by norm_num) (by positivity)
      linarith
    exact_mod_cast (show (1 : ℝ) < X.p by linarith)
  have := noZeroSMul_mvPoly O (BVar (2 * segS X.TT j + 1) X.m (X.seg C₀ CE1 CE2 j).t)
  obtain ⟨h0, hg⟩ := badShare_spec X.p (segForm O X.p X.m (X.seg C₀ CE1 CE2 j))
    (segLat O X.p X.m (X.seg C₀ CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm))
    (Formalism.MainNotions.flipOneThree.depthD CA X.p X.a X.TT.card X.N1 X.m X.Y)
  exact ⟨depthD_nonneg CA hCA X.p X.a X.TT.card X.N1 X.m X.Y hp hm, h0, hg⟩

theorem posAdd_iff {n' : ℕ} (x y : Fin n') (d : ℕ) (hd1 : 1 ≤ d) (hdn : d ≤ n') :
    posAdd x d = y ↔ posAdd y (n' - d) = x := by
  simp only [posAdd, Fin.ext_iff, Fin.val_mk]
  constructor
  · intro h
    rw [← h, Nat.mod_add_mod, show x.val + d + (n' - d) = x.val + n' by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt x.isLt]
  · intro h
    rw [← h, Nat.mod_add_mod, show y.val + (n' - d) + d = y.val + n' by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt y.isLt]

theorem nearestEven {n' : ℕ} (TT : Finset (Fin n')) (y : Fin n') (hy : ¬ IsTypeV y)
    (hE : ∃ x ∈ TT, IsTypeV x) :
    dMinus TT y ≠ 0 ∧ Formalism.MainNotions.flipOneThree.dPrev TT y = dMinus TT y ∧
      Formalism.MainNotions.flipOneThree.yPrev TT y = posAdd y (n' - dMinus TT y) := by
  classical
  have hyl := y.isLt
  obtain ⟨x0, hx0, hx0e⟩ := hE
  have hx0l := x0.isLt
  have hS : ∃ d : ℕ, 0 < d ∧ d ≤ n' ∧ posAdd y (n' - d) ∈ TT ∧ IsTypeV (posAdd y (n' - d)) := by
    set d0 := (y.val + n' - x0.val) % n' with hd0
    have hne : x0 ≠ y := fun h => hy (h ▸ hx0e)
    have hd0pos : 0 < d0 := by
      rcases Nat.eq_zero_or_pos d0 with h | h
      · exfalso; apply hne
        have hdm := Nat.div_add_mod (y.val + n' - x0.val) n'
        have hq : (y.val + n' - x0.val) / n' < 2 := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
        rw [← hd0, h] at hdm
        interval_cases hqv : (y.val + n' - x0.val) / n' <;> (apply Fin.ext; omega)
      · exact h
    have hd0lt : d0 < n' := Nat.mod_lt _ (by omega)
    refine ⟨d0, hd0pos, hd0lt.le, ?_⟩
    have hpx : posAdd x0 d0 = y := by
      apply Fin.ext
      simp only [posAdd, hd0]
      rw [Nat.add_mod_mod]
      have : x0.val + (y.val + n' - x0.val) = y.val + n' := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hyl]
    have := (posAdd_iff x0 y d0 hd0pos hd0lt.le).1 hpx
    rw [this]; exact ⟨hx0, hx0e⟩
  have hdM : dMinus TT y = Nat.find hS := by unfold dMinus; rw [dif_pos hS]
  obtain ⟨hm1, hmn, hmT, hmV⟩ := Nat.find_spec hS
  have hmlt : Nat.find hS < n' := by
    rcases lt_or_eq_of_le hmn with h | h
    · exact h
    · exfalso
      rw [h, Nat.sub_self] at hmV
      apply hy
      have : posAdd y 0 = y := by apply Fin.ext; simp [posAdd, Nat.mod_eq_of_lt hyl]
      rwa [this] at hmV
  have hmem : Nat.find hS ∈ {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y} :=
    ⟨hm1, _, hmT, hmV, (posAdd_iff _ y _ hm1 hmn).2 rfl⟩
  have hP : Formalism.MainNotions.flipOneThree.dPrev TT y = Nat.find hS := by
    unfold Formalism.MainNotions.flipOneThree.dPrev
    apply le_antisymm (Nat.sInf_le hmem)
    have hne : ({d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y} : Set ℕ).Nonempty := ⟨_, hmem⟩
    obtain ⟨h1, x, hxT, hxV, hxy⟩ := Nat.sInf_mem hne
    by_contra hlt
    push Not at hlt
    have hle : sInf {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y} ≤ n' := by omega
    have hx := (posAdd_iff x y _ h1 hle).1 hxy
    have := Nat.find_min' hS ⟨h1, hle, hx ▸ hxT, hx ▸ hxV⟩
    omega
  refine ⟨by rw [hdM]; omega, by rw [hP, hdM], ?_⟩
  rw [hdM]
  apply Fin.ext
  show (y.val + (n' - Formalism.MainNotions.flipOneThree.dPrev TT y % n')) % n' = (posAdd y (n' - Nat.find hS)).val
  rw [hP, Nat.mod_eq_of_lt hmlt]
  rfl

open Classical in
theorem sum_boxLoc {n' : ℕ} (TT : Finset (Fin n')) (W : Finset ℤ) (f : (TT → ℤ) → ℝ) :
    ∑ a ∈ boxLoc n' TT W, f (fun t => a t) = ∑ aa ∈ Fintype.piFinset (fun _ : TT => W), f aa := by
  refine Finset.sum_nbij' (fun a => fun t : TT => a t) (fun aa i => if h : i ∈ TT then aa ⟨i, h⟩ else 0)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [boxLoc, Finset.mem_coe, Fintype.mem_piFinset] at ha ⊢
    intro t
    simpa [t.2] using ha t
  · intro aa haa
    simp only [boxLoc, Finset.mem_coe, Fintype.mem_piFinset] at haa ⊢
    intro i
    by_cases h : i ∈ TT
    · simpa [h] using haa ⟨i, h⟩
    · simp [h]
  · intro a ha
    simp only [boxLoc, Finset.mem_coe, Fintype.mem_piFinset] at ha
    funext i
    by_cases h : i ∈ TT
    · simp [h]
    · have hi := ha i
      simp only [h, if_false, Finset.mem_singleton] at hi
      simp [h, hi]
  · intro aa _
    funext t
    simp [t.2]
  · intro a _
    rfl

open Classical in
theorem card_boxLoc {n' : ℕ} (TT : Finset (Fin n')) (W : Finset ℤ) :
    (boxLoc n' TT W).card = W.card ^ TT.card := by
  simp [boxLoc, Fintype.card_piFinset, apply_ite Finset.card, Finset.prod_ite,
    Finset.filter_mem_eq_inter]

theorem meanLoc_eq (D : Formalism.BasicNotions.D7) (K : Consts) (s : Formalism.BasicNotions.Scale) {n' : ℕ} (TT : Finset (Fin n')) (m : ℕ)
    (Y a bl bu : ℝ) (κ : (TT → ℤ) → (TT → ℤ) → ℝ) (hA : winA D s = Formalism.MainNotions.flipOneThree.IaZ m Y a)
    (hB : winB D K s = Formalism.MainNotions.flipOneThree.IbZ bl bu) :
    meanLoc D K s n' TT (fun aw bw => κ (fun t => aw t) (fun t => bw t)) = Formalism.MainNotions.flipOneThree.meanKap TT m Y a bl bu κ := by
  unfold meanLoc Formalism.MainNotions.flipOneThree.meanKap
  rw [hA, hB, card_boxLoc, card_boxLoc]
  push_cast
  congr 1
  rw [← sum_boxLoc TT (Formalism.MainNotions.flipOneThree.IaZ m Y a) (fun aa => ∑ bb ∈ Fintype.piFinset (fun _ : TT => Formalism.MainNotions.flipOneThree.IbZ bl bu), κ aa bb)]
  refine Finset.sum_congr rfl fun aw _ => ?_
  exact sum_boxLoc TT (Formalism.MainNotions.flipOneThree.IbZ bl bu) (fun bb => κ (fun t => aw t) bb)

open Formalism.MainNotions.G Formalism.BasicNotions

def ibW (D : D7) (K : Consts) (s : Scale) : ℝ := Nstar D s * s.x ^ s.eps * La K s * s.b' / D.R.k

def OrbitSegs (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ (n' : ℕ) (TT : Finset (Fin n')),
    IsGoodOrbit n' TT (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x →
    L2 D L.sc < goodU L.sc.delta1 → 3 * Gp L.sc ≤ n' →
    (∃ x ∈ TT, IsTypeV x) ∧ 2 ≤ numSeg TT ∧ Formalism.MainNotions.flipOneThree.EvenGapHyp TT (Gp L.sc) (N1 L.sc)

theorem scale_facts (s : Scale) : 1 < s.a ∧ 0 < s.b' ∧ 0 < s.X' ∧ s.a / s.b' = s.X' := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 < s.L := by
    unfold Scale.L
    exact Real.rpow_pos_of_pos (by linarith) _
  have hb : 1 < s.b := by
    unfold Scale.b
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr hL
  have ha : 1 < s.a := by
    unfold Scale.a
    nlinarith
  have hX : 0 < s.X' := by
    unfold Scale.X'
    exact Real.exp_pos _
  have hb' : 0 < s.b' := by
    unfold Scale.b'
    exact div_pos (by linarith) hX
  refine ⟨ha, hb', hX, ?_⟩
  unfold Scale.b'
  field_simp

set_option maxHeartbeats 2000000 in

theorem hypI_69_to_13 (D : D7) (L : SizeData₂ D) (K : Consts) (C₀ CH : ℝ) (hK : K.Nonneg) (hC₀ : C₀ = K.La)
    (hCH0 : 0 ≤ CH) (hCHk : CH ≤ K.kI) (hCHD : CH ≤ K.DI) (hCHr : 2 * CH ≤ K.rho) (hc : 0 ≤ cG L)
    (p n' : ℕ) (TT : Finset (Fin n')) (hp0 : L.sc.p0 D.R.k ≤ (p : ℝ)) (hpX : (p : ℝ) < L.sc.X')
    (hband : ¬ InBand0 D K L.sc p) (hH : Formalism.MainNotions.AuxBlock8.HypI D L K p n' TT.card)
    (hseg : (∃ x ∈ TT, IsTypeV x) ∧ 2 ≤ numSeg TT ∧ Formalism.MainNotions.flipOneThree.EvenGapHyp TT (Gp L.sc) (N1 L.sc)) :
    Formalism.MainNotions.flipOneThree.HypI C₀ CH p n' (D.R.k - 1) TT (Gp L.sc) (N1 L.sc) (L.sc.x ^ (Scale.A / 2)) (L.sc.x ^ L.sc.eps / 20)
      L.sc.a L.sc.b' L.sc.b' (L.sc.b' + ibW D K L.sc) ⌊cG L⌋₊ (DIf K L p n') (8 * (DIf K L p n' + 1)) := by
  obtain ⟨ha1, hb', hX', haX⟩ := scale_facts L.sc
  obtain ⟨hE, h2s, hgap⟩ := hseg
  dsimp only [Formalism.MainNotions.AuxBlock8.HypI] at hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hH
  subst hC₀
  have hk3 : 3 ≤ D.R.k := by omega
  have hkR : ((D.R.k - 1 : ℕ) : ℝ) + 1 = (D.R.k : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (show 0 < D.R.k by omega)
  have hLa0 : 0 ≤ La K L.sc := by
    unfold La; exact mul_nonneg (mul_nonneg hK.1 (by positivity)) (Real.log_nonneg ha1.le)
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hY1 : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)
  have hNs : 0 ≤ Nstar D L.sc := by unfold Nstar Scale.delta1; positivity
  have hIb : 0 ≤ ibW D K L.sc := by unfold ibW; positivity
  have hIbb : 2 * ibW D K L.sc / L.sc.b' = 2 * (Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc) / D.R.k := by
    unfold ibW; field_simp
  have hN1 : (0 : ℝ) ≤ (N1 L.sc : ℝ) := Nat.cast_nonneg _
  have hsub : L.sc.b' + ibW D K L.sc - L.sc.b' = ibW D K L.sc := by ring
  have hde : 2 * Formalism.MainNotions.flipOneThree.deI CH K.La (D.R.k - 1) (N1 L.sc) L.sc.a L.sc.b' L.sc.b' (L.sc.b' + ibW D K L.sc) ≤
      rho D K L.sc := by
    unfold Formalism.MainNotions.flipOneThree.deI rho
    rw [hkR, hsub]
    have hL : Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a = La K L.sc := rfl
    rw [hL]
    have e : 2 * (CH * (N1 L.sc : ℝ) * La K L.sc / (D.R.k : ℝ) + 2 * ibW D K L.sc / L.sc.b') =
        (2 * CH) * ((N1 L.sc : ℝ) * La K L.sc) / (D.R.k : ℝ) + 2 * (2 * ibW D K L.sc / L.sc.b') := by ring
    rw [e, hIbb]
    have hm : (2 * CH) * ((N1 L.sc : ℝ) * La K L.sc) / (D.R.k : ℝ) ≤ K.rho * ((N1 L.sc : ℝ) * La K L.sc) / (D.R.k : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCHr (mul_nonneg hN1 hLa0)) hk0.le
    have e2 : K.rho * (N1 L.sc : ℝ) * La K L.sc / (D.R.k : ℝ) = K.rho * ((N1 L.sc : ℝ) * La K L.sc) / (D.R.k : ℝ) := by ring
    have e3 : 2 * (2 * (Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc) / (D.R.k : ℝ)) =
        4 * Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc / (D.R.k : ℝ) := by ring
    linarith
  have hp1 : (1 : ℝ) < p := by
    have : (1 : ℝ) < (D.R.k : ℝ) ^ 2 * (L.sc.x ^ (Scale.A / 2)) ^ 2 := by
      have h3k : (3 : ℝ) ≤ D.R.k := by exact_mod_cast hk3
      have hk2 : (9 : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by nlinarith
      have hY2 : (1 : ℝ) ≤ (L.sc.x ^ (Scale.A / 2)) ^ 2 := by nlinarith
      calc (1 : ℝ) < 9 * 1 := by norm_num
        _ ≤ (D.R.k : ℝ) ^ 2 * (L.sc.x ^ (Scale.A / 2)) ^ 2 := mul_le_mul hk2 hY2 (by norm_num) (by positivity)
    linarith
  have hlogb : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg hp1 ha1.le
  refine ⟨hY1, ?_, hE, h2s, hgap, ?_, ?_, h5, hb', le_rfl, by linarith, ?_, ?_, hCHk.trans h8, ?_, ?_, ?_, h2,
    ?_, ?_, ?_, ?_, le_rfl, ?_⟩
  · rw [hkR]; exact h1
  · unfold N1 orbitWindowCount; omega
  · omega
  · rw [hkR, hsub]; exact h6
  · rw [hsub]
    have : ibW D K L.sc = Nstar D L.sc * L.sc.x ^ L.sc.eps * La K L.sc * L.sc.b' / D.R.k := rfl
    rw [this]
    linarith only [h7]
  · rw [hkR]; exact h11
  · rw [hkR, haX]; exact h9
  · linarith only [hde, h3]
  · rw [hkR]
    have : 0 ≤ (TT.card : ℝ) * La K L.sc ^ 2 := by positivity
    have e : CH * (TT.card : ℝ) * Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a ^ 2 = CH * ((TT.card : ℝ) * La K L.sc ^ 2) := by
      unfold Formalism.MainNotions.flipOneThree.LaI La; ring
    have e' : K.kI * (TT.card : ℝ) * La K L.sc ^ 2 = K.kI * ((TT.card : ℝ) * La K L.sc ^ 2) := by ring
    rw [e]; rw [e'] at h10
    exact (mul_le_mul_of_nonneg_right hCHk this).trans h10
  · intro d hd ⟨hlo, hhi⟩
    apply hband
    refine ⟨hp0, hpX, d, hd.pos, ?_, ?_⟩
    · rw [haX] at hlo
      refine le_trans ?_ hlo
      exact mul_le_mul_of_nonneg_left (by linarith) hX'.le
    · rw [haX] at hhi
      refine le_trans hhi ?_
      exact mul_le_mul_of_nonneg_left (by linarith) hX'.le
  · rw [hkR]
    have : ((⌊cG L⌋₊ : ℕ) : ℝ) ≤ cG L := Nat.floor_le hc
    exact this.trans h12
  · rw [hkR]
    refine le_trans ?_ (Nat.le_ceil _)
    have hDI : 0 ≤ K.DI := hCH0.trans hCHD
    have hB : 0 ≤ (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a := by
      positivity
    have e1 : CH * (TT.card : ℝ) * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
        Real.logb p L.sc.a = (CH * (TT.card : ℝ)) * ((L.sc.x ^ (Scale.A / 2)) ^ 2 *
          ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a) := by ring
    have e2 : K.DI * NplusF L.sc n' * (L.sc.x ^ (Scale.A / 2)) ^ 2 * ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) *
        Real.logb p L.sc.a = (K.DI * NplusF L.sc n') * ((L.sc.x ^ (Scale.A / 2)) ^ 2 *
          ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hCHD h13 (Nat.cast_nonneg _) hDI) hB
  · rw [hkR]
    refine le_trans ?_ h14
    have hcl : ((⌊cG L⌋₊ : ℕ) : ℝ) ≤ cG L := Nat.floor_le hc
    have hA : 0 ≤ (D.R.k : ℝ) ^ 3 * (TT.card : ℝ) * Qp L.sc p ^ 4 := by unfold Qp; positivity
    have hBB : (((8 * (DIf K L p n' + 1) : ℕ) : ℝ) + (TT.card : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) +
        (n' : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ)) ≤ (8 * ((DIf K L p n' : ℝ) + 1)) + (TT.card : ℝ) * cG L + (n' : ℝ) * cG L := by
      push_cast
      have := mul_le_mul_of_nonneg_left hcl (Nat.cast_nonneg (α := ℝ) TT.card)
      have := mul_le_mul_of_nonneg_left hcl (Nat.cast_nonneg (α := ℝ) n')
      linarith
    have hB0 : 0 ≤ (((8 * (DIf K L p n' + 1) : ℕ) : ℝ) + (TT.card : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) +
        (n' : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ)) := by positivity
    have e1 : CH * (D.R.k : ℝ) ^ 3 * (TT.card : ℝ) * ((p : ℝ) ^ Gp L.sc) ^ 4 *
        (((8 * (DIf K L p n' + 1) : ℕ) : ℝ) + (TT.card : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) + (n' : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ)) *
        L.sc.x ^ (Scale.A / 2) = (CH * ((D.R.k : ℝ) ^ 3 * (TT.card : ℝ) * Qp L.sc p ^ 4) *
        (((8 * (DIf K L p n' + 1) : ℕ) : ℝ) + (TT.card : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) + (n' : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ))) *
        L.sc.x ^ (Scale.A / 2) := by unfold Qp; ring
    have e2 : K.kI * (D.R.k : ℝ) ^ 3 * (TT.card : ℝ) * Qp L.sc p ^ 4 *
        ((8 * ((DIf K L p n' : ℝ) + 1)) + (TT.card : ℝ) * cG L + (n' : ℝ) * cG L) * L.sc.x ^ (Scale.A / 2) =
        (K.kI * ((D.R.k : ℝ) ^ 3 * (TT.card : ℝ) * Qp L.sc p ^ 4) *
        ((8 * ((DIf K L p n' : ℝ) + 1)) + (TT.card : ℝ) * cG L + (n' : ℝ) * cG L)) * L.sc.x ^ (Scale.A / 2) := by ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hCHk hA) hBB hB0 (mul_nonneg (hCH0.trans hCHk) hA)

set_option maxHeartbeats 2000000 in
open Classical in

theorem tI_le_tIf (D : D7) (L : SizeData₂ D) (K : Consts) (C : ℝ) (hK : K.Nonneg) (hC0 : 0 ≤ C)
    (hCt1 : 2 * C ≤ K.kappaThresholdOne) (hCt2 : C ≤ K.kappaThresholdTwo) (hc : 0 ≤ cG L) (p n' : ℕ) (TT : Finset (Fin n'))
    (a b : Fin n' → ℤ) (hE : ∃ x ∈ TT, IsTypeV x) (hp1 : (1 : ℝ) < p) (hpb : (p : ℝ) < L.sc.a / L.sc.b')
    (hk : 1 ≤ D.R.k) (hNp : (TT.card : ℝ) ≤ NplusF L.sc n') :
    Formalism.MainNotions.flipOneThree.tI K.La C p n' (D.R.k - 1) TT (Gp L.sc) (N1 L.sc) L.sc.a L.sc.b' ⌊cG L⌋₊
      (8 * (DIf K L p n' + 1)) a b ≤ tIf K L p n' TT a b := by
  obtain ⟨ha1, hb', hX', haX⟩ := scale_facts L.sc
  have hkR : ((D.R.k - 1 : ℕ) : ℝ) + 1 = (D.R.k : ℝ) := by
    rw [Nat.cast_sub hk]; push_cast; ring
  have hk0 : (0 : ℝ) < D.R.k := by exact_mod_cast (show 0 < D.R.k by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hLa0 : 0 ≤ La K L.sc := by
    unfold La; exact mul_nonneg (mul_nonneg hK.1 (by positivity)) (Real.log_nonneg ha1.le)
  have hlogb : 0 ≤ Real.logb p L.sc.a := Real.logb_nonneg hp1 ha1.le
  have hcl : ((⌊cG L⌋₊ : ℕ) : ℝ) ≤ cG L := Nat.floor_le hc
  have hN : (0 : ℝ) ≤ (TT.card : ℝ) := Nat.cast_nonneg _
  have hN1 : (0 : ℝ) ≤ (N1 L.sc : ℝ) := Nat.cast_nonneg _
  have hQ : 0 ≤ Qp L.sc p := by unfold Qp; positivity
  have hbp : L.sc.b' ≤ L.sc.a / p := by
    rw [le_div_iff₀ hp0]
    have := (lt_div_iff₀ hb').1 hpb
    linarith

  have hsum : (∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
        min (b y : ℝ) ((a (Formalism.MainNotions.flipOneThree.yPrev TT y) : ℝ) / (p : ℝ) ^ Formalism.MainNotions.flipOneThree.dPrev TT y)) =
      ∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
        (if dMinus TT y = 0 then 0 else
          min (b y : ℝ) ((a (posAdd y (n' - dMinus TT y)) : ℝ) / (p : ℝ) ^ dMinus TT y)) := by
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨hne, hd, hyp⟩ := nearestEven TT y (Finset.mem_filter.1 hy).2 hE
    rw [if_neg hne, hd, hyp]
  unfold Formalism.MainNotions.flipOneThree.tI tIf
  dsimp only
  rw [hsum, hkR]

  have i1a : L.sc.b' / p ≤ L.sc.a / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hp0 (by positivity)]
    have := (le_div_iff₀ hp0).1 hbp
    nlinarith
  have i1b : Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a * L.sc.b' / (D.R.k : ℝ) ≤
      La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) := by
    have hL : Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a = La K L.sc := rfl
    rw [hL]
    have e : La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) = La K L.sc * (L.sc.a / p) / D.R.k := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbp hLa0) hk0.le
  have hin69 : 0 ≤ L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) := by positivity
  have hL : Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a * L.sc.a / ((p : ℝ) * D.R.k) = La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) := rfl
  have t1 : C * (TT.card : ℝ) * (N1 L.sc : ℝ) * (L.sc.a / (p : ℝ) ^ 2 + L.sc.b' / p +
        Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a * L.sc.a / (p * (D.R.k : ℝ)) +
        Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a * L.sc.b' / (D.R.k : ℝ)) ≤
      K.kappaThresholdOne * (TT.card : ℝ) * (N1 L.sc : ℝ) * (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) := by
    rw [hL]
    have hin : L.sc.a / (p : ℝ) ^ 2 + L.sc.b' / p + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) +
        Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a * L.sc.b' / (D.R.k : ℝ) ≤
        2 * (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k)) := by linarith
    have hNN : 0 ≤ (TT.card : ℝ) * (N1 L.sc : ℝ) := mul_nonneg hN hN1
    have key := mul_le_mul_of_nonneg_left hin (mul_nonneg hC0 hNN)
    calc C * (TT.card : ℝ) * (N1 L.sc : ℝ) * (L.sc.a / (p : ℝ) ^ 2 + L.sc.b' / p +
          La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a * L.sc.b' / (D.R.k : ℝ))
        = C * ((TT.card : ℝ) * (N1 L.sc : ℝ)) * (L.sc.a / (p : ℝ) ^ 2 + L.sc.b' / p +
          La K L.sc * L.sc.a / ((p : ℝ) * D.R.k) + Formalism.MainNotions.flipOneThree.LaI K.La (N1 L.sc) L.sc.a * L.sc.b' / (D.R.k : ℝ)) := by ring
      _ ≤ C * ((TT.card : ℝ) * (N1 L.sc : ℝ)) * (2 * (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k))) := key
      _ = (2 * C) * ((TT.card : ℝ) * (N1 L.sc : ℝ) * (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k))) := by ring
      _ ≤ K.kappaThresholdOne * ((TT.card : ℝ) * (N1 L.sc : ℝ) * (L.sc.a / (p : ℝ) ^ 2 + La K L.sc * L.sc.a / ((p : ℝ) * D.R.k))) :=
          mul_le_mul_of_nonneg_right hCt1 (mul_nonneg hNN hin69)
      _ = _ := by ring

  have hc8 : (((8 * (DIf K L p n' + 1) : ℕ) : ℝ)) + C * (TT.card : ℝ) * (D.R.k : ℝ) * Real.logb p L.sc.a +
      4 * (TT.card : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) + 2 * (n' : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) ≤ c6f K L p n' := by
    push_cast
    unfold c6f
    have hNp0 : (0 : ℝ) ≤ NplusF L.sc n' := hN.trans hNp
    have hT2 : (0 : ℝ) ≤ K.kappaThresholdTwo := hC0.trans hCt2
    have e1 : C * (TT.card : ℝ) * (D.R.k : ℝ) * Real.logb p L.sc.a ≤
        K.kappaThresholdTwo * NplusF L.sc n' * (D.R.k : ℝ) * Real.logb p L.sc.a := by
      have := mul_le_mul hCt2 hNp hN hT2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hk0.le) hlogb
    have e2 : 4 * (TT.card : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) ≤ 4 * NplusF L.sc n' * cG L := by
      have := mul_le_mul hNp hcl (Nat.cast_nonneg _) hNp0
      linarith
    have e3 := mul_le_mul_of_nonneg_left hcl (by positivity : (0 : ℝ) ≤ 2 * (n' : ℝ))
    push_cast at e2 e3
    linarith
  have hin2 : (p : ℝ) ^ Gp L.sc * ((((8 * (DIf K L p n' + 1) : ℕ) : ℝ)) + C * (TT.card : ℝ) * (D.R.k : ℝ) *
        Real.logb p L.sc.a + 4 * (TT.card : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) + 2 * (n' : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ)) +
        (D.R.k : ℝ) * (p : ℝ) ^ Gp L.sc + (D.R.k : ℝ) * Real.logb p L.sc.a + ((⌊cG L⌋₊ : ℕ) : ℝ) ≤
      Qp L.sc p * c6f K L p n' + (D.R.k : ℝ) * Qp L.sc p +
        (D.R.k : ℝ) * Real.logb p L.sc.a + cG L := by
    have := mul_le_mul_of_nonneg_left hc8 hQ
    unfold Qp at this ⊢
    linarith
  have hin20 : 0 ≤ Qp L.sc p * c6f K L p n' + (D.R.k : ℝ) * Qp L.sc p +
      (D.R.k : ℝ) * Real.logb p L.sc.a + cG L := by
    have : 0 ≤ K.kappaThresholdTwo := hC0.trans hCt2
    have hNp0 : (0 : ℝ) ≤ NplusF L.sc n' := hN.trans hNp
    have : 0 ≤ c6f K L p n' := by unfold c6f; positivity
    positivity
  have hin2' : 0 ≤ (p : ℝ) ^ Gp L.sc * ((((8 * (DIf K L p n' + 1) : ℕ) : ℝ)) + C * (TT.card : ℝ) * (D.R.k : ℝ) *
        Real.logb p L.sc.a + 4 * (TT.card : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) + 2 * (n' : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ)) +
        (D.R.k : ℝ) * (p : ℝ) ^ Gp L.sc + (D.R.k : ℝ) * Real.logb p L.sc.a + ((⌊cG L⌋₊ : ℕ) : ℝ) := by positivity
  have t2 := mul_le_mul (mul_le_mul_of_nonneg_right hCt2 hN) hin2 hin2' (mul_nonneg (hC0.trans hCt2) hN)
  have t3 : 2 * (n' : ℝ) * ((⌊cG L⌋₊ : ℕ) : ℝ) ≤ 2 * (n' : ℝ) * cG L :=
    mul_le_mul_of_nonneg_left hcl (by positivity)
  linarith

theorem winA_eq (D : D7) (s : Scale) (hk : 1 ≤ D.R.k) :
    winA D s = Formalism.MainNotions.flipOneThree.IaZ (D.R.k - 1) (s.x ^ (Scale.A / 2)) s.a := by
  unfold winA Formalism.MainNotions.flipOneThree.IaZ
  rw [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel]

theorem winB_eq (D : D7) (K : Consts) (s : Scale) :
    winB D K s = Formalism.MainNotions.flipOneThree.IbZ s.b' (s.b' + ibW D K s) := rfl

theorem kappa_share_of_least_serving (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (hX : KapIDef X K) :
    Formalism.MainNotions.AuxBlock8.adm7 D L X K := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS TT _ _ _ _ _ _ _ a b _ lam0 hbase hdom
  exact (hX.mem p n' TT a b).2 W Qq O Kf ι σ j w hS lam0 hbase hdom

set_option maxHeartbeats 2000000 in

theorem type_one_hypothesis_of_segments (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Cm CH C : ℝ) (hX : KapIDef X K)
    (hK : K.Nonneg) (hCH0 : 0 ≤ CH) (hCHk : CH ≤ K.kI) (hCHD : CH ≤ K.DI) (hCHr : 2 * CH ≤ K.rho) (hC0 : 0 ≤ C)
    (hCt1 : 2 * C ≤ K.kappaThresholdOne) (hCt2 : C ≤ K.kappaThresholdTwo) (hCm : C ≤ Cm) (hc : 0 ≤ cG L) (hOrb : OrbitSegs D L)
    (h : Formalism.MainNotions.flipOneThree.Conclusion2 D K.La CH C) : Formalism.MainNotions.AuxBlock8.adm8 D L X K Cm := by
  intro p n' hp TT hG hL2 hG3 hp0 hpX hband hH
  refine ⟨fun a b => (hX.mem_Icc p n' TT a b).1, ?_⟩
  have hseg := hOrb n' TT hG hL2 hG3
  have hH13 := hypI_69_to_13 D L K K.La CH hK rfl hCH0 hCHk hCHD hCHr hc p n' TT hp0 hpX hband hH hseg
  obtain ⟨κ, hκ0, hmean, hLP⟩ := h p n' (D.R.k - 1) TT (Gp L.sc) (N1 L.sc) _ _ _ _ _ _ _ _ _ hH13
  have hk : 1 ≤ D.R.k := by
    have := hH13.2.2.2.2.2.2.1
    omega
  have hpb : (p : ℝ) < L.sc.a / L.sc.b' := hH13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hWA := winA_eq D L.sc hk
  have hWB := winB_eq D K L.sc
  have hpt : ∀ a ∈ boxLoc n' TT (winA D L.sc), ∀ b ∈ boxLoc n' TT (winB D K L.sc),
      X.kapI p n' TT a b ≤ κ (fun t => a t) (fun t => b t) := by
    intro a ha b hb
    apply hX.le
    refine ⟨hκ0 _ _, ?_⟩
    intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS lam0 hbase hdom
    refine hLP W Qq O Kf ι σ j w hS a b lam0 ⟨hbase, hdom, fun s hs => ⟨?_, ?_⟩⟩ _ ?_
    · classical
      have := (Fintype.mem_piFinset.1 ha) s
      simp only [if_pos hs] at this
      rw [← hWA]; exact this
    · classical
      have := (Fintype.mem_piFinset.1 hb) s
      simp only [if_pos hs] at this
      rw [← hWB]; exact this
    · exact (tI_le_tIf D L K C hK hC0 hCt1 hCt2 hc p n' TT a b hseg.1 hp1 hpb hk
        hH.2.2.2.2.2.2.2.2.2.2.2.2.1).trans (Nat.le_ceil _)
  have hmono : meanLoc D K L.sc n' TT (X.kapI p n' TT) ≤
      meanLoc D K L.sc n' TT (fun a b => κ (fun t => a t) (fun t => b t)) := by
    unfold meanLoc
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hpt a ha b hb
  rw [meanLoc_eq D K L.sc TT (D.R.k - 1) _ _ _ _ κ hWA hWB] at hmono
  refine hmono.trans (hmean.trans ?_)
  have hY : 0 < L.sc.x ^ (Scale.A / 2) := Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  apply div_le_div_of_nonneg_right _ hY.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

section LogVal
open Formalism.MainNotions.CovariantDegrees

theorem padicGe_add {p : ℕ} [Fact p.Prime] {x y : ℚ} {c : ℝ} (hx : PadicGe p x c) (hy : PadicGe p y c) :
    PadicGe p (x + y) c := by
  unfold PadicGe at *
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · simpa using (Or.inr hx : x = 0 ∨ c ≤ (padicValRat p x : ℝ))
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  have h1 := padicValRat.min_le_padicValRat_add (p := p) hxy
  have h2 : (min (padicValRat p x) (padicValRat p y) : ℝ) ≤ (padicValRat p (x + y) : ℝ) := by
    exact_mod_cast h1
  exact (le_min hx hy).trans (by simpa using h2)

theorem padicGe_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) {c : ℝ}
    (h : ∀ i ∈ s, PadicGe p (f i) c) : PadicGe p (∑ i ∈ s, f i) c := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp [PadicGe]) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha]
  exact padicGe_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem padicValNat_lt_of_lt_pow {p : ℕ} [hp : Fact p.Prime] {y t : ℕ} (hy : 1 ≤ y) (hlt : y < p ^ (t + 1)) :
    padicValNat p y ≤ t := by
  by_contra hc
  push_neg at hc
  have h1 : p ^ (t + 1) ∣ y := (pow_dvd_pow p (Nat.succ_le_of_lt hc)).trans pow_padicValNat_dvd
  have h2 := Nat.le_of_dvd hy h1
  omega

theorem logVal_clause1 (p : ℕ) (hp : p.Prime) (t s : ℕ) :
    PadicGe p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * ∑ y ∈ Finset.Ico 1 (p ^ (t + 1)), ((y : ℚ) ^ s)⁻¹) s := by
  haveI := Fact.mk hp
  rw [Finset.mul_sum]
  apply padicGe_sum
  intro y hy
  rw [Finset.mem_Ico] at hy
  have hy0 : (y : ℚ) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
  have hP : ((p ^ (t + 1) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.ne_zero
  right
  rw [padicValRat.mul (pow_ne_zero _ hP) (inv_ne_zero (pow_ne_zero _ hy0)), padicValRat.inv,
    padicValRat.pow, padicValRat.pow, padicValRat.of_nat, padicValRat.of_nat,
    padicValNat.prime_pow]
  have hv : ((padicValRat p (y : ℚ) : ℤ) : ℝ) ≤ t := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat_lt_of_lt_pow hy.1 hy.2
  push_cast
  nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]

theorem logVal_holds : Formalism.MainNotions.ColumnSystems.logVal := by
  intro p hp hp5 t s hs
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨logVal_clause1 p hp t s, ?_⟩
  rcases logVal_clause1 p hp t s with h0 | h1
  · left; rw [h0, zero_div]
  right
  set x := ((p ^ (t + 1) : ℕ) : ℚ) ^ s * ∑ y ∈ Finset.Ico 1 (p ^ (t + 1)), ((y : ℚ) ^ s)⁻¹ with hxdef
  by_cases hx : x = 0
  · exfalso
    rw [hx, padicValRat.zero] at h1
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs
    push_cast at h1
    linarith
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  rw [padicValRat.div hx hs0]
  have hps : ((padicValRat p (s : ℚ) : ℤ) : ℝ) = (padicValNat p s : ℝ) := by
    have e : padicValRat p (s : ℚ) = ((padicValNat p s : ℕ) : ℤ) := padicValRat.of_nat
    simp [e]
  have hvs : 4 * (padicValNat p s : ℝ) + 1 ≤ s := by
    have hb : (1 : ℝ) + (padicValNat p s : ℝ) * 4 ≤ (1 + 4) ^ padicValNat p s :=
      one_add_mul_le_pow (by norm_num) _
    have h5 : ((1 : ℝ) + 4) ^ padicValNat p s ≤ (p : ℝ) ^ padicValNat p s := by
      apply pow_le_pow_left₀ (by norm_num); norm_num; exact_mod_cast hp5
    have hd : p ^ padicValNat p s ∣ s := (padicValNat_dvd_iff_le (show s ≠ 0 by omega)).mpr le_rfl
    have hle : p ^ padicValNat p s ≤ s := Nat.le_of_dvd (by omega) hd
    have hle' : (p : ℝ) ^ padicValNat p s ≤ s := by exact_mod_cast hle
    linarith
  have hp4 : 1 / ((p : ℝ) - 1) ≤ 1 / 4 := by
    have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  push_cast
  rw [hps]
  linarith

theorem decomposition_gives_log_valuation (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.UnitFunctionExpansion D) : Formalism.MainNotions.ColumnSystems.adm12 D := ⟨h, logVal_holds⟩

end LogVal

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.GradedWeylDivisibility

theorem span_prod_smul {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {S : Type*} [Fintype S] [DecidableEq S]
    {A : S → Type*} [∀ s, CommRing (A s)] [∀ s, Algebra R (A s)] (φ : ∀ s, A s →ₐ[R] B)
    (M M' : ∀ s, Submodule R (A s)) (c : S → R) (hc : ∀ s, ∀ x ∈ M s, c s • x ∈ M' s) :
    ∀ P ∈ Submodule.span R {P | ∃ F : ∀ s, A s, (∀ s, F s ∈ M s) ∧ P = ∏ s, φ s (F s)},
      (∏ s, c s) • P ∈ Submodule.span R {P | ∃ F : ∀ s, A s, (∀ s, F s ∈ M' s) ∧ P = ∏ s, φ s (F s)} := by
  intro P hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun s => c s • F s, fun s => hc s _ (hF s), ?_⟩
    simp only [map_smul]
    simp only [Algebra.smul_def]
    rw [Finset.prod_mul_distrib, map_prod]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem tensorLat_smul {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] [DecidableEq S]
    {k n : ℕ} (M M' : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) (c : S → R)
    (hc : ∀ s, ∀ x ∈ M s, c s • x ∈ M' s) : ∀ P ∈ tensorLat R K M, (∏ s, c s) • P ∈ tensorLat R K M' :=
  span_prod_smul (fun s => (blockEmb K s).restrictScalars R) M M' c hc

theorem tenV_smul {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] (P : Places p O Kf)
    (M M' : ∀ v, Submodule O (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)) (c : Fin P.nV → O)
    (hc : ∀ v, ∀ x ∈ M v, c v • x ∈ M' v) : ∀ X ∈ P.tenV M, (∏ v, c v) • X ∈ P.tenV M' :=
  span_prod_smul (fun v => (P.vEmb v).restrictScalars O) M M' c hc

theorem funMod_smul {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {P : Places p O Kf} (C : Level P) (Hv Hv' : P.Tup → Submodule O P.Xsp) (c : O)
    (hc : ∀ L, P.IsLatTup L → ∀ x ∈ Hv L, c • x ∈ Hv' L) : ∀ F ∈ C.funMod Hv, c • F ∈ C.funMod Hv' := by
  intro F hF
  simp only [Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker] at hF ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := hF
  refine ⟨⟨fun L hL => ?_, fun L hL => ?_⟩, fun γ L => ?_⟩
  · simpa using hc L hL _ (h1 L hL)
  · rw [map_smul, h2 L hL, smul_zero]
  · rw [map_smul, h3 γ L, smul_zero]

def wExp (p m : ℕ) (lam : Fin (m + 1) → ℤ) : ℕ := N0 (m + 1) * deF p (m + 1) (ellWt lam)

def WeylSandwichG (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∀ (m : ℕ) (lam : Fin (m + 1) → ℤ) (Λ : Submodule (D.gat u w hg).O (Fin (m + 1) → (D.gat u w hg).Kf)),
      (∀ x ∈ H0 (D.gat u w hg).O m lam Λ,
        (((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ wExp (D.what₂.places.resChar w) m lam) • x ∈
          Dl0 (D.gat u w hg).O m lam Λ) ∧
      Dl0 (D.gat u w hg).O m lam Λ ≤ H0 (D.gat u w hg).O m lam Λ

def ExpBoundG (D : D7) {L : SizeData₂ D} (X : Inst D L) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∑ v, ∑ s : Fin ((D.gat u w hg).P.n' v),
      wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s) ≤
        X.ep (D.what₂.places.resChar w)

theorem fk_logb_ge_one (D : D7) (L : SizeData₂ D) (p : ℕ) (hp : p.Prime) (hpa : (p : ℝ) ≤ L.sc.a) :
    1 ≤ (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 1 ≤ Real.logb p L.sc.a := by
    rw [Real.le_logb_iff_rpow_le hp1 (by linarith), Real.rpow_one]; exact hpa
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have h1 := D.R.one_le_n
    have : 1 ≤ D.R.f := by unfold Formalism.BasicNotions.Ranks.f; omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 2 := by
    have h5 := D.R.five_le_k
    have : (1 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    nlinarith
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul hf hk zero_le_one (by linarith)) hlog zero_le_one (by positivity)

theorem weyl_sandwich_of_factors (D : D7) (L : SizeData₂ D) (X : Inst D L) (Ce : ℝ) (hCe : 0 ≤ Ce) (hEp : EpDef X Ce)
    (hW : WeylSandwichG D) (hE : ExpBoundG D X) : Formalism.MainNotions.AuxBlock8.adm9 D L X Ce := by
  refine ⟨fun p hp hpa => hEp.le p hCe (fk_logb_ge_one D L p hp hpa), fun u w hg _ => ?_⟩

  have hv : ∀ (L : (D.gat u w hg).P.Tup) (v : Fin (D.gat u w hg).P.nV), ∀ x ∈ Hten (D.gat u w hg).O ((D.gat u w hg).P.lam0 v) (fun s => extO (D.gat u w hg).O ((D.gat u w hg).P.ι v) ((D.gat u w hg).P.σ v) s.val (L v)),
      (∏ s : Fin ((D.gat u w hg).P.n' v), (((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s))) • x ∈
        HtenW (D.gat u w hg).O ((D.gat u w hg).P.lam0 v) (fun s => extO (D.gat u w hg).O ((D.gat u w hg).P.ι v) ((D.gat u w hg).P.σ v) s.val (L v)) := by
    intro L v
    exact tensorLat_smul _ _ _ fun s x hx => (hW u w hg (D.gat u w hg).P.m _ _).1 x hx
  have hv' : ∀ (L : (D.gat u w hg).P.Tup) (v : Fin (D.gat u w hg).P.nV), ∀ x ∈ HtenW (D.gat u w hg).O ((D.gat u w hg).P.lam0 v) (fun s => extO (D.gat u w hg).O ((D.gat u w hg).P.ι v) ((D.gat u w hg).P.σ v) s.val (L v)),
      (∏ _s : Fin ((D.gat u w hg).P.n' v), (1 : (D.gat u w hg).O)) • x ∈
        Hten (D.gat u w hg).O ((D.gat u w hg).P.lam0 v) (fun s => extO (D.gat u w hg).O ((D.gat u w hg).P.ι v) ((D.gat u w hg).P.σ v) s.val (L v)) := by
    intro L v
    exact tensorLat_smul _ _ _ fun s x hx => by rw [one_smul]; exact (hW u w hg (D.gat u w hg).P.m _ _).2 hx
  have hT : ∀ L : (D.gat u w hg).P.Tup, ∀ x ∈ (D.gat u w hg).P.Htup L,
      (∏ v, ∏ s : Fin ((D.gat u w hg).P.n' v), (((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s))) • x ∈ (D.gat u w hg).P.HtupW L :=
    fun L => tenV_smul (D.gat u w hg).P _ _ _ fun v x hx => hv L v x hx
  have hT' : ∀ L : (D.gat u w hg).P.Tup, ∀ x ∈ (D.gat u w hg).P.HtupW L, (∏ _v : Fin (D.gat u w hg).P.nV, ∏ _s : Fin ((D.gat u w hg).P.n' _v), (1 : (D.gat u w hg).O)) • x ∈ (D.gat u w hg).P.Htup L :=
    fun L => tenV_smul (D.gat u w hg).P _ _ _ fun v x hx => hv' L v x hx
  have hprod : (∏ v, ∏ s : Fin ((D.gat u w hg).P.n' v), (((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s))) =
      ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ (∑ v, ∑ s : Fin ((D.gat u w hg).P.n' v), wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s)) := by
    simp only [Finset.prod_pow_eq_pow_sum]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hE u w hg)
  refine ⟨?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    show (((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ X.ep (D.what₂.places.resChar w)) • F ∈ (D.gat u w hg).M
    rw [hk, pow_add, mul_comm, mul_smul]
    have : (((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ (∑ v, ∑ s : Fin ((D.gat u w hg).P.n' v), wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s))) • F ∈ (D.gat u w hg).M := by
      rw [GAtP.M, GAtP.funMod, Submodule.mem_pi]
      intro i _
      rw [← hprod]
      exact funMod_smul ((D.gat u w hg).lev i) _ _ _ (fun L _ x hx => hT L x hx) (F i) ((Submodule.mem_pi.1 hF) i (Set.mem_univ _))
    exact Submodule.smul_mem _ _ this
  · intro F hF
    rw [GAtP.Mna, GAtP.funMod, Submodule.mem_pi]
    intro i _
    have := funMod_smul ((D.gat u w hg).lev i) _ _ (∏ _v : Fin (D.gat u w hg).P.nV, ∏ _s : Fin ((D.gat u w hg).P.n' _v), (1 : (D.gat u w hg).O)) (fun L _ x hx => hT' L x hx)
      (F i) ((Submodule.mem_pi.1 hF) i (Set.mem_univ _))
    simpa using this

def ModelSandwichG (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (m : ℕ) (lam : Fin (m + 1) → ℤ), Antitone lam →
    (∀ x ∈ Submodule.map (MvPolynomial.mapAlgHom (Algebra.ofId (D.gat u w hg).O (D.gat u w hg).Kf)).toLinearMap
        (dualWeyl (D.gat u w hg).O (m + 1) (m + 1) (nuOf lam)),
      (((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ wExp (D.what₂.places.resChar w) m lam) • x ∈
        Submodule.map (MvPolynomial.mapAlgHom (Algebra.ofId (D.gat u w hg).O (D.gat u w hg).Kf)).toLinearMap
          (weyl (D.gat u w hg).O (m + 1) (m + 1) le_rfl (nuOf lam))) ∧
    Submodule.map (MvPolynomial.mapAlgHom (Algebra.ofId (D.gat u w hg).O (D.gat u w hg).Kf)).toLinearMap
        (weyl (D.gat u w hg).O (m + 1) (m + 1) le_rfl (nuOf lam)) ≤
      Submodule.map (MvPolynomial.mapAlgHom (Algebra.ofId (D.gat u w hg).O (D.gat u w hg).Kf)).toLinearMap
        (dualWeyl (D.gat u w hg).O (m + 1) (m + 1) (nuOf lam))

theorem weylSandwich_of_model (D : D7) (h : ModelSandwichG D) : WeylSandwichG D := by
  intro u w hg m lam Λ
  by_cases hlam : Antitone lam
  · obtain ⟨h1, h2⟩ := h u w hg m lam hlam
    unfold H0 Dl0
    rw [if_pos hlam, if_pos hlam]
    constructor
    · intro x hx
      rw [Submodule.mem_iInf] at hx ⊢
      intro g
      have hx' := hx g
      rw [Submodule.mem_iInf] at hx' ⊢
      intro hgL
      obtain ⟨y, hy, rfl⟩ := hx' hgL
      refine ⟨(((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ wExp (D.what₂.places.resChar w) m lam) • y, ?_, ?_⟩
      · unfold Formalism.GradedWeylDivisibility.nablaL at hy
        unfold deltaL
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.map_smul]
        exact h1 _ (Submodule.mem_comap.1 hy)
      · simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
        rw [smul_comm]
    · intro x hx
      rw [Submodule.mem_iInf] at hx ⊢
      intro g
      have hx' := hx g
      rw [Submodule.mem_iInf] at hx' ⊢
      intro hgL
      obtain ⟨y, hy, rfl⟩ := hx' hgL
      refine ⟨y, ?_, rfl⟩
      unfold deltaL at hy
      unfold Formalism.GradedWeylDivisibility.nablaL
      rw [SetLike.mem_coe, Submodule.mem_comap]
      exact h2 (Submodule.mem_comap.1 hy)
  · unfold H0 Dl0
    rw [if_neg hlam, if_neg hlam]
    refine ⟨fun x hx => ?_, le_rfl⟩
    rw [(Submodule.mem_bot _).1 hx, smul_zero]
    exact Submodule.zero_mem _

open Formalism.MainNotions.G Formalism.BasicNotions

def TiedSys (D : D7) (Y : LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (LinearSubstitution : Formalism.MainNotions.FormalGroupSystem.Sys (D.what₂.places.resChar w)) : Prop :=
  ∃ std vp unif eO eO_spec dG dG_spec om,
    LinearSubstitution = Formalism.MainNotions.FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg) (Y.Ch u w hg) std vp unif eO eO_spec dG
                      dG_spec om

theorem foldr_map_comp {α β : Type*} (f : α → β → β) (l : List α) (x : β) :
    (l.map f).foldr (fun g h => g ∘ h) id x = l.foldr (fun a y => f a y) x := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, Function.comp_apply, ih]

theorem foldr_map' {α β γ : Type*} (f : α → β) (g : β → γ → γ) (l : List α) (x : γ) :
    (l.map f).foldr g x = l.foldr (fun a y => g (f a) y) x := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, ih]

theorem eO_eq_vUnit {p : ℕ} (G : GAtP p) (vp : G.O) (unif : Irreducible vp) (eO : ℕ)
    (h : Associated (p : G.O) (vp ^ eO)) : (eO : ℝ) = vUnit G := by
  obtain ⟨u, hu⟩ := h
  have h1 := congrArg (IsDiscreteValuationRing.addVal G.O) hu
  rw [AddValuation.map_mul, IsDiscreteValuationRing.addVal_eq_zero_of_unit, add_zero,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer unif, nsmul_one] at h1
  unfold vUnit
  rw [h1]
  simp

theorem scale_pow_mono {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] (vp : O) (hvp : algebraMap O Kf vp ≠ 0) (N : Submodule O X) {a b : ℤ}
    (hab : b ≤ a) {x : X} (hx : x ∈ scale ((algebraMap O Kf vp) ^ a) N) :
    x ∈ scale ((algebraMap O Kf vp) ^ b) N := by
  rw [scale, Submodule.mem_map] at hx ⊢
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨(vp ^ (a - b).toNat) • n, N.smul_mem _ hn, ?_⟩
  show (algebraMap O Kf vp ^ b) • (vp ^ (a - b).toNat • n) = (algebraMap O Kf vp ^ a) • n
  rw [← algebraMap_smul Kf (vp ^ (a - b).toNat) n, smul_smul, map_pow, ← zpow_natCast,
    ← zpow_add₀ hvp, Int.toNat_of_nonneg (sub_nonneg.mpr hab), add_sub_cancel]

def SysU (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (low : D.what₂.Word → D.what₂.places.Pl → ℝ) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
        (dG_spec : _) (om : _) (Y5 : Formalism.MainNotions.FormalGroupSystem.Pend (Formalism.MainNotions.FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg)
          (Y.Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
        Formalism.MainNotions.FormalGroupSystem.VolumeRatio₂ D _ Y5 ∧ Formalism.MainNotions.FormalGroupSystem.adm11 D _ Y5 ∧ Formalism.MainNotions.FormalGroupSystem.LowTermBound D _ Y5 ∧
        Function.Injective (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf) ∧
        ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
          (∀ v, v ∉ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg) → ∀ j < D.R.m, Y5.LowAt j v (Fn v (j + 1))) ∧
          low u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ v ∈ Finset.univ \ (reps X (D.what₂.places.resChar w)).image (Y.vOf u w hg),
            Fn v j) - ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)

open Classical in

theorem lower_bound_of_large_residue (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (low : D.what₂.Word → D.what₂.places.Pl → ℝ) (hP : SysU D L X Y low)
    (hNum : Formalism.MainNotions.FormalGroupSystem.SmallResidueCharComparison D L X Y K)
    (hLarge : ∀ (w : D.what₂.places.Pl), Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) < 1 →
      ∀ t0 ∈ reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        gU X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 - Pr X K (bL L) (D.what₂.places.resChar w) j t0 ≤ 0 ∧
        g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤ 0) :
    Formalism.MainNotions.AuxBlock8.UnitBoundLowTerm D L X Y K low := by
  intro hT hLT u w hg VVs VV' p hVVs hVV' F hF
  obtain ⟨hFact, std, vp, unif, eO, eO_spec, dG, dG_spec, om, Y5, hU2, h11, h5D, hinjK, Fn, hFn, hdiv⟩ :=
    hP hT hLT u w hg
  obtain ⟨hmm, -, -, -, hinj, -⟩ := hLT u w hg
  set vOf := Y.vOf u w hg with hvOf
  have hVVr : VV' ⊆ reps X p := hVV'.trans hVVs
  set A : Prop := 1 ≤ Real.logb p (2 * L.sc.a) with hA
  let Gn : Fin (D.gat u w hg).P.nV → ℕ → ℝ := fun v j =>
    if h : ∃ t0 ∈ VV', vOf t0 = v then
      (if A then gU X K (aL L) (bL L) p j (Classical.choose h) else min (Formalism.MainNotions.FormalGroupSystem.gB p (Y.Fl u w hg).t ((Y.Fl u w hg).TT v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j) (Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j)) else 0
  let PRn : Fin (D.gat u w hg).P.nV → ℕ → ℝ := fun v j =>
    if h : ∃ t0 ∈ VV', vOf t0 = v then (if A then Pr X K (bL L) p j (Classical.choose h) else Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j) else 0
  let G0n : Fin (D.gat u w hg).P.nV → ℕ → ℝ := fun v j =>
    if h : ∃ t0 ∈ reps X p, vOf t0 = v then
      (if A then max (g0 X K (aL L) (bL L) p j (Classical.choose h)) 0 else 0) else Fn v j
  let S : Fin (D.gat u w hg).P.nV → ℝ := fun v => ∑ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, max (Gn v j - PRn v j - G0n v j) 0
  let BB := VV'.image vOf
  have chV : ∀ t0 ∈ VV', ∀ h : ∃ t1 ∈ VV', vOf t1 = vOf t0, Classical.choose h = t0 := by
    intro t0 ht0 h
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    exact hinj (hVVr h1) (hVVr ht0) h2
  have chR : ∀ t0 ∈ reps X p, ∀ h : ∃ t1 ∈ reps X p, vOf t1 = vOf t0, Classical.choose h = t0 := by
    intro t0 ht0 h
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    exact hinj h1 ht0 h2
  have hlift : ∀ j, j ∈ SizeData₂.lifts D ↔ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm := by
    intro j; rw [hmm]; rfl

  have hI : ∀ t0 ∈ VV', ∀ j ∈ SizeData₂.lifts D,
      max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0) (max (g0 X K (aL L) (bL L) p j t0) 0) ≤
        max (Gn (vOf t0) j - PRn (vOf t0) j) (G0n (vOf t0) j) := by
    intro t0 ht0 j hj
    have h : ∃ t1 ∈ VV', vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
    have h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0 := ⟨t0, hVVr ht0, rfl⟩
    simp only [Gn, PRn, G0n, dif_pos h, dif_pos h', chV t0 ht0 h, chR t0 (hVVr ht0) h']
    by_cases hAA : A
    · simp only [if_pos hAA]; exact le_rfl
    · simp only [if_neg hAA]
      obtain ⟨h1, h2⟩ := hLarge w (lt_of_not_ge hAA) t0 (hVVr ht0) j hj
      have : max (g0 X K (aL L) (bL L) p j t0) 0 = 0 := max_eq_right h2
      rw [this]
      exact le_trans (max_le h1 le_rfl) (le_max_right _ _)
  have hII : ∀ t0 ∈ reps X p, ∀ j ∈ SizeData₂.lifts D, max (g0 X K (aL L) (bL L) p j t0) 0 ≤ G0n (vOf t0) j := by
    intro t0 ht0 j hj
    have h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
    simp only [G0n, dif_pos h', chR t0 ht0 h']
    by_cases hAA : A
    · simp only [if_pos hAA]; exact le_rfl
    · simp only [if_neg hAA]; exact (max_eq_right (hLarge w (lt_of_not_ge hAA) t0 ht0 j hj).2).le

  have c1 : ∀ v ∈ BB, ∀ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, Gn v j ≤ Formalism.MainNotions.FormalGroupSystem.gB p (Y.Fl u w hg).t ((Y.Fl u w hg).TT v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j := by
    intro v hv j hj
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv
    have h : ∃ t1 ∈ VV', vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
    simp only [Gn, dif_pos h, chV t0 ht0 h]
    by_cases hAA : A
    · simp only [if_pos hAA]; exact (hNum hT hLT u w hg hAA t0 (hVVr ht0) j ((hlift j).2 hj)).1
    · simp only [if_neg hAA]; exact min_le_left _ _
  have c2 : ∀ v, ∀ j < (Y.Fl u w hg).mm, Y5.LowAt j v (G0n v (j + 1)) := by
    intro v j hj
    by_cases h : ∃ t0 ∈ reps X p, vOf t0 = v
    · obtain ⟨t0, ht0, rfl⟩ := h
      refine Formalism.MainNotions.FormalGroupSystem.lowAt_max D _ Y5 hU2 h11 (vOf t0) j hj _ ?_
      have h' : ∃ t1 ∈ reps X p, vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
      simp only [G0n, dif_pos h', chR t0 ht0 h']
      by_cases hAA : A
      · simp only [if_pos hAA]
        exact max_le_max ((hNum hT hLT u w hg hAA t0 ht0 (j + 1)
          ((hlift (j + 1)).2 (Finset.mem_Icc.2 ⟨by omega, by omega⟩))).2.1) le_rfl
      · simp only [if_neg hAA]; exact le_max_right _ _
    · simp only [G0n, dif_neg h]
      refine hFn v (fun hv => h ?_) j (by rw [← hmm]; exact hj)
      obtain ⟨t0, ht0, h0⟩ := Finset.mem_image.1 hv
      exact ⟨t0, ht0, h0⟩
  have c3 : ∀ v ∈ BB, ∀ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) j ≤ PRn v j := by
    intro v hv j hj
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hv
    have h : ∃ t1 ∈ VV', vOf t1 = vOf t0 := ⟨t0, ht0, rfl⟩
    simp only [PRn, dif_pos h, chV t0 ht0 h]
    by_cases hAA : A
    · simp only [if_pos hAA]; exact (hNum hT hLT u w hg hAA t0 (hVVr ht0) j ((hlift j).2 hj)).2.2
    · simp only [if_neg hAA]; exact le_rfl
  have hnodup : (VV'.toList.map vOf).Nodup :=
    List.Nodup.map_on (fun a ha b hb hab => hinj (hVVr (Finset.mem_toList.1 ha)) (hVVr (Finset.mem_toList.1 hb)) hab)
      (Finset.nodup_toList VV')
  have hmem : yProd Y u w hg VV' F ∈ (Formalism.MainNotions.FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) (Y.Lv u w hg) (Y.Ch u w hg) std vp unif eO eO_spec dG
      dG_spec om).Iprod S BB := by
    apply Submodule.subset_span
    have heq : yProd Y u w hg VV' F =
        (VV'.toList.map vOf).foldr (fun v F' => ((D.gat u w hg).yv v)^[(Y.Fl u w hg).mm] F') F := by
      unfold yProd
      rw [foldr_map_comp, foldr_map', hmm]
    refine ⟨BB, subset_refl _, VV'.toList.map vOf, hnodup, by ext; simp [BB], F, ?_, heq⟩
    rw [Finset.sdiff_self, Finset.sum_empty, zpow_zero]
    exact ⟨F, hF, one_smul (D.gat u w hg).Kf F⟩
  have hv := h5D Gn G0n PRn S BB c1 c2 c3 (fun v _ => le_rfl) _ hmem
  have hv2 : (Y.Ch u w hg).chainK (Y.Fl u w hg).mm (yProd Y u w hg VV' F) ∈
      scale ((algebraMap (D.gat u w hg).O (D.gat u w hg).Kf vp) ^
        ⌈(∑ j ∈ Finset.Icc 1 (Y.Fl u w hg).mm, (∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) +
            ∑ v ∈ Finset.univ \ BB, G0n v j) - ∑ j ∈ Finset.range (Y.Fl u w hg).mm, (dG j : ℝ)) * (eO : ℝ)⌉)
        ((Y.Lv u w hg).Int (Y.Fl u w hg).mm) := hv
  rw [hmm] at hv2

  have hj : ∀ j ∈ SizeData₂.lifts D, (∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0)
        (max (g0 X K (aL L) (bL L) p j t0) 0)) + (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) +
        ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0 + ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j ≤
      ∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ Finset.univ \ BB, G0n v j := by
    intro j hjl
    have e1 : ∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0) (max (g0 X K (aL L) (bL L) p j t0) 0) ≤
        ∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) := by
      rw [Finset.sum_image (fun a ha b hb hab => hinj (hVVr ha) (hVVr hb) hab)]
      exact Finset.sum_le_sum fun t0 ht0 => hI t0 ht0 j hjl
    have hunion : (VVs \ VV') ∪ (reps X p \ VVs) = reps X p \ VV' := by
      ext t; simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨hVVs h1, h2⟩
        · exact ⟨h1, fun h => h2 (hVV' h)⟩
      · rintro ⟨h1, h2⟩
        by_cases h : t ∈ VVs
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h1, h⟩
    have hdisj : Disjoint (VVs \ VV') (reps X p \ VVs) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      exact (Finset.mem_sdiff.1 h2).2 (Finset.mem_sdiff.1 h1).1
    have e2 : (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) +
        ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0 =
        ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0 := by
      rw [← Finset.sum_union hdisj, hunion]
    have hinjR : Set.InjOn vOf ↑(reps X p \ VV') :=
      fun a ha b hb hab => hinj (Finset.mem_sdiff.1 ha).1 (Finset.mem_sdiff.1 hb).1 hab
    have e3 : ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0 +
        ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j ≤ ∑ v ∈ Finset.univ \ BB, G0n v j := by
      have h1 : ∑ t0 ∈ reps X p \ VV', max (g0 X K (aL L) (bL L) p j t0) 0 ≤
          ∑ v ∈ (reps X p \ VV').image vOf, G0n v j := by
        rw [Finset.sum_image hinjR]
        exact Finset.sum_le_sum fun t0 ht0 => hII t0 (Finset.mem_sdiff.1 ht0).1 j hjl
      have h2 : ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j =
          ∑ v ∈ Finset.univ \ (reps X p).image vOf, G0n v j := by
        refine Finset.sum_congr rfl fun v hv => ?_
        have hn : ¬ ∃ t0 ∈ reps X p, vOf t0 = v := fun ⟨t0, ht0, h0⟩ =>
          (Finset.mem_sdiff.1 hv).2 (Finset.mem_image.2 ⟨t0, ht0, h0⟩)
        simp only [G0n, dif_neg hn]
      have hsplit : Finset.univ \ BB = ((reps X p \ VV').image vOf) ∪ (Finset.univ \ (reps X p).image vOf) := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image, BB]
        constructor
        · intro hv
          by_cases h : ∃ t0 ∈ reps X p, vOf t0 = v
          · obtain ⟨t0, ht0, rfl⟩ := h
            exact Or.inl ⟨t0, ⟨ht0, fun h' => hv ⟨t0, h', rfl⟩⟩, rfl⟩
          · exact Or.inr h
        · rintro (⟨t0, ⟨ht0, hn⟩, rfl⟩ | h)
          · rintro ⟨t1, ht1, h1⟩
            exact hn (hinj (hVVr ht1) ht0 h1 ▸ ht1)
          · rintro ⟨t1, ht1, rfl⟩
            exact h ⟨t1, hVVr ht1, rfl⟩
      have hdisj2 : Disjoint ((reps X p \ VV').image vOf) (Finset.univ \ (reps X p).image vOf) := by
        rw [Finset.disjoint_left]
        intro v h1 h2
        obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 h1
        exact (Finset.mem_sdiff.1 h2).2 (Finset.mem_image.2 ⟨t0, (Finset.mem_sdiff.1 ht0).1, rfl⟩)
      rw [hsplit, Finset.sum_union hdisj2, h2]
      linarith
    linarith
  have hTB : (∑ j ∈ SizeData₂.lifts D, ((∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0)
        (max (g0 X K (aL L) (bL L) p j t0) 0)) + (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) +
        ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0)) + low u w ≤
      (∑ j ∈ Finset.Icc 1 D.R.m, (∑ v ∈ BB, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ Finset.univ \ BB, G0n v j)) -
        ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := by
    have h1 := Finset.sum_le_sum hj
    have h2 : low u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m, ∑ v ∈ Finset.univ \ (reps X p).image vOf, Fn v j) -
        ∑ j ∈ Finset.range D.R.m, (dG j : ℝ) := hdiv
    unfold SizeData₂.lifts at h1
    unfold SizeData₂.lifts
    rw [Finset.sum_add_distrib] at h1
    linarith
  have hvp0 : algebraMap (D.gat u w hg).O (D.gat u w hg).Kf vp ≠ 0 :=
    (map_ne_zero_iff _ hinjK).mpr unif.ne_zero
  refine ⟨vp, unif, scale_pow_mono vp hvp0 _ (Int.ceil_mono ?_) hv2⟩
  rw [← eO_eq_vUnit (D.gat u w hg) vp unif eO eO_spec]
  exact mul_le_mul_of_nonneg_right hTB (Nat.cast_nonneg _)

theorem type_one_hypothesis_of_bounds (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Cm CH C : ℝ) (hX : KapIDef X K)
    (hK : K.Nonneg) (hCH0 : 0 ≤ CH) (hCHk : CH ≤ K.kI) (hCHD : CH ≤ K.DI) (hCHr : 2 * CH ≤ K.rho) (hC0 : 0 ≤ C)
    (hCt1 : 2 * C ≤ K.kappaThresholdOne) (hCt2 : C ≤ K.kappaThresholdTwo) (hCm : C ≤ Cm) (hc : 0 ≤ cG L)
    (h : Formalism.MainNotions.flipOneThree.Conclusion2 D K.La CH C) : Formalism.MainNotions.AuxBlock8.adm8 D L X K Cm :=
  type_one_hypothesis_of_segments D L X K Cm CH C hX hK hCH0 hCHk hCHD hCHr hC0 hCt1 hCt2 hCm hc
    (Formalism.MainNotions.G.TopChoiceBounds.orbit_segments D L) h

theorem isotypic_multiplicity_of_reducibility_alt (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) : Formalism.MainNotions.PlaneGramData.adm1 D :=
  isotypic_multiplicity_of_reducibility D h (polIsoDecompB_of D h2)

open Formalism.MainNotions.G Formalism.BasicNotions

theorem expBound_of (D : D7) (L : SizeData₂ D) (X : Inst D L) (Ce : ℝ) (hCe : 1 ≤ Ce) (hEp : EpDef X Ce)
    (P : ParameterChoice' D L) (T : GatTies D) : ExpBoundG D X := by
  intro u w hg
  have hk := T.gat_k u w hg
  have ha4 : (4 : ℝ) ≤ L.sc.a := P.four_le_a
  have hka : (D.R.k : ℝ) ≤ L.sc.a := P.k_le_a
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := P.five_le_k

  have hpos : ∀ v (s : Fin ((D.gat u w hg).P.n' v)),
      (wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s) : ℝ) ≤
        (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a := by
    intro v s
    have hprime : (D.what₂.places.resChar w).Prime := ((D.gat u w hg).P.setting v).prime
    have hp1 : (1 : ℝ) < (D.what₂.places.resChar w : ℝ) := by exact_mod_cast hprime.one_lt
    have hl := gat_ellWt_lamAt_le P T u w hg v s
    have hloga : 0 ≤ Real.logb (D.what₂.places.resChar w) L.sc.a := Real.logb_nonneg hp1 (by linarith)
    unfold wExp deF N0
    set kk := (D.gat u w hg).P.m + 1 with hkk_def
    have hkk : (kk : ℝ) = D.R.k := by exact_mod_cast hk
    set ℓ := ellWt (lamAt ((D.gat u w hg).P.lam0 v) s) with hℓ
    have hN0 : (((kk * (kk - 1) / 2 : ℕ)) : ℝ) ≤ (kk : ℝ) ^ 2 / 2 := by
      have h1 : (((kk * (kk - 1) / 2 : ℕ)) : ℝ) ≤ ((kk * (kk - 1) : ℕ) : ℝ) / 2 := Nat.cast_div_le
      have h2 : ((kk * (kk - 1) : ℕ) : ℝ) ≤ (kk : ℝ) ^ 2 := by
        have : kk * (kk - 1) ≤ kk * kk := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        calc ((kk * (kk - 1) : ℕ) : ℝ) ≤ ((kk * kk : ℕ) : ℝ) := by exact_mod_cast this
          _ = (kk : ℝ) ^ 2 := by push_cast; ring
      linarith
    have hk5' : (5 : ℝ) ≤ (kk : ℝ) := by rw [hkk]; exact hk5
    have hn1 : 1 ≤ ℓ + kk - 1 := by
      have : (5 : ℕ) ≤ kk := by exact_mod_cast hk5'
      omega
    have hlog : ((Nat.log (D.what₂.places.resChar w) (ℓ + kk - 1) : ℕ) : ℝ) ≤
        2 * Real.logb (D.what₂.places.resChar w) L.sc.a := by
      refine (Real.natLog_le_logb _ _).trans ?_
      have hcast : (((ℓ + kk - 1 : ℕ)) : ℝ) ≤ L.sc.a ^ 2 := by
        have e : (((ℓ + kk - 1 : ℕ)) : ℝ) = (ℓ : ℝ) + (kk : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [e, hkk]; nlinarith
      calc Real.logb (D.what₂.places.resChar w) (((ℓ + kk - 1 : ℕ)) : ℝ)
          ≤ Real.logb (D.what₂.places.resChar w) (L.sc.a ^ 2) :=
            Real.logb_le_logb_of_le hp1 (by exact_mod_cast Nat.pos_of_ne_zero (by omega)) hcast
        _ = 2 * Real.logb (D.what₂.places.resChar w) L.sc.a := by
            rw [Real.logb_pow]; push_cast; ring
    push_cast
    rw [← hkk]
    calc (((kk * (kk - 1) / 2 : ℕ)) : ℝ) * ((Nat.log (D.what₂.places.resChar w) (ℓ + kk - 1) : ℕ) : ℝ)
        ≤ ((kk : ℝ) ^ 2 / 2) * (2 * Real.logb (D.what₂.places.resChar w) L.sc.a) :=
          mul_le_mul hN0 hlog (Nat.cast_nonneg _) (by positivity)
      _ = (kk : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a := by ring

  have hcard : (∑ v, ((D.gat u w hg).P.n' v : ℝ)) = (D.R.f : ℝ) := by
    have h1 : (∑ v, (D.gat u w hg).P.n' v) = Fintype.card (Σ v : Fin (D.gat u w hg).P.nV, Fin ((D.gat u w hg).P.n' v)) := by
      rw [Fintype.card_sigma]; simp
    have h2 : Fintype.card (Σ v : Fin (D.gat u w hg).P.nV, Fin ((D.gat u w hg).P.n' v)) = D.R.f := by
      rw [Fintype.card_congr (T.gat_pos u w hg), D.what₂.card_Tau]
    rw [← Nat.cast_sum, h1, h2]
  have hsum : ((∑ v, ∑ s : Fin ((D.gat u w hg).P.n' v),
      wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s) : ℕ) : ℝ) ≤
      (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a) := by
    push_cast
    calc (∑ v, ∑ s : Fin ((D.gat u w hg).P.n' v),
          ((wExp (D.what₂.places.resChar w) (D.gat u w hg).P.m (lamAt ((D.gat u w hg).P.lam0 v) s) : ℕ) : ℝ))
        ≤ ∑ v, ∑ _s : Fin ((D.gat u w hg).P.n' v), (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a :=
          Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun s _ => hpos v s
      _ = (∑ v, ((D.gat u w hg).P.n' v : ℝ)) * ((D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_mul]
      _ = _ := by rw [hcard]
  rw [hEp]
  refine Nat.cast_le.1 (le_trans ?_ (Nat.le_ceil _))
  have hloga : 0 ≤ Real.logb (D.what₂.places.resChar w) L.sc.a :=
    div_nonneg (Real.log_nonneg (by linarith)) (Real.log_natCast_nonneg _)
  have hx : 0 ≤ (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a := by positivity
  calc _ ≤ (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a) := hsum
    _ = 1 * ((D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a) := by ring
    _ ≤ Ce * ((D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) L.sc.a) :=
        mul_le_mul_of_nonneg_right hCe hx
    _ = _ := by ring

open Formalism.MainNotions.G Formalism.BasicNotions

theorem LPprime_cast {W Qq O Kf : Type*} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf]
    [Algebra O Kf] {p : ℕ} {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {w : O} {r t Dd : ℕ} {κ : ℝ} {cStar : ℕ}
    {n1 n2 m1 m2 : ℕ} (hn : n1 = n2) (hm : m1 = m2) (lam : Fin n2 → Fin (m2 + 1) → ℤ)
    (h : LPprime (W := W) p n1 ι σ w r (fun (s : Fin n1) (i : Fin (m1 + 1)) => lam (Fin.cast hn s) (Fin.cast (by rw [hm]) i))
      t Dd κ cStar) :
    LPprime (W := W) p n2 ι σ w r lam t Dd κ cStar := by
  subst hn
  subst hm
  exact h

theorem not_split_of_class_zero {D : D7} {p : ℕ} (h : IsResidueClassZero D p) : ¬ IsSg D p := by
  intro h2
  unfold IsSg at h2
  rw [h] at h2
  cases h2

theorem period_eq_addOrderOf_class_zero {D : D7} {p : ℕ} (h : IsResidueClassZero D p) : nP D p = addOrderOf (hP D p) := by
  unfold nP
  rw [if_neg (not_split_of_class_zero h)]

theorem shift_eq_generator_class_zero {D : D7} {p : ℕ} (h : IsResidueClassZero D p) : stepP D p = hP D p := by
  unfold stepP
  rw [if_neg (not_split_of_class_zero h)]

theorem bs_add_nsmul {D : D7} {L : SizeData₂ D} (X : Inst D L) (h t : HH D) (i : ℕ) : X.bs h (t + i • h) = X.bs h t := by
  induction i with
  | zero => simp only [zero_smul, add_zero]
  | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]

theorem bs_bs {D : D7} {L : SizeData₂ D} (X : Inst D L) (h t : HH D) : X.bs h (X.bs h t) = X.bs h t := by
  obtain ⟨i, hi⟩ := X.bs_orb h t
  calc X.bs h (X.bs h t) = X.bs h (X.bs h t + i • h) := (bs_add_nsmul X h _ i).symm
    _ = X.bs h t := by rw [hi]

theorem Nv_eq_card {D : D7} {L : SizeData₂ D} (X : Inst D L) {p : ℕ} (hc : IsResidueClassZero D p) {t0 : HH D}
    (ht0 : t0 ∈ reps X p) : Nv X p t0 = (topsPos D p t0).card := by
  classical
  obtain ⟨t1, -, rfl⟩ := Finset.mem_image.1 ht0
  have hstep := shift_eq_generator_class_zero hc
  set h := hP D p
  set t0 := X.bs (stepP D p) t1 with ht0def
  have hbs : X.bs h t0 = t0 := by rw [ht0def, hstep, bs_bs]
  unfold Nv topsOn
  rw [hstep]
  have hinj : Function.Injective (fun i : Fin (addOrderOf h) => t0 + (i : ℕ) • h) := by
    intro i j hij
    simp only [add_right_inj] at hij
    have hpos : 0 < addOrderOf h := addOrderOf_pos h
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf i.2 j.2 hij)
  rw [← Finset.card_map ⟨_, hinj⟩]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk, topsPos, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨htT, hbt⟩
    obtain ⟨i, hi⟩ := X.bs_orb h t
    rw [hbt] at hi
    refine ⟨⟨i % addOrderOf h, Nat.mod_lt _ (addOrderOf_pos h)⟩, ?_, ?_⟩
    · show t0 + (i % addOrderOf h) • h ∈ D.host.TT
      rw [mod_addOrderOf_nsmul, hi]; exact htT
    · show t0 + (i % addOrderOf h) • h = t
      rw [mod_addOrderOf_nsmul]; exact hi
  · rintro ⟨i, hiT, rfl⟩
    exact ⟨hiT, by rw [bs_add_nsmul, hbs]⟩

theorem inBand_of_inBand0 {D : D7} {K : Consts} {s : Scale} {p : ℕ} (h : rho D K s ≤ rhoB D K s)
    (h0 : InBand0 D K s p) : InBand D K s p := by
  obtain ⟨hp0, hX, d, hd, h1, h2⟩ := h0
  have hX0 : 0 < s.X' := by unfold Scale.X'; exact Real.exp_pos _
  refine ⟨hp0, hX, d, hd, le_trans ?_ h1, h2.trans ?_⟩ <;> nlinarith

def StdSubAt (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (D.gat u w hg).P.nV),
    ∃ (Os Ks : Type) (_ : CommRing Os) (_ : IsDomain Os) (_ : IsDiscreteValuationRing Os) (_ : Field Ks)
      (_ : Algebra Os Ks) (ιs : (D.gat u w hg).P.Qq v →+* Ks) (js : (D.gat u w hg).P.W v →+* Os) (ws : Os)
      (φ : Os →+* (D.gat u w hg).O) (φK : Ks →+* (D.gat u w hg).Kf),
      (∀ x : Os, φK (algebraMap Os Ks x) = algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (φ x)) ∧ φ.Finite ∧
      UnramifiedQuadraticSetting (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) ((D.gat u w hg).P.W v) ((D.gat u w hg).P.Qq v)
        Os Ks ιs ((D.gat u w hg).P.σ v) js ws ∧
      φK.comp ιs = (D.gat u w hg).P.ι v ∧ φ.comp js = (D.gat u w hg).P.j v ∧ φ ws = (D.gat u w hg).P.w

def HypIAt (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) : Prop :=
  ∀ p, Cand D L K p → L.sc.p0 D.R.k ≤ (p : ℝ) → ∀ t0 ∈ goodReps X p,
    L2 D L.sc < goodU L.sc.delta1 ∧ 3 * Gp L.sc ≤ addOrderOf (hP D p) ∧
    Formalism.MainNotions.AuxBlock8.HypI D L K p (addOrderOf (hP D p)) (topsPos D p t0).card ∧
    ∀ s ∈ topsPos D p t0, wPos D p t0 (aL L) s ∈ winA D L.sc ∧ wPos D p t0 (bL L) s ∈ winB D K L.sc

def HypIIAt (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) : Prop :=
  ∀ p, Cand D L K p → (p : ℝ) < L.sc.p0 D.R.k → ∀ t0 ∈ goodReps X p,
    2 * L1 D L.sc p ≤ L2 D L.sc ∧ L2 D L.sc < goodU L.sc.delta1 ∧ 3 * Gp L.sc ≤ addOrderOf (hP D p) ∧
    ((topsPos D p t0).card : ℝ) ≤ NplusF L.sc (addOrderOf (hP D p)) ∧
    (∀ s ∈ topsPos D p t0, wPos D p t0 (aL L) s ∈ winA D L.sc ∧ wPos D p t0 (bL L) s ∈ winB D K L.sc) ∧
    (∀ s ∈ topsPos D p t0, (L.sc.a - cG L) + (⌊cG L⌋₊ : ℝ) ≤ (wPos D p t0 (aL L) s : ℝ) ∧
      (wPos D p t0 (aL L) s : ℝ) ≤ 2 * (L.sc.a - cG L) - (⌊cG L⌋₊ : ℝ) ∧
      (wPos D p t0 (bL L) s : ℝ) + 2 * (⌊cG L⌋₊ : ℝ) ≤ c0num L) ∧
    13 ≤ p ∧ 2 ≤ rG L.sc ∧ N1 L.sc ^ 2 ≤ rG L.sc * (topsPos D p t0).card ∧
    (rG L.sc : ℝ) ≤ L.sc.x ^ Scale.A ∧
    (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A) ≤ (p : ℝ) ^ ((L1 D L.sc p : ℤ) - 1) ∧
    256 * (D.R.k : ℝ) ^ 2 * ((topsPos D p t0).card : ℝ) * (L.sc.x ^ Scale.A) ^ 2 ≤
      (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A) ∧
    N1 L.sc + 2 * rG L.sc + rG L.sc ≤ D.R.k ∧
    K.kII' * (N1 L.sc : ℝ) ^ 2 * Real.log L.sc.a ≤ D.R.k ∧
    K.szII * (D.R.k : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * ((topsPos D p t0).card : ℝ) * Qp L.sc p ^ 5 *
        ((8 * ((DIIf K L p (addOrderOf (hP D p)) : ℝ) + 1)) +
          ((rG L.sc : ℝ) * ((topsPos D p t0).card : ℝ) * c0num L +
            2 * (rG L.sc : ℝ) * ((addOrderOf (hP D p) : ℕ) : ℝ) * cG L)) *
        L.sc.x ^ Scale.A ≤ L.sc.a - cG L

set_option maxHeartbeats 2000000 in
open Classical in

theorem linear_programming_input_of_hypotheses (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (h6 : Formalism.MainNotions.AuxBlock8.adm6 D L K) (h7 : Formalism.MainNotions.AuxBlock8.adm7 D L X K) (hStd : StdSubAt D) (hBC : LPBaseChange)
    (hI : HypIAt D L X K) (hII : HypIIAt D L X K) (hrho : rho D K L.sc ≤ rhoB D K L.sc) :
    Formalism.MainNotions.CornerGLContinuity.OrbitLatticeBounds D L X Y K := by
  intro hT hLT u w hg
  dsimp only
  intro t0 ht0
  simp only [VV] at ht0
  split_ifs at ht0 with hcs
  swap
  · exact absurd ht0 (Finset.notMem_empty _)
  obtain ⟨hcand, -⟩ := hcs
  have hgood := ht0
  obtain ⟨hrep, hGood⟩ := Finset.mem_filter.1 ht0
  obtain ⟨hmm, -, hc, hr, -, -, horb⟩ := hLT u w hg
  obtain ⟨hn', hpos⟩ := horb t0 hrep
  have hk := hT.gat_k u w hg
  have hc0 : IsResidueClassZero D (D.what₂.places.resChar w) := hcand.2.2.1
  set v := Y.vOf u w hg t0 with hv
  have hm : D.R.k - 1 = (D.gat u w hg).P.m := by omega
  refine LPprime_cast hn'.symm hm ((D.gat u w hg).P.lam0 v) ?_

  have hcl : (Y.Fl u w hg).c ≤ ⌊cG L⌋₊ := Nat.le_floor hc
  have hmemTT : ∀ s : Fin (addOrderOf (hP D (D.what₂.places.resChar w))),
      (Fin.cast hn'.symm s ∈ (Y.Fl u w hg).TT v ↔ s ∈ topsPos D (D.what₂.places.resChar w) t0) := by
    intro s
    rw [(hpos (Fin.cast hn'.symm s)).2.1]
    simp only [topsPos, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_cast]
  have hbase : IsBaseWeight (topsPos D (D.what₂.places.resChar w) t0) (wPos D (D.what₂.places.resChar w) t0 (aL L)) (wPos D (D.what₂.places.resChar w) t0 (bL L)) ⌊cG L⌋₊
      (fun (s : Fin (addOrderOf (hP D (D.what₂.places.resChar w)))) (i : Fin (D.R.k - 1 + 1)) =>
        (D.gat u w hg).P.lam0 v (Fin.cast hn'.symm s) (Fin.cast (by rw [hm]) i)) := by
    intro s
    have hB := (Y.Fl u w hg).base v (Fin.cast hn'.symm s)
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · have hs' := (hmemTT s).2 hs
      obtain ⟨h0, hl, hmid⟩ := hB.1 hs'
      obtain ⟨ha, hb⟩ := (hpos (Fin.cast hn'.symm s)).2.2.1 hs'
      refine ⟨?_, ?_, fun i hi0 him => ?_⟩
      · have e : (Fin.cast (by rw [hm]) (0 : Fin (D.R.k - 1 + 1)) : Fin ((D.gat u w hg).P.m + 1)) = 0 := Fin.ext rfl
        simp only [e, h0, ha, wPos, Fin.val_cast]
      · have e : (Fin.cast (by rw [hm]) (Fin.last (D.R.k - 1)) : Fin ((D.gat u w hg).P.m + 1)) = Fin.last (D.gat u w hg).P.m :=
          Fin.ext (by simp [hm])
        simp only [e, hl, hb, wPos, Fin.val_cast]
      · exact (hmid _ (by simpa using hi0) (by simp only [Fin.val_cast]; omega)).trans (by exact_mod_cast hcl)
    · have hs' : Fin.cast hn'.symm s ∉ (Y.Fl u w hg).TT v := fun h => hs ((hmemTT s).1 h)
      exact fun i => (hB.2 hs' _).trans (by exact_mod_cast hcl)
  have hdom : IsDominant (fun (s : Fin (addOrderOf (hP D (D.what₂.places.resChar w)))) (i : Fin (D.R.k - 1 + 1)) =>
      (D.gat u w hg).P.lam0 v (Fin.cast hn'.symm s) (Fin.cast (by rw [hm]) i)) := by
    intro s a b hab
    exact ((D.gat u w hg).P.dom v (Fin.cast hn'.symm s)) ((Fin.cast_le_cast _).2 hab)
  obtain ⟨Os, Ks, _, _, _, _, _, ιs, js, ws, φ, φK, hcomp, hfin, hSs, hι, hj, hw⟩ := hStd u w hg v
  have hSet := hSs
  rw [hn'] at hSet
  have hSetR : HidaSetting (D.what₂.places.resChar w) (addOrderOf (hP D (D.what₂.places.resChar w))) ((D.gat u w hg).P.W v)
      ((D.gat u w hg).P.Qq v) (D.gat u w hg).O (D.gat u w hg).Kf (φK.comp ιs) ((D.gat u w hg).P.σ v) (φ.comp js) (φ ws) := by
    rw [hι, hj, hw, ← hn']; exact (D.gat u w hg).P.setting v
  rw [← hι, ← hw]
  refine hBC _ _ _ _ Os Ks _ _ ιs _ js ws φ φK hcomp hfin hSet.1 hSetR _ _ _ _ _ _ _ ?_
  have hNv : Nv X (D.what₂.places.resChar w) t0 = (topsPos D (D.what₂.places.resChar w) t0).card := Nv_eq_card X hc0 hrep
  have hnP : nP D (D.what₂.places.resChar w) = addOrderOf (hP D (D.what₂.places.resChar w)) := period_eq_addOrderOf_class_zero hc0
  by_cases hp0 : ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k
  · obtain ⟨h1, h2, h3, h4, hwin, hbnd, h13, hr2, hN1, hrY, hpL, h256, hk3, hkLa, hsz⟩ := hII _ hcand hp0 t0 hgood
    have hrr : (D.gat u w hg).P.r = rG L.sc := by rw [hr, if_pos hp0]
    rw [hrr]
    have htv : tv X K (aL L) (bL L) (D.what₂.places.resChar w) t0 = tIIf K L (D.what₂.places.resChar w) (addOrderOf (hP D (D.what₂.places.resChar w))) (topsPos D (D.what₂.places.resChar w) t0).card := by
      unfold tv; rw [if_pos hp0, hnP, hNv]
    have hDp : Dp K L (D.what₂.places.resChar w) = DIIf K L (D.what₂.places.resChar w) (addOrderOf (hP D (D.what₂.places.resChar w))) := by unfold Dp; rw [if_pos hp0, hnP]
    have hkap : kapv X K (aL L) (bL L) (D.what₂.places.resChar w) t0 = kapIIf K L (topsPos D (D.what₂.places.resChar w) t0).card := by
      unfold kapv kapLoc; rw [if_pos hp0]
    rw [htv, hDp, hkap]
    exact h6 (D.what₂.places.resChar w) (addOrderOf (hP D (D.what₂.places.resChar w))) ((D.gat u w hg).P.W v) ((D.gat u w hg).P.Qq v) Os Ks ιs ((D.gat u w hg).P.σ v) js ws hSet
      (topsPos D (D.what₂.places.resChar w) t0) hGood h1 h2 h3 h4 hp0 (wPos D (D.what₂.places.resChar w) t0 (aL L)) (wPos D (D.what₂.places.resChar w) t0 (bL L)) hwin hbnd _ hbase hdom
      h13 hr2 hN1 hrY hpL h256 hk3 hkLa hsz
  · have hp0' : L.sc.p0 D.R.k ≤ ((D.what₂.places.resChar w : ℕ) : ℝ) := le_of_not_gt hp0
    obtain ⟨h2, h3, hHI, hwin⟩ := hI _ hcand hp0' t0 hgood
    have hrr : (D.gat u w hg).P.r = 1 := by rw [hr, if_neg hp0]
    rw [hrr]
    have htv : tv X K (aL L) (bL L) (D.what₂.places.resChar w) t0 =
        tIf K L (D.what₂.places.resChar w) (addOrderOf (hP D (D.what₂.places.resChar w))) (topsPos D (D.what₂.places.resChar w) t0) (wPos D (D.what₂.places.resChar w) t0 (aL L)) (wPos D (D.what₂.places.resChar w) t0 (bL L)) := by
      unfold tv; rw [if_neg hp0]
    have hDp : Dp K L (D.what₂.places.resChar w) = DIf K L (D.what₂.places.resChar w) (addOrderOf (hP D (D.what₂.places.resChar w))) := by unfold Dp; rw [if_neg hp0, hnP]
    have hkap : kapv X K (aL L) (bL L) (D.what₂.places.resChar w) t0 =
        X.kapI (D.what₂.places.resChar w) (addOrderOf (hP D (D.what₂.places.resChar w))) (topsPos D (D.what₂.places.resChar w) t0) (wPos D (D.what₂.places.resChar w) t0 (aL L)) (wPos D (D.what₂.places.resChar w) t0 (bL L)) := by
      unfold kapv kapLoc; rw [if_neg hp0]
    rw [htv, hDp, hkap]
    exact h7 (D.what₂.places.resChar w) (addOrderOf (hP D (D.what₂.places.resChar w))) ((D.gat u w hg).P.W v) ((D.gat u w hg).P.Qq v) Os Ks ιs ((D.gat u w hg).P.σ v) js ws hSet
      (topsPos D (D.what₂.places.resChar w) t0) hGood h2 h3 hp0' hcand.2.1 (fun h0 => hcand.2.2.2.2 hp0' (inBand_of_inBand0 hrho h0)) hHI (wPos D (D.what₂.places.resChar w) t0 (aL L))
      (wPos D (D.what₂.places.resChar w) t0 (bL L)) hwin _ hbase hdom

end Formalism.MainNotions.G.Joints
