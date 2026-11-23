import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteRestrictionVanishing

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.levTop_pf :
    SlotBasic → LevTop := by
  intro hS E _ _ _ n S Z N hSec hZ hG
  obtain ⟨hinv, -, hloc, -, -, hinert, hK⟩ := hS E n S hSec
  have mem : ∀ (M : ∀ w : GlobalTheory.BCT.Pl E, Subgroup (GlobalTheory.BCT.GLw n w)) (x : GF E n),
      x ∈ Lev S M ↔ ∀ i : GlobalTheory.BCT.Pl E × Bool, Sl S i → qw n i.1 i.2 x ∈ M i.1 := by
    intro M x
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have hKq : ∀ k ∈ PositivityTheory.Rg.BcB.G8.Kf E n, ∀ i : GlobalTheory.BCT.Pl E × Bool, Sl S i →
      qw n i.1 i.2 k ∈ GlobalTheory.LFun.KGL i.1 n := fun k hk => (mem _ k).1 ((hK k).2 hk)
  have hsub : (Lev S N : Set (GF E n)) ⊆ (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GF E n)) := by
    intro x hx
    exact (hK x).1 ((mem _ x).2 fun i hi => (hG i.1).2.1 ((mem N x).1 hx i hi))
  have hset : (Lev S N : Set (GF E n)) = (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GF E n)) ∩
      ⋂ i ∈ {i : GlobalTheory.BCT.Pl E × Bool | i.1 ∈ Z ∧ Sl S i},
        (qw n i.1 i.2) ⁻¹' (N i.1 : Set (GlobalTheory.BCT.GLw n i.1)) := by
    ext x
    constructor
    · intro hx
      refine ⟨hsub hx, ?_⟩
      simp only [Set.mem_iInter]
      exact fun i hi => (mem N x).1 hx i hi.2
    · rintro ⟨hx, hx'⟩
      simp only [Set.mem_iInter] at hx'
      refine (mem N x).2 fun i hi => ?_
      by_cases hz : i.1 ∈ Z
      · exact hx' i ⟨hz, hi⟩
      · rw [(hG i.1).2.2.2 hz]
        exact hKq x hx i hi
  have hfinZ : {i : GlobalTheory.BCT.Pl E × Bool | i.1 ∈ Z ∧ Sl S i}.Finite :=
    ((Z.finite_toSet).prod (Set.finite_univ (α := Bool))).subset fun i hi => ⟨hi.1, trivial⟩
  have hopen : IsOpen (Lev S N : Set (GF E n)) := by
    rw [hset]
    refine GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.inter (hfinZ.isOpen_biInter fun i _ => ?_)
    exact ((hG i.1).1).preimage (hloc i.1 i.2).2.1
  refine ⟨hopen, ?_, ?_, ?_⟩
  · exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen (Lev S N) hopen) hsub
  · intro k hk
    have hq0 : ∀ w, qw n w false (GlobalTheory.BCT.thF E n k) = qw n w true k := fun w => rfl
    have hq1 : ∀ w, qw n w true (GlobalTheory.BCT.thF E n k) = qw n w false k := by
      intro w
      change qw n w false (GlobalTheory.BCT.thF E n (GlobalTheory.BCT.thF E n k)) = _
      rw [hinv]
    refine (mem N _).2 ?_
    rintro ⟨w, b⟩ ⟨hw, hb⟩
    cases b with
    | true =>
      exact (hq1 w).symm ▸ (mem N k).1 hk (w, false) ⟨hw, by simp⟩
    | false =>
      change qw n w false (GlobalTheory.BCT.thF E n k) ∈ N w
      rw [hq0]
      by_cases hs : GlobalTheory.UnitaryBC.IsSplitAt w
      · exact (mem N k).1 hk (w, true) ⟨hw, fun _ => hs⟩
      · have hz : w ∉ Z := fun h => hs (hZ w h).2
        have h0 : qw n w false k ∈ N w := (mem N k).1 hk (w, false) ⟨hw, by simp⟩
        rw [(hG w).2.2.2 hz] at h0 ⊢
        exact (hinert w hs k).2 h0
  · intro k hk x hx
    refine (mem N _).2 fun i hi => ?_
    rw [map_mul, map_mul, map_inv]
    exact (hG i.1).2.2.1 _ (hKq k hk i hi) _ ((mem N x).1 hx i hi)
