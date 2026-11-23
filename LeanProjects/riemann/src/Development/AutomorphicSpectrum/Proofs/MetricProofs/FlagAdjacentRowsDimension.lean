import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionComplementEquivStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentFamilyAnalyticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticSpaceNonemptyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionThirdStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticProjectionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentOrbitEqualityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFifthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionFourthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NullSetImageUnderHoloMapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticBadLocusNullStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSeventhStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

set_option maxHeartbeats 4000000 in

theorem fibre_charts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∃ (U B : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) ∧ (∀ m, MeasurableSet (B m) ∧ B m ⊆ U m) ∧ IsParamCover FA.S.A (fun m => {z | Fin.tail z ∈ U m}) (fun m => {z | Fin.tail z ∈ B m}) ΦY ∧ IsParamCover RW.A (fun m => {z | Fin.tail (Fin.tail z) ∈ U m}) (fun m => {z | Fin.tail (Fin.tail z) ∈ B m}) ΦW ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ΦY m z ∉ bdry FA.S.s) ∧ ∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb hdim RW q hq h0 h1 hinj
  have hj := M.j_le
  have hbN := b.2
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hblk : ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) := by
    unfold lastCol at hca
    split_ifs at hca <;> omega
  obtain ⟨e⟩ := GlobalTheory.T.flag_dimension_complement_equiv Ψ N j n d τ ca cb hj hlt hblk hdim
  obtain ⟨lc1, lc2, lc3, lc4, lc5⟩ := GlobalTheory.T.lower_unipotent_family_analytic Ψ N j τ ca cb hlt hblk
  haveI hSne := GlobalTheory.T.flag_analytic_space_nonempty K ι Φ y Ψ N j M n d BM FA
  haveI hWne := GlobalTheory.T.flag_adjacent_twisted_resolution_third K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW
  have hpi := GlobalTheory.T.flag_analytic_projection_bijective K ι Φ y Ψ N j M n d BM FA
  have hgood := GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM
  have hnot : ∀ z : (Σ k, ι k) → ℂ, z ∉ mcPts FA.Re.J := fun z => by
    rw [FA.J_top]; exact GlobalTheory.CompanionTheory.Ar.PB.Proj.not_mem_mcPts_top _
  have hRinj : ∀ x x', SameOrbit (FA.Re.R.lift x x) (FA.Re.R.lift x' x') → x = x' := fun x x' h =>
    FA.Re.R.inj x x' (hnot _) h
  have hWinj : ∀ x x', SameOrbit (RW.lift x x) (RW.lift x' x') → x = x' := fun x x' h =>
    RW.inj x x' (GlobalTheory.CompanionTheory.Ar.PB.Proj.not_mem_mcPts_top _) h
  let base : (Fin d → ℂ) → Fin n → ℂ := fun w i => w (e.symm (Sum.inl i))
  let cc : (Fin d → ℂ) → FC.CIdx Ψ N j τ ca cb → ℂ := fun w c => w (e.symm (Sum.inr c))
  let mk : (Fin n → ℂ) → (FC.CIdx Ψ N j τ ca cb → ℂ) → Fin d → ℂ := fun u c i => Sum.elim u c (e i)
  have base_mk : ∀ u c, base (mk u c) = u := fun u c => by
    funext i; simp [base, mk]
  have cc_mk : ∀ u c, cc (mk u c) = c := fun u c => by
    funext i; simp [cc, mk]
  have base_cont : Continuous base := continuous_pi fun i => continuous_apply _
  have base_an : AnalyticOnNhd ℂ base Set.univ := fun w _ =>
    AnalyticAt.pi fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (e.symm (Sum.inl i))).analyticAt w
  have cc_an : AnalyticOnNhd ℂ cc Set.univ := fun w _ =>
    AnalyticAt.pi fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (e.symm (Sum.inr i))).analyticAt w
  let Hh : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ' w => FC.Lc τ ca cb (cc w) τ'
  have hclosed : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary _ _ BM.Rb.A BM.L BM.s BM.sec
  have hOd : ∀ l, IsOpen (BM.O l \ bdry BM.s) := fun l => (BM.O_open l).sdiff hclosed
  let Ut : Fin BM.Rb.A.n → Fin BM.q → Set (Fin d → ℂ) := fun kb l =>
    {w | base w ∈ (BM.Rb.A.chart kb).target ∧ (BM.Rb.A.chart kb).symm (base w) ∈ BM.O l \ bdry BM.s}
  let bpt : Fin BM.Rb.A.n → (Fin d → ℂ) → BM.Rb.X := fun kb w => (BM.Rb.A.chart kb).symm (base w)
  have hUo : ∀ kb l, IsOpen (Ut kb l) := fun kb l => by
    have h1 := (BM.Rb.A.chart kb).continuousOn_symm.isOpen_inter_preimage (BM.Rb.A.chart kb).open_target (hOd l)
    exact h1.preimage base_cont
  have hbpc : ∀ kb l, ContinuousOn (bpt kb) (Ut kb l) := fun kb l =>
    (BM.Rb.A.chart kb).continuousOn_symm.comp base_cont.continuousOn fun w hw => hw.1
  have hbpa : ∀ kb l k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bpt kb) (Ut kb l ∩ bpt kb ⁻¹' (BM.Rb.A.chart k).source) :=
    fun kb l k w hw => AnalyticAt.comp (g := BM.Rb.A.chart k ∘ (BM.Rb.A.chart kb).symm) (f := base)
      (BM.Rb.A.holo kb k _ ⟨hw.1.1, hw.2⟩) (base_an w trivial)
  have hfam := fun (kb : Fin BM.Rb.A.n) (l : Fin BM.q) =>
    GlobalTheory.T.flag_adjacent_twisted_resolution_fifth K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq h0 h1 hinj l (Ut kb l) Hh (bpt kb) (hUo kb l)
      (fun τ' r s w _ => AnalyticAt.comp (g := fun c => FC.Lc τ ca cb c τ' r s) (f := cc) (lc2 τ' r s _ trivial) (cc_an w trivial))
      (hbpc kb l) (hbpa kb l) (fun w hw => ⟨hw.2, fun τ' => lc1 _ τ'⟩)
  choose ΦYt ΦWt hYc hYa hWc hWa hYs hWs using hfam
  obtain ⟨x₁⟩ := hSne
  obtain ⟨k₁, hk₁⟩ := BM.Rb.A.cover (FA.pr x₁)
  obtain ⟨l₁, hl₁⟩ := BM.O_cover (FA.pr x₁)
  haveI : Nonempty (Fin BM.Rb.A.n × Fin BM.q) := ⟨(k₁, l₁)⟩
  obtain ⟨tm, htm⟩ := exists_surjective_nat (Fin BM.Rb.A.n × Fin BM.q)
  let Ss : ℕ → Set BM.Rb.X := fun m => (BM.Rb.A.chart (tm m).1).source ∩ BM.O (tm m).2
  have hSo : ∀ m, IsOpen (Ss m) := fun m => (BM.Rb.A.chart (tm m).1).open_source.inter (BM.O_open _)
  let pc : ℕ → Set BM.Rb.X := fun m => Ss m \ ⋃ i ∈ Finset.range m, Ss i
  have hpc_dis : ∀ m m', m < m' → Disjoint (pc m) (pc m') := fun m m' hm =>
    Set.disjoint_left.2 fun x hx hx' => hx'.2 (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hm)) hx.1)
  have hpc_cov : ∀ x, ∃ m, x ∈ pc m := fun x => by
    have hex : ∃ m, x ∈ Ss m := by
      obtain ⟨k, hk⟩ := BM.Rb.A.cover x
      obtain ⟨l, hl⟩ := BM.O_cover x
      obtain ⟨m, hm⟩ := htm (k, l)
      exact ⟨m, by simp only [Ss, hm]; exact ⟨hk, hl⟩⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, fun hx => ?_⟩
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Nat.find_min hex (Finset.mem_range.1 hi) hxi
  let U : ℕ → Set (Fin d → ℂ) := fun m => Ut (tm m).1 (tm m).2
  let B : ℕ → Set (Fin d → ℂ) := fun m => U m ∩ bpt (tm m).1 ⁻¹' pc m
  have hBm : ∀ m, MeasurableSet (B m) := fun m => by
    have hpre : ∀ i, IsOpen (U m ∩ bpt (tm m).1 ⁻¹' Ss i) := fun i =>
      (hbpc _ _).isOpen_inter_preimage (hUo _ _) (hSo i)
    have : B m = (U m ∩ bpt (tm m).1 ⁻¹' Ss m) \ ⋃ i ∈ Finset.range m, (U m ∩ bpt (tm m).1 ⁻¹' Ss i) := by
      ext w
      constructor
      · rintro ⟨hU, hS, hn⟩
        exact ⟨⟨hU, hS⟩, fun h => hn (by
          obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 h
          exact Set.mem_iUnion₂.2 ⟨i, hi, hwi.2⟩)⟩
      · rintro ⟨⟨hU, hS⟩, hn⟩
        exact ⟨hU, hS, fun h => hn (by
          obtain ⟨i, hi, hwi⟩ := Set.mem_iUnion₂.1 h
          exact Set.mem_iUnion₂.2 ⟨i, hi, hU, hwi⟩)⟩
    rw [this]
    exact (hpre m).measurableSet.diff
      (Finset.measurableSet_biUnion _ fun i _ => (hpre i).measurableSet)
  let ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X := fun m => ΦYt (tm m).1 (tm m).2
  let ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X := fun m => ΦWt (tm m).1 (tm m).2
  let Gm : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ := fun m w r s =>
    minorIJ ((Hh τ w)ᴴ * BM.G (tm m).2 τ (bpt (tm m).1 w) * Hh τ w) (insert (![ca, cb] r) ((stepCols N j a).erase ca))
        (insert (![ca, cb] s) ((stepCols N j a).erase ca)) /
      minorIJ ((Hh τ w)ᴴ * BM.G (tm m).2 τ (bpt (tm m).1 w) * Hh τ w) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)
  have w_ext : ∀ w w' : Fin d → ℂ, base w = base w' → cc w = cc w' → w = w' := fun w w' h1 h2 => by
    funext i
    have hi : e.symm (e i) = i := e.symm_apply_apply i
    rcases hei : e i with u | c
    · rw [← hi, hei]; exact congrFun h1 u
    · rw [← hi, hei]; exact congrFun h2 c
  have tail1C : Continuous (Fin.tail : (Fin (d + 1) → ℂ) → Fin d → ℂ) := continuous_pi fun i => continuous_apply _
  have tail2C : Continuous (fun z : Fin (d + 2) → ℂ => (Fin.tail (Fin.tail z) : Fin d → ℂ)) :=
    continuous_pi fun i => continuous_apply _
  have hinjY : ∀ m, Set.InjOn (ΦY m) {z | Fin.tail z ∈ U m} := fun m z hz z' hz' heq => by
    have e1 : bpt (tm m).1 (Fin.tail z) = bpt (tm m).1 (Fin.tail z') := by
      rw [← (hYs _ _ z hz).1, ← (hYs _ _ z' hz').1]; exact congrArg FA.pr heq
    have e2 : base (Fin.tail z) = base (Fin.tail z') := (BM.Rb.A.chart (tm m).1).symm.injOn hz.1 hz'.1 e1
    obtain ⟨x₀, hx₀⟩ := hpi.2 (ΦY m z)
    have o1 := (hYs _ _ z hz).2 x₀ hx₀
    have o2 := (hYs _ _ z' hz').2 x₀ (hx₀.trans heq)
    rw [← e1] at o2
    have e3 := GlobalTheory.T.lower_unipotent_orbit_equality K ι Φ y Ψ N j M n BM (tm m).2 (bpt (tm m).1 (Fin.tail z)) hz.2.1
      (FC.Lca τ ca cb (cc (Fin.tail z)) (z 0)) (FC.Lca τ ca cb (cc (Fin.tail z')) (z' 0))
      (lc4 _ _) (lc4 _ _) (orbit_trans (orbit_symm o1) o2)
    obtain ⟨e4, e5⟩ := lc5 _ _ _ _ e3
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail z', w_ext _ _ e2 e4, e5]
  have hdisY : ∀ m m', m < m' → Disjoint (ΦY m '' {z | Fin.tail z ∈ B m}) (ΦY m' '' {z | Fin.tail z ∈ B m'}) :=
    fun m m' hm => Set.disjoint_left.2 fun x hx hx' => by
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨z', hz', heq⟩ := hx'
      have e1 := (hYs _ _ z hz.1).1
      have e2 := (hYs _ _ z' hz'.1).1
      have hb1 : FA.pr (ΦY m z) ∈ pc m := by
        show FA.pr (ΦYt _ _ z) ∈ _
        rw [e1]; exact hz.2
      have hb2 : FA.pr (ΦY m z) ∈ pc m' := by
        rw [← heq]
        show FA.pr (ΦYt _ _ z') ∈ _
        rw [e2]; exact hz'.2
      exact Set.disjoint_left.1 (hpc_dis m m' hm) hb1 hb2
  have hnull_un : ∀ {e' : ℕ} {X' : Type} [TopologicalSpace X'] (A' : FinHolAtlas e' X') (Z : Fin BM.q → Set X'),
      (∀ l, IsNull A' (Z l)) → IsNull A' (⋃ l, Z l) := fun A' Z h k => by
    rw [Set.preimage_iUnion, Set.inter_iUnion]
    exact measure_iUnion_null fun l => h l k
  have hnull_mono : ∀ {e' : ℕ} {X' : Type} [TopologicalSpace X'] (A' : FinHolAtlas e' X') {Z Z' : Set X'},
      Z' ⊆ Z → IsNull A' Z → IsNull A' Z' := fun A' _ _ hs h k =>
    measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono hs)) (h k)
  refine ⟨U, B, Gm, ΦY, ΦW, fun m => hUo _ _, fun m => ⟨hBm m, Set.inter_subset_left⟩, ⟨fun m =>
    ⟨(hUo _ _).preimage tail1C, hYc _ _, hinjY m, hYa _ _⟩, fun m => ⟨(hBm m).preimage ?_, fun z hz => hz.1⟩, ?_, ?_⟩,
    ⟨fun m => ⟨(hUo _ _).preimage tail2C, hWc _ _, ?_, hWa _ _⟩, fun m => ⟨(hBm m).preimage ?_, fun z hz => hz.1⟩, ?_, ?_⟩,
    ?_, ?_⟩
  · exact tail1C.measurable
  · intro m m' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hdisY m m' h
    · exact (hdisY m' m h).symm
  · refine hnull_mono _ ?_ (GlobalTheory.T.null_set_image_under_holoMap (d + 1) FA.S.X FA.Re.R.X FA.S.A FA.Re.R.A FA.Re.π _ FA.Re.holo
      (hnull_un _ _ (GlobalTheory.T.flag_analytic_bad_locus_null K ι Φ y Ψ N j M n d BM FA)))
    intro x hx
    obtain ⟨x₀, rfl⟩ := hpi.2 x
    obtain ⟨m, hm⟩ := hpc_cov (FA.pr (FA.Re.π x₀))
    refine ⟨x₀, Set.mem_iUnion.2 ⟨(tm m).2, hm.1.2, ?_⟩, rfl⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, a', ho⟩ := GlobalTheory.T.flag_analytic_plucker_column_swap K ι Φ y Ψ N j M n d BM FA τ ca cb hlt hblk (tm m).2 x₀ hm.1.2 hcon.2
    have hbs := hm.1.1
    let w := mk ((BM.Rb.A.chart (tm m).1) (FA.pr (FA.Re.π x₀))) c
    have hbw : bpt (tm m).1 w = FA.pr (FA.Re.π x₀) := by
      show (BM.Rb.A.chart (tm m).1).symm (base w) = _
      rw [base_mk]; exact (BM.Rb.A.chart (tm m).1).left_inv hbs
    have hwU : w ∈ U m := ⟨by
      show base w ∈ _
      rw [base_mk]; exact (BM.Rb.A.chart (tm m).1).map_source hbs, by
      show bpt (tm m).1 w ∈ _
      rw [hbw]; exact ⟨hm.1.2, hcon.1⟩⟩
    have hzt : Fin.tail (Fin.cons a' w : Fin (d + 1) → ℂ) = w := Fin.tail_cons _ _
    have hz : Fin.tail (Fin.cons a' w : Fin (d + 1) → ℂ) ∈ U m := by rw [hzt]; exact hwU
    obtain ⟨x₁', hx₁'⟩ := hpi.2 (ΦY m (Fin.cons a' w))
    have o := (hYs _ _ _ hz).2 x₁' hx₁'
    rw [hzt] at o
    have o' : SameOrbit (FA.Re.R.lift x₁' x₁') (FC.flagPt M (BM.F (tm m).2) (FC.bvec BM (tm m).2 (bpt (tm m).1 w))
      (FC.Lca τ ca cb (cc w) a')) := o
    rw [hbw, cc_mk] at o'
    have e1 : x₁' = x₀ := hRinj _ _ (orbit_trans o' (orbit_symm ho))
    refine hx (Set.mem_iUnion.2 ⟨m, Fin.cons a' w, ?_, by rw [← hx₁', e1]⟩)
    show Fin.tail (Fin.cons a' w : Fin (d + 1) → ℂ) ∈ B m
    rw [hzt]
    refine ⟨hwU, ?_⟩
    show bpt (tm m).1 w ∈ pc m
    rw [hbw]; exact hm
  · intro z hz z' hz' heq
    have e0 := (hWs _ _ z hz).2
    have e0' := (hWs _ _ z' hz').2
    have hq0 : ΦY m (Fin.cons (z 0) (Fin.tail (Fin.tail z))) = ΦY m (Fin.cons (z' 0) (Fin.tail (Fin.tail z'))) := by
      have := congrArg (q 0) heq
      rwa [show q 0 (ΦW m z) = _ from e0.1, show q 0 (ΦW m z') = _ from e0'.1] at this
    have hq1 : ΦY m (Fin.tail z) = ΦY m (Fin.tail z') := by
      have := congrArg (q 1) heq
      rwa [show q 1 (ΦW m z) = _ from e0.2, show q 1 (ΦW m z') = _ from e0'.2] at this
    have t1 := hinjY m (x₁ := (Fin.cons (z 0) (Fin.tail (Fin.tail z)) : Fin (d + 1) → ℂ))
      (x₂ := (Fin.cons (z' 0) (Fin.tail (Fin.tail z')) : Fin (d + 1) → ℂ))
      (by show Fin.tail (Fin.cons (z 0) (Fin.tail (Fin.tail z)) : Fin (d + 1) → ℂ) ∈ U m
          rw [Fin.tail_cons]; exact hz)
      (by show Fin.tail (Fin.cons (z' 0) (Fin.tail (Fin.tail z')) : Fin (d + 1) → ℂ) ∈ U m
          rw [Fin.tail_cons]; exact hz') hq0
    have t2 := hinjY m (x₁ := Fin.tail z) hz hz' hq1
    have t3 : z 0 = z' 0 := by simpa using congrFun t1 0
    rw [← Fin.cons_self_tail z, ← Fin.cons_self_tail z', t2, t3]
  · exact tail2C.measurable
  · intro m m' hne
    have key : ∀ m m', m < m' → Disjoint (ΦW m '' {z | Fin.tail (Fin.tail z) ∈ B m})
        (ΦW m' '' {z | Fin.tail (Fin.tail z) ∈ B m'}) := fun m m' hm => Set.disjoint_left.2 fun x hx hx' => by
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨z', hz', heq⟩ := hx'
      have e0 := (hWs _ _ z hz.1).2.1
      have e0' := (hWs _ _ z' hz'.1).2.1
      have hq0 : ΦY m (Fin.cons (z 0) (Fin.tail (Fin.tail z))) = ΦY m' (Fin.cons (z' 0) (Fin.tail (Fin.tail z'))) := by
        have := congrArg (q 0) heq
        rw [show q 0 (ΦW m z) = _ from e0, show q 0 (ΦW m' z') = _ from e0'] at this
        exact this.symm
      refine Set.disjoint_left.1 (hdisY m m' hm) ⟨_, ?_, rfl⟩ ⟨_, ?_, hq0.symm⟩
      · show Fin.tail (Fin.cons (z 0) (Fin.tail (Fin.tail z)) : Fin (d + 1) → ℂ) ∈ B m
        rw [Fin.tail_cons]; exact hz
      · show Fin.tail (Fin.cons (z' 0) (Fin.tail (Fin.tail z')) : Fin (d + 1) → ℂ) ∈ B m'
        rw [Fin.tail_cons]; exact hz'
    rcases lt_or_gt_of_ne hne with h | h
    · exact key m m' h
    · exact (key m' m h).symm
  · refine hnull_mono _ ?_ (hnull_un _ _ (GlobalTheory.T.flag_adjacent_twisted_resolution_seventh K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq h0 h1 hinj))
    intro x hx
    obtain ⟨m, hm⟩ := hpc_cov (FA.pr (q 0 x))
    refine Set.mem_iUnion.2 ⟨(tm m).2, hm.1.2, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, a₀, a₁, ho⟩ := GlobalTheory.T.flag_adjacent_twisted_resolution_fourth K ι Φ y Ψ N j M n d BM FA τ a b k₀ ca cb hb hs hk hca hcb RW q hq h0 h1 hinj
      (tm m).2 x hm.1.2 (fun p => (hcon.2 p).1) (fun p => (hcon.2 p).2)
    have hbs := hm.1.1
    let w := mk ((BM.Rb.A.chart (tm m).1) (FA.pr (q 0 x))) c
    have hbw : bpt (tm m).1 w = FA.pr (q 0 x) := by
      show (BM.Rb.A.chart (tm m).1).symm (base w) = _
      rw [base_mk]; exact (BM.Rb.A.chart (tm m).1).left_inv hbs
    have hwU : w ∈ U m := ⟨by
      show base w ∈ _
      rw [base_mk]; exact (BM.Rb.A.chart (tm m).1).map_source hbs, by
      show bpt (tm m).1 w ∈ _
      rw [hbw]; exact ⟨hm.1.2, hcon.1⟩⟩
    let z : Fin (d + 2) → ℂ := Fin.cons a₀ (Fin.cons a₁ w)
    have hzt : Fin.tail (Fin.tail z) = w := by
      show Fin.tail (Fin.tail (Fin.cons a₀ (Fin.cons a₁ w) : Fin (d + 2) → ℂ)) = w
      rw [Fin.tail_cons, Fin.tail_cons]
    have hz0 : z 0 = a₀ := rfl
    have hz1 : z 1 = a₁ := rfl
    have hz : Fin.tail (Fin.tail z) ∈ U m := by rw [hzt]; exact hwU
    have o := (hWs _ _ z hz).1
    rw [hzt, hz0, hz1] at o
    have o' : SameOrbit (RW.lift (ΦW m z) (ΦW m z)) (FC.wVec M (BM.F (tm m).2) (FC.bvec BM (tm m).2 (bpt (tm m).1 w))
      (FC.Lca τ ca cb (cc w) a₀) τ a k₀ ca cb (a₁ - a₀)) := o
    rw [hbw, cc_mk] at o'
    have e1 : ΦW m z = x := hWinj _ _ (orbit_trans o' (orbit_symm ho))
    refine hx (Set.mem_iUnion.2 ⟨m, z, ?_, e1⟩)
    show Fin.tail (Fin.tail z) ∈ B m
    rw [hzt]
    refine ⟨hwU, ?_⟩
    show bpt (tm m).1 w ∈ pc m
    rw [hbw]; exact hm
  · intro m z hz hmem
    have h2 : FA.S.s (ΦY m z) (ΦY m z) = 0 := hmem
    rw [FA.s_eq] at h2
    have h3 : FA.pr (ΦY m z) ∈ bdry BM.s := h2
    have e1 : FA.pr (ΦY m z) = bpt (tm m).1 (Fin.tail z) := (hYs _ _ z hz).1
    rw [e1] at h3
    exact hz.2.2 h3
  · intro m
    refine ⟨(tm m).2, Hh, bpt (tm m).1,
      fun τ' r s w _ => AnalyticAt.comp (g := fun c => FC.Lc τ ca cb c τ' r s) (f := cc) (lc2 τ' r s _ trivial) (cc_an w trivial),
      hbpc _ _, hbpa _ _, fun w hw => ⟨hw.2, fun τ' => lc1 _ τ'⟩, fun w _ r s => rfl, fun z hz x₀ hx₀ => ?_,
      fun z hz => (hWs _ _ z hz).2⟩
    obtain ⟨hg1, hg2, hg3, hg4⟩ := hgood (tm m).2 _ hz.2.1
    refine ⟨_, (hYs _ _ z hz).2 x₀ hx₀, ?_, fun τ' i => ?_⟩
    · rw [FC.basePart_flagPt]; exact hg4
    · have := FC.exactAt_flagPt M (BM.F (tm m).2) hg3
        (Function.update (fun τ' => Hh τ' (Fin.tail z)) τ (Hh τ (Fin.tail z) * (1 + Matrix.single cb ca (z 0)))) (τ', i)
      rw [Function.update_apply] at this
      exact this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
