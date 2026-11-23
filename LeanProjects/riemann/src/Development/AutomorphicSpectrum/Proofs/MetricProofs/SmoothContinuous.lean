import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantSingularPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphismStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BiholomorphicLiftSystemStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationAntiholomorphicChartsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemRealStructureStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailCutA
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.Cj
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fs_conj (a : K → ℤ) : IsConjInvariantH (fsHerm ι a) := fun z => by
  simp [fsHerm_h, refNorm]

theorem not_mem_top {P : Ideal (MRing ι)} (hP : P = ⊤) (z : (Σ k, ι k) → ℂ) : z ∉ mcPts P := by
  subst hP
  intro h
  have := h.2 1 trivial
  simp at this

theorem sameOrbit_base {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem smooth_continuous {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {f : X → ℝ}
    (hf : A.Smooth f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) := by
    have hm : (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ ∈ nhds (A.chart j x) := by
      simpa using (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
    exact ((hf j).contDiffAt hm).continuousAt
  have h2 := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

def clampT (T t : ℝ) : ℝ := if 0 < t ∧ t ≤ T then t else T

theorem clampT_pos {T : ℝ} (hT : 0 < T) (t : ℝ) : 0 < clampT T t := by
  unfold clampT; split_ifs with h
  · exact h.1
  · exact hT

theorem clampT_le {T : ℝ} (t : ℝ) : clampT T t ≤ T := by
  unfold clampT; split_ifs with h
  · exact h.2
  · exact le_rfl

theorem clampT_eq {T t : ℝ} (h0 : 0 < t) (h1 : t ≤ T) : clampT T t = t := by
  unfold clampT; rw [if_pos ⟨h0, h1⟩]

def avgSys {e : ℕ} {σ : Type} (S : AnSys e σ) (c : S.X → S.X) (C T : ℝ)
    (hreg : ∀ a, IsRegFamily S.A S.Θ S.L S.s (S.th a) (S.ph a)
      (fun t y => (S.phT a t y + S.phT a t (c y)) / 2) C T)
    (hc2 : ∀ a, IsRegFamilyC2 S.A S.s (S.ph a) (fun t y => (S.phT a t y + S.phT a t (c y)) / 2)) :
    AnSys e σ :=
  { S with
    phT := fun a t y => (S.phT a t y + S.phT a t (c y)) / 2
    C := C
    t₀ := T
    reg := hreg
    c2 := hc2 }

def avgLine {D : ℕ} {σ : Type} {S : AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : Realis S P) (T : ℝ) :
    Option σ → ℝ → HermLine ι
  | none, t => Re.line none t
  | some p, t => conjAvg (Re.line (some p) (clampT T t))

def avgRe {D : ℕ} {σ : Type} {S : AnSys D (Option σ)} {P : Ideal (MRing ι)} (Re : Realis S P)
    (c : S.X → S.X) (C T : ℝ)
    (hreg : ∀ a, IsRegFamily S.A S.Θ S.L S.s (S.th a) (S.ph a)
      (fun t y => (S.phT a t y + S.phT a t (c y)) / 2) C T)
    (hc2 : ∀ a, IsRegFamilyC2 S.A S.s (S.ph a) (fun t y => (S.phT a t y + S.phT a t (c y)) / 2))
    (hT0 : 0 < T) (hT : T ≤ S.t₀)
    (hline : ∀ a t, 0 < t → t ≤ T → ∀ x,
      Real.log ((avgLine Re T a t).h (Re.R.lift x x)) = Real.log ((Re.ref a).h (Re.R.lift x x)) +
        (S.phT a t (Re.π x) + S.phT a t (c (Re.π x))) / 2) :
    Realis (avgSys S c C T hreg hc2) P :=
  { Re with
    line := avgLine Re T
    line_deg := fun a t => by
      cases a with
      | none => exact Re.line_deg none t
      | some p => exact Re.line_deg (some p) _
    line_smooth := fun a t h0 h1 => by
      cases a with
      | none => exact Re.line_smooth none t h0 (le_trans h1 hT)
      | some p => exact conjAvg_smooth (Re.line_smooth (some p) _ (clampT_pos hT0 t) ((clampT_le t).trans hT))
    line_eq := hline }

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem onStep_conjAvg (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {A : HermLine ι} (hA : M.OnStep p A) :
    M.OnStep p (conjAvg A) := by
  intro z z' hb hk
  change Real.sqrt |A.h z * A.h (cj z)| = Real.sqrt |A.h z' * A.h (cj z')|
  rw [hA z z' hb hk, hA (cj z) (cj z') ?_ ?_]
  · funext q
    exact congrArg (starRingEnd ℂ) (congrFun hb q)
  · intro k hk' m
    exact congrArg (starRingEnd ℂ) (hk k hk' m)

theorem conj_of_flagAn [Fintype Ψ] {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}
    (FA : FlagAn BM d)
    (h1 : ∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) →
      (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x)
    (h2 : ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) →
      (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) :
    ∃ FA' : FlagAn BM d, ∀ a t, IsConjInvariantH (FA'.Re.line a t) := by
  have hdeg : IsDegreeOff FA.S.A FA.Re.R.A FA.Re.π 1 ∅ := by
    have := FA.Re.degree
    rwa [FA.deg_one, FA.br_empty] at this
  obtain ⟨g, hgπ, hπg, hgh⟩ := GlobalTheory.T.holomorphic_degree_one_biholomorphism FA.S.A FA.Re.R.A FA.Re.π FA.Re.holo hdeg
  have hsys := GlobalTheory.T.biholomorphic_lift_system FA.J_top FA.Re.R FA.S.A g FA.Re.π hgπ hπg hgh FA.Re.holo
  obtain ⟨c, hspec, hcont, hinv⟩ := GlobalTheory.T.lift_system_complex_conjugation hsys
  have hanal := GlobalTheory.T.conjugation_antiholomorphic_charts hsys c hspec hcont
  have hmem : ∀ r, FA.Re.R.lift r r ∈ mcPts (mCoordIdeal y) := fun r =>
    FA.Re.R.mem r r (FA.Re.R.mem_U r)

  have hbase : ∀ x, SameOrbit (BM.Rb.lift (FA.pr (c x)) (FA.pr (c x)))
      (cj (BM.Rb.lift (FA.pr x) (FA.pr x))) := by
    intro x
    have e1 := FA.pr_eq (g (c x))
    have e2 := FA.pr_eq (g x)
    rw [hπg] at e1 e2
    have e3 := sameOrbit_base M.blk (hspec x)
    refine sameOrbit_trans (sameOrbit_symm e1) (sameOrbit_trans e3 ?_)
    exact sameOrbit_cj e2
  have hs_eq : ∀ x, FA.S.s x x = BM.s (FA.pr x) (FA.pr x) := fun x => by rw [FA.s_eq]
  have hbd : ∀ x, x ∈ bdry FA.S.s ↔ FA.pr x ∈ bdry BM.s := fun x => by
    change FA.S.s x x = 0 ↔ BM.s (FA.pr x) (FA.pr x) = 0
    rw [hs_eq]
  have hrW : ∀ x, rW FA.S.L FA.S.s x = rW BM.L BM.s (FA.pr x) := fun x => by
    unfold rW logNormSec
    rw [hs_eq, FA.L_eq]
    rfl
  have hcb : ∀ x, c x ∈ bdry FA.S.s ↔ x ∈ bdry FA.S.s := fun x => by
    rw [hbd, hbd]; exact (h1 _ _ (hbase x)).1
  have hcr : ∀ x, rW FA.S.L FA.S.s (c x) = rW FA.S.L FA.S.s x := fun x => by
    rw [hrW, hrW]; exact (h1 _ _ (hbase x)).2

  have href : ∀ a, IsConjInvariantH (FA.Re.ref a) := fun a => by
    cases a with
    | none => rw [FA.ref_none]; exact fs_conj _
    | some p => rw [FA.ref_some]; exact fs_conj _
  have hth : ∀ a x, ∃ V : Set FA.S.X, IsOpen V ∧ x ∈ V ∧ ∃ G : FA.S.X → ℂ, FA.S.A.HoloOn V G ∧
      ∀ y' ∈ V, (FA.S.th a).φ (c x) (c y') - (FA.S.th a).φ x y' = (G y').re := fun a =>
    GlobalTheory.T.lift_system_real_structure hsys c hspec hcont hanal (FA.Re.ref a) (href a) (FA.S.th a) fun x => by
      obtain ⟨V, hV, hxV, G, hG, hGe⟩ := FA.Re.ref_pot a (g x) (Set.mem_univ _)
      refine ⟨g ⁻¹' V, hV.preimage hgh.1, hxV, G ∘ g, holoOn_comp hgh hG, fun y' hy' => ?_⟩
      have := hGe (g y') hy'
      simp only [potOf, LocPot.pullback, hπg] at this
      exact this

  have hph : ∀ p, ∀ x ∉ bdry FA.S.s, FA.S.ph (some p) (c x) = FA.S.ph (some p) x := by
    intro p x hx
    have hx' : c x ∉ bdry FA.S.s := fun h => hx ((hcb x).1 h)
    have e1 := FA.hom_eq p (g x) (by rw [hπg]; exact hx)
    have e2 := FA.hom_eq p (g (c x)) (by rw [hπg]; exact hx')
    rw [hπg] at e1 e2
    have hpx : FA.pr x ∉ bdry BM.s := fun h => hx ((hbd x).2 h)
    have hzz := FA.pr_eq (g x)
    rw [hπg] at hzz
    have hinvh : (BM.hom p).h (cj (FA.Re.R.lift (g x) (g x))) = (BM.hom p).h (FA.Re.R.lift (g x) (g x)) :=
      h2 p _ (hmem (g x)) (FA.pr x) hpx hzz
    have ho := log_sub_orbit (BM.hom p) (FA.Re.ref (some p)) (by rw [BM.hom_deg, FA.ref_some]; rfl)
      (cj_nonzero (hmem (g x)).1) (hspec x)
    have hr : (FA.Re.ref (some p)).h (cj (FA.Re.R.lift (g x) (g x))) =
        (FA.Re.ref (some p)).h (FA.Re.R.lift (g x) (g x)) := href (some p) _
    rw [hinvh, hr] at ho
    linarith
  have hphall : ∀ a, ∀ x ∉ bdry FA.S.s, FA.S.ph a (c x) = FA.S.ph a x := fun a => by
    cases a with
    | none => intro x _; rw [FA.ph_none.1]; rfl
    | some p => exact hph p

  have hreg : ∀ a, ∃ C' t' : ℝ, IsRegFamily FA.S.A FA.S.Θ FA.S.L FA.S.s (FA.S.th a) (FA.S.ph a)
        (fun t y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2) C' t' ∧
      IsRegFamilyC2 FA.S.A FA.S.s (FA.S.ph a) fun t y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2 :=
    fun a => GlobalTheory.T.conjugation_invariant_singular_potential (d + 1) FA.S.X FA.S.A FA.S.Θ FA.S.L FA.S.s FA.S.nb FA.S.m FA.S.W FA.S.potL FA.S.sec
      FA.S.snc FA.S.norm_le FA.S.potΘ FA.S.posΘ c hcont hinv hanal hcb hcr (FA.S.th a) (FA.S.ph a) (FA.S.phT a)
      FA.S.C FA.S.t₀ (FA.S.sing a).1 (hth a) (hphall a) (FA.S.reg a) (FA.S.c2 a)
  choose Cf tf hregf hc2f using hreg
  have hne : (Finset.univ : Finset (Option (Ψ × Fin N))).Nonempty := ⟨none, Finset.mem_univ _⟩
  set T : ℝ := min (min (Finset.univ.inf' hne tf) FA.S.t₀) (Real.exp (-1)) with hTdef
  have ht00 : 0 < FA.S.t₀ := (FA.S.reg none).1
  have hT0 : 0 < T := by
    refine lt_min (lt_min ?_ ht00) (Real.exp_pos _)
    rw [Finset.lt_inf'_iff]
    exact fun a _ => (hregf a).1
  have hTS : T ≤ FA.S.t₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hTf : ∀ a, T ≤ tf a := fun a =>
    ((min_le_left _ _).trans (min_le_left _ _)).trans (Finset.inf'_le _ (Finset.mem_univ a))
  have hTe : T ≤ Real.exp (-1) := min_le_right _ _
  set Cs : ℝ := ∑ a, |Cf a| with hCs
  have hCle : ∀ a, |Cf a| ≤ Cs := fun a =>
    Finset.single_le_sum (f := fun a => |Cf a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hreg' : ∀ a, IsRegFamily FA.S.A FA.S.Θ FA.S.L FA.S.s (FA.S.th a) (FA.S.ph a)
      (fun t y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2) Cs T := fun a =>
    (GlobalTheory.T.singular_weight_monotone_regularization (d + 1) FA.S.X FA.S.A FA.S.Θ FA.S.L FA.S.s FA.S.nb FA.S.m FA.S.W FA.S.potL FA.S.sec
      FA.S.snc FA.S.norm_le FA.S.potΘ FA.S.posΘ).2.1 _ _ _ _ _ _ _ (hCle a) hT0 (hTf a) hTe (hregf a) (FA.S.sing a).1

  have hline : ∀ a t, 0 < t → t ≤ T → ∀ x,
      Real.log ((avgLine FA.Re T a t).h (FA.Re.R.lift x x)) =
        Real.log ((FA.Re.ref a).h (FA.Re.R.lift x x)) +
        (FA.S.phT a t (FA.Re.π x) + FA.S.phT a t (c (FA.Re.π x))) / 2 := by
    intro a t h0 ht x
    cases a with
    | none =>
      have e := FA.Re.line_eq none t h0 (ht.trans hTS) x
      change Real.log ((FA.Re.line none t).h (FA.Re.R.lift x x)) = _
      rw [e, FA.ph_none.2 t]
      simp
    | some p =>
      change Real.log ((conjAvg (FA.Re.line (some p) (clampT T t))).h (FA.Re.R.lift x x)) = _
      rw [clampT_eq h0 ht, conjAvg_log _ (hmem x).1]
      have e1 := FA.Re.line_eq (some p) t h0 (ht.trans hTS) x
      have e2 := FA.Re.line_eq (some p) t h0 (ht.trans hTS) (g (c (FA.Re.π x)))
      rw [hπg] at e2
      have hsp := hspec (FA.Re.π x)
      rw [hgπ] at hsp
      have ho := log_sub_orbit (FA.Re.line (some p) t) (FA.Re.ref (some p)) (FA.Re.line_deg _ _)
        (cj_nonzero (hmem x).1) hsp
      have hr : (FA.Re.ref (some p)).h (cj (FA.Re.R.lift x x)) = (FA.Re.ref (some p)).h (FA.Re.R.lift x x) :=
        href (some p) _
      rw [hr] at ho
      linarith
  have hpot : ∀ a t, (∀ y', FA.S.phT a t (c y') = FA.S.phT a t y') →
      (avgSys FA.S c Cs T hreg' hc2f).potT a t = FA.S.potT a t := by
    intro a t h
    have e : (fun y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2) = FA.S.phT a t := by
      funext y'
      rw [h y']
      ring
    change FA.S.th a + LocPot.ofFun (fun y' => (FA.S.phT a t y' + FA.S.phT a t (c y')) / 2) =
      FA.S.th a + LocPot.ofFun (FA.S.phT a t)
    rw [e]
  refine ⟨{ S := avgSys FA.S c Cs T hreg' hc2f
            Re := avgRe FA.Re c Cs T hreg' hc2f hT0 hTS hline
            J_top := FA.J_top
            deg_one := FA.deg_one
            br_empty := FA.br_empty
            ref_some := FA.ref_some
            ref_none := FA.ref_none
            line_none := FA.line_none
            ph_none := ⟨FA.ph_none.1, fun t => ?_⟩
            pos_none := ?_
            pr := FA.pr
            pr_holo := FA.pr_holo
            pr_eq := FA.pr_eq
            L_eq := FA.L_eq
            s_eq := FA.s_eq
            hom_eq := FA.hom_eq
            step := fun p t => onStep_conjAvg M (FA.step p _)
            step_ph := ?_
            flat := ?_ }, ?_⟩
  · change (fun y' => (FA.S.phT none t y' + FA.S.phT none t (c y')) / 2) = 0
    rw [FA.ph_none.2 t]
    funext y'
    simp
  · obtain ⟨c₀, hc₀, hp⟩ := FA.pos_none
    refine ⟨c₀, hc₀, fun t => ?_⟩
    rw [hpot none t fun y' => by rw [FA.ph_none.2 t]; rfl]
    exact hp t
  · refine fun p (x : FA.Re.R.X) (x' : FA.Re.R.X) hpr hblk => ?_
    obtain ⟨hph0, hpt⟩ := FA.step_ph p x x' hpr hblk
    refine ⟨hph0, fun t => ?_⟩
    change (FA.S.phT (some p) t (FA.Re.π x) + FA.S.phT (some p) t (c (FA.Re.π x))) / 2 =
      (FA.S.phT (some p) t (FA.Re.π x') + FA.S.phT (some p) t (c (FA.Re.π x'))) / 2
    have hinj : FA.pr (c (FA.Re.π x)) = FA.pr (c (FA.Re.π x')) := by
      refine BM.Rb.inj _ _ (not_mem_top rfl _) (sameOrbit_trans (hbase (FA.Re.π x)) ?_)
      have hpr' : FA.pr (FA.Re.π x) = FA.pr (FA.Re.π x') := hpr
      rw [hpr']
      exact sameOrbit_symm (hbase (FA.Re.π x'))
    have hb : ∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k,
        FA.Re.R.lift (g (c (FA.Re.π x))) (g (c (FA.Re.π x))) ⟨k, m⟩ =
          a * FA.Re.R.lift (g (c (FA.Re.π x'))) (g (c (FA.Re.π x'))) ⟨k, m⟩ := by
      intro k hk
      obtain ⟨a, ha⟩ := hblk k hk
      have hs1 := hspec (FA.Re.π x)
      have hs2 := hspec (FA.Re.π x')
      rw [hgπ] at hs1 hs2
      obtain ⟨b, hb0, hbe⟩ := hs1
      obtain ⟨b', hb0', hbe'⟩ := hs2
      refine ⟨b k * starRingEnd ℂ a * (b' k)⁻¹, fun m => ?_⟩
      have e1 := congrFun hbe ⟨k, m⟩
      have e2 := congrFun hbe' ⟨k, m⟩
      rw [e1, e2]
      have e3 : FA.Re.R.lift x x ⟨k, m⟩ = a * FA.Re.R.lift x' x' ⟨k, m⟩ := ha m
      simp only [cj]
      rw [e3, map_mul]
      have := hb0' k
      field_simp
    have hlast := (FA.step_ph p (g (c (FA.Re.π x))) (g (c (FA.Re.π x')))
      (by rw [hπg, hπg]; exact hinj) hb).2 t
    rw [hπg, hπg] at hlast
    rw [hpt t, hlast]
  · intro p hp t
    have hs : FA.S.A.Smooth (FA.S.ph (some p)) := by
      have h0 := ((FA.S.reg (some p)).2.2 FA.S.t₀ ht00 le_rfl).1
      rwa [(FA.flat p hp FA.S.t₀).2.2] at h0
    have hc1 := smooth_continuous hs
    have hd : Dense (bdry FA.S.s)ᶜ :=
      interior_eq_empty_iff_dense_compl.1 (LeviFormBoundaryTopology.interior_bdry_eq_empty FA.S.sec FA.S.snc)
    have hcp : ∀ y', FA.S.ph (some p) (c y') = FA.S.ph (some p) y' :=
      congrFun (Continuous.ext_on hd (hc1.comp hcont) hc1 fun y' hy' => hph p y' hy')
    obtain ⟨f1, f2, f3⟩ := FA.flat p hp t
    have hpt : ∀ y', FA.S.phT (some p) t (c y') = FA.S.phT (some p) t y' := by
      rw [f3]; exact hcp
    have e := hpot (some p) t hpt
    refine ⟨?_, ?_, ?_⟩
    · rw [e]; exact f1
    · rw [e]; exact f2
    · change (fun y' => (FA.S.phT (some p) t y' + FA.S.phT (some p) t (c y')) / 2) = FA.S.ph (some p)
      funext y'
      rw [hpt y', f3]
      ring
  · intro a t
    cases a with
    | none =>
      change IsConjInvariantH (FA.Re.line none t)
      rw [FA.line_none]
      exact fs_conj _
    | some p => exact conjAvg_conj _

end GlobalTheory.CompanionTheory.Ar.PB.Cj

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flagAn_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), Nonempty (FlagAn BM d) → (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) → (x' ∈ bdry BM.s ↔ x ∈ bdry BM.s) ∧ rW BM.L BM.s x' = rW BM.L BM.s x) → (∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ bdry BM.s → SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z) → ∃ FA : FlagAn BM d, ∀ a t, IsConjInvariantH (FA.Re.line a t) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM hFA h1 h2
  obtain ⟨FA⟩ := hFA
  exact Cj.conj_of_flagAn FA h1 h2

end GlobalTheory.CompanionTheory.Ar.PB
