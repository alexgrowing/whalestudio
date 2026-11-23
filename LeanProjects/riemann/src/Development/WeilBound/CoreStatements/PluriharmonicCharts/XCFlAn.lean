import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists
import Development.WeilBound.CoreStatements.PluriharmonicCharts.NotMemTop
import Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJOneSelf
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackThirdStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_fl_an

open GlobalTheory.CompanionTheory.Ar.PB.FA GlobalTheory.CompanionTheory.Ar.PB.StepW
open scoped ContDiff

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem onStep_fs (M : FlagModel y Ψ N j) (p : Ψ × Fin N) : M.OnStep p (fsHerm ι (M.dy p)) := by
  intro z z' h1 h2
  rw [fsHerm_h, fsHerm_h, refNorm, refNorm]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : ∀ p', M.blk p' ≠ some k
  · have : ∀ i, z ⟨k, i⟩ = z' ⟨k, i⟩ := fun i => congrFun h1 ⟨⟨k, hk⟩, i⟩
    simp only [this]
  · by_cases hk' : M.blk p = some k
    · simp only [h2 k hk']
    · have : M.dy p k = 0 := by
        unfold FlagModel.dy
        rw [dif_neg hk, if_neg hk']
      simp [this]

theorem isPsh_of_univ {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X} {P : LocPot X}
    (hU : ∀ x, x ∈ U) (h : IsPshOn A U P) : IsPsh A P :=
  fun x j w hw v => h x j w ⟨hw.1, hw.2, hU _⟩ v

theorem step_member [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n e : ℕ} (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr)
    (hbd : bdry BM.s = ∅) (hh : ∀ p, BM.hom p = fsHerm ι (M.dy p))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (pL : IsPotential R.A (BM.L.pullback pr hp.1))
    (sL : IsSection R.A (BM.L.pullback pr hp.1) fun x y => BM.s (pr x) (pr y))
    (nL : IsSNC R.A (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) BM.m fun k => pr ⁻¹' BM.W k)
    (p : Ψ × Fin N) :
    ∃ C₅ : ℝ, IsStepMember BM R pr hp p 0 (fun _ => 0) (fun _ => fsHerm ι (M.dy p)) C₅ C₅
      (Real.exp (-Real.exp 1)) := by
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ e R
  have hfsa : IsSmoothHerm (fsHerm ι (M.dy p)) := FlagHeightMultilinear.isSmoothHerm_fsHerm _
  have hU : ∀ x, x ∈ (bdry fun x y => BM.s (pr x) (pr y))ᶜ := fun x hx => by
    have : pr x ∈ bdry BM.s := hx
    rw [hbd] at this
    exact this
  have hpts : ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ id = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)) :=
    fun x => ⟨R.lift x x, R.mem x x (R.mem_U x), rfl, hb x⟩
  have hyp : IsStepHyp M BM p id id R pr := ⟨isBlockMap_id, fun k _ => ⟨k, rfl⟩, hp, hpts⟩
  have h0 : stepPh M BM p id R pr = 0 := by
    funext x
    unfold stepPh
    split_ifs
    · rw [stepGap, hh, sub_self]; rfl
    · rfl
  have hps := PositivityTheory.Xgp.plurisubharmonic_charts.isPshOn_stepPot K ι Φ y Ψ N j M n BM p K ι id id e R pr hp
    (GlobalTheory.T.flag_gap_pullback_third K ι Φ y Ψ N j M n BM p K ι id id e R pr hyp)
  rw [h0] at hps
  have hps' : IsPsh R.A (potOf R (fsHerm ι (M.dy p)) + LocPot.ofFun (0 : R.X → ℝ)) := isPsh_of_univ hU hps
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ ∞ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  obtain ⟨C₀, s0, r0, c0⟩ := (GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members e R.X R.A
    (potOf R (fsHerm ι fun _ => 1)) _ _ BM.nb BM.m _ pL sL nL hn (hA _ hfs) hΘ).2.2 _ 0 (hA _ hfsa) hsm0 hps'
  refine ⟨C₀, s0, r0, c0, fun _ => rfl, fun _ => onStep_fs M p, fun t _ _ => ⟨hfsa, fun x => by simp⟩,
    fun x _ => by rw [hh]; simp, fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩, fun hc t => ⟨?_, hps', rfl⟩⟩
  have flat := GlobalTheory.CompanionTheory.Ar.PB.FA.Flat.flat_off_boundary K ι Φ y Ψ N j M n BM p hc K ι id id isBlockMap_id
    (fun k _ => ⟨k, rfl⟩) e R pr hp 0 hpts (fun x _ z _ _ => by rw [hh]; simp)
  exact isPsh_of_univ hU flat.2

theorem flagAn_of_res [Fintype Ψ] [DecidableEq Ψ]
    (M : FlagModel y Ψ N j) {n : ℕ} (d : ℕ) (BM : BaseMetric M n) (R : AnLogRes (mCoordIdeal y) ⊤ (d + 1))
    (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr) (harith : IsArithVar (mCoordIdeal y) (d + 2))
    (hbd : bdry BM.s = ∅) (hh : ∀ p, BM.hom p = fsHerm ι (M.dy p))
    (hb : ∀ x, SameOrbit (basePart M.blk (R.lift x x)) (BM.Rb.lift (pr x) (pr x)))
    (hch : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin (d + 1) → ℂ)) (kb : Fin BM.Rb.A.n) (σ : Fin n ↪ Fin (d + 1)),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (BM.Rb.A.chart kb).source ∧
        ∀ i, BM.Rb.A.chart kb (pr x') i = ψ x' (σ i))) :
    ∃ FA : FlagAn BM d, ∀ p t, FA.Re.line (some p) t = fsHerm ι (M.dy p) := by
  obtain ⟨pL, sL, nL, B, hB⟩ := GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection (d + 1) n R.X BM.Rb.X R.A BM.Rb.A BM.Bat pr hp BM.L BM.s BM.nb BM.m BM.W
    BM.potL BM.sec BM.snc BM.norm_le hch
  have hn : ∀ x, logNormSec (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x ≤ 0 :=
    fun x => BM.norm_le (pr x)
  obtain ⟨hA, hfs, hΘ⟩ := GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential K ι _ (d + 1) R
  have hfsa : ∀ a : K → ℤ, IsSmoothHerm (fsHerm ι a) := GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm
  choose C₅ hm using fun p => step_member M BM R pr hp hbd hh hb pL sL nL p
  let ph : Ψ × Fin N → R.X → ℝ := fun _ => 0
  let phT : Ψ × Fin N → ℝ → R.X → ℝ := fun _ _ => 0
  let line : Ψ × Fin N → ℝ → HermLine ι := fun p _ => fsHerm ι (M.dy p)
  let C := C₅
  let t₀ : Ψ × Fin N → ℝ := fun _ => Real.exp (-Real.exp 1)
  obtain ⟨m₁, m₂, m₃⟩ := GlobalTheory.CompanionTheory.Ar.PB.enlarging_constants_smooth_members (d + 1) R.X R.A (potOf R (fsHerm ι fun _ => 1)) _ _ BM.nb BM.m _ pL sL nL hn
    (hA _ hfs) hΘ
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ ∞ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  have hpsh0 : IsPsh R.A (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)) := by
    intro x jj z hz w
    have e1 : (potOf R (fsHerm ι fun _ => 1) + LocPot.ofFun (0 : R.X → ℝ)).φ x ∘ (R.A.chart jj).symm =
        (potOf R (fsHerm ι fun _ => 1)).φ x ∘ (R.A.chart jj).symm := by
      funext u
      show (potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ) = _
      rw [add_zero]
      rfl
    rw [e1]
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hΘ x jj z ⟨hz.1, hz.2.1⟩ w hw).le
  obtain ⟨C₀, s0, r0, c0⟩ := m₃ _ 0 (hA _ hfs) hsm0 hpsh0
  obtain ⟨D₅, hD₅⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim C₀ C₅
  obtain ⟨D, hD⟩ := common_bound fun o : Option (Ψ × Fin N) => o.elim |C₀| fun p => |C p|
  obtain ⟨T, hT0, hT⟩ := common_scale (fun o : Option (Option (Ψ × Fin N)) =>
    o.elim (Real.exp (-1)) fun o' => o'.elim (Real.exp (-Real.exp 1)) t₀) (by
      rintro (_ | _ | p)
      · exact Real.exp_pos _
      · exact Real.exp_pos _
      · exact (hm p).2.1.1)
  have hT1 : T ≤ Real.exp (-1) := hT none
  have hm' : ∀ p, IsStepMember BM R pr hp p (ph p) (phT p) (line p) D₅ D T := fun p =>
    IsStepMember.mono m₁ m₂ (hm p) (hD₅ (some p)) (hD (some p)) hT0 (hT (some (some p))) hT1
  have s0' := m₁ _ _ _ _ (hD₅ none) s0
  have r0' := m₂ _ _ _ _ _ _ _ (hD none) hT0 (hT (some none)) hT1 r0 (hA _ hfs)
  let S : AnSys (d + 1) (Option (Ψ × Fin N)) :=
    { X := R.X
      A := R.A
      Θ := potOf R (fsHerm ι fun _ => 1)
      L := BM.L.pullback pr hp.1
      s := fun x y => BM.s (pr x) (pr y)
      nb := BM.nb
      m := BM.m
      W := fun k => pr ⁻¹' BM.W k
      potΘ := hA _ hfs
      posΘ := hΘ
      potL := pL
      sec := sL
      snc := nL
      norm_le := hn
      th := fun o => o.elim (potOf R (fsHerm ι fun _ => 1)) fun p => potOf R (fsHerm ι (M.dy p))
      ph := fun o => o.elim 0 ph
      phT := fun o => o.elim (fun _ => 0) phT
      C₅ := D₅
      C := D
      t₀ := T
      sing := by
        rintro (_ | p)
        · exact s0'
        · exact (hm' p).1
      reg := by
        rintro (_ | p)
        · exact r0'
        · exact (hm' p).2.1
      c2 := by
        rintro (_ | p)
        · exact c0
        · exact (hm' p).2.2.1 }
  let Re : Realis S (mCoordIdeal y) :=
    { arith := harith
      J := ⊤
      R := R
      π := id
      holo := ⟨continuous_id, fun jj k => R.A.holo jj k⟩
      deg := 1
      deg_pos := one_pos
      br := ∅
      degree := degree_id_self R.A
      ref := fun o => o.elim (fsHerm ι fun _ => 1) fun p => fsHerm ι (M.dy p)
      ref_smooth := by
        rintro (_ | p)
        · exact hfs
        · exact hfsa _
      ref_pot := by
        rintro (_ | p) <;>
        exact fun x _ => ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
          fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
      line := fun o t => o.elim (fsHerm ι fun _ => 1) fun p => line p t
      line_deg := by
        rintro (_ | p) t
        · rfl
        · exact (hm' p).2.2.2.1 t
      line_smooth := by
        rintro (_ | p) t h0 h1
        · exact hfs
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).1
      line_eq := by
        rintro (_ | p) t h0 h1 x
        · exact (add_zero _).symm
        · exact ((hm' p).2.2.2.2.2.1 t h0 h1).2 x }
  refine ⟨{ S := S, Re := Re, J_top := rfl, deg_one := rfl, br_empty := rfl, ref_some := fun _ => rfl, ref_none := rfl,
            line_none := fun _ => rfl, ph_none := ⟨rfl, fun _ => rfl⟩, pos_none := ?_, pr := pr, pr_holo := hp,
            pr_eq := hb, L_eq := rfl, s_eq := rfl, hom_eq := ?_, step := ?_, step_ph := ?_, flat := ?_ }, fun _ _ => rfl⟩
  · refine ⟨1, one_pos, fun t x jj z _ w => ?_⟩
    have e1 : (S.potT none t + S.Θ.rsmul (-1)).φ x ∘ (S.A.chart jj).symm = fun _ => (0 : ℝ) := by
      funext u
      show ((potOf R (fsHerm ι fun _ => 1)).φ x _ + (0 : ℝ)) + (-1) * (potOf R (fsHerm ι fun _ => 1)).φ x _ = 0
      ring
    rw [e1]
    simp [levi]
  · exact fun p x hx => (hm' p).2.2.2.2.2.2.1 x hx
  · exact fun p t => (hm' p).2.2.2.2.1 t
  · exact fun p x x' h1 h2 => (hm' p).2.2.2.2.2.2.2.1 x x' h1 h2
  · exact fun p h1 t => (hm' p).2.2.2.2.2.2.2.2 h1 t

end PositivityTheory.Xgp.c_fl_an

end

theorem PositivityTheory.Xgp.t_c_fl_an : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n), IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → bdry BM.s = ∅ → (∀ p, BM.hom p = fsHerm ι (M.dy p)) → ∃ FA : FlagAn BM d, ∀ p t, FA.Re.line (some p) t = fsHerm ι (M.dy p) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM harith hd hbd hh
  obtain ⟨e, R, he, pr, hp, hpts, hch⟩ := PositivityTheory.Xgp.c_smooth.main K ι Φ y Ψ N j M n (d + 1) BM.Rb hd (fun _ => True) K ι id id
    isBlockMap_id (fun k => ⟨fun _ => by
      by_cases h : ∀ p', M.blk p' ≠ some k
      · exact Or.inl h
      · push Not at h
        obtain ⟨p, hp⟩ := h
        exact Or.inr ⟨p, trivial, hp⟩, fun _ => ⟨k, rfl⟩⟩)
  obtain rfl := he fun _ => trivial
  refine PositivityTheory.Xgp.c_fl_an.flagAn_of_res M d BM R pr hp harith hbd hh (fun x => ?_) hch
  obtain ⟨z, -, hz, ho⟩ := hpts x
  have hz' : z = R.lift x x := hz
  rw [← hz']
  exact ho
