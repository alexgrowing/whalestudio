import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import Formalism.LocalToGlobal.ProjectiveLattices.OneCusp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfB
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ValAtAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfDefinite
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TranscendenceDegreeRatiosCuspFormsComponents
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvatureMarginsDefiniteCaseStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RunWeightDominantAndGapsDefiniteCaseStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspFormNonzeroEveryComponentStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

noncomputable section

namespace GlobalTheory.ArchDefinite

section Model

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_pos_le_firstMinimum_definiteForm (X : Data E r) (hr : 0 < r) (hp : X.p0 = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, ε ≤ X.la1 x := by
  obtain ⟨C, hCc, hCd, hcov⟩ := GlobalTheory.DefiniteFrames.exists_compact_of_definite E r X (Or.inl hp)
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    obtain ⟨γ, -, b, -, hmem⟩ := hcov x hx
    rw [hCe] at hmem
    exact hmem.elim
  · obtain ⟨y, hyC, hmin⟩ :=
      hCc.exists_isMinOn hCne ((ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimum_continuousOn X).mono hCd)
    refine ⟨X.la1 y, ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom X hr (hCd hyC), fun x hx => ?_⟩
    obtain ⟨γ, hγ, b, hb, hmem⟩ := hcov x hx
    have hle : X.la1 y ≤ X.la1 (lact γ (rmul x b)) := isMinOn_iff.mp hmin _ hmem
    rwa [ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimum_biinvariant X hγ hx hb] at hle

private theorem pnorm_pos_of_ne_zero' (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (h : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx τ).2 i
    rw [h0] at this
    simp at this
  unfold Data.pnorm
  refine mul_pos (norm_pos_iff.mpr h) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

theorem exists_le_sum_sq (X : Data E r) (hp : X.p0 = 0) (la : Wt X.Ψ r) {N : ℕ}
    (P : Fin N → Frame X.Ψ r → ℂ) (hP : ∀ i, X.IsSec la (P i)) (hz : ∀ x ∈ X.dom, ∃ i, P i x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, c ≤ ∑ i, X.pnorm la (P i) x ^ 2 := by
  obtain ⟨C, hCc, hCd, hcov⟩ := GlobalTheory.DefiniteFrames.exists_compact_of_definite E r X (Or.inl hp)
  have hinv : ∀ x ∈ X.dom, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
      ∑ i, X.pnorm la (P i) (lact γ (rmul x b)) ^ 2 = ∑ i, X.pnorm la (P i) x ^ 2 := by
    intro x hx γ hγ b hb
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ReciprocityTheory.ChartRestriction.G.AR.Inst.pointwiseNorm_invariance_holds r X la (P i) (hP i) γ hγ x hx b hb]
  have hpos : ∀ x ∈ X.dom, 0 < ∑ i, X.pnorm la (P i) x ^ 2 := by
    intro x hx
    obtain ⟨i, hi⟩ := hz x hx
    have h0 : 0 < X.pnorm la (P i) x := pnorm_pos_of_ne_zero' X la (P i) hx hi
    calc (0 : ℝ) < X.pnorm la (P i) x ^ 2 := pow_pos h0 2
      _ ≤ ∑ j, X.pnorm la (P j) x ^ 2 :=
        Finset.single_le_sum (f := fun j => X.pnorm la (P j) x ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    obtain ⟨γ, -, b, -, hmem⟩ := hcov x hx
    rw [hCe] at hmem
    exact hmem.elim
  · have hcont : ContinuousOn (fun x => ∑ i, X.pnorm la (P i) x ^ 2) C :=
      (continuousOn_finsetSum _ fun i _ =>
        (ReciprocityTheory.ChartRestriction.G.AR.Up.BigB.pnorm_contOn X la (hP i)).pow 2).mono hCd
    obtain ⟨y, hyC, hmin⟩ := hCc.exists_isMinOn hCne hcont
    refine ⟨_, hpos y (hCd hyC), fun x hx => ?_⟩
    obtain ⟨γ, hγ, b, hb, hmem⟩ := hcov x hx
    have hle := isMinOn_iff.mp hmin _ hmem
    rwa [hinv x hx γ hγ b hb] at hle

private theorem antitone_of_succ_le_torus_haar_measure {r : ℕ} (f : Fin r → ℤ) (hf : ∀ a b : Fin r, (b : ℕ) = a + 1 → f b ≤ f a) :
    ∀ a b : Fin r, a ≤ b → f b ≤ f a := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_le_mk] at hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ n hn ih =>
    intro hb
    exact (hf ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega))

private theorem exists_injective_leviM_eq_sum_weight_sq (X : Data E r) (hp : X.p0 = 0) (x0 : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X))
    (hz : cpt X x0 z ∈ X.dom) :
    ∃ D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ), Function.Injective D ∧ ∀ (la : Wt X.Ψ r) ξ,
      leviM X (phla X la) x0 z ξ = ∑ e : Ent X,
        ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) * ‖D ξ (Fintype.equivFin (Ent X) e)‖ ^ 2 := by
  obtain ⟨x1, D, -, hD, -, hdiag, -⟩ := GlobalTheory.FrameThetaCompare.transfer X x0 z hz
  refine ⟨D, hD, fun la ξ => ?_⟩
  have h := hdiag la ξ
  change GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 la z ξ = _
  rw [h, GlobalTheory.FrameThetaCompare.diagForm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [sgn, hp]

private theorem leviM_pos_of_isStrictDom (X : Data E r) (hp : X.p0 = 0) (la : Wt X.Ψ r) (hla : IsStrictDom X la)
    (x0 : Frame X.Ψ r) (hx0 : x0 ∈ X.dom) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)) (hz : cpt X x0 z ∈ X.dom) (ξ : Fin (nd X) → ℂ)
    (hξ : ξ ≠ 0) : 0 < leviM X (phla X la) x0 z ξ := by
  obtain ⟨D, hD, hl⟩ := exists_injective_leviM_eq_sum_weight_sq X hp x0 z hz
  rw [hl]
  have hDξ : D ξ ≠ 0 := fun h => hξ (hD (h.trans (map_zero D).symm))
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hDξ
  have hm' : D ξ m ≠ 0 := by simpa using hm
  set m2 : Fin (Fintype.card (Ent X)) := m with hm2
  have hterm : ∀ e : Ent X, 0 ≤ ((la e.1 e.2.1.2 : ℝ) - (la e.1 e.2.1.1 : ℝ)) *
      ‖D ξ (Fintype.equivFin (Ent X) e)‖ ^ 2 := by
    intro e
    have hlt := (hla e.1).2.1 e.2.1.2 e.2.1.1 (by omega) e.2.2
    have : (la e.1 e.2.1.1 : ℝ) < la e.1 e.2.1.2 := by exact_mod_cast hlt
    positivity
  set e0 := (Fintype.equivFin (Ent X)).symm m2 with he0
  refine Finset.sum_pos' (fun e _ => hterm e) ⟨e0, Finset.mem_univ _, ?_⟩
  have hlt := (hla e0.1).2.1 e0.2.1.2 e0.2.1.1 (by omega) e0.2.2
  have h1 : (0 : ℝ) < (la e0.1 e0.2.1.2 : ℝ) - (la e0.1 e0.2.1.1 : ℝ) := by
    have : (la e0.1 e0.2.1.1 : ℝ) < la e0.1 e0.2.1.2 := by exact_mod_cast hlt
    linarith
  have h2 : (0 : ℝ) < ‖D ξ (Fintype.equivFin (Ent X) e0)‖ ^ 2 := by
    rw [he0, Equiv.apply_symm_apply]
    exact pow_pos (norm_pos_iff.mpr hm') 2
  exact mul_pos h1 h2

theorem exists_archInM (X : Data E r) (hr : 0 < r) (hp : X.p0 = 0) (hΨ : Nonempty X.Ψ) (L F : Wt X.Ψ r) (T N : ℕ)
    (hn : 2 ≤ nd X) (hT : 11 * nd X ^ 2 ≤ T) (hL : IsStrictDom X L)
    (hgap : ∀ (τ : X.Ψ) (a b : Fin r), (b : ℕ) = a + 1 →
      (F - kapW X - nd X • L) τ b + 2 * (L τ a - L τ b) ≤ (F - kapW X - nd X • L) τ a)
    (w : Fin N → Frame X.Ψ r → ℂ) (hw : ∀ k, w k ∈ X.SSgt L 0) (hw0 : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0)
    (th2 : Frame X.Ψ r → ℂ) (h2 : th2 ∈ X.SSgt ((nd X + 4) • L - F) 0) (h20 : ∃ x ∈ X.dom, th2 x ≠ 0)
    (thp : Frame X.Ψ r → ℂ) (h3 : thp ∈ X.SSgt F 0) (h30 : ∃ x ∈ X.dom, thp x ≠ 0) :
    ∃ (Xa : ArchInM X) (hN : Xa.N = N) (k0 : Fin N), Xa.L = L ∧ Xa.Fp = F ∧ Xa.T = T ∧ Xa.c1 = 1 ∧
      (∀ a, Xa.w a = w (Fin.cast hN a)) ∧ Xa.i * (Xa.g0 / 2) = 1 ∧ (∀ x, Xa.et x * Xa.th1 x = w k0 x ^ 2) ∧
      GlobalTheory.Shares.Margins X Xa := by
  classical
  have hniso : ∀ ξ, ¬ X.IsIso ξ := GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite X (Or.inl hp)
  have hsec : ∀ k, X.IsSec L (w k) := fun k => (hw k).1.1.1

  have hA2 : ∀ τ (a b : Fin r), a ≤ b →
      (F - kapW X - nd X • L) τ b - 2 * L τ b ≤ (F - kapW X - nd X • L) τ a - 2 * L τ a := fun τ =>
    antitone_of_succ_le_torus_haar_measure (fun i => (F - kapW X - nd X • L) τ i - 2 * L τ i) fun a b hab => by
      have := hgap τ a b hab; linarith
  have hLa : ∀ τ (a b : Fin r), a ≤ b → L τ b ≤ L τ a := by
    intro τ a b hab
    rcases hab.lt_or_eq with h | h
    · exact ((hL τ).2.1 a b (by omega) h).le
    · rw [h]
  have hA : ∀ τ (a b : Fin r), a ≤ b → (F - kapW X - nd X • L) τ b ≤ (F - kapW X - nd X • L) τ a := by
    intro τ a b hab
    have h1 := hA2 τ a b hab
    have h2 := hLa τ a b hab
    linarith
  obtain ⟨x1, hx1, hth2⟩ := h20
  obtain ⟨k0, hk0⟩ := hw0 x1 hx1
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_firstMinimum_definiteForm X hr hp
  obtain ⟨cw, hcw, hcwle⟩ := exists_le_sum_sq X hp L w hsec hw0
  have hTpos : (0 : ℝ) < T := by
    have : 44 ≤ T := by nlinarith
    exact_mod_cast (show 0 < T by omega)

  have hsq : (fun x => w k0 x ^ 2) ∈ X.SSgt (2 • L - 0) 0 := by
    have hs : X.IsSec (2 • L - 0) (fun x => w k0 x ^ 2) := by
      have := ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership.sec_mul X (hsec k0) (hsec k0)
      have e1 : (2 • L - 0 : Wt X.Ψ r) = L + L := by rw [sub_zero, two_nsmul]
      have e2 : (fun x => w k0 x ^ 2) = w k0 * w k0 := by funext x; simp [sq]
      rw [e1, e2]; exact this
    obtain ⟨C0, hC0⟩ := (hw k0).1.1.2
    have hpn : ∀ x ∈ X.dom, X.pnorm (2 • L - 0) (fun x => w k0 x ^ 2) x = X.pnorm L (w k0) x ^ 2 := by
      intro x hx
      have h1 := ReciprocityTheory.ChartRestriction.G.AR.Up.UpDivD.pnorm_sq X hx (2 • L - 0) (fun x => w k0 x ^ 2)
      have h2 := ReciprocityTheory.ChartRestriction.G.AR.Up.UpDivD.pnorm_sq X hx L (w k0)
      have h3 : phla X (2 • L - 0) x = 2 * phla X L x := by
        rw [sub_zero, ReciprocityTheory.ChartRestriction.G.AR.Up.UpDivD.phla_nsmul X hx 2 L]; norm_num
      rw [← pow_left_inj₀ (GlobalTheory.FrameThetaCompare.pnorm_nonneg X _ _ x)
        (pow_nonneg (GlobalTheory.FrameThetaCompare.pnorm_nonneg X _ _ x) 2) two_ne_zero, h1, ← pow_mul,
        show 2 * 2 = 2 * 2 from rfl, pow_mul, h2, h3, norm_pow]
      rw [show -(2 * phla X L x) = -phla X L x + -phla X L x by ring, Real.exp_add]
      ring
    have hbdd : X.IsBddSec (2 • L - 0) (fun x => w k0 x ^ 2) := by
      refine ⟨hs, C0 ^ 2, fun x hx => ?_⟩
      rw [hpn x hx]
      exact pow_le_pow_left₀ (GlobalTheory.FrameThetaCompare.pnorm_nonneg X _ _ x) (hC0 x hx) 2
    exact ⟨⟨hbdd, fun ξ hξ => absurd hξ (hniso ξ)⟩, fun ξ hξ => absurd hξ (hniso ξ)⟩
  have hSD2 : IsStrictDom X (2 • L - 0) := by
    intro τ
    refine ⟨fun i j hij hj => ?_, fun i j hi hij => ?_, fun i j hi hj => ?_⟩
    · exact absurd hj (by omega)
    · have := (hL τ).2.1 i j hi hij
      have e : ∀ k, (2 • L - 0 : Wt X.Ψ r) τ k = 2 * L τ k := fun k => by simp [two_mul]
      rw [e, e]
      linarith
    · exact absurd hi (by omega)
  let Xa : ArchInM X :=
    { L := L, de := 0, Fp := F, T := T, i := 1, g0 := 2, N := N, c := 1 / (2 * T), c1 := 1, a1 := 1, rr := 0
      n_ge := hn
      T_ge := hT
      i_pos := le_rfl
      genus_pos := by norm_num
      c_pos := by positivity
      frame_theta_const_pos := one_pos
      frame_theta_weight_pos := one_pos
      rr_nonneg := le_rfl
      Tcg0 := by
        rw [le_iff_eq_or_lt]; left
        field_simp
        try norm_num
      rr_le := by simp
      w := w
      w_van := hw
      w_nz := hw0
      ph := fun _ => 0
      ph_inv := fun _ _ _ _ _ _ => rfl
      ph_nonneg := fun _ _ => le_rfl
      p1 := ⟨1, ε, one_pos, hε, fun x hx hlt => absurd (hle x hx) (not_le.mpr hlt)⟩
      p2 := fun x _ => by simp; positivity
      p3 := ⟨1 / cw, fun x hx => by
        have h1 : (1 : ℝ) ≤ 1 / cw * ∑ k, X.pnorm L (w k) x ^ 2 := by
          rw [one_div, inv_mul_eq_div, le_div_iff₀ hcw, one_mul]
          exact hcwle x hx
        simpa using h1⟩
      et := fun _ => 1
      genus_even := even_two
      et_sec := by simpa using GlobalTheory.BigTrdeg.isSec_one X
      et_ne := ⟨x1, hx1, one_ne_zero⟩
      p4 := ⟨1, fun x _ => by simp [Data.pnorm]⟩
      th1 := fun x => w k0 x ^ 2
      firstTheta_vanishes := hsq
      firstTheta_ne_zero := ⟨x1, hx1, pow_ne_zero 2 hk0⟩
      th2 := th2
      secondTheta_vanishes := h2
      secondTheta_ne_zero := ⟨x1, hx1, hth2⟩
      thp := thp
      thp_van := h3
      thp_ne := h30
      ps0 := fun _ => 0
      potential_invariant := fun _ _ _ _ _ _ => rfl
      potential_smooth := fun _ _ => contDiffOn_const
      base_psi_levi_lower_bound := fun x0 _ z _ ξ => by
        have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.RgC.leviV_const (n := nd X) (0 : ℝ) z ξ
        rw [Complex.ofReal_zero] at h0
        simp [leviM, h0]
      base_psi_weighted_cf := ⟨⟨0, 0, fun x _ => by simp⟩, fun η _ _ =>
        ⟨0, 0, fun x _ ξ hξ _ => absurd hξ (hniso ξ)⟩⟩
      posL := fun x0 hx0 z hz ξ hξ => leviM_pos_of_isStrictDom X hp L hL x0 hx0 z hz ξ hξ
      posLde := fun x0 hx0 z hz ξ hξ => leviM_pos_of_isStrictDom X hp _ hSD2 x0 hx0 z hz ξ hξ
      posF := ⟨1, one_pos, fun t _ _ x0 _ z hz ξ => by
        obtain ⟨D, -, hl⟩ := exists_injective_leviM_eq_sum_weight_sq X hp x0 z hz
        simp only [mul_zero, zero_div, zero_mul, sub_zero, mul_one]
        rw [hl, hl, Finset.mul_sum]
        refine Finset.sum_le_sum fun e _ => ?_
        have h := hA2 e.1 e.2.1.2 e.2.1.1 e.2.2.le
        have h' : (2 : ℝ) * ((L e.1 e.2.1.2 : ℝ) - (L e.1 e.2.1.1 : ℝ)) ≤
            ((F - kapW X - nd X • L) e.1 e.2.1.2 : ℝ) - ((F - kapW X - nd X • L) e.1 e.2.1.1 : ℝ) := by
          have : ((2 * (L e.1 e.2.1.2 - L e.1 e.2.1.1) : ℤ) : ℝ) ≤
              (((F - kapW X - nd X • L) e.1 e.2.1.2 - (F - kapW X - nd X • L) e.1 e.2.1.1 : ℤ) : ℝ) := by
            exact_mod_cast (by linarith)
          push_cast at this; linarith
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right h' (by positivity)⟩ }
  refine ⟨Xa, rfl, k0, rfl, rfl, rfl, rfl, fun a => rfl, by norm_num [Xa], fun x => one_mul _, ?_⟩
  exact GlobalTheory.T.curvature_margins_definite_case E r X Xa hp hΨ (fun _ => rfl) hL hA

end Model

open ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.ArchInputs in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem archAt_nonempty_of_definite : ∀ (D : D7) (T : Top D) (h : LawsP T) (EX : ErrX D) (p : ℕ) (hj : InR D D.R.m) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D D.R.m) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p D.R.m → PageOK large₂ (recPJ h D.R.m hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h D.R.m hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ (N : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp D.R.m wL), NoCommonZero (T.Q.Xo D.R.m) T.Q.c (fun i => (w i).1) → Nonempty (GlobalTheory.Shares.ArchAt h D.R.m w wF Tn 1) := by
  intro D T h EX p hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hPar hPg hC N w hNZ
  classical
  have hG : GenFrEx (T.Q.Xo D.R.m) T.Q.c :=
    (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo D.R.m) T.Q.c).1
  obtain ⟨⟨g0, hg0, -⟩, hnz⟩ :=
    GlobalTheory.T.exists_cuspForm_nonzero_everyComponent D T h D.R.m hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hG hPg
  obtain ⟨-, -, -, -, -, w2, hG2, th, -, hth, -⟩ :=
    ((Formalism.MainNotions.Gaps.FamilyHypotheses.hypC_iff large₂ _ H C2 A2 7 CT S ka wL wF Tn nP nW h0 nus).mp hC).2.2.2.2
  have hσ : GoodEmb T.Q.c T.σ₀ := Formalism.L2.Pj.Core.good_σ₀ T.toCore
  have hT11 : 11 * WeightFamilies.dimY D D.R.m ^ 2 ≤ Tn := by
    obtain ⟨-, hSet, -⟩ := hPg.hyp
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h11, -, -⟩ := hSet
    exact h11
  have hdim2 : 2 ≤ WeightFamilies.dimY D D.R.m := by
    have h1 := GlobalTheory.ArchInputs.two_mul_dimY (D := D) D.R.m hj
    have h2 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast GlobalTheory.ArchInputs.f_pos D
    have h3 : (8 : ℝ) ≤ D.R.r := by exact_mod_cast hPg.r8
    have h4 : (56 : ℝ) ≤ (D.R.r : ℝ) * ((D.R.r : ℝ) - 1) := by nlinarith
    have h5 := mul_le_mul h2 h4 (by norm_num) (by linarith)
    have : (2 : ℝ) ≤ WeightFamilies.dimY D D.R.m := by linarith
    exact_mod_cast this
  have hr : 0 < D.R.r := by have := hPg.r8; omega
  have key : ∀ k : (T.U D.R.m T.σ₀).Comp, ∃ (Xa : ArchInM ((T.U D.R.m T.σ₀).X k)) (hN : Xa.N = N) (k0 : Fin N),
      Xa.L = laR T D.R.m wL k ∧ Xa.Fp = laR T D.R.m wF k ∧ Xa.T = Tn ∧ Xa.c1 = 1 ∧
      (∀ a, Xa.w a = rdR h D.R.m (w (Fin.cast hN a)) k) ∧ Xa.i * (Xa.g0 / 2) = 1 ∧
      (∀ x, Xa.et x * Xa.th1 x = rdR h D.R.m (w k0) k x ^ 2) ∧ Margins ((T.U D.R.m T.σ₀).X k) Xa := by
    intro k
    obtain ⟨hadd, hsm, -, -, hnd, -⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h D.R.m hj k
    obtain ⟨hp0, hSD, hgap⟩ :=
      GlobalTheory.T.runWeight_dominant_and_gaps_definiteCase D T h D.R.m hj large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0 hPg.hyp rfl hPg.r8 k
    have hw2 : laR T D.R.m w2 k =
        (nd ((T.U D.R.m T.σ₀).X k) + 4) • laR T D.R.m wL k - laR T D.R.m wF k := by
      have heq : wadd w2 wF = wsmul (WeightFamilies.dimY D D.R.m + 4) wL :=
        GlobalTheory.ArchInputs.wt_ext (j := D.R.m) (funext fun τ => funext fun i => hG2.2.1 τ i)
          (funext fun τ => funext fun i => hG2.2.2 τ i) hG2.1
      have e := hadd w2 wF
      rw [heq, hsm] at e
      rw [hnd]
      exact eq_sub_of_add_eq e.symm
    have hgap' : ∀ (τ : ((T.U D.R.m T.σ₀).X k).Ψ) (a b : Fin D.R.r), (b : ℕ) = a + 1 →
        (laR T D.R.m wF k - kapW ((T.U D.R.m T.σ₀).X k) - nd ((T.U D.R.m T.σ₀).X k) • laR T D.R.m wL k : ReciprocityTheory.ChartRestriction.G.FD.Wt ((T.U D.R.m T.σ₀).X k).Ψ D.R.r) τ b +
            2 * (laR T D.R.m wL k τ a - laR T D.R.m wL k τ b) ≤
          (laR T D.R.m wF k - kapW ((T.U D.R.m T.σ₀).X k) - nd ((T.U D.R.m T.σ₀).X k) • laR T D.R.m wL k : ReciprocityTheory.ChartRestriction.G.FD.Wt ((T.U D.R.m T.σ₀).X k).Ψ D.R.r) τ a := by
      rw [hnd]; exact hgap
    obtain ⟨x2, hx2, h2ne⟩ := (hnz w2 th hth).2 T.σ₀ hσ k
    obtain ⟨x3, hx3, h3ne⟩ := (hnz wF g0 hg0).2 T.σ₀ hσ k
    exact exists_archInM _ hr hp0 (GlobalTheory.PoincareSeriesCompare.nonempty_type _) _ _ Tn N
      (by rw [hnd]; exact hdim2) (by rw [hnd]; exact hT11) hSD hgap'
      (fun i => rdR h D.R.m (w i) k) (fun i => GlobalTheory.Shares.spanMem_rdR h D.R.m hj wL (w i) k)
      (GlobalTheory.BigTrdeg.exists_rdU_ne_zero (T.U D.R.m T.σ₀) k hNZ)
      (rdR h D.R.m th k) (hw2 ▸ GlobalTheory.Shares.spanMem_rdR h D.R.m hj w2 th k) ⟨x2, hx2, h2ne⟩
      (rdR h D.R.m g0 k) (GlobalTheory.Shares.spanMem_rdR h D.R.m hj wF g0 k) ⟨x3, hx3, h3ne⟩
  choose Xa hN k0 hL hF hTn hc hw hi het hmar using key
  refine ⟨⟨Xa, fun k => (GlobalTheory.Shares.WtDic.weights_dictionary D T h D.R.m hj k).2.2.2.2.1,
    hN, hL, hF, hTn, hc, hw, fun k => ?_, hmar⟩⟩
  have hnd := (GlobalTheory.Shares.WtDic.weights_dictionary D T h D.R.m hj k).2.2.2.2.1
  refine ⟨fun jj => ?_, fun jj => ?_⟩
  · exact GlobalTheory.ArchInputs.homRel_of_cusp h D.R.m hj wL (by rw [hnd])
      (fun a => (w (Fin.cast (hN k) (jj a))).1)
      (fun a => (Formalism.L2.Pj.esec_mem_C h hj).mp (w (Fin.cast (hN k) (jj a))).2) k _
      (fun a x => by rw [hw k]; rfl)
  · rw [hi k]
    refine GlobalTheory.ArchInputs.homRel_of_cusp h D.R.m hj (wsmul 2 wL) (by rw [hnd])
      (Fin.cons ((w (k0 k)).1 ^ 2) fun a => (w (Fin.cast (hN k) (jj a))).1 ^ 2)
      (fun a => Fin.cases (GlobalTheory.ArchInputs.pow_mem_cusp h D.R.m hj wL ((Formalism.L2.Pj.esec_mem_C h hj).mp (w (k0 k)).2) (by norm_num))
        (fun b => GlobalTheory.ArchInputs.pow_mem_cusp h D.R.m hj wL
          ((Formalism.L2.Pj.esec_mem_C h hj).mp (w (Fin.cast (hN k) (jj b))).2) (by norm_num)) a) k _ ?_
    intro a x
    refine Fin.cases ?_ (fun b => ?_) a
    · simp only [Fin.cons_zero]; rw [pow_one, het k, map_pow]; rfl
    · simp only [Fin.cons_succ]; rw [hw k, map_pow]; rfl

end GlobalTheory.ArchDefinite
