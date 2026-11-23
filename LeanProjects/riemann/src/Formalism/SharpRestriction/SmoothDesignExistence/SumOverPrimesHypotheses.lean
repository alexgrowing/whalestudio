import Formalism.SharpRestriction.SmoothDesignExistence.ProvedFamilyStatementClosed
import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSab
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.OrbitAdmissibleOfSplitBound
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.GrowthBounds.JointsTw
import Formalism.SharpRestriction.Divisibility.ChainOperators.GenericFramesLetters
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.UniformBoundAllData
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LogbAddOneNonneg
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LocalBoundElevenComparison
import Formalism.SharpRestriction.Divisibility.ChainOperators.OrbitEntryBounds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SzConstantTerm
import Formalism.PeriodIntegrals.SzCt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SzEatI
import Formalism.PeriodIntegrals.SzEatI
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverP
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.SixteenLeMulOfStdOfHypOfHyp0
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

section Sz

open Formalism.MainNotions.G

theorem szCt_fam {eps : ℝ} (Fm : FamP eps) : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ u : (Fm.D x i).what₂.Word, ∑ t : HH (Fm.D x i), ctD (Fm.D x i) u j t ≤
      2 * ((Fm.D x i).host.TT.card : ℝ) * (Fm.L x i).sc.b + 2 * ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.k * (Fm.L x i).sc.b' := by
  obtain ⟨x0, hx0⟩ := sz_constant_term eps Fm.Ct Fm.CGam Fm.Cc Fm.CT2 Fm.PK
  refine ⟨x0, fun x hx hx1 i => hx0 (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i)
    ⟨Fm.L_eps x i, Fm.Ct_eq x i, Fm.CGam_eq x i, Fm.Cc_eq x i, Fm.secondConstant_eq x i, Fm.params_K x hx1 i⟩
    (by rw [Fm.L_x x i hx1]; exact hx) (Fm.sizes x hx1 i)⟩

theorem szEatI_fam {eps : ℝ} (Fm : FamP eps) : ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ (IsResidueClassZero (Fm.D x i) p ∨ IsSg (Fm.D x i) p) ∧ ¬ (IsResidueClassZero (Fm.D x i) p ∧ hP (Fm.D x i) p = 0) ∧
        (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) →
      ∑ p ∈ S, Real.log p * (EatI (Fm.L x i) Fm.GK Fm.cX.err j p - max 0 (WeilJacquetShalikaLaw.FkindA (Fm.D x i) j p)) ≤
        C * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n) := by
  obtain ⟨C, hC, x0, hx0⟩ := sz_eat_identity Fm.GK Fm.cX.err eps Fm.Ct Fm.CGam Fm.Cc Fm.CT2 Fm.PK
  refine ⟨C, hC, x0, fun x hx hx1 i => hx0 (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i)
    ⟨Fm.L_eps x i, Fm.Ct_eq x i, Fm.CGam_eq x i, Fm.Cc_eq x i, Fm.secondConstant_eq x i, Fm.params_K x hx1 i⟩
    (by rw [Fm.L_x x i hx1]; exact hx) (Fm.sizes x hx1 i)⟩

theorem one_le_Xpp {D : D7} (L : SizeData₂ D) (h : SizesAt L) (hm : 1 ≤ D.R.m) : 1 ≤ L.sc.X'' D.R.n := by
  obtain ⟨τ⟩ := S.Inh.tau_index_set_nonempty D
  have hX : SizeXpp L := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw : L.sc.w'' D.R.n ≤ wj D 1 τ := S.wj_ge L τ 1 le_rfl hm
  have hpos : 0 < wj D 1 τ := lt_of_lt_of_le (S.w''_pos L) hw
  have hr := hX 1 τ 1 τ le_rfl hm le_rfl hm
  nlinarith

theorem admissible_size_family {eps : ℝ} (Fm : FamP eps) (hD : DGamSize Fm) : ∃ C : ℝ, 0 ≤ C ∧ ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), WeilJacquetShalikaLaw.TypePrimeSizeConds (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err C := by
  obtain ⟨xz, hz⟩ := szCt_fam Fm
  obtain ⟨Ce, hCe, xe, he⟩ := szEatI_fam Fm
  obtain ⟨Cd, xd, hd⟩ := hD
  refine ⟨max Ce (max Cd 0), le_trans (le_max_right _ _) (le_max_right _ _), max xz (max xe xd), fun x hx h1 i => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨ez, ee, ed⟩ := hx
  refine ⟨hz x ez h1 i, J.factDGam_mono (hd x ed i) (le_trans (le_max_left _ _) (le_max_right _ _)), fun j hj S hS => ?_⟩
  have hm : 1 ≤ (Fm.D x i).R.m := by
    simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
    omega
  have hlog : 0 ≤ Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n) := Real.log_nonneg (one_le_Xpp (Fm.L x i) (Fm.sizes x h1 i) hm)
  have hb : 0 < (Fm.L x i).sc.b := by unfold Scale.b; positivity
  have hf : (0 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) := Nat.cast_nonneg _
  have hnn : 0 ≤ ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n) :=
    mul_nonneg (mul_nonneg hf hb.le) hlog
  refine (he x ee h1 i j hj S hS).trans ?_
  calc Ce * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n)
      = Ce * (((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n)) := by ring
    _ ≤ max Ce (max Cd 0) * (((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
    _ = max Ce (max Cd 0) * ((Fm.D x i).R.f : ℝ) * (Fm.L x i).sc.b * Real.log ((Fm.L x i).sc.X'' (Fm.D x i).R.n) := by ring

end Sz

section Re

open Formalism.MainNotions.G

def reY {D : D7} (Y : LatInst D)
    (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Y.Fl u w hg), Chain Lv) : LatInst D where
  vOf := Y.vOf
  Fl := Y.Fl
  Lv := fun u w hg => (LC (D.what₂.muAt w) u w hg).1
  Ch := fun u w hg => (LC (D.what₂.muAt w) u w hg).2
  Vram := Y.Vram

def reW {D : D7} (Y : LatInst D) (LC : _) : WeilJacquetShalikaLaw.TwLoc D (reY Y LC) := ⟨LC, fun _ _ _ => rfl⟩

theorem serv_re {D : D7} {L : SizeData₂ D} {X : Inst D L} {Y : LatInst D} {K : Consts} {c : LatCmp D} {Dx : DivX D}
    {T : TwForms D} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C : ℝ} (LC : _)
    (h : WeilJacquetShalikaLaw.Serv D L X (reY Y LC) K c Dx T lev Xe ce C) : WeilJacquetShalikaLaw.Serv D L X Y K c Dx T lev Xe ce C := by
  unfold WeilJacquetShalikaLaw.Serv at h ⊢
  refine ⟨h.1, ?_, h.2.2⟩
  have h2 := h.2.1
  unfold WeilJacquetShalikaLaw.Conclusion1 at h2 ⊢
  intro hT
  have hT' : WeilJacquetShalikaLaw.Ties9 D L X (reY Y LC) c := { hT with }
  exact h2 hT'

theorem num_re {D : D7} {L : SizeData₂ D} {X : Inst D L} {Y : LatInst D} {K : Consts} (LC : _)
    (h : FormalGroupSystem.SmallResidueCharComparison D L X Y K) : FormalGroupSystem.SmallResidueCharComparison D L X (reY Y LC) K := h

end Re

open Classical in

def SysTw (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (K : G.Consts) (Dx : DivX D) {Y : G.LatInst D} (W : WeilJacquetShalikaLaw.TwLoc D Y)
    (lev : LevelData D) (Xe : ErrX D) (ce : ErrC) (sp : ℝ) : Prop :=
  ErrDefs D L Xe lev K ce → ∀ μ, DV.Used D μ → ∀ (hT : GatTies D), G.LatTied hT X (W.Yt μ) →
    ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w ∉ Dx.Qp μ →
    ∃ (_ : Fact (D.what₂.places.resChar w).Prime) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _)
      (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) ((W.Yt μ).Fl u w hg)
        ((W.Yt μ).Lv u w hg) ((W.Yt μ).Ch u w hg) std vp unif eO eO_spec dG dG_spec om)),
      FormalGroupSystem.admitted D _ Y5 ∧
      ∃ Fn : Fin (D.gat u w hg).P.nV → ℕ → ℝ,
        (∀ v, v ∉ (G.reps X (D.what₂.places.resChar w)).image ((W.Yt μ).vOf u w hg) → ∀ j < D.R.m,
          Y5.LowAt j v (Fn v (j + 1))) ∧
        WeilJacquetShalikaLaw.lowS L Xe K ce sp u w ≤ (∑ j ∈ Finset.Icc 1 D.R.m,
          ∑ v ∈ Finset.univ \ (G.reps X (D.what₂.places.resChar w)).image ((W.Yt μ).vOf u w hg), Fn v j) -
            ∑ j ∈ Finset.range D.R.m, (dG j : ℝ)

structure SumOverPrimesHypotheses (𝒞 : FamClass) : Prop where

  twU : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (reW (Fm.Gy x i) LC) ∧ SysTw (Fm.D x i) (Fm.L x i)
      (Fm.Gx x i) Fm.GK (Fm.X x i) (reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1

  pdv : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ E : KerEnt (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw,
      (E.UnUnit ∧ OrbitPlaces.KmapRat E ∧ OrbitPlaces.KFi (Fm.D x i) (Fm.ex x hx i).tw ∧ OrbitPlaces.Stab0 (Fm.D x i)) ∧
      ∃ (ep : _) (be : _) (sg : _),
        OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) ∧
        OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) ∧
        OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.Gx x i) Fm.GK ∧
        OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) ∧
        OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) ∧
        OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg)

theorem typeG_ne_d {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (k : Fin 2) : D.host.g k ≠ D.host.d := by
  have hs := P.level_split _ (D.host.g_level k)
  intro h
  rw [h] at hs
  simp only [Host.cls, primeClass] at hs
  split_ifs at hs

theorem closed_large_pos {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (K0 : TransportedAlt) (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 0 < eps → Fm.Large K0 CH → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  unfold Closed at hP ⊢
  obtain ⟨ε1, hε1, hP⟩ := hP
  refine ⟨ε1, hε1, fun eps he he1 => ?_⟩
  obtain ⟨K, hK⟩ := hP eps he he1
  refine ⟨⟨max K.pre K0.pre, fun l => max (K.t l) (K0.t l), fun l => max (K.mid l) (K0.mid l),
    fun l => max (K.last l) (K0.last l)⟩, fun Fm CH hC hL => ?_⟩
  unfold Formalism.MainNotions.FamP.Large at hL
  obtain ⟨h1, -, h3, h4⟩ := hL
  have hLK : Fm.Large K CH := by
    unfold Formalism.MainNotions.FamP.Large
    exact ⟨fun c hc => (le_max_left _ _).trans (h1 c hc), trivial,
      fun c hc => (le_max_left _ _).trans (h3 c hc), fun c hc => (le_max_left _ _).trans (h4 c hc)⟩
  have hLK0 : Fm.Large K0 CH := by
    unfold Formalism.MainNotions.FamP.Large
    exact ⟨fun c hc => (le_max_right _ _).trans (h1 c hc), trivial,
      fun c hc => (le_max_right _ _).trans (h3 c hc), fun c hc => (le_max_right _ _).trans (h4 c hc)⟩
  exact h Fm CH he hLK0 (hK Fm CH hC hLK)

theorem three_le_split {eps : ℝ} (Fm : FamP eps) (h0 : 0 < eps) {x : ℝ} (hx : (3 : ℝ) ^ (5 / Fm.ez) ≤ x) (h1 : Fm.x1 < x)
    (i : Fm.Ix x) : 3 ≤ (Fm.D x i).host.splitBound := by
  have hez : 0 < Fm.ez := by rw [← Fm.L_ez x i]; exact (Fm.L x i).sc.ez_pos
  have hL := (Fm.L x i).split_tie
  rw [Fm.L_x x i h1, Fm.L_ez x i] at hL
  refine le_trans (Nat.le_floor ?_) hL
  have he : 5 / Fm.ez * (Fm.ez / 5) = 1 := by field_simp
  calc ((3 : ℕ) : ℝ) = ((3 : ℝ) ^ (5 / Fm.ez)) ^ (Fm.ez / 5) := by
        rw [← Real.rpow_mul (by norm_num), he, Real.rpow_one]; norm_num
    _ ≤ x ^ (Fm.ez / 5) := Real.rpow_le_rpow (by positivity) hx (by positivity)

theorem sum_over_primes_service (𝒞 : FamClass) (hD : Closed 𝒞 fun Fm _ => DGamSize Fm) (h : SumOverPrimesHypotheses 𝒞) :
    Closed 𝒞 fun Fm _ => WeilJacquetShalikaLaw.ServF Fm := by
  have hpdv := h.pdv
  have h01 : OrbitPlaces.OrbitLetterBoundsAll 11 1 := DIV.Bridge.DworkPowerSeriesWeights.split_bound_eleven_one
  refine closed_large_pos ⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩
    (hD.and (h.twU.and (hpdv.and (G.num_closed 𝒞 FormalGroupSystem.Pf.stmtNumE))))
    fun {eps} Fm CH hpos hL ⟨hDg, ⟨xb, hb⟩, ⟨xc, hc⟩, ⟨xn, hnum⟩⟩ => ?_
  have hpr1 : 1 ≤ Fm.GK.Pr1 := le_of_eq Fm.fixed.1.symm
  have hCL : OrbitPlaces.CLarge 11 1 Fm.GK Fm.cX.err :=
    OrbitPlaces.cLarge_of_fixed Fm.fixed.2.2.2.2.1 Fm.fixed.2.2.2.2.2.1 Fm.fixed.2.1 (by rw [Fm.fixed.2.2.1]; norm_num)
  obtain ⟨Cs, hCs, xa, ha⟩ := admissible_size_family Fm hDg
  refine ⟨Cs, hCs, max (max xa xb) (max (max xc ((3 : ℝ) ^ (5 / Fm.ez))) xn), fun x hx h1 i => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨ea, eb⟩, ⟨ec, ef⟩, en⟩ := hx
  obtain ⟨LC, hV, hSys⟩ := hb x eb h1 i
  have hU := G.Joints.unit_bound_of_sum_over_primes _ _ _ _ _ _ (reW (Fm.Gy x i) LC) _ _ _ 1 (FormalGroupSystem.Pf.stmt_proved _) hSys
    (num_re LC (hnum x en i))
    (G.TopChoiceBounds.hLarge_proved _ _ Fm.GK_nonneg hpr1 (Fm.params x h1 i))
  obtain ⟨E, ⟨hUn, hR, hKF, hS0⟩, ep, be, sg, b0, b0c, a', ei, sd, sh⟩ := hc x ec h1 i
  have gd : OrbitPlaces.TypePrimeNotDiscriminant (Fm.D x i) := fun k => typeG_ne_d (Fm.params x h1 i) k
  have o := DIV.Inh.orbit_admissible_of_split_bound (Fm.D x i) (three_le_split Fm hpos ef h1 i)
  have hW : OrbitPlaces.SB E := fun _ _ _ _ _ _ B hB => (DIV.Lemmas.theta_isometry_facts_hold (Fm.D x i) _ _ _ _ _ B).1 hB
  have hK : OrbitPlaces.KForm (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) (Fm.X x i) (Fm.ex x h1 i).tw 1 :=
    OrbitPlaces.kform_of_ker E _ (fun _ _ => rfl) rfl hW hUn hR hKF
      (Or.inr ⟨rfl, hS0⟩)
  have hA : OrbitPlaces.admitted (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK (Fm.X x i) (Fm.ex x h1 i).tw
      (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) E ep be sg) Fm.cX.err 1 11 1 :=
    ⟨hK, o, gd, b0, b0c, h01, a', ei, sd, sh, hCL⟩
  obtain ⟨n, c, d, it⟩ := J.four_orbit_conditions_of_proof (lev := (Fm.ex x h1 i).lev) (Xe := (Fm.ex x h1 i).errX)
    (OrbitPlaces.lift_bounds_of_essential hA (DIV.Lemmas.OrbitEntryBounds.orbit_entry_bounds_hold _ _ _ _ _ _ _ 11 1 h01 sd sh hCL))
  have hAdm : WeilJacquetShalikaLaw.admitted (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (reY (Fm.Gy x i) LC) Fm.GK (Fm.X x i) (Fm.ex x h1 i).tw
      (reW (Fm.Gy x i) LC) (Fm.ex x h1 i).lev (Fm.ex x h1 i).errX Fm.cX.err 1 :=
    ⟨hU, WeilJacquetShalikaLaw.local_theorem_of_statement _ (FormalGroupSystem.Pf.stmtAt_proved _), it, n, c, d⟩
  exact serv_re LC (WeilJacquetShalikaLaw.serv_of (WeilJacquetShalikaLaw.Proof.stmt_proved _ _ _ _ _ _ _) (reW (Fm.Gy x i) LC) hV hAdm
    (ha x ea h1 i))

end Formalism.MainNotions.Pk

end
