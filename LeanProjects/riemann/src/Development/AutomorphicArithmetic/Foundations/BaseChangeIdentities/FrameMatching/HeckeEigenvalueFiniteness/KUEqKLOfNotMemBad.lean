import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.PowEigAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.CompFixSAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVectorGivesLocalComponentSphericalVectStatement

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.FX
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

def GcHecke : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
  ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (c : (Fin n → ℤ) →₀ ℂ), IsHecke (iwU n w b) (gc w b ϖ c)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)}
  {S : Finset (Pl E)} (F₀ : Frame0 hR π S) (T' : Finset (Pl E)) (c : Pl E → (Fin n → ℤ) →₀ ℂ) (e : ∀ w : Pl E, GLw n w → ℂ)
  (b : ∀ w : Pl E, GLw n w)

theorem loc_KU_eq_iwU_of_mem {w : Pl E} (hw : w ∈ T') : (F₀.loc T' c e b).KU w = iwU n w (b w) := if_pos hw

theorem KU_off {w : Pl E} (hw : w ∉ T') : (F₀.loc T' c e b).KU w = F₀.d₀.KU w := by
  have h0 : w ∉ F₀.d₀.T := by rw [F₀.T₀]; exact Finset.notMem_empty w
  unfold LocData.KU
  rw [if_neg hw, if_neg h0]

theorem KU_eq_KL_of_not_mem_bad {w : Pl E} (h1 : w ∉ F₀.d₀.S₀) (h2 : w ∉ F₀.d₀.Bad) : F₀.d₀.KU w = KL n w := by
  have h0 : w ∉ F₀.d₀.T := by rw [F₀.T₀]; exact Finset.notMem_empty w
  unfold LocData.KU
  rw [if_neg h0, if_neg h1, if_neg h2]

theorem levOff (hT : ∀ w ∈ T', w ∈ F₀.Sec ∧ IsWitt n w (b w)) :
    U.LevelOff F₀.Sec (F₀.loc T' c e b).B (F₀.loc T' c e b).KU := by
  refine ⟨fun w hw => ?_, ⟨fun w => ?_, ?_⟩, fun w hw => ?_⟩
  · rcases Finset.mem_union.1 (Finset.mem_coe.1 hw) with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact (hT w h).1
      · exact (F₀.S₀ w h).1
    · exact (F₀.bad w h).1
  · by_cases hw : w ∈ T'
    · rw [loc_KU_eq_iwU_of_mem F₀ T' c e b hw]
      exact ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_iwU n w _, GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w _ (hT w hw).2.1, fun k hk => hk⟩
    · rw [KU_off F₀ T' c e b hw]
      exact F₀.levFam.1 w
  · filter_upwards [F₀.levFam.2, T'.finite_toSet.compl_mem_cofinite] with w h1 h2
    rw [KU_off F₀ T' c e b h2, h1]
  · have h1 : w ∉ T' := fun h => hw (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have h2 : w ∉ F₀.d₀.S₀ := fun h => hw (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have h3 : w ∉ F₀.d₀.Bad := fun h => hw (Finset.mem_union_right _ h)
    rw [KU_off F₀ T' c e b h1, KU_eq_KL_of_not_mem_bad F₀ h2 h3]

theorem hasLevel (hT : ∀ w ∈ T', IsWitt n w (b w) ∧ w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad) :
    HasLevel F₀.Sec π (F₀.loc T' c e b).KU := by
  refine F₀.level _ fun w => ?_
  by_cases hw : w ∈ T'
  · rw [loc_KU_eq_iwU_of_mem F₀ T' c e b hw, KU_eq_KL_of_not_mem_bad F₀ (hT w hw).2.1 (hT w hw).2.2]
    exact GlobalTheory.CompanionTheory.IwLevels.iwU_le_KL n w _ (hT w hw).1.1
  · rw [KU_off F₀ T' c e b hw]

theorem loc_ok (hT : ∀ w ∈ T', w ∉ F₀.d₀.S₀ ∧ w ∉ F₀.d₀.Bad)
    (hc : ∀ w ∈ T', (↑(c w).support : Set (Fin n → ℤ)) ⊆ coneGL n 2) (he : ∀ w ∈ F₀.d₀.S₀, IsHk (F₀.d₀.K' w) (e w)) :
    (F₀.loc T' c e b).Ok :=
  ⟨⟨Finset.disjoint_left.2 fun w hw => (hT w hw).1, Finset.disjoint_left.2 fun w hw => (hT w hw).2, F₀.ok₀.disj.2.2⟩,
    F₀.ok₀.unif, hc, fun w hw => ⟨(F₀.ok₀.K' w hw).1, (F₀.ok₀.K' w hw).2.1, (F₀.ok₀.K' w hw).2.2.1, (F₀.ok₀.K' w hw).2.2.2.1,
      (F₀.ok₀.K' w hw).2.2.2.2.1, he w hw⟩, F₀.ok₀.L, F₀.ok₀.LS, F₀.ok₀.fix⟩

theorem loc_mok (hCone : ConeTwo) (h0 : MLM.MOk F₀.d₀) (hT : ∀ w ∈ T', ¬ IsSplitAt w ∧ IsWitt n w (b w))
    (hc : ∀ w ∈ T', (↑(c w).support : Set (Fin n → ℤ)) ⊆ coneGL n 2) : MLM.MOk (F₀.loc T' c e b) := by
  refine ⟨fun w hw => ⟨(hT w hw).1, (hT w hw).2, (F₀.unif w).1, fun x hx => ⟨fun i j hij => ?_, ?_⟩⟩, h0.S, h0.badS, h0.badI⟩
  · have := hc w hw hx i j hij
    omega
  · by_cases hn : 2 ≤ n
    · exact hCone n x hn (hc w hw hx)
    · exact ⟨fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega)⟩

theorem eig_B (hG : GcHecke) (hP : PowEig) (hA : LocAlg) (hdis : ∀ w ∈ T', ¬ IsSplitAt w ∧ w ∉ F₀.d₀.S₀)
    (hlev : ∀ w, GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) ((F₀.loc T' c e b).KU w))
    (σ : ∀ w : Pl E, SmIrr (UL n w)) (hne : ∀ w ∈ F₀.d₀.Bad, fixed (σ w).ρ ((F₀.loc T' c e b).KU w) ≠ ⊥)
    (hT : ∀ w ∈ T', ∃ y : fixed (σ w).ρ (iwU n w (b w)), y ≠ 0 ∧ locOp (σ w) (iwU n w (b w)) (gc w (b w) (F₀.d₀.ϖ w) (c w)) y = y)
    (hS : ∀ w ∈ F₀.d₀.S₀, IsHecke ((F₀.d₀.K' w).subgroupOf (UL n w)) (fun y => e w y.1) ∧
      ∃ y : fixed (σ w).ρ ((F₀.d₀.K' w).subgroupOf (UL n w)), y ≠ 0 ∧
        locOp (σ w) ((F₀.d₀.K' w).subgroupOf (UL n w)) (fun y => e w y.1) y = y) (m : ℕ) :
    ∀ w ∈ (F₀.loc T' c e b).B, ∃ y, y ≠ 0 ∧ locOp (σ w) ((F₀.loc T' c e b).KU w) ((F₀.loc T' c e b).gU m w) y = y := by
  intro w hw
  have key : ∀ (K' : Subgroup (UL n w)) (g : UL n w → ℂ), (F₀.loc T' c e b).KU w = K' → (F₀.loc T' c e b).g₀ w = g →
      IsHecke K' g → (∃ y : fixed (σ w).ρ K', y ≠ 0 ∧ locOp (σ w) K' g y = y) →
      ∃ y, y ≠ 0 ∧ locOp (σ w) ((F₀.loc T' c e b).KU w) ((F₀.loc T' c e b).gU m w) y = y := by
    rintro K' g rfl rfl hH ⟨y, hy0, hy⟩
    exact ⟨y, hy0, hP E n w (σ w) _ (hlev w) _ hH y hy m⟩
  by_cases h1 : w ∈ T'
  · exact key _ _ (if_pos h1) (if_pos h1) (hG E n w (hdis w h1).1 _ _ _) (hT w h1)
  by_cases h2 : w ∈ F₀.d₀.S₀
  · exact key _ _ ((if_neg h1).trans (if_pos h2)) ((if_neg h1).trans (if_pos h2)) (hS w h2).1 (hS w h2).2
  have h3 : w ∈ F₀.d₀.Bad := by
    rcases Finset.mem_union.1 hw with h | h
    · exact absurd (Finset.mem_union.1 h) (not_or.2 ⟨h1, h2⟩)
    · exact h
  have h0 : IsHecke ((F₀.loc T' c e b).KU w) (0 : UL n w → ℂ) := ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩
  have hL := (hA E n w (σ w) _ (hlev w) 0 0 h0 h0).2.2.2.2.2.2
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (hne w h3)
  refine key _ (U.lone ((F₀.loc T' c e b).KU w)) rfl ((if_neg h1).trans (if_neg h2)) hL.1
    ⟨⟨y, hy⟩, fun h => hy0 (congrArg Subtype.val h), ?_⟩
  exact (LinearMap.congr_fun hL.2 _).trans rfl

end UpperTheory.HeckeLevelFrameExistence

namespace UpperTheory.HeckeLevelFrameExistence

set_option maxHeartbeats 1000000 in
theorem frameEx_of (hUS : USide) (hSph : SphOne) (hSpec : SpecTrace) (hA : LocAlg) (hTb : ExTb) (hSat : Inert.SatEx)
    (hUnif : Inert.UnifOf) (hCE : ConeEig) (hSC : SatCompAt) (hCI : CandIndep) (hCF : CandFin) (hM0 : FrameBoundModuleCondition)
    (hCone : ConeTwo) (hG : GcHecke) (hC : LocC) (hLE : LocE) (hMu : MuVal) (hP : PowEig) : FrameEx := by
  intro hR E _ _ _ hE n hn π hπ S F₀ T
  obtain ⟨T', b, hne, hT', -, hTle⟩ := hTb hR E hE n hn π hπ S F₀ T
  have hL : ∀ c e, U.LevelOff F₀.Sec (F₀.loc T' c e b).B (F₀.loc T' c e b).KU := fun c e =>
    levOff F₀ T' c e b fun w hw => ⟨(hT' w hw).1, (hT' w hw).2.2.2.1⟩
  obtain ⟨fam⟩ := U.uFam_of hUS hE hn F₀.hSec F₀.lam (hL 0 0).2.1
  obtain ⟨i₀, hi₀⟩ := fam.all π hπ F₀.hlam
    (hasLevel F₀ T' 0 0 b fun w hw => ⟨(hT' w hw).2.2.2.1, (hT' w hw).2.2.2.2⟩)
  obtain ⟨hZ, hD, m₀, hm₀⟩ := hCF hR E hE n hn π hπ S F₀ T' 0 0 b fun w hw => ⟨(hT' w hw).2.1, (hT' w hw).2.2.2.2⟩
  choose Z hZf hZ using hZ

  have hT : ∀ w, ∃ cw : (Fin n → ℤ) →₀ ℂ, w ∈ T' → (↑cw.support : Set (Fin n → ℤ)) ⊆ coneGL n 2 ∧
      (∃ y : fixed (fam.σ i₀ w).ρ (iwU n w (b w)), y ≠ 0 ∧
        locOp (fam.σ i₀ w) (iwU n w (b w)) (gc w (b w) (F₀.d₀.ϖ w) cw) y = y) ∧
      ∀ i s (h : LocData.admitted n (F₀.C.a i) s) ξa ξb, (ξa, ξb) ∈ Z i w →
        (cw.sum fun x t => t * (-qh w) ^ (-vRes n (F₀.C.a i) (lOf x) s) * ev2 w ξa ξb (restr x _ h.2.1) (restr x _ h.2.2)) ≠ 0 →
        PositivityTheory.Rg.BcB.N3.Mono ξa ∧ PositivityTheory.Rg.BcB.N3.Mono ξb ∧ ∀ (ϖ : w.adicCompletion E) (q : ℕ), IsUnramInv ϖ (cj w) q →
          ∀ α, HasSatAt π w (cj w) ϖ q α →
            (Finset.univ.val.map ξa).map (· * (F₀.μ ^ (n - F₀.C.a i)).val w) +
              (Finset.univ.val.map ξb).map (· * (F₀.μ ^ F₀.C.a i).val w) = GlobalTheory.LGrp.bcParam n α := by
    intro w
    by_cases hw : w ∈ T'
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    obtain ⟨hsec, hs, hu, hb, -⟩ := hT' w hw
    obtain ⟨q', hq'⟩ := hUnif E hE w hs _ (F₀.unif w).1
    have hadm : IsAdmissible (fam.σ i₀ w).ρ :=
      ⟨(fam.σ i₀ w).smooth, fun K hK _ => ((fam.comp i₀).2.2.2 w hsec).2.2 K hK⟩
    obtain ⟨α', hα'⟩ := hSat E n w hs (b w) _ q' hb (F₀.unif w).1 hq' _ hadm (GlobalTheory.T.unramifiedVector_gives_localComponent_sphericalVector E hE n π hπ w _ (hi₀ w hsec) hu)
    obtain ⟨ξ, hξm, hξ, y, hy0, hy⟩ := hCE E n w hs (b w) _ q' _ α' hb (F₀.unif w).1 hq' hadm hα'
    obtain ⟨cw, h1, h2, h3⟩ := hC E n w F₀.C.ι F₀.C.a (fun i => Z i w) ξ F₀.C.le (fun i => hZf i w) hξm
    refine ⟨cw, fun _ => ⟨h1, ⟨y, hy0, by rw [hy cw h1, h2, one_smul]⟩, fun i s h ξa ξb hz h0 => ?_⟩⟩
    obtain ⟨a1, a2, a3⟩ := h3 i s h ξa ξb hz h0
    refine ⟨a1, a2, fun ϖ q hq α hα => ?_⟩
    have hϖ : ϖ ≠ 0 := by
      rintro rfl
      have := hq.2.2.2.1
      rw [map_zero] at this
      exact WithZero.coe_ne_zero this.symm
    rw [hMu E _ _ F₀.hμ w hs, hMu E _ _ F₀.hμ w hs, a3, hξ]
    exact (hSC E n π hπ w hs _ (b w) (Units.mk0 ϖ hϖ) _ q q' α α' (hi₀ w hsec) hb (F₀.unif w).1 hq hq' hα hα').symm
  choose c hc using hT

  have hS : ∀ w, ∃ (ew : GLw n w → ℂ) (mw : ℕ), w ∈ F₀.d₀.S₀ → IsHk (F₀.d₀.K' w) ew ∧
      (IsHecke ((F₀.d₀.K' w).subgroupOf (UL n w)) (fun y => ew y.1) ∧
        ∃ y : fixed (fam.σ i₀ w).ρ ((F₀.d₀.K' w).subgroupOf (UL n w)), y ≠ 0 ∧
          locOp (fam.σ i₀ w) ((F₀.d₀.K' w).subgroupOf (UL n w)) (fun y => ew y.1) y = y) ∧
      (∃ P : SmIrr (GLw n w), IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ ∧
        ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' 0 0 b) i s₁ s₂ Pa Pb D → ∀ τ : SmIrr (GLw n w),
          GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt D w) → IsEmpty (τ.ρ.Equiv P.ρ) →
            ∀ y ∈ fixed τ.ρ (F₀.d₀.K' w), hk τ.ρ (F₀.d₀.K' w) ew y = 0) ∧
      ∀ i s₁ s₂ Pa Pb D, F₀.Cand (F₀.loc T' 0 0 b) i s₁ s₂ Pa Pb D →
        Module.finrank ℂ ↥(fixed (prodAt D w) (F₀.d₀.K' w)) < mw := by
    intro w
    by_cases hw : w ∈ F₀.d₀.S₀
    swap
    · exact ⟨0, 0, fun h => absurd h hw⟩
    obtain ⟨k, Dl, hDl⟩ := hD w hw
    have hwT : w ∉ T' := fun h => (hT' w h).2.2.2.2.1 hw
    have hK : (F₀.loc T' 0 0 b).KU w = (F₀.d₀.K' w).subgroupOf (UL n w) := (if_neg hwT).trans (if_pos hw)
    have hfix := ((fam.comp i₀).2.2.2 w (F₀.S₀ w hw).1).2.1
    rw [hK] at hfix
    obtain ⟨ew, P, h1, h2, h3, h4, h5⟩ := hLE E n w (F₀.S₀ w hw).2 _ (F₀.ok₀.K' w hw).1 (F₀.ok₀.K' w hw).2.1 (F₀.K'_lev w hw)
      _ hfix k Dl
    refine ⟨ew, (Finset.univ.sup fun j => Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w))) + 1, fun _ =>
      ⟨h1, ⟨h2, h4⟩, ⟨P, h3 π (hi₀ w (F₀.S₀ w hw).1), fun i s₁ s₂ Pa Pb D hcand τ hτ => ?_⟩, fun i s₁ s₂ Pa Pb D hcand => ?_⟩⟩
    · obtain ⟨j, hj, -⟩ := hDl i s₁ s₂ Pa Pb D hcand
      exact h5 j τ ((hj τ).1 hτ)
    · obtain ⟨j, -, hj, -⟩ := hDl i s₁ s₂ Pa Pb D hcand
      rw [hj]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j => Module.finrank ℂ ↥(fixed (prodAt (Dl j) w) (F₀.d₀.K' w)))
        (Finset.mem_univ j))
  choose e mS he using hS
  have hcand : ∀ {i s₁ s₂ Pa Pb D}, F₀.Cand (F₀.loc T' c e b) i s₁ s₂ Pa Pb D → F₀.Cand (F₀.loc T' 0 0 b) i s₁ s₂ Pa Pb D :=
    fun h => (hCI hR E n π S F₀ T' c 0 e 0 b b _ _ _ _ _ _).1 h
  let m : ℕ := m₀ + F₀.d₀.S₀.sup mS + 1
  let fam' : U.UFam F₀.Sec F₀.lam (F₀.loc T' c e b).KU := fam
  obtain ⟨R⟩ := U.uMod_of hSph hSpec hE fam' (hL c e) ((F₀.loc T' c e b).gU m)
  obtain ⟨v, hv0, hv1, hv2⟩ := R.eig i₀ (eig_B F₀ T' c e b hG hP hA (fun w hw => ⟨(hT' w hw).2.1, (hT' w hw).2.2.2.2.1⟩)
    (hL c e).2.1.1 (fam.σ i₀) (fun w hw => ((fam.comp i₀).2.2.2 w (F₀.bad w hw).1).2.1) (fun w hw => (hc w hw).2.1)
    (fun w hw => (he w hw).2.1) m)
  exact ⟨{
    d := F₀.loc T' c e b
    same := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    m := m
    m_pos := Nat.succ_le_succ (Nat.zero_le _)
    ok := loc_ok F₀ T' c e b (fun w hw => (hT' w hw).2.2.2.2) (fun w hw => (hc w hw).1) fun w hw => (he w hw).1
    mok := loc_mok F₀ T' c e b hCone (hM0 hR E hE n hn π S F₀) (fun w hw => ⟨(hT' w hw).2.1, (hT' w hw).2.2.2.1⟩)
      fun w hw => (hc w hw).1
    T_ne := hne
    T_in := fun w hw => ⟨(hT' w hw).1, (hT' w hw).2.1, (hT' w hw).2.2.1, (hT' w hw).2.2.2.1⟩
    T_le := hTle
    levOff := hL c e
    fam := fam'
    R := R
    i₀ := i₀
    comp := hi₀
    v := v
    v_ne := hv0
    uv := hv1
    vblk := hv2
    choiceT := fun i s₁ s₂ Pa Pb D h w hw s ha ξa ξb hj h0 =>
      (hc w hw).2.2 i s ha ξa ξb (hZ i w s₁ s₂ Pa Pb D (hcand h) hw ξa ξb hj) h0
    choiceS := fun w hw => by
      obtain ⟨P, h1, h2⟩ := (he w hw).2.2.1
      exact ⟨P, h1, fun i s₁ s₂ Pa Pb D h => h2 i s₁ s₂ Pa Pb D (hcand h)⟩
    choiceM := fun i s₁ s₂ Pa Pb D h => ⟨fun w hw => by
        have h1 := (he w hw).2.2.2 i s₁ s₂ Pa Pb D (hcand h)
        have h2 : mS w ≤ F₀.d₀.S₀.sup mS := Finset.le_sup hw
        omega, fun w hw => by
        have h1 := hm₀ i s₁ s₂ Pa Pb D (hcand h) w hw
        omega⟩ }⟩

end UpperTheory.HeckeLevelFrameExistence

end
