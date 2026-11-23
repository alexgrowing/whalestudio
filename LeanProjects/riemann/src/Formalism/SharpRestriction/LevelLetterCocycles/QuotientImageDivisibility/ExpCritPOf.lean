import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IndepPhiCmp
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IndepOfSpan

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section CritB3

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}

theorem expCritP_of [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) [IsDomain O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hinj : Function.Injective (algebraMap O LL))
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hFr : IsFractionRing O LL)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt) :
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x →
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d →
        ((∃ k : ℕ, Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1) →
          (x ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1 ↔ ∀ k : ℤ, k < 0 → d k = 0)) := by
  intro T hT i ζ hζ x d hDL hd ⟨k, hk⟩
  have hs : W.s = 1 := hA.2.1
  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have h9T := ((h9 T hT) hs hA.2.2).2.2 hfin
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W := h9T.1
  have hmod := h9T.2
  obtain ⟨hN, hAg⟩ := gam_of_tie W hs C
  obtain ⟨-, hval, hAdd, -, -, -, -⟩ := expRules_of W h4 hN hAg hA T hT i ζ hζ
  constructor
  · intro hx
    obtain ⟨d', hd', hn'⟩ := pullJ_exp W hA h4 C h4W T hT i hζ x hx
    rw [isExp_unique W T i ζ hd hd']
    exact hn'
  · intro hneg
    obtain ⟨⟨e, he⟩, hB2⟩ := hB hA T hT (i - 1)
    have hi1 : i - 1 + ((1 : ℕ) : ZMod n) = i := by push_cast; ring
    have hqΔ : ∀ δ ∈ W.DelF, W.γA δ (Formalism.MainNotions.LiftingTheory.qp W) = Formalism.MainNotions.LiftingTheory.qp W := by
      intro δ hδ
      simp only [Formalism.MainNotions.LiftingTheory.qp, map_add, map_natCast, hring.1 δ hδ]
    have hDLy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (i - 1 + ((1 : ℕ) : ZMod n)) (Formalism.MainNotions.LiftingTheory.qp W ^ k • x) := by
      rw [hi1]
      refine ⟨by rw [smul_comm, hDL.1], fun δ hδ => ?_⟩
      rw [RL.γD_smulA, map_pow, hqΔ δ hδ, hDL.2 δ hδ]
    obtain ⟨a, ha, -⟩ := (hB2 _ e he 1).1 _ hk hDLy

    have hE : ∀ m, ∃ Em : ℤ → T.V ⊗[Qp] BdR,
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (((W.φD T) ^ 1) (e m)) Em ∧ (∀ j : ℤ, j < 0 → Em j = 0) ∧
          Em 0 = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V)
            (W.cmp T ⟨e m, (he.1 m).1⟩)) := by
      intro m
      rw [pow_one]
      exact phi_exp W hs C h4W T hT i hζ (e m) (he.1 m).1 (he.1 m).2.1
    choose Em hEx hEn hE0 using hE
    have hsumExp : ∀ s : Finset (Fin (Module.finrank LL T.V)),
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (∑ m ∈ s, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m) • ((W.φD T) ^ 1) (e m))
          (∑ m ∈ s, smulS (W.lev i ζ (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m))) (Em m)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact isExp_zero W T i ζ
      | insert m s hm ih =>
        rw [Finset.sum_insert hm, Finset.sum_insert hm]
        exact hAdd _ _ _ _ (isExp_smulA W T i ζ (hEx m) _) ih
    have hy := hsumExp Finset.univ
    rw [← ha] at hy
    have heq := isExp_unique W T i ζ (isExp_smulA W T i ζ hd (Formalism.MainNotions.LiftingTheory.qp W ^ k)) hy
    obtain ⟨u, hu, hlq⟩ := (expRing_of W hring hA i ζ hζ).1
    have hdLB : LB 0 d := fun j hj => hneg j hj

    let Fil : ℤ → Submodule LL (T.V ⊗[Qp] BdR) := fun a => if a ≤ 0 then ⊤ else ⊥
    have hFa : Antitone Fil := by
      intro a b hab
      by_cases hb : b ≤ 0
      · rw [show Fil a = ⊤ from if_pos (le_trans hab hb), show Fil b = ⊤ from if_pos hb]
      · rw [show Fil b = ⊥ from if_neg hb]; exact bot_le
    haveI := fd_ιDi W hA hD T hT i
    have hDLφ : ∀ m, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (((W.φD T) ^ 1) (e m)) := by
      intro m
      rw [pow_one]
      refine ⟨Formalism.MainNotions.N.Pv.LocalLengthBound.letter_phi W T i (he.1 m).2.1, fun δ hδ => ?_⟩
      rw [← W.φγ_comm, (he.1 m).2.2 δ hδ]
    have hEmem : ∀ m j, Em m j ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ⊓ Fil (-j) := by
      intro m j
      refine Submodule.mem_inf.2 ⟨hval _ _ (hDLφ m) (hEx m) j, ?_⟩
      by_cases hj : j < 0
      · rw [hEn m j hj]; exact Submodule.zero_mem _
      · rw [show Fil (-j) = ⊤ from if_pos (by omega)]; exact Submodule.mem_top
    have h₁ : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ⊓ Fil 1 = ⊥ := by
      rw [show Fil 1 = ⊥ from if_neg (by norm_num), inf_bot_eq]
    have hind : ∀ c : Fin (Module.finrank LL T.V) → LL,
        (∀ j, ∑ m, c m • Em m j ∈ Fil (-j + 1)) → c = 0 := by
      intro c hc
      have h0 := hc 0
      rw [show Fil (-(0 : ℤ) + 1) = ⊥ from if_neg (by norm_num), Submodule.mem_bot] at h0
      apply indep_phi_cmp W inferInstance hFr hring T (h3 T hT) hmod (i - 1) e he c
      rw [← h0]
      exact Finset.sum_congr rfl fun m _ => by rw [hE0 m]
    have hdg : ∀ j : ℤ, ∑ m, smulS (W.lev i ζ (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m))) (Em m) j ∈
        Fil ((k : ℤ) - j) := by
      intro j
      have e1 := congrFun heq j
      rw [Finset.sum_apply] at e1
      rw [← e1]
      by_cases hj : j < k
      · have h0 : smulS (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ k)) d j = 0 := by
          rw [map_pow, hlq, mul_pow, mul_comm, smulS_mul hdLB, smulS_X_pow (LB_smulS hdLB _)]
          exact LB_smulS hdLB _ _ (by omega)
        rw [h0]; exact Submodule.zero_mem _
      · rw [show Fil ((k : ℤ) - j) = ⊤ from if_pos (by omega)]; exact Submodule.mem_top
    have hdvd := MC.dvd_of_dg hFa (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i) 1 h₁ hEmem hind k _ hdg

    let ψ : PowerSeries O →+* PowerSeries LL := (W.lev i ζ).toRingHom.comp (at0Hom W hring)
    have hψa : ∀ f, ψ f = W.lev i ζ (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f) := fun f => by
      show W.lev i ζ (at0Hom W hring f) = _
      rw [at0Hom_apply]
    have hψC : ∀ o : O, ψ (PowerSeries.C o) = PowerSeries.C (algebraMap O LL o) := by
      intro o
      rw [hψa, evalZero_C, AlgHom.commutes, PowerSeries.algebraMap_apply]
    have hqpe : W.π₀ + algebraMap O (LetA O n) ((PD.p : ℕ) : O) = Formalism.MainNotions.LiftingTheory.qp W := by
      rw [map_natCast]; rfl
    have hψ : ψ (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = PowerSeries.X * u := by
      rw [hψa, ← at0Hom_apply W hring, map_add, at0Hom_apply, at0Hom_apply, evalZero_X_eq_pi0 W hring, evalZero_C,
        hqpe, hlq, mul_comm]
    have hdiv : ∀ m, (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ k ∣ a m := fun m =>
      Wd.dvd_of_dvd_image hinj ((PD.p : ℕ) : O) ψ hψC u hu hψ hlm k (a m)
        (by rw [hψa]; exact hdvd m)
    choose g hg using hdiv
    have hat0 : ∀ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (a m) =
        Formalism.MainNotions.LiftingTheory.qp W ^ k * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (g m) := by
      intro m
      rw [hg m, evalZero_mul W hring, ← at0Hom_apply W hring
        ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ k), map_pow, map_add, at0Hom_apply,
        at0Hom_apply, evalZero_X_eq_pi0 W hring, evalZero_C, hqpe]
    have hx' : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = Formalism.MainNotions.LiftingTheory.qp W ^ k •
        ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (g m) • ((W.φD T) ^ 1) (e m) := by
      rw [ha, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [hat0 m, mul_smul]
    rw [qp_pow_cancel W hring T k hx']
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨e m, ⟨(he.1 m).1, (he.1 m).2⟩, rfl⟩)

theorem expCrit_of [NeZero n] [IsDomain O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hinj : Function.Injective (algebraMap O LL))
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hFr : IsFractionRing O LL)
    (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W) (C : CmpTie W E ιdR p1 tS zS)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (h4W : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt) (hΔ : PtTrans W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W := by
  intro hA T hT i ζ hζ x d hDL hd
  have hs : W.s = 1 := hA.2.1
  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W := (((h9 T hT) hs hA.2.2).2.2 hfin).1
  exact ⟨expCritN_of W hA inferInstance hFr h1 h3 h4 h5 hD hring (gamΔ_of_tie W C) hΔ T hT i ζ hζ
      x d hDL hd,
    expCritP_of W hA hinj hlm hFr h3 h4 h9 hD hB C h4W T hT i ζ hζ x d hDL hd⟩

end CritB3

end Formalism.MainNotions.N.Pv.LocalLengthBound
