import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.JumpsLetExists
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.GammaLevelsExpansion

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Crit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def GamNΔ : Prop :=
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ ζ' : LL) (δ : W.Gam) (a : ℕ),
    IsPrimitiveRoot ζ PD.p → ζ' = ζ ^ a →
    ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ δ : O) - (a : LL)) →
    ∀ (x : ↥(W.N T)) (hx : W.γD T δ (x : W.DD T) ∈ W.N T) (k : ℤ),
      W.levN T i ζ ⟨W.γD T δ x, hx⟩ k = (algebraMap O LL (W.χΓ δ : O)) ^ k • W.levN T i ζ' x k

def PtTrans : Prop :=
  ∀ ζ ζ' : LL, IsPrimitiveRoot ζ PD.p → IsPrimitiveRoot ζ' PD.p → ∃ δ ∈ W.DelF, ∃ a : ℕ,
    ζ' = ζ ^ a ∧ ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ δ : O) - (a : LL))

theorem gamΔ_of_tie {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) : GamNΔ W := by
  intro T hT i ζ ζ' δ a hζ hζ' hv x hx k
  rw [C.levN_eq, C.levN_eq, C.levB_Γ T hT δ i ζ ζ' 1 a (by rwa [pow_one]) hv hζ' x hx k, map_smul]

theorem isExp_self (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T} (hx : x ∈ W.N T) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x (W.levN T i ζ ⟨x, hx⟩) := by
  have h1 : (1 : LetA O n) • x ∈ W.N T := by rwa [one_smul]
  obtain ⟨m, hm⟩ := W.levN_supp T i ζ ⟨x, hx⟩
  refine ⟨⟨m, hm⟩, 1, h1, by rw [map_one]; exact one_ne_zero, fun k => ?_⟩
  have e : (⟨(1 : LetA O n) • x, h1⟩ : ↥(W.N T)) = ⟨x, hx⟩ := Subtype.ext (one_smul _ _)
  rw [e, map_one, conv_eq, smulS_one hm]

theorem isExp_smulA (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T}
    {d : ℤ → T.V ⊗[Qp] BdR} (hd : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d) (a' : LetA O n) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (a' • x) (smulS (W.lev i ζ a') d) := by
  obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hd
  have hmem : a • (a' • x) ∈ W.N T := by rw [smul_comm]; exact (W.N T).smul_mem a' ha
  refine ⟨⟨m, LB_smulS hm _⟩, a, hmem, hla, fun k => ?_⟩
  have e1 : (⟨a • (a' • x), hmem⟩ : ↥(W.N T)) = a' • (⟨a • x, ha⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_comm])
  rw [e1, levN_smulS, funext he]
  show smulS (W.lev i ζ a') (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (smulS (W.lev i ζ a') d) k
  rw [smulS_comm hm]

theorem expCritN_of [NeZero n] (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hdom : IsDomain O)
    (hFr : IsFractionRing O LL) (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W)
    (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hΓ : GamNΔ W) (hΔ : PtTrans W) :
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
      ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x →
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d →
        ((∃ k : ℕ, Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ W.N T) →
          (x ∈ W.N T ↔ ∀ k, d k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k))) := by
  intro T hT i ζ hζ x d hDL hd ⟨k, hk⟩
  have hs : W.s = 1 := hA.2.1
  haveI := hdom
  have hp := p_ne_zero_LL W
  have hFl : Antitone (Formalism.MainNotions.WachCoordinates.FilLev W T i 0) := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0
  constructor
  · intro hx j
    rw [isExp_unique W T i ζ hd (isExp_self W T i ζ hx)]
    exact (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1 ⟨x, hx⟩ j
  · intro hcoef
    obtain ⟨w, hw⟩ := hR.2.2.2.2.1
    rw [eat_qp] at hw
    have hQ : W.Q = (w : LetA O n) * Formalism.MainNotions.LiftingTheory.qp W := by rw [MC.Q_eq_q W hs, hw]
    have hQk : W.Q ^ k • x ∈ W.N T := by
      rw [hQ, mul_pow, mul_smul]; exact (W.N T).smul_mem _ hk
    refine memCrit_of W hA hFr h1 h3 h4 h5 hD T hT i x k hQk hDL.1 fun ζ' hζ' j => ?_

    obtain ⟨u, hu0, hq⟩ := MC.lev_q_eq W i hζ hp
    have hlevQ : W.lev i ζ W.Q = PowerSeries.X * u := by rw [MC.Q_eq_q W hs]; exact hq
    obtain ⟨m, hm⟩ := hd.1
    have hEQ : W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ = smulS ((PowerSeries.X * u) ^ k) d := by
      have := isExp_unique W T i ζ (isExp_self W T i ζ hQk) (isExp_smulA W T i ζ hd (W.Q ^ k))
      rw [this, map_pow, hlevQ]
    have hDgζ : ∀ j : ℤ, W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ j ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 ((k : ℤ) - j) := by
      intro j
      rw [hEQ, mul_pow, smulS_mul hm, smulS_X_pow (LB_smulS hm _)]
      have := Dg_smulS hFl hm (s := 0) (fun j => by simpa using hcoef j) (u ^ k) (j - k)
      simp only at this ⊢
      rwa [show (0 : ℤ) - (j - (k : ℤ)) = (k : ℤ) - j by ring] at this

    obtain ⟨δ, hδ, a, hζa, hv⟩ := hΔ ζ' ζ hζ' hζ
    have hγy : W.γD T δ (W.Q ^ k • x) ∈ W.N T := W.N_Γ T δ _ hQk
    obtain ⟨vv, hvv, hvu⟩ := gam_q W δ
    obtain ⟨vU, rfl⟩ := hvu
    have hγQ : W.γA δ W.Q = W.Q * vU := by rw [MC.Q_eq_q W hs]; exact hvv
    have eγ : W.γD T δ (W.Q ^ k • x) = ((vU : LetA O n) ^ k) • (W.Q ^ k • x) := by
      rw [RL.γD_smulA, map_pow, hDL.2 δ hδ, hγQ, mul_pow, mul_comm, mul_smul]
    have eback : W.Q ^ k • x = (((vU⁻¹ : (LetA O n)ˣ) : LetA O n) ^ k) • W.γD T δ (W.Q ^ k • x) := by
      rw [eγ, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hsub : (⟨W.Q ^ k • x, hQk⟩ : ↥(W.N T)) =
        (((vU⁻¹ : (LetA O n)ˣ) : LetA O n) ^ k) • (⟨W.γD T δ (W.Q ^ k • x), hγy⟩ : ↥(W.N T)) :=
      Subtype.ext eback
    have htr : ∀ j, W.levN T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩ j =
        (algebraMap O LL (W.χΓ δ : O)) ^ j • W.levN T i ζ ⟨W.Q ^ k • x, hQk⟩ j :=
      fun j => hΓ T hT i ζ' ζ δ a hζ' hζa hv ⟨W.Q ^ k • x, hQk⟩ hγy j
    have hDg' : ∀ j : ℤ, W.levN T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩ j ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T i 0 ((k : ℤ) - j) := fun j => by
      rw [htr j]; exact Submodule.smul_mem _ _ (hDgζ j)
    obtain ⟨m', hm'⟩ := W.levN_supp T i ζ' ⟨W.γD T δ (W.Q ^ k • x), hγy⟩
    rw [hsub, levN_smulS]
    exact Dg_smulS hFl hm' hDg' _ j

end Crit

end Formalism.MainNotions.N.Pv.LocalLengthBound
