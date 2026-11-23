import Formalism.SharpRestriction.LevelLetterCocycles.InNOfPiLam

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem γA_apply (g : W.Gam) (a : LetA O n) (i : ZMod n) : W.γA g a i = W.γ₀ g (a i) := rfl

theorem q_unit (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0) :
    ∃ w : LetA O n, W.q = w * ps W 0 ∧ ∃ w' : LetA O n, w * w' = 1 ∧
      ∀ i, PowerSeries.constantCoeff (w' i) = 1 := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Formalism.MainNotions.UnusedSlot80.SatW.Eat_π₀] at hw
  have hq : (W.π₀ + ((PD.p : ℕ) : LetA O n)) = ps W 0 := by rw [ps_zero]; rfl
  rw [hq] at hw
  refine ⟨w, hw, ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.mul_inv w, fun i => ?_⟩
  have h1 : PowerSeries.constantCoeff (W.q i) =
      PowerSeries.constantCoeff ((w : LetA O n) i) * PowerSeries.constantCoeff (ps W 0 i) := by
    rw [hw, Pi.mul_apply, map_mul]
  rw [show W.q i = W.q₀ from rfl, Formalism.MainNotions.UnusedSlot80.ArcF.constantCoeff_q_zero_eq_p] at h1
  have h2 : PowerSeries.constantCoeff (ps W 0 i) = ((PD.p : ℕ) : O) := by
    rw [ps_zero]
    simp [LocWach.π₀, lA, Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR]
  rw [h2] at h1
  have hw1 : PowerSeries.constantCoeff ((w : LetA O n) i) = 1 := by
    have : ((PD.p : ℕ) : O) * (PowerSeries.constantCoeff ((w : LetA O n) i) - 1) = 0 := by
      linear_combination -h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hp0
    · exact sub_eq_zero.1 h
  have h3 : PowerSeries.constantCoeff ((w : LetA O n) i) *
      PowerSeries.constantCoeff (((w⁻¹ : (LetA O n)ˣ) : LetA O n) i) = 1 := by
    rw [← map_mul, ← Pi.mul_apply, Units.mul_inv]
    simp
  rwa [hw1, one_mul] at h3

theorem lam_zero (A : ArcP n) (a : ZMod n) : abelian₂ W A a 0 = 1 := by simp [abelian₂]

theorem cmpD_lam (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (hT : Win W A T) :
    ∀ e : ℕ, ∃ t : ℕ, ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T c' y →
      cmpD W T (abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y) =
        ((PD.p : LL) ^ t) • ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ e) (cmpD W T y) := by
  intro e
  induction e with
  | zero => exact ⟨0, fun y _ => by simp [lam_zero]⟩
  | succ e ih =>
    obtain ⟨t, ht⟩ := ih
    set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
    refine ⟨H + t, fun y hy => ?_⟩
    set z : W.DD T := abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y with hzdef
    obtain ⟨z', hz'N, hz'l, hzz'⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W hs hR h5 A hA c' hc' e T hT _
      (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e hy)
    rw [one_smul] at hzz'
    have hzN : z ∈ W.N T := by rw [hzdef, hzz']; exact hz'N.1
    have hzl : (letE (c' + (e : ZMod n)) : LetA O n) • z = z := by rw [hzdef, hzz']; exact hz'l
    have h5T := h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
    have hQ : W.Q = W.q := by simp [LocWach.Q, hs]
    set i : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with hidef
    have hzNl : z ∈ W.Nl T (i - 1) := by
      rw [show i - 1 = c' + (e : ZMod n) by rw [hidef]; push_cast; ring]
      exact ⟨z, hzN, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hzl⟩
    have hM := h5T.1 i z hzNl
    rw [hQ] at hM
    have hMH : Mw A.G₀ A.S A.η (A.ty i) ≤ H := by
      have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' (e + 1) (e + 1) (by omega) le_rfl
      rwa [Nat.sub_self] at this
    have hqN : W.q ^ H • W.φD T z ∈ W.N T := by
      obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hMH
      rw [hdd, pow_add, mul_comm, mul_smul]
      exact (W.N T).smul_mem _ hM
    have hφl : (letE i : LetA O n) • W.φD T z = W.φD T z := by
      have := φD_pow_letter W T (c' + (e : ZMod n)) z hzl 1
      rw [pow_one] at this
      rwa [show c' + (e : ZMod n) + ((1 : ℕ) : ZMod n) = i by rw [hidef]; push_cast; ring] at this
    have hql : (letE i : LetA O n) • (W.q ^ H • W.φD T z) = W.q ^ H • W.φD T z := by
      rw [smul_comm, hφl]
    obtain ⟨w, hw, w', hww, hw'⟩ := q_unit W hR hp0
    have hp0w : ps W 0 = w' * W.q := by
      rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
    have e1 : abelian₂ W A i (e + 1) • ((W.φD T) ^ (e + 1)) y = w' ^ H • (W.q ^ H • W.φD T z) := by
      rw [hidef, lam_succ, pow_apply_succ, smul_smul, hzdef, φD_smulA, smul_smul, hp0w]
      unfold LamUp
      congr 1; ring
    have hk : W.Q ^ H • W.φD T ((⟨z, hzN⟩ : ↥(W.N T)) : W.DD T) ∈ W.N T := by rw [hQ]; exact hqN
    have e2 := h3.2.2 ⟨z, hzN⟩ H hk
    have e3 : (⟨W.Q ^ H • W.φD T z, hk⟩ : ↥(W.N T)) = ⟨W.q ^ H • W.φD T z, hqN⟩ := Subtype.ext (by show W.Q ^ H • W.φD T z = W.q ^ H • W.φD T z; rw [hQ])
    rw [e3] at e2
    rw [e1, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T ((W.N T).smul_mem _ hqN),
      Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T i _ _ hqN hql, e2, Pi.pow_apply, map_pow, hw', one_pow, map_one,
      one_smul, ← Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hzN, hzdef, ht y hy, map_smul, smul_smul, ← pow_add, pow_succ' _ e,
      Module.End.mul_apply]

end Formalism.MainNotions.UnusedSlot80.LevC
