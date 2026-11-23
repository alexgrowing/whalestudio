import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSAddLeft
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ConstantCoeffQZeroEqP
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Pi0PowSmulInjective

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem exists_X_pow_mul (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (w : ℕ) (u : PowerSeries LL), PowerSeries.constantCoeff u ≠ 0 ∧ f = PowerSeries.X ^ w * u := by
  have hex : ∃ w, PowerSeries.coeff w f ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (PowerSeries.ext fun w => by simpa using h w)
  obtain ⟨w, h1, hmin⟩ : ∃ w, PowerSeries.coeff w f ≠ 0 ∧ ∀ m < w, PowerSeries.coeff m f = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => by
      have := Nat.find_min hex hm
      push Not at this
      exact this⟩
  have hdvd : PowerSeries.X ^ w ∣ f := PowerSeries.X_pow_dvd_iff.2 hmin
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨w, u, ?_, hu⟩
  rw [hu, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h1
  exact h1

theorem smulS_div {m : ℤ} {e : ℤ → V} (he : LB m e) (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (m' : ℤ) (d : ℤ → V), LB m' d ∧ smulS f d = e := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  set e' : ℤ → V := fun k => e (k + w) with he'
  have hLB' : LB (m - w) e' := fun k hk => he _ (by omega)
  refine ⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_⟩
  rw [smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem smulS_inj {m : ℤ} {d d' : ℤ → V} (hd : LB m d) (hd' : LB m d') (f : PowerSeries LL)
    (hf : f ≠ 0) (h : smulS f d = smulS f d') : d = d' := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  have h0 : smulS (PowerSeries.X ^ w * u) (d - d') = 0 := by
    rw [smulS_sub hd hd', h, sub_self]
  rw [smulS_mul (LB_sub hd hd'), smulS_X_pow (LB_smulS (LB_sub hd hd') _)] at h0
  have h1 : smulS u (d - d') = 0 := by
    funext k
    have := congrFun h0 (k + w)
    simpa using this
  have h2 := smulS_inv (LB_sub hd hd') u hu
  rw [h1] at h2
  have h3 : smulS u⁻¹ (0 : ℤ → V) = 0 := by
    funext k
    simp [smulS]
  rw [h3] at h2
  exact sub_eq_zero.1 h2.symm

theorem smulS_comm {m : ℤ} {d : ℤ → V} (hd : LB m d) (f g : PowerSeries LL) :
    smulS f (smulS g d) = smulS g (smulS f d) := by
  rw [← smulS_mul hd, ← smulS_mul hd, mul_comm]

theorem smulS_mem {m : ℤ} {d : ℤ → V} (hd : LB m d) (D : Submodule LL V) (hD : ∀ k, d k ∈ D)
    (f : PowerSeries LL) (k : ℤ) : smulS f d k ∈ D := by
  have := Dg_smulS (Fil := fun _ : ℤ => D) (fun _ _ _ => le_rfl) hd (s := 0)
    (fun k => hD k) f k
  simpa using this

end Div

section Exp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem conv_eq {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv f d = smulS f d := rfl

theorem p_ne_zero_LL (W' : LocWach PD LL O v n) : (PD.p : LL) ≠ 0 := by
  intro h
  have := W'.v_l
  rw [h, AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this

theorem eat_qp :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ =
      Formalism.MainNotions.LiftingTheory.qp W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]

theorem expRing_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := by
  intro hA i ζ hζ
  have hs : W.s = 1 := hA.2.1
  have hp := p_ne_zero_LL W
  obtain ⟨u₀, hu₀, hq⟩ := MC.lev_q_eq W i hζ hp
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [eat_qp] at hw

  have hqp : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) =
      (W.lev i ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u₀) * PowerSeries.X := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
      rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, map_mul, hq]
    ring
  have hunit : IsUnit (W.lev i ζ ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * u₀) :=
    ((Units.isUnit _).map _).mul
      (PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 hu₀))
  have hcq : PowerSeries.constantCoeff (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W)) = 0 := by
    rw [hqp, map_mul, PowerSeries.constantCoeff_X, mul_zero]
  have hcpi : PowerSeries.constantCoeff (W.lev i ζ W.π₀) = -(PD.p : LL) := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = W.π₀ + ((PD.p : ℕ) : LetA O n) := rfl
    rw [e, map_add, map_natCast, map_add, map_natCast] at hcq
    linear_combination hcq
  refine ⟨⟨_, hunit, hqp⟩, hcpi, ?_⟩

  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.1
  rw [eat_qp] at hw'
  have hp1 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  have hcφ : PowerSeries.constantCoeff (W.lev i ζ (W.φA W.π₀)) = 0 := by
    rw [hw', map_mul, map_mul, map_pow, map_mul, map_mul, map_pow, hcq,
      zero_pow (by omega), mul_zero]
  have e2 : Formalism.MainNotions.LiftingTheory.pk W 1 = W.φA W.π₀ + ((PD.p : ℕ) : LetA O n) := by
    simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, map_natCast]
  rw [e2, PowerSeries.isUnit_iff_constantCoeff, map_add, map_natCast, map_add, hcφ, zero_add,
    map_natCast]
  exact isUnit_iff_ne_zero.2 hp

def GamN : Prop :=
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : ↥(W.N T)) (hx : W.γ T (x : W.DD T) ∈ W.N T) (k : ℤ),
      W.levN T i ζ ⟨W.γ T x, hx⟩ k = (algebraMap O LL (W.χΓ W.gam : O)) ^ k • W.levN T i ζ x k

def GamA : Prop :=
  ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ f : LetA O n,
    W.lev i ζ (W.γA W.gam f) = PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ f)

theorem gam_of_tie (hs : W.s = 1) {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O]
    [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW}
    {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (C : CmpTie W E ιdR p1 tS zS) : GamN W ∧ GamA W := by
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - ((1 : ℕ) : LL)) := by
    simp only [Nat.cast_one]
    rw [W.gam_gen, hs, Nat.cast_one]
  refine ⟨fun T hT i ζ hζ x hx k => ?_, fun i ζ hζ f => ?_⟩
  · rw [C.levN_eq, C.levN_eq]
    have e := C.levB_Γ T hT W.gam i ζ ζ 1 1 (by rwa [pow_one]) hv (by rw [pow_one]) x hx k
    have e' : (⟨W.γ T x, hx⟩ : ↥(W.N T)) = ⟨W.γD T W.gam x, hx⟩ := rfl
    rw [e', e, map_smul]
  · exact C.lev_Γ W.gam i ζ ζ 1 1 (by rwa [pow_one]) hv (by rw [pow_one]) f

end Exp

end Formalism.MainNotions.N.Pv.LocalLengthBound
