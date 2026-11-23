import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrechetContinuousContinuousOnOrbitHasDerivAt
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DualEmb

open PI.UpqRep GlobalTheory.DerivedAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

private theorem hasDerivAt_exp_smul_apply_zero'
    (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j c : Fin (2 * r + k + 1)) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y) j c) (Y j c) 0 := by
  letI instNR : NormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      (@PseudoMetricSpace.toUniformSpace _ (@SeminormedRing.toPseudoMetricSpace _
        (@NormedRing.toSeminormedRing _ instNR))) :=
    (inferInstance : CompleteSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y) ((0 : ℝ) : ℂ) := hasDerivAt_exp_smul_const Y _
  let f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M j c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let e : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap f
  have he : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, e M = M j c := fun M => rfl
  have h2 := (e.hasFDerivAt.comp_hasDerivAt _ h1).comp_ofReal
  simp only [Function.comp_def, he, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem hasDerivAt_inv_exp_entry (X : Mx k r) (j c : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) (-X j c) 0 := by
  have h := hasDerivAt_exp_smul_apply_zero' (-X) j c
  have hfun : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c) =
      fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-X)) j c := by
    funext t
    rw [smul_neg, Matrix.exp_neg]
  rw [hfun]
  simpa using h

theorem lie_part₁ (Y : Mx k r) :
    InLieHpk k r ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  have hI := Gp91.GlobalTheory.CWDeriv.hInvol k r
  have h := (AAInvW.ana_hpartMem hI Y).1
  rw [AAInvW.ana_hpart1_eq hI] at h
  rw [← sub_eq_add_neg]
  exact h

theorem lie_part₂ (Y : Mx k r) :
    InLieHpk k r ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) := by
  have hI := Gp91.GlobalTheory.CWDeriv.hInvol k r
  have h := (AAInvW.ana_hpartMem hI Y).2.1
  rw [AAInvW.ana_hpart2_eq hI] at h
  rw [sub_neg_eq_add]
  exact h

theorem io_dsig (hK : PI.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}
    (hR : R.IsDG ε mu) {RI : Fin (2 * r + k + 1) → Rep k r}
    {muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ}
    {io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H} {pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H}
    (hI : ∀ s, (RI s).IsDG ε (muI s)) (hT : TensRaw dualM R RI io pr) (s : Fin (2 * r + k + 1))
    {X : Mx k r} (hX : InLieHpk k r X) {y : (RI s).H} (hy : y ∈ (RI s).sm) (c : Fin (2 * r + k + 1)) :
    io s c (dsig (k := k) (r := r) (RI s).σ X y) =
      dsig (k := k) (r := r) R.σ X (io s c y) - ∑ j, X j c • io s j y := by
  classical
  have hsmc := hT.io_sm s c
  have hcw : PI.BesselMapUniq.IsCWCont (RI s).σ (io s c) := by
    have h0 := hsmc.cont [] (by simp)
    exact h0
  have hL := ((Gp91.GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r ε (muI s) (RI s) (hI s) R.H (io s c)
      hsmc.add hsmc.smul hcw) y hy).2 X hX
  have hDA := Gp91.GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR X hX
  have hexp : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ BranchingSupport.GG k r :=
    fun t => Gp91.GlobalTheory.DerivedAction.exp_mem hX t
  have hfun : (fun t : ℝ => io s c ((RI s).σ (NormedSpace.exp ((t : ℂ) • X)) y)) =
      fun t : ℝ => ∑ j, (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c •
        R.σ (NormedSpace.exp ((t : ℂ) • X)) (io s j y) := by
    funext t
    have h := congrFun (hT.io_eq s _ (hexp t) y hy) c
    simpa [BranchingSupport.act, BranchingSupport.dualM, Matrix.transpose_apply] using h
  rw [hfun] at hL
  have hR' : HasDerivAt (fun t : ℝ => ∑ j, (NormedSpace.exp ((t : ℂ) • X))⁻¹ j c •
        R.σ (NormedSpace.exp ((t : ℂ) • X)) (io s j y))
      (∑ j, ((NormedSpace.exp (((0 : ℝ) : ℂ) • X))⁻¹ j c • dsig (k := k) (r := r) R.σ X (io s j y) +
        (-X j c) • R.σ (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) (io s j y))) 0 := by
    have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ => (hasDerivAt_inv_exp_entry X j c).smul
      ((hDA.1 (io s j y) ((hT.io_sm s j).mem y hy)).2))
    convert hs using 1
    funext t
    simp [Finset.sum_apply]
  have key := hL.unique hR'
  have hone : R.σ 1 = 1 := by
    obtain ⟨P, ⟨⟨hPu, -⟩, -⟩, hds⟩ := hR.ds
    have h1 := hds.2.2.1.1.1
    simp only [mul_one] at h1
    rwa [Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hPu)] at h1
  rw [key]
  simp [hone, Matrix.one_apply, Finset.sum_add_distrib, ite_smul, sub_eq_add_neg]

end GlobalTheory.DualEmb

namespace GlobalTheory

open DualEmb

theorem dualTens_io_dC : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H), (∀ s, (RI s).IsDG ε (muI s)) → TensRaw dualM R RI io pr → ∀ s Y, ∀ y ∈ (RI s).sm, ∀ c, io s c ((RI s).dC Y y) = R.dC Y (io s c y) - ∑ j, Y j c • io s j y := by
  intro hK k r ε mu R hR RI muI io pr hI hT s Y y hy c
  have h1 := DualEmb.lie_part₁ (k := k) (r := r) Y
  have h2 := DualEmb.lie_part₂ (k := k) (r := r) Y
  have e1 := DualEmb.io_dsig hK hR hI hT s h1 hy c
  have e2 := DualEmb.io_dsig hK hR hI hT s h2 hy c
  have hsmc := hT.io_sm s c
  have hd1 := ((Gp91.GlobalTheory.DerivedAction.derived_action hK k r ε (muI s) (RI s) (hI s) _ h1).1 y hy).1
  have hd2 := ((Gp91.GlobalTheory.DerivedAction.derived_action hK k r ε (muI s) (RI s) (hI s) _ h2).1 y hy).1
  have hzero : (0 : (RI s).H) ∈ (RI s).sm := by
    have hneg : -y ∈ (RI s).sm := by
      have := Gp91.GlobalTheory.CWDeriv.sm_comb (R := RI s) 1 hy hy hy
      simpa using this
    have h3 := Gp91.GlobalTheory.CWDeriv.sm_comb (R := RI s) (1 / 2) hy hneg hy
    have e : (1 / 2 : ℂ) • (y - -y) - y = 0 := by
      rw [sub_neg_eq_add, ← two_smul ℂ y, smul_smul]
      norm_num
    rwa [e] at h3
  have hsmul : ∀ (a : ℂ) {v : (RI s).H}, v ∈ (RI s).sm → a • v ∈ (RI s).sm := by
    intro a v hv
    have := Gp91.GlobalTheory.CWDeriv.sm_comb (R := RI s) a hv hzero hzero
    simpa using this
  have hYsplit : ∀ j, ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) j c +
      Complex.I * ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) j c =
      Y j c := by
    intro j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hsum : ∑ j, Y j c • io s j y =
      ∑ j, ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) j c • io s j y +
        Complex.I • ∑ j, ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) j c •
          io s j y := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hYsplit j, add_smul, mul_smul]
  simp only [BranchingSupport.Rep.dC]
  rw [hsmc.add _ hd1 _ (hsmul Complex.I hd2), hsmc.smul Complex.I _ hd2, e1, e2, hsum, smul_sub]
  abel

end GlobalTheory

end
