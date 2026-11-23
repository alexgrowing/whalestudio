import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCoeff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuous

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjRowLevel

private theorem inner_R_eq_inner_R_inv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a : X.B.I.GA)
    (x z : X.B.I.L2 X.B.μf X.B.fund) : ⟪x, X.B.R a z⟫_ℂ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
  obtain ⟨h1, hmul, hnorm, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  let L : X.B.I.L2 X.B.μf X.B.fund →ₗᵢ[ℂ] X.B.I.L2 X.B.μf X.B.fund :=
    { toLinearMap := (X.B.R a⁻¹ : X.B.I.L2 X.B.μf X.B.fund →ₗ[ℂ] X.B.I.L2 X.B.μf X.B.fund)
      norm_map' := hnorm a⁻¹ }
  have hback : X.B.R a⁻¹ (X.B.R a z) = z := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, inv_mul_cancel, h1]
    rfl
  calc ⟪x, X.B.R a z⟫_ℂ = ⟪L x, L (X.B.R a z)⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
      show ⟪X.B.R a⁻¹ x, X.B.R a⁻¹ (X.B.R a z)⟫_ℂ = _
      rw [hback]

private theorem e_inv_mul_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2)
    (y : X.B.I.Gf) : X.B.e (k⁻¹ * y) = X.chi2 k * X.B.e y := by
  classical
  obtain ⟨_, hmulK, hinvK, hchi, hnorm⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have he : ∀ z, X.B.e z = if z ∈ X.K2 then star (X.chi2 z) / ((X.B.μf X.K2).toReal : ℂ) else 0 :=
    X.e_eq
  have hunit : X.chi2 k * star (X.chi2 k) = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hnorm k hk]
    norm_num
  by_cases hy : y ∈ X.K2
  · have hky : k⁻¹ * y ∈ X.K2 := hmulK _ (hinvK _ hk) _ hy
    have hsplit : X.chi2 y = X.chi2 k * X.chi2 (k⁻¹ * y) := by
      rw [← hchi _ hk _ hky, mul_inv_cancel_left]
    rw [he, he, if_pos hky, if_pos hy, hsplit, star_mul']
    linear_combination (-(star (X.chi2 (k⁻¹ * y)) / ((X.B.μf X.K2).toReal : ℂ))) * hunit
  · have hky : k⁻¹ * y ∉ X.K2 := fun h => hy (by simpa using hmulK _ hk _ h)
    rw [he, he, if_neg hky, if_neg hy, mul_zero]

theorem reg_comp_Re {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨-, hmul, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  ext1 y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_R_eq_inner_R_inv X, X.B.Re_spec.2, X.B.Re_spec.2]
  have hstep : ∀ g : X.B.I.Gf,
      ⟪X.B.R (1, k)⁻¹ x, X.B.R (1, g) y⟫_ℂ = ⟪x, X.B.R (1, k * g) y⟫_ℂ := by
    intro g
    have hprod : (((1 : X.B.I.Ginf), k * g) : X.B.I.GA) = (1, k) * (1, g) := by simp
    rw [hprod, hmul, ContinuousLinearMap.comp_apply]
    exact (inner_R_eq_inner_R_inv X (1, k) x _).symm
  simp_rw [hstep]
  have hinv := integral_mul_left_eq_self (μ := X.B.μf)
    (fun g' => X.B.e (k⁻¹ * g') * ⟪x, X.B.R (1, g') y⟫_ℂ) k
  simp only [inv_mul_cancel_left] at hinv
  rw [hinv]
  simp_rw [e_inv_mul_eq_chi2_mul X k hk, mul_assoc]
  exact integral_const_mul _ _
private theorem contRep_mul_right_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Φ : X.B.Hs →L[ℂ] L2X X)
    (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) (v : X.B.Hs) {ψ : X.B.I.GA → ℂ}
    (hψ : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ v) ψ) (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) :
    ∀ z, ψ (z * ((1 : X.B.I.Ginf), κ)) = X.chi2 κ * ψ z := by
  obtain ⟨A, -, hA⟩ := Submodule.mem_map.1 hΦ
  have hΦv : Φ v = X.B.Re (A v) := by
    rw [← hA]
    rfl
  have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1 : X.B.I.Ginf), κ)
  have hR : X.B.R ((1 : X.B.I.Ginf), κ) (Φ v) = X.chi2 κ • Φ v := by
    rw [hΦv, ← ContinuousLinearMap.comp_apply, reg_comp_Re X κ hκ, ContinuousLinearMap.smul_apply]
  rw [hR] at h1
  have h2 := Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 κ) hψ
  have heq := Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 h2
  intro z
  simpa using congrFun heq z

theorem conjMap_level : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ _ _ t c _ hconj _ Φ hΦ hcont u k hk g
  obtain ⟨ψ, hψ⟩ := hcont u
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hmem, hval⟩ := hconj k
  have hk' : ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧
      ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hmem.1 hk
  have hv := hval hk
  obtain ⟨hp1, hp2⟩ := hk'
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 := ⟨_, rfl⟩
  have hq : (iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹) = ((1 : X.B.I.Ginf), κ) := Prod.ext hp1 hκdef.symm
  have hκ : κ ∈ X.K2 := by
    rw [hκdef]
    exact hp2
  have hv' : star (X.chi2 κ) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k := by
    rw [hκdef]
    exact hv
  have hsplit : (iotaX X h).toMulEquiv (g * k * t⁻¹) =
      (iotaX X h).toMulEquiv (g * t⁻¹) * ((1 : X.B.I.Ginf), κ) := by
    rw [← hq]
    calc (iotaX X h).toMulEquiv (g * k * t⁻¹)
        = (iotaX X h).toMulEquiv (g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹)) := by
          rw [show g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹) = g * k * t⁻¹ by group]
      _ = _ := map_mul _ _ _
  change star (ψ ((iotaX X h).toMulEquiv (g * k * t⁻¹))) = _ * star (ψ ((iotaX X h).toMulEquiv (g * t⁻¹)))
  rw [hsplit, contRep_mul_right_eq_chi2_mul X Φ hΦ _ hψ κ hκ, star_mul', hv']

end GlobalTheory.ConjRowLevel
