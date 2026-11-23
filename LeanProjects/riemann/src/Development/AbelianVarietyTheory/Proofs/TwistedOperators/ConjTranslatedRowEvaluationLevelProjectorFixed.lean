import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHH.LevelFix

theorem castGA_symm_mem {I I' : Formalism.MainNotions.S.AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

theorem iotaX_symm_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ : X.B.I.GA) (hγ : γ ∈ X.B.I.GFset) : (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
  refine (Formalism.IndefR.RationalEmbedding.iota_rat D ((iotaX X h).symm γ)).2 ?_
  show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact castGA_symm_mem _ γ hγ

theorem mult_lev {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev
  | zero => intro v k _ g; simp
  | add x y _ _ hx hy =>
    intro v k hk g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx v k hk g, hy v k hk g, mul_add]
  | smul a x _ hx =>
    intro v k hk g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx v k hk g]
    ring

end GlobalTheory.RowEvalHH.LevelFix

open GlobalTheory.RowEvalHH GlobalTheory.RowEvalHH.LevelFix in

theorem GlobalTheory.RowEvalHH.Re_evF : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → ∀ S ∈ EP R F, ∀ y : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ), X.B.Re (GlobalTheory.RowEvalHH.evF R X h t c S y) = GlobalTheory.RowEvalHH.evF R X h t c S y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c ht hLM S hS y
  classical
  have hSM := Formalism.IndefR.Mult.goodPart_le _ _ _ _ _ hS
  have hcl := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (MP R) R.θ _ _ hSM (vecOf R X c y)
  have hlev := mult_lev hSM (vecOf R X c y)
  let ιY : X.B.I.GA ≃* GA D (Yc D 0) := (iotaX X h).symm.toMulEquiv
  unfold evF
  by_cases hm : MemLp (fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X)
  · rw [dif_pos hm]
    set f : X.B.I.GA → ℂ := fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) with hf
    have hm0 : MemLp (fun x => star (f x)) 2 (muX X) := hm.star
    have eF : star (hm.toLp f) = hm0.toLp (fun x => star (f x)) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_star (hm.toLp f), hm.coeFn_toLp, hm0.coeFn_toLp] with x a1 a2 a3
      rw [a1, a3, Pi.star_apply, a2]
    rw [eF]
    have hfY : ∀ x, f x = S (vecOf R X c y) (ιY x * t) := fun x => rfl
    have hinv : ∀ γ ∈ X.B.I.GFset, ∀ x, star (f (γ * x)) = star (f x) := by
      intro γ hγ x
      congr 1
      rw [hfY, hfY, map_mul, mul_assoc]
      exact hcl.2 _ (iotaX_symm_rat X h γ hγ) _
    have hmeas : Measurable fun x => star (f x) := by
      haveI : IsTopologicalGroup (GA D (D.sp.Y 0)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
      have : Continuous f := hcl.1.comp ((iotaX X h).symm.continuous.mul continuous_const)
      exact (continuous_star.comp this).measurable
    have hright : ∀ k ∈ X.K2, ∀ x, star (f (x * (1, k))) = X.chi2 k * star (f x) := by
      intro k hk x
      have ek : (kap X h t k : GA D (Yc D 0)) = t⁻¹ * ιY (1, k) * t := rfl
      have e2 : ιY (x * (1, k)) * t = (ιY x * t) * kap X h t k := by
        rw [ek, map_mul]
        simp only [mul_assoc, mul_inv_cancel_left]
      have h1 : f (x * (1, k)) = star (X.chi2 k) * f x := by
        have hl := hlev _ (hLM k hk).1 (ιY x * t)
        rw [(hLM k hk).2] at hl
        rw [hfY, hfY, e2]
        exact hl
      rw [h1, star_mul', star_star, mul_comm]
    have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
    have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
    have hKM : MeasurableSet X.K2 := (Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL).isOpen.measurableSet
    have hfix : ∀ᵐ z ∂(X.B.I.muA X.B.μf), ∫ g, X.B.e g * star (f (z * (1, g))) ∂X.B.μf = star (f z) := by
      refine Filter.Eventually.of_forall fun z => ?_
      have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
      have hfun : (fun g => X.B.e g * star (f (z * (1, g)))) =
          X.K2.indicator (fun _ => star (f z) / ((X.B.μf X.K2).toReal : ℂ)) := by
        funext g
        rw [X.e_eq g]
        by_cases hg : g ∈ X.K2
        · have hg' : g ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
          rw [if_pos hg', Set.indicator_of_mem hg, hright g hg z]
          have hn : ‖X.chi2 g‖ = 1 := hK.2.2.2.2 g hg
          have hc : star (X.chi2 g) * X.chi2 g = 1 := by
            rw [RCLike.star_def, RCLike.conj_mul, hn]; simp
          show star (X.chi2 g) / ((X.B.μf X.K2).toReal : ℂ) * (X.chi2 g * star (f z)) =
            star (f z) / ((X.B.μf X.K2).toReal : ℂ)
          rw [div_mul_eq_mul_div, ← mul_assoc, hc, one_mul]
        · have hg' : g ∉ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
          rw [if_neg hg', Set.indicator_of_notMem hg, zero_mul]
      rw [hfun, integral_indicator hKM, setIntegral_const]
      simp only [measureReal_def, Complex.real_smul]
      have hC : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hC]
    exact Formalism.L2.SG.Pf.idempotent_fixes_invariant_L2 X (fun x => star (f x)) hmeas hinv hm0 hfix
  · rw [dif_neg hm]
    have h0 : (star (0 : L2X X)) = 0 := (Formalism.L2.SG.RowDict.conjL (muX X)).map_zero
    rw [h0, map_zero]

end
