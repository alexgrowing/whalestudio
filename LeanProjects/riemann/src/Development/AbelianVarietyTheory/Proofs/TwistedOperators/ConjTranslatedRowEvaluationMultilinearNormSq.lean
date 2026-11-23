import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHHNorm

open GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem norm_sq_toLp_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {f : X.B.I.GA → ℂ} (hf : MemLp f 2 (muX X)) :
    ‖(hf.toLp f : L2X X)‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(muX X) := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h1 : (fun a => ⟪(hf.toLp f : L2X X) a, (hf.toLp f : L2X X) a⟫_ℂ) =
      fun a => (((‖(hf.toLp f : L2X X) a‖ ^ 2 : ℝ)) : ℂ) := by
    funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h1, integral_complex_ofReal]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

def phi (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R))
    (y : ∀ τ, Wsub R X c τ) : X.B.I.GA → ℂ :=
  fun x => ev (MP R) (vecOf R X c y) S
    (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)

theorem vecOf_update [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau)
    (z : Wsub R X c τ) :
    vecOf R X c (Function.update y τ z) =
      Function.update (vecOf R X c y) τ ⟨(c τ).symm (z : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z⟩ := by
  funext σ
  by_cases hσ : σ = τ
  · subst hσ
    simp [vecOf]
  · simp [vecOf, Function.update_of_ne hσ]

theorem phi_add [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (y : ∀ τ, Wsub R X c τ)
    (τ : D.what₂.Tau) (z₁ z₂ : Wsub R X c τ) :
    phi R X h t c S (Function.update y τ (z₁ + z₂)) =
      phi R X h t c S (Function.update y τ z₁) + phi R X h t c S (Function.update y τ z₂) := by
  funext x
  simp only [phi, ev_apply, vecOf_update, Pi.add_apply]
  have e : (⟨(c τ).symm ((z₁ + z₂ : Wsub R X c τ) : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (z₁ + z₂)⟩ :
      (MP R).sm τ) = ⟨(c τ).symm (z₁ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z₁⟩ +
        ⟨(c τ).symm (z₂ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z₂⟩ :=
    Subtype.ext (by simp)
  rw [e, S.map_update_add]
  rfl

theorem phi_smul [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (y : ∀ τ, Wsub R X c τ)
    (τ : D.what₂.Tau) (a : ℂ) (z : Wsub R X c τ) :
    phi R X h t c S (Function.update y τ (a • z)) =
      (starRingEnd ℂ a) • phi R X h t c S (Function.update y τ z) := by
  funext x
  simp only [phi, ev_apply, vecOf_update, Pi.smul_apply]
  have e : (⟨(c τ).symm ((a • z : Wsub R X c τ) : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (a • z)⟩ :
      (MP R).sm τ) = (starRingEnd ℂ a) • ⟨(c τ).symm (z : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z⟩ :=
    Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ])
  rw [e, S.map_update_smul]
  rfl

end GlobalTheory.RowEvalHHNorm

namespace GlobalTheory.RowEvalHHNorm

open GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem phi_memLp_integral (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (K : ℝ)
    (hK : ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) →
      MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)) 2 (muX X) ∧
      ∫ x, ‖ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)‖ ^ 2 ∂(muX X) = K)
    (y : ∀ τ, Wsub R X c τ) :
    MemLp (phi R X h t c S y) 2 (muX X) ∧
      ∫ x, ‖phi R X h t c S y x‖ ^ 2 ∂(muX X) = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  by_cases h0 : ∃ τ, (y τ : X.B.H (X.pl.symm τ)) = 0
  · obtain ⟨τ, hτ⟩ := h0
    have hv : vecOf R X c y τ = 0 := Subtype.ext (by simp [vecOf, hτ])
    have hz : phi R X h t c S y = 0 := by
      funext x
      simp only [phi, ev_apply, S.map_coord_zero τ hv]
      rfl
    have hp : ∏ σ, ‖(y σ : X.B.H (X.pl.symm σ))‖ ^ 2 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ τ) (by simp [hτ])
    rw [hz, hp]
    refine ⟨MeasureTheory.MemLp.zero, ?_⟩
    simp
  · push_neg at h0
    have hn : ∀ τ, ‖((c τ).symm (y τ : X.B.H (X.pl.symm τ)) : (MP R).H τ)‖ = ‖(y τ : X.B.H (X.pl.symm τ))‖ :=
      fun τ => LinearIsometryEquiv.norm_map _ _
    have hpos : ∀ τ, 0 < ‖(y τ : X.B.H (X.pl.symm τ))‖ := fun τ => norm_pos_iff.2 (h0 τ)
    let u : (MP R).Vec := fun τ => ((‖(y τ : X.B.H (X.pl.symm τ))‖⁻¹ : ℝ) : ℂ) • vecOf R X c y τ
    have hu : ∀ τ, ‖(u τ : (MP R).H τ)‖ = 1 := by
      intro τ
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      show |‖(y τ : X.B.H (X.pl.symm τ))‖⁻¹| * ‖((c τ).symm (y τ : X.B.H (X.pl.symm τ)) : (MP R).H τ)‖ = 1
      rw [hn, abs_of_pos (inv_pos.2 (hpos τ)), inv_mul_cancel₀ (hpos τ).ne']
    have hvec : vecOf R X c y = fun τ => ((‖(y τ : X.B.H (X.pl.symm τ))‖ : ℝ) : ℂ) • u τ := by
      funext τ
      apply Subtype.ext
      simp only [u, Submodule.coe_smul, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hpos τ).ne', Complex.ofReal_one, one_smul]
    set a : ℂ := ∏ τ, ((‖(y τ : X.B.H (X.pl.symm τ))‖ : ℝ) : ℂ) with ha
    have hphi : phi R X h t c S y = fun x => a * ev (MP R) u S
        (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) := by
      funext x
      simp only [phi, ev_apply]
      rw [hvec, S.map_smul_univ]
      rfl
    obtain ⟨hm, hi⟩ := hK u hu
    have hna : ‖a‖ = ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ := by
      rw [ha, norm_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hphi]
    refine ⟨hm.const_mul a, ?_⟩
    simp only [norm_mul, mul_pow]
    rw [integral_const_mul, hi, hna, Finset.prod_pow]
    ring

theorem evF_multilinear_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ∀ S ∈ EP R F, ∃ (f : MultilinearMap ℂ (fun τ => ↥(GlobalTheory.RowEvalHH.Wsub R X c τ)) (L2X X)) (K : ℝ), (∀ y, f y = GlobalTheory.RowEvalHH.evF R X h t c S y) ∧ ∀ y, ‖f y‖ ^ 2 = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM t c ht S hS
  obtain ⟨c0, -, hc0⟩ := GlobalTheory.EvalNormTransfer.evalTranslate_norm R F X h hL hG hM t ht
  set K : ℝ := c0 * (ipM (MP R) R.ν0 R.fd0 S S).re with hKdef
  have hK : ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) →
      MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)) 2 (muX X) ∧
      ∫ x, ‖ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)‖ ^ 2 ∂(muX X) = K := fun v₀ hv =>
    ⟨(hc0 v₀ hv S hS).1, (hc0 v₀ hv S hS).2.1⟩
  have hmem : ∀ y, MemLp (phi R X h t c S y) 2 (muX X) := fun y =>
    (phi_memLp_integral R X h t c S K hK y).1
  let L : (∀ τ, Wsub R X c τ) → L2X X := fun y => (hmem y).toLp (phi R X h t c S y)
  have hL_add : ∀ [DecidableEq D.what₂.Tau] (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau) (z₁ z₂ : Wsub R X c τ),
      L (Function.update y τ (z₁ + z₂)) = L (Function.update y τ z₁) + L (Function.update y τ z₂) := by
    intro _ y τ z₁ z₂
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (phi_add R X h t c S y τ z₁ z₂) x)
  have hL_smul : ∀ [DecidableEq D.what₂.Tau] (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau) (a : ℂ) (z : Wsub R X c τ),
      L (Function.update y τ (a • z)) = (starRingEnd ℂ a) • L (Function.update y τ z) := by
    intro _ y τ a z
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (phi_smul R X h t c S y τ a z) x)
  let f : MultilinearMap ℂ (fun τ => ↥(Wsub R X c τ)) (L2X X) :=
    { toFun := fun y => conjL (muX X) (L y)
      map_update_add' := fun y τ z₁ z₂ => by
        rw [hL_add, map_add]
      map_update_smul' := fun y τ a z => by
        rw [hL_smul, LinearIsometryEquiv.map_smulₛₗ, starRingEnd_self_apply] }
  refine ⟨f, K, fun y => ?_, fun y => ?_⟩
  · show conjL (muX X) (L y) = evF R X h t c S y
    unfold evF
    split
    · rfl
    · exact absurd (hmem y) ‹_›
  · show ‖conjL (muX X) (L y)‖ ^ 2 = _
    rw [LinearIsometryEquiv.norm_map, norm_sq_toLp_eq]
    exact (phi_memLp_integral R X h t c S K hK y).2

end GlobalTheory.RowEvalHHNorm
