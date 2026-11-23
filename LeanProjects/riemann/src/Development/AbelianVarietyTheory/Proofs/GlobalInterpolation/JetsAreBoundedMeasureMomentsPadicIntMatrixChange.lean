import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.MomN

def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zc_eq_zcHom {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) : zc x = zcHom q x := rfl

theorem zc_continuous' {q : ℕ} [Fact q.Prime] : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def linZ {q : ℕ} [Fact q.Prime] {κ κ' : Type} [Fintype κ] (a : κ' → κ → ℤ_[q]) :
    C(κ → ℤ_[q], κ' → ℤ_[q]) :=
  ⟨fun x i => ∑ j, a i j * x j, by fun_prop⟩

def pullCLM {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : C(Y, ℂ_[q]) →L[ℂ_[q]] C(X, ℂ_[q]) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.comp A
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp } 1 (fun f => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
        exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => f.norm_coe_le_norm (A x))

theorem pullCLM_norm_le {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) : ‖(pullCLM (q := q) A)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem pullCLM_apply {q : ℕ} [Fact q.Prime] {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (A : C(X, Y)) (f : C(Y, ℂ_[q])) : pullCLM A f = f.comp A := rfl

def monoC {q : ℕ} [Fact q.Prime] {κ : Type} {k : ℕ} (σ : Fin k → κ) : C(κ → ℤ_[q], ℂ_[q]) :=
  ⟨fun x => ∏ l, zc (x (σ l)), by
    refine continuous_finset_prod _ fun l _ => zc_continuous'.comp (continuous_apply (σ l))⟩

theorem momInt_push (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (v : κ → V) (w : κ' → V) (c : κ' → κ → ℂ) (a : κ' → κ → ℤ_[q])
    (G : V → ℂ) (hc : ∀ i j, ι (c i j) = zc (a i j)) (hw : ∀ i, w i = ∑ j, c i j • v j) (h : MomInt ι v G) :
    MomInt ι w G := by
  classical
  obtain ⟨μ, hμ, hm⟩ := h
  refine ⟨μ.comp (pullCLM (linZ a)), ?_, ?_⟩
  · calc ‖μ.comp (pullCLM (linZ a))‖ ≤ ‖μ‖ * ‖pullCLM (q := q) (linZ a)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hμ (pullCLM_norm_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro k j f hf
    have hfe : pullCLM (linZ a) f = ∑ σ : Fin k → κ, (∏ l, zc (a (j l) (σ l))) • monoC σ := by
      ext x
      rw [pullCLM_apply, ContinuousMap.comp_apply, hf]
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        monoC, ContinuousMap.coe_mk, linZ]
      simp only [zc_eq_zcHom, map_sum, map_mul]
      rw [Finset.prod_univ_sum]
      simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]
    have hd : iteratedFDeriv ℂ k G 0 (fun l => w (j l)) =
        ∑ σ : Fin k → κ, (∏ l, c (j l) (σ l)) • iteratedFDeriv ℂ k G 0 (fun l => v (σ l)) := by
      simp only [hw]
      rw [ContinuousMultilinearMap.map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      exact ContinuousMultilinearMap.map_smul_univ _ _ _
    rw [ContinuousLinearMap.comp_apply, hfe, hd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_eq_mul, map_mul, map_prod, map_smul, smul_eq_mul, ← hm k σ (monoC σ) (fun _ => rfl)]
    simp only [hc]

end GlobalTheory.MomN
