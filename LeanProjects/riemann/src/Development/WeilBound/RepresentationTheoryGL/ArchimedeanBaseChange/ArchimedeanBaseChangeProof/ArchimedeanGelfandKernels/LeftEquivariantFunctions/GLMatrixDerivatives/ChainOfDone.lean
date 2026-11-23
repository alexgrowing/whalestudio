import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfFin

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Done

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc PositivityTheory.RgBcC.LfSt.ChainPf.Ker PositivityTheory.RgBcC.LfSt.ChainPf.Gam PositivityTheory.RgBcC.LfSt.ChainPf.Top
  PositivityTheory.RgBcC.LfSt.ChainPf.Fin

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem chainOf'_of (hDC : DCinCE) (hP : ParamInt) (hA : ActDer) (hI : IBPAct) (hK : KapEquiv) (hU : Unimod)
    (hR : RCalc) (hL : LgFacts) : ChainOf' := by
  intro hWE _hWS hG hKZ n lam E Fr ε ι S Γ T hC _ _ μ _ k val τ hk
  haveI := FiniteDimensional.complete ℂ E.V
  have hDW : DCwave := PositivityTheory.RgBcC.LfSt.ChainOf2.dCwave_of hDC
  have hZ : ZopDC := PositivityTheory.RgBcC.LfSt.ChainOf2.zopDC
  obtain ⟨m, c, w, g, ks, hks, hsum, -⟩ := hk
  have hks1 : ∀ i, ContDiffOn ℝ ∞ (ks i) (GLs n) := fun i => (hks i).2.1
  have hkc1 : ∀ i, Cpt (ks i) := fun i => (hks i).2.2.1
  have hke1 : ∀ i, ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ks i (y * k₂.1) = ks i y * E.ρ k₂ := by
    intro i y hy k₂
    have := (hks i).2.2.2.1 y hy 1 k₂
    simpa using this

  have hsm : ContDiffOn ℝ ∞ k (GLs n) :=
    (ContDiffOn.sum fun i _ => (hks1 i).const_smul (c i)).congr fun y hy => hsum y hy
  have hcp : Cpt k := by
    choose R hR using hkc1
    refine ⟨∑ i, max (R i) 0, fun y hy hlt => ?_⟩
    rw [hsum y hy]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : R i ≤ ∑ j, max (R j) 0 :=
      (le_max_left _ _).trans (Finset.single_le_sum (f := fun j => max (R j) 0) (fun j _ => le_max_right _ _)
        (Finset.mem_univ i))
    rw [hR i y hy (lt_of_le_of_lt hle hlt), smul_zero]
  have hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂ := by
    intro y hy k₂
    rw [hsum _ (mul_mem_GLs hy (unitary_mem_GLs k₂)), hsum y hy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hke1 i y hy k₂, smul_mul_assoc]
  have hcont : ∀ i, ContinuousOn (ks i) (GLs n) := fun i => (hks1 i).continuousOn
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]

  let ΓE : E.V ≃L[ℂ] E.V := ContinuousLinearEquiv.equivOfInverse Γ Γ
    (fun v => by rw [← ContinuousLinearMap.mul_apply, hC.Γsq]; rfl)
    (fun v => by rw [← ContinuousLinearMap.mul_apply, hC.Γsq]; rfl)
  have hΓρ : ∀ k₀ : Matrix.unitaryGroup (Fin n) ℂ, Γ * E.ρ k₀ = E.ρ k₀ * Γ := by
    intro k₀
    have := hC.ΓFr k₀.1 (unitary_mem_GLs k₀)
    rwa [hC.onK] at this
  have hA' : ∀ (k₀ : Matrix.unitaryGroup (Fin n) ℂ) v, ΓE (E.ρ k₀ v) = E.ρ k₀ (ΓE v) := by
    intro k₀ v
    show Γ (E.ρ k₀ v) = E.ρ k₀ (Γ v)
    rw [← ContinuousLinearMap.mul_apply, hΓρ]
    rfl
  have hΓc : ∀ f ∈ CE E, act μ E k (fun x => Γ (f x)) 1 = Γ (act μ E k f 1) := by
    intro f hf
    have hfΓ : ContinuousOn (fun x => Γ (f x)) (GLs n) := continuousOn_const.clm_apply hf.1.continuousOn
    rw [act_sum hL μ E c ks k hsum hcont hkc1 _ hfΓ 1 h1, act_sum hL μ E c ks k hsum hcont hkc1 _ hf.1.continuousOn 1 h1,
      map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    exact act_equiv hWE μ E ΓE hA' (w i) (g i) (ks i) (hks i).2 f hf

  have hDc : ∀ f ∈ CE E, act μ E k (DC ε Fr f) 1 = DC ε Fr (act μ E k f) 1 := by
    intro f hf
    have hDf := hDC n lam E Fr ε ι S Γ T hC f hf
    have hsmooth : ∀ i, ContDiffOn ℝ ∞ (act μ E (ks i) f) (GLs n) := fun i =>
      (hA hU n μ E (ks i) f (hks1 i) (hkc1 i) hf.1).1
    have eqk : Set.EqOn (act μ E k f) (fun x => ∑ i, c i • act μ E (ks i) f x) (GLs n) := fun x hx =>
      act_sum hL μ E c ks k hsum hcont hkc1 f hf.1.continuousOn x hx
    rw [act_sum hL μ E c ks k hsum hcont hkc1 _ hDf.1.continuousOn 1 h1, dc_congr ε Fr (isOpen_GLs n) eqk h1,
      dc_sum ε Fr c _ fun i => ((hsmooth i).differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds h1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [act_dc hDW hP hZ hG hWE hC μ (w i) (g i) τ (hks i).1 (ks i) (hks i).2 f hf]
  intro y hy
  refine ⟨gamma_of_comm hKZ hL Γ hΓρ μ k hsm.continuousOn hke hΓc y hy, ?_⟩
  exact dc_of_comm hA hI hK hKZ hU hR hL hC μ k hsm hcp hke hDc y hy

end PositivityTheory.RgBcC.LfSt.ChainPf.Done
