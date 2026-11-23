import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmoothCuspFormFrechetModerateGrowthRepStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFiniteDense

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.TypeSum

section WordCurve

variable {n : ℕ}

theorem dRep_fsum {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (w : ι → H) (hw : ∀ j, Sm ε σ (w j)) :
    dRep σ Z (∑ j ∈ s, c j • w j) = ∑ j ∈ s, c j • dRep σ Z (w j) := by
  classical
  have hl : ∀ Y ∈ [Z], Y ∈ lieSet ε := by simpa using hZ
  have hsm : ∀ t : Finset ι, Sm ε σ (∑ j ∈ t, c j • w j) := fun t =>
    (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).sum_mem fun j _ =>
      (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).smul_mem _ (hw j)
  induction s using Finset.induction_on with
  | empty =>
    have := Dw_smul h.1 hl (0 : ℂ) (x := (0 : H)) (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).zero_mem
    simp only [zero_smul, Dw, List.foldr_cons, List.foldr_nil] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have e1 := Dw_add h.1 hl ((GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).smul_mem (c a) (hw a)) (hsm s)
    have e2 := Dw_smul h.1 hl (c a) (hw a)
    simp only [Dw, List.foldr_cons, List.foldr_nil] at e1 e2
    rw [e1, e2, ih]

theorem exists_coord (ε : Fin n → Bool) : ∃ (d : ℕ) (B : Fin d → Mx n) (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)),
    (∀ i, B i ∈ lieSet ε) ∧ ∀ Y ∈ lieSet ε, Y = ∑ i, φ i Y • B i := by
  let b := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  choose g hg using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨_, fun i => b i, g, fun i => (b i).2, fun Y hY => ?_⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at e
  conv_lhs => rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := LinearMap.congr_fun (hg i) ⟨Y, hY⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [this]
  rfl

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem analyticAt_coord (X Y : Mx n) (φ : Mx n →ₗ[ℝ] ℝ) :
    AnalyticAt ℝ (fun t : ℝ => ((φ (NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) : ℝ) : ℂ)) 0 := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (t • X)) 0 :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const)
  have h2 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (-(t • X))) 0 :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const).neg
  have h3 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) 0 :=
    (h2.fun_mul analyticAt_const).fun_mul h1
  have h4 := ((LinearMap.toContinuousLinearMap φ).analyticAt _).comp h3
  exact (Complex.ofRealCLM.analyticAt _).comp h4

end

theorem wordCurve : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ → ∀ X : Matrix (Fin n) (Fin n) ℂ, X ∈ GlobalTheory.SmoothGlob.lieSet ε → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Y ∈ GlobalTheory.SmoothGlob.lieSet ε) → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℝ → ℂ) (w : Fin m → H), (∀ j, AnalyticAt ℝ (c j) 0) ∧ (∀ j, Formalism.MainNotions.S.IsKFin ε σ (w j)) ∧ ∀ t : ℝ, List.foldr (Formalism.L2.Theta.dRep σ) v (l.map fun Y => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) = ∑ j, c j t • w j := by
  intro n ε H _ _ _ σ h X hX l hl v hv
  obtain ⟨d, B, φ, hB, hφ⟩ := exists_coord (n := n) ε
  induction l with
  | nil => exact ⟨1, fun _ _ => 1, fun _ => v, fun _ => analyticAt_const, fun _ => hv, fun t => by simp⟩
  | cons Y l ih =>
    obtain ⟨m, c, w, hc, hw, he⟩ := ih (fun Z hZ => hl Z (List.mem_cons_of_mem _ hZ))
    have hY := hl Y List.mem_cons_self
    let A : ℝ → Mx n := fun t => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)
    have hA : ∀ t, A t ∈ lieSet ε := fun t => by
      show NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X) ∈ lieSet ε
      rw [Matrix.exp_neg]
      exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (exp_mem_UJ hX t) hY
    let e := (finProdFinEquiv (m := m) (n := d)).symm
    refine ⟨m * d, fun k t => c (e k).1 t * ((φ (e k).2 (A t) : ℝ) : ℂ),
      fun k => dRep σ (B (e k).2) (w (e k).1), fun k => (hc _).fun_mul (analyticAt_coord X Y _),
      fun k => isKFin_dRep n ε H σ h _ (hw _) _ (hB _), fun t => ?_⟩
    rw [List.map_cons, List.foldr_cons, he t]
    change dRep σ (A t) _ = _
    rw [dRep_fsum h (hA t) Finset.univ _ w (fun j => h.2.2.1 _ (hw j))]
    have hs : ∀ j, dRep σ (A t) (w j) = ∑ i, ((φ i (A t) : ℝ) : ℂ) • dRep σ (B i) (w j) := fun j => by
      conv_lhs => rw [hφ _ (hA t)]
      exact h.dRep_sum hB (h.2.2.1 _ (hw j)) _
    simp only [hs, Finset.smul_sum, smul_smul]
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv e _ _ fun k => rfl).symm

end WordCurve

theorem eq_zero_of_iteratedDeriv_eq_zero : ∀ f : ℝ → ℂ, AnalyticOnNhd ℝ f Set.univ → (∀ m : ℕ, iteratedDeriv m f 0 = 0) → ∀ t, f t = 0 := by
  intro f hf h0 t
  obtain ⟨p, r, hp⟩ := hf 0 trivial
  have hc : ∀ m (y : ℝ), p m (fun _ => y) = 0 := by
    intro m y
    have e1 := hp.factorial_smul 1 m
    rw [← iteratedDeriv_eq_iteratedFDeriv, h0 m] at e1
    have e2 : p m (fun _ => (1 : ℝ)) = 0 := by
      exact (smul_eq_zero.1 e1).resolve_left (Nat.factorial_ne_zero m)
    have e3 := (p m).map_smul_univ (fun _ => y) (fun _ => (1 : ℝ))
    simp only [smul_eq_mul, mul_one] at e3
    rw [e3, e2, smul_zero]
  have hev : f =ᶠ[nhds 0] 0 := by
    filter_upwards [EMetric.ball_mem_nhds (0 : ℝ) hp.r_pos] with y hy
    have := hp.hasSum (y := y) (by simpa using hy)
    simp only [hc, zero_add] at this
    exact (this.unique hasSum_zero).symm ▸ rfl
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ trivial hev trivial

section Coef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem analyticAt_coef (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    AnalyticAt ℝ (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) 0 := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := GlobalTheory.LowTypeDetermined.exists_factor (isUnit_Jm ε) h.1 hℓ
  have hsm : Sm ε σ v := h.2.2.1 v hv
  choose N c w hc hw he using fun i => wordCurve n ε H σ h X hX (S i) (hS i) v hv
  have key : ∀ t : ℝ, ℓ (σ (NormedSpace.exp (t • X)) v) =
      ∑ i, ∑ j, c i j t * Λ i (σ (NormedSpace.exp (t • X)) (w i j)) := by
    intro t
    have hg := exp_mem_UJ hX t
    rw [hΛ _ (hsm.translate h.1 hg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := Dw_translate h.1 hg hsm (hS i)
    have e2 : (NormedSpace.exp (t • X))⁻¹ = NormedSpace.exp (-(t • X)) := (Matrix.exp_neg _).symm
    simp only [Dw] at e1
    rw [e1, e2, he i t, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  have ha : ∀ i j, AnalyticAt ℝ (fun t : ℝ => Λ i (σ (NormedSpace.exp (t • X)) (w i j))) 0 := by
    intro i j
    have := ((hHC.analytic h.1 h.2.1 (hw i j)).clm ((Λ i).restrictScalars ℝ)).analytic_exp (g := 1)
      (one_mem_UJ ε) hX 0
    simpa only [one_mul, ContinuousLinearMap.coe_restrictScalars'] using this
  have hsum : AnalyticAt ℝ (fun t : ℝ => ∑ i, ∑ j, c i j t * Λ i (σ (NormedSpace.exp (t • X)) (w i j))) 0 := by
    exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => (hc i j).fun_mul (ha i j)
  exact hsum.congr (Filter.Eventually.of_forall fun t => (key t).symm)

theorem analyticOnNhd_coef (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    AnalyticOnNhd ℝ (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) Set.univ := by
  intro t₀ _
  have hg := exp_mem_UJ hX t₀
  have h1 := analyticAt_coef hHC h (sobCont_translate h.1 hℓ hg) hv hX
  have h2 : AnalyticAt ℝ (fun t : ℝ => t - t₀) t₀ := analyticAt_id.sub analyticAt_const
  have h3 := h1.comp_of_eq h2 (sub_self t₀)
  refine h3.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_def, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [← sigma_mul h.1 hg (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem hasDerivAt_coef1 (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {u : H} (hu : Sm ε σ u)
    {X : Mx n} (hX : X ∈ lieSet ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) (ℓ (σ (NormedSpace.exp (s • X)) (dRep σ X u))) s := by
  have hs := exp_mem_UJ hX s
  have h1 := h.hasDerivAt_sobFun ((sobFun_of_sobCont hℓ).translate h.1 hs) hu hX
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = ℓ (σ _ (σ _ u))
  rw [← sigma_mul h.1 hs (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem isKFin_iterate (h : Std ε σ) {X : Mx n} (hX : X ∈ lieSet ε) (m : ℕ) {u : H} (hu : IsKFin ε σ u) :
    IsKFin ε σ ((dRep σ X)^[m] u) := by
  induction m with
  | zero => exact hu
  | succ m ih => rw [Function.iterate_succ_apply']; exact isKFin_dRep n ε H σ h _ ih X hX

theorem iteratedDeriv_coef (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {X : Mx n}
    (hX : X ∈ lieSet ε) (m : ℕ) : ∀ u : H, IsKFin ε σ u →
    iteratedDeriv m (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) =
      fun t => ℓ (σ (NormedSpace.exp (t • X)) ((dRep σ X)^[m] u)) := by
  induction m with
  | zero => intro u _; simp
  | succ m ih =>
    intro u hu
    have hd : deriv (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) =
        fun t => ℓ (σ (NormedSpace.exp (t • X)) (dRep σ X u)) :=
      funext fun t => (hasDerivAt_coef1 h hℓ (h.2.2.1 u hu) hX t).deriv
    rw [iteratedDeriv_succ', hd, ih _ (isKFin_dRep n ε H σ h u hu X hX)]
    funext t
    rw [Function.iterate_succ_apply]

theorem coef_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) (h0 : ∀ u, IsKFin ε σ u → ℓ u = 0) {v : H} (hv : IsKFin ε σ v) {X : Mx n}
    (hX : X ∈ lieSet ε) (t : ℝ) : ℓ (σ (NormedSpace.exp (t • X)) v) = 0 := by
  refine eq_zero_of_iteratedDeriv_eq_zero _ (analyticOnNhd_coef hHC h hℓ hv hX) (fun m => ?_) t
  rw [iteratedDeriv_coef h hℓ hX m v hv]
  simp only [zero_smul, NormedSpace.exp_zero, sigma_one h.1]
  exact h0 _ (isKFin_iterate h hX m hv)

theorem orbit_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) (h0 : ∀ u, IsKFin ε σ u → ℓ u = 0) {v : H} (hv : IsKFin ε σ v) {g : Mx n}
    (hg : g ∈ UJset ε) : ℓ (σ g v) = 0 := by
  have hk := mul_exp_neg_polarLog_mem_compact (ε := ε) hg
  have hL' : polarLog g ∈ lieSet ε := (polarLog_mem_hermitian_part (ε := ε) hg).1
  have e : g = (g * NormedSpace.exp (-polarLog g)) * NormedSpace.exp ((1 : ℝ) • polarLog g) := by
    rw [one_smul]; exact polar_decomposition_eq
  rw [e, sigma_mul h.1 (K_le_UJ hk) (exp_mem_UJ hL' 1)]
  exact coef_eq_zero (ℓ := ℓ ∘ₗ (σ (g * NormedSpace.exp (-polarLog g)) : H →ₗ[ℂ] H)) hHC h
    (sobCont_translate h.1 hℓ (K_le_UJ hk)) (fun u hu => h0 _ (isKFin_translate hu hk)) hv hL' 1

end Coef

theorem eq_zero_of_kFin : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ℓ w = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  intro hHC D V S M τ ℓ hℓ h0 w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := std_of_isDS hHC (M.ds τ)
  have hℓ' : Sobolev₂ (lieSet (M.ε τ)) (M.σ τ) ℓ :=
    GlobalTheory.SmoothCyclic.sobCont_transport (M.fr_unit τ) (M.fr_gram τ) hℓ
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
  have hw' : Sm (M.ε τ) (M.σ τ) w := (GlobalTheory.SmoothCyclic.sm_eq M τ).le hw
  exact h.eq_zero_of_orbit hℓ' (h.2.2.1 a ha) ha0
    (fun g hg => orbit_eq_zero hHC h hℓ' (fun u hu => h0 u hu) ha hg) hw'

end GlobalTheory.KFiniteDense
