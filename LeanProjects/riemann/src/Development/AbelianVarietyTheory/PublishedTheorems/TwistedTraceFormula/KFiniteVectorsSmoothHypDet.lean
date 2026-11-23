import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteVectorsSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwinesStatement
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding

noncomputable section

open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff

namespace GlobalTheory.KFinSmoothModel

section Avg

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_avg (ρ : G → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u)
    {w : G → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) :
    ∃ T : H →L[ℂ] H, ∀ u, T u = ∫ x, w x • ρ x u ∂μ := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun x : tsupport w => ρ x) fun u => by
    obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn (hρ u).continuousOn
    exact ⟨C, fun x => hC x x.2⟩
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ x, w x • ρ x u ∂μ
      map_add' := fun u v => by
        simp only [map_add, smul_add]
        exact integral_add (CompanionTheory.D.gk.admitted.Gard.integrable_w μ ρ hρ hw hc u)
          (CompanionTheory.D.gk.admitted.Gard.integrable_w μ ρ hρ hw hc v)
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  refine ⟨L.mkContinuous ((∫ x, ‖w x‖ ∂μ) * C) fun u => ?_, fun u => rfl⟩
  have hwi : Integrable (fun x => ‖w x‖) μ := (hw.integrable_of_hasCompactSupport hc).norm
  rw [mul_assoc, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall fun x => ?_)
  rw [norm_smul]
  by_cases hx : w x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (((ρ x).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hC ⟨x, subset_tsupport _ hx⟩) (norm_nonneg _))) (norm_nonneg _)

end Avg

section Garding

open PI.UpqRep CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_smooth_ext {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) σ)
    (hcont : ∀ v, ContinuousOn (fun g => σ g v) (UJset ε)) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y]
    (hY : ∀ T : H →L[ℂ] H, (∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u)) → ∀ y ∈ Y, T y ∈ Y) {v : H} (hv : v ∈ Y)
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] (γ : P → Matrix (Fin n) (Fin n) ℂ)
    (hγ : ∀ a b, ContDiff ℝ ∞ fun t => γ t a b) (hγU : ∀ t, γ t ∈ UJset ε) :
    ContDiff ℝ ∞ fun t => σ (γ t) v := by
  obtain ⟨h1, hm⟩ := hσ
  let ρ : UJ ε → H →L[ℂ] H := fun x => σ (toM x)
  have hρ : ∀ u, Continuous fun x => ρ x u := fun u =>
    (hcont u).comp_continuous emb_toM.continuous toM_mem
  have hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u) := fun x y u => by
    simp only [ρ, toM_mul, hm _ (toM_mem x) _ (toM_mem y), ContinuousLinearMap.comp_apply]
  have hρ1 : ∀ u, ρ 1 u = u := fun u => by simp only [ρ, toM_one, h1, one_apply_eq_self]
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close ρ hρ hρ1 Y
  have hVi : V⁻¹ ∈ 𝓝 (1 : UJ ε) := inv_mem_nhds_one _ hV
  rw [emb_toM.isInducing.nhds_eq_comap, mem_comap] at hVi
  obtain ⟨W, hW, hWV⟩ := hVi
  have hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩ := exists_bump (inter_mem hW hD)
  let w : UJ ε → ℝ := fun x => f (toM x⁻¹)
  have hw : Continuous w := hf.continuous.comp (emb_toM.continuous.comp continuous_inv)
  have hc : HasCompactSupport w := by
    refine HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_
    by_contra h
    exact hx (hfS _ h)
  have h0 : 0 ≤ w := fun x => hf0 _
  have hw1 : w 1 ≠ 0 := by simpa only [w, inv_one, toM_one] using hf1
  obtain ⟨T, hT⟩ := exists_avg (muG ε) ρ hρ hw hc
  have hTK : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    obtain ⟨k', rfl⟩ := exists_toM (inUJ_of_mem_Kset hk)
    rw [hT, hT]
    refine T_comm (muG ε) ρ hρ hmul hw hc h0 hw1 k' (fun x => ?_) u
    simp only [w, _root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.1, hfk _ hk.1]
  have hinj : ∀ y ∈ Y, T y = 0 → y = 0 := by
    intro y hy hTy
    rw [hT] at hTy
    refine eq_zero_of_alt_alt (muG ε) ρ hρ hw hc h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy
    have : x⁻¹ ∈ V⁻¹ := hWV (hSW (hfS _ hx)).1
    simpa using this
  obtain ⟨u, rfl⟩ := exists_preimage Y T (hY T hTK) hinj v hv
  have hγ' : ContDiff ℝ ∞ γ := contDiff_pi.2 fun a => contDiff_pi.2 fun b => hγ a b
  have := (contDiff_avg (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS).comp hγ'
  convert this using 1
  funext t
  obtain ⟨g', hg'⟩ := exists_toM (ε := ε) (hγU t)
  simp only [Function.comp_apply, ← hg']
  show ρ g' (T u) = _
  rw [hT, apply_alt (muG ε) ρ hρ hmul hw hc]
  simp only [w, _root_.mul_inv_rev, inv_inv, toM_mul]

end Garding

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.GKModule GlobalTheory.RealInd
open GlobalTheory.SmoothGlob (lieSet)

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_entry {n k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) a b :=
  (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp
    (GlobalTheory.GardingVec.contDiff_expProd Xs)

end

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smoothVec_of_kFin (h : IsAdmRep ε π) {v : H} (hv : IsKFin ε π v) : SmoothVec (lieSet ε) π v := by
  have hd : ∀ v, IsKFin ε π v → v ∈ ⨆ Λ, GlobalTheory.KFinDual.kIso ε π Λ :=
    GlobalTheory.KFinDual.decomp n ε H π (GlobalTheory.KFinDual.isURepOn_K h) (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H π h.1 h.2.1 h.2.2.1).1
  haveI : ∀ Λ, FiniteDimensional ℂ (GlobalTheory.KFinDual.kIso ε π Λ) := GlobalTheory.KFinDual.finiteDimensional_kIso h
  obtain ⟨s, hs⟩ := GlobalTheory.KFinDual.exists_finset hd v hv
  intro k Xs hX
  refine exists_smooth_ext h.1 h.2.1 (s.sup (GlobalTheory.KFinDual.kIso ε π)) (fun T hT y hy => ?_) hs _
    (contDiff_entry Xs) fun t => ?_
  · have : (s.sup (GlobalTheory.KFinDual.kIso ε π)).map (T : H →ₗ[ℂ] H) ≤ s.sup (GlobalTheory.KFinDual.kIso ε π) := by
      rw [Submodule.map_le_iff_le_comap]
      refine Finset.sup_le fun Λ hΛ => ?_
      rw [← Submodule.map_le_iff_le_comap]
      exact (GlobalTheory.KFinDual.map_kIso_le (fun k hk y _ => hT k hk y) Λ).trans (Finset.le_sup hΛ)
    exact this ⟨y, hy, rfl⟩
  · refine GlobalTheory.GardingVec.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) (hX i) _

def lieSub (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := lieSet ε
  zero_mem' := by simp [lieSet, inG]
  add_mem' := fun {X Y} (hX : inG ε X) (hY : inG ε Y) => by
    change inG ε (X + Y)
    unfold inG at *
    rw [conjTranspose_add, add_mul, mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := fun c X (hX : inG ε X) => by
    change inG ε (c • X)
    unfold inG at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]

theorem conj_mem_lieSet {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : X ∈ lieSet ε) :
    k * X * k⁻¹ ∈ lieSet ε := by
  have h1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
  have h2 : kᴴ * Jm ε = Jm ε * kᴴ := by
    have := congrArg conjTranspose hk.2
    simpa only [conjTranspose_mul, Jm_conjTranspose] using this.symm
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  change (k * X * k⁻¹)ᴴ * Jm ε + Jm ε * (k * X * k⁻¹) = 0
  rw [Matrix.inv_eq_right_inv h1]
  calc (k * X * kᴴ)ᴴ * Jm ε + Jm ε * (k * X * kᴴ) = k * Xᴴ * (kᴴ * Jm ε) + (Jm ε * k) * X * kᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = k * (Xᴴ * Jm ε + Jm ε * X) * kᴴ := by
        rw [h2, ← hk.2]; simp only [mul_add, add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', mul_zero, zero_mul]

theorem kFin_dRep (h : IsAdmRep ε π) {v : H} (hv : IsKFin ε π v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) : IsKFin ε π (dRep π X v) := by
  obtain ⟨S, hS, hvS, hSK⟩ := hv
  have sm : ∀ w : S, SmoothVec (lieSet ε) π (w : H) := fun w => smoothVec_of_kFin h ⟨S, hS, w.2, hSK⟩
  let B : lieSub ε →ₗ[ℝ] S →ₗ[ℝ] H := LinearMap.mk₂ ℝ (fun Y w => dRep π Y.1 w.1)
    (fun Y Z w => (GlobalTheory.GKLie.dRep_add_bracket h.1 (sm w) Y.2 Z.2).1)
    (fun c Y w => GlobalTheory.GKLie.dRep_smul π c Y.1 w.1)
    (fun Y w w' => GlobalTheory.GKLie.dRep_add_vec (sm w) (sm w') Y.2)
    (fun c Y w => by
      have := GlobalTheory.GKLie.dRep_smul_vec (sm w) Y.2 (c : ℂ)
      simpa only [Complex.coe_smul, Submodule.coe_smul_of_tower] using this)
  haveI : Module.Finite ℝ S := Module.Finite.trans ℂ S
  obtain ⟨t, ht⟩ : (LinearMap.range (TensorProduct.lift B)).FG := Module.Finite.iff_fg.1 inferInstance
  let A : Set H := {x | ∃ Y ∈ lieSet ε, ∃ w ∈ S, dRep π Y w = x}
  have hle : Submodule.span ℂ A ≤ Submodule.span ℂ (t : Set H) := by
    rw [← Submodule.span_span_of_tower ℝ ℂ (t : Set H), ht]
    refine Submodule.span_mono ?_
    rintro _ ⟨Y, hY, w, hw, rfl⟩
    exact ⟨(⟨Y, hY⟩ : lieSub ε) ⊗ₜ ⟨w, hw⟩, rfl⟩
  refine ⟨Submodule.span ℂ A, Submodule.finiteDimensional_of_le hle,
    Submodule.subset_span ⟨X, hX, v, hvS, rfl⟩, fun k hk x hx => ?_⟩
  have : Submodule.span ℂ A ≤ (Submodule.span ℂ A).comap (π k : H →ₗ[ℂ] H) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Y, hY, w, hw, rfl⟩
    exact Submodule.subset_span ⟨_, conj_mem_lieSet hk hY, _, hSK k hk w hw,
      GlobalTheory.T.derivedRep_conj_maxCompact_intertwines n ε H π h.1 k hk Y hY w (sm ⟨w, hw⟩)⟩
  exact this hx

end GlobalTheory.KFinSmoothModel

namespace GlobalTheory.Published

open GlobalTheory.KFinSmoothModel in

theorem kFiniteVectorsSmooth_holds : KFiniteVectorsSmooth := fun _ ε _ _ _ _ π h =>
  ⟨fun _ hv => smoothVec_of_kFin h hv, fun _ hv => hv, GlobalTheory.GKModule.isKStableOn_kFinVec ε π,
    fun _ hX _ hv => kFin_dRep h hv hX⟩

theorem kFiniteVectorsSmooth_hyp_det {n : ℕ} (ε : Fin n → Bool) :
    GlobalTheory.RealInd.IsAdmRep ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧
      GlobalTheory.GKModule.kFinVec ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) = ⊤ :=
  ⟨(GlobalTheory.RealInd.isIrrAdm_det ε).2.1, eq_top_iff.2 fun _ _ => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩⟩

end GlobalTheory.Published

end
