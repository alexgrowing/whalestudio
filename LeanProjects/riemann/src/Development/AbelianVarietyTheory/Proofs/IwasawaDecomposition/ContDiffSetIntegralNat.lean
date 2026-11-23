import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasFDerivAtSetIntegral

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology

namespace GlobalTheory.GardingVec

theorem contDiff_setIntegral_nat {X P E : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {a : X → E} (ha : Continuous a)
    (m : ℕ) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ψ : P × E → F),
      ContDiff ℝ ∞ Ψ → ContDiff ℝ m fun p => ∫ x in K, Ψ (p, a x) ∂μ := by
  first
  | exact @_root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral
  | exact _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral
  | (apply _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral ..)

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_list_prod {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (l : List (P → Matrix (Fin n) (Fin n) ℂ)) (h : ∀ f ∈ l, ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => (l.map fun f => f p).prod := by
  induction l with
  | nil => simpa using contDiff_const
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))

theorem contDiff_expProd {n k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
  have := contDiff_list_prod (List.ofFn fun i => fun t : Fin k → ℝ => NormedSpace.exp (t i • Xs i)) (by
    intro f hf
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    have h1 : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact h1.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const))
  simpa [List.map_ofFn, Function.comp_def] using this

theorem contDiff_conjTranspose {n : ℕ} : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => xᴴ
      map_add' := fun x y => conjTranspose_add x y
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  exact (LinearMap.toContinuousLinearMap L).contDiff

open Formalism.MainNotions.S in

theorem exists_garding {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) :
    ∃ v : H, v ≠ 0 ∧ ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ x →
      (∀ t, x t ∈ UJset ε) → ContDiff ℝ ∞ fun t => σ (x t) v := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set μ := Formalism.REAL.muG ε
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hcont w).comp_continuous hu hmem
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := hmem 1
  have hnb : {g | ‖σ g w - w‖ < ‖w‖ / 2} ∈ 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hcont w 1 hone) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [h1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφU, hφc, hφ, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hu
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  refine ⟨∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ, ?_, ?_⟩
  · intro h0
    have e1 : ∫ g : Formalism.REAL.UJ ε, (φ (umat g) • σ (umat g) w - φ (umat g) • w) ∂μ
        = -((∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ) • w) := by
      rw [integral_sub hint (hψi.smul_const w), h0, integral_smul_const, zero_sub]
    have e2 : ‖∫ g : Formalism.REAL.UJ ε, (φ (umat g) • σ (umat g) w - φ (umat g) • w) ∂μ‖
        ≤ ∫ g : Formalism.REAL.UJ ε, φ (umat g) * (‖w‖ / 2) ∂μ := by
      refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : φ (umat g) = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs ⟨hφU (subset_tsupport _ hg), hmem g⟩)) (hφ0 _)
    rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at e2
    nlinarith [mul_pos hpos hwpos]
  · intro k x hx hxG
    let y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => Formalism.REAL.Jm ε * (x t)ᴴ * Formalism.REAL.Jm ε
    have hy : ContDiff ℝ ∞ y := (contDiff_const.mul (contDiff_conjTranspose.comp hx)).mul contDiff_const
    have hyx : ∀ t, y t * x t = 1 := fun t => by
      have h : (x t)ᴴ * Formalism.REAL.Jm ε * x t = Formalism.REAL.Jm ε := hxG t
      calc y t * x t = Formalism.REAL.Jm ε * ((x t)ᴴ * Formalism.REAL.Jm ε * x t) := by simp only [y, Matrix.mul_assoc]
        _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]
    have hxy : ∀ t, x t * y t = 1 := fun t => mul_eq_one_comm.1 (hyx t)
    have hform : ∀ t, σ (x t) (∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ)
        = ∫ g : Formalism.REAL.UJ ε, φ (y t * umat g) • σ (umat g) w ∂μ := by
      intro t
      obtain ⟨z, hz⟩ : x t ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
        rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact hxG t
      have hz' : umat z = x t := hz
      rw [← ContinuousLinearMap.integral_comp_comm _ hint,
        ← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => φ (y t * umat g) • σ (umat g) w) z]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have e : umat (z * g) = x t * umat g := by rw [← hz']; rfl
      simp only [e]
      rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, hmul _ (hxG t) _ (hmem g),
        ContinuousLinearMap.map_smul_of_tower]
      rfl
    simp only [hform]
    refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
    have hC : IsCompact (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1) (tsupport φ)) :=
      ((isCompact_closedBall t₀ 1).image hx.continuous).mul hφc
    have hK := hemb.isCompact_preimage hC
    have hs : ContDiff ℝ ∞ fun t => ∫ g in (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹'
        (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1) (tsupport φ)),
        φ (y t * umat g) • σ (umat g) w ∂μ :=
      contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
        (fun z : (Fin k → ℝ) × (Matrix (Fin n) (Fin n) ℂ × H) => φ (y z.1 * z.2.1) • z.2.2)
        ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
          (contDiff_snd.comp contDiff_snd))
    refine hs.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    refine hg ⟨x t, ⟨t, ht, rfl⟩, y t * umat g, subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
    show x t * (y t * umat g) = umat g
    rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]

theorem conj_mem {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg' : gᴴ * G * g = G) :
    P * g * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [h, hg', ← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem exp_mem {n : ℕ} {G X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (hX : Xᴴ * G + G * X = 0) (t : ℝ) :
    (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G := by
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹ := by
    have h2 : Xᴴ = G * (-X) * G⁻¹ := by
      rw [Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
        Matrix.mul_one]
    rw [conjTranspose_smul, h2]
    simp
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp (t • X)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem list_prod_mem {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (l : List (Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ g ∈ l, gᴴ * G * g = G) : l.prodᴴ * G * l.prod = G := by
  induction l with
  | nil => simp
  | cons g l ih =>
    have h1 := h g (by simp)
    have h2 := ih fun g hg => h g (by simp [hg])
    rw [List.prod_cons, conjTranspose_mul]
    calc l.prodᴴ * gᴴ * G * (g * l.prod) = l.prodᴴ * (gᴴ * G * g) * l.prod := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]

theorem exists_smoothVec {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    ∃ v : H, v ≠ 0 ∧ Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  obtain ⟨v, hv, hs⟩ := exists_garding hσ
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  refine ⟨v, hv, fun k Xs hX => hs k _ ((contDiff_const.mul (contDiff_expProd Xs)).mul contDiff_const) fun t => ?_⟩
  refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sm_ne_bot (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ ≠ ⊥ := by
  obtain ⟨h1, h2, h3, -⟩ := M.ds τ
  obtain ⟨v, hv, hs⟩ := exists_smoothVec h3 (M.fr_unit τ) (M.fr_gram τ)
  exact (Submodule.ne_bot_iff _).2 ⟨v, Submodule.subset_span hs, hv⟩

end GlobalTheory.GardingVec
