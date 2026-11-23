import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AvgFam

section Compact

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsFiniteMeasure μ]

theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

def intCLM : C(K, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ k, f k ∂μ
      map_add' := fun f g => integral_add (integrable_of_continuous μ f.continuous)
        (integrable_of_continuous μ g.continuous)
      map_smul' := fun c f => integral_smul c _ }
    (μ.real Set.univ) fun f => by
      rw [mul_comm]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k => f.norm_coe_le_norm k)

theorem continuous_avg {Y : Type} [TopologicalSpace Y] {F : K → Y → ℂ}
    (hF : Continuous fun p : K × Y => F p.1 p.2) : Continuous fun x => ∫ k, F k x ∂μ := by
  let Φ : C(Y × K, ℂ) := ⟨fun p => F p.2 p.1, hF.comp continuous_swap⟩
  exact (intCLM μ).continuous.comp Φ.curry.continuous

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem hasDerivAt_avg (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {F : K → GA D V → ℂ} (hF : ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V)
    (hFc : ∀ x, Continuous fun k => F k x)
    (hGc : Continuous fun p : K × GA D V => Rder θ V τ X (F p.1) p.2) (g : GA D V) :
    HasDerivAt (fun t : ℝ => ∫ k, F k (g * oneP θ V τ X t) ∂μ) (∫ k, Rder θ V τ X (F k) g ∂μ) 0 := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hc1 : Continuous fun p : K × ℝ => Rder θ V τ X (F p.1) (g * oneP θ V τ X p.2) :=
    hGc.comp (continuous_fst.prodMk (continuous_const.mul ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).comp continuous_snd)))
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn
    hc1.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun t k => F k (g * oneP θ V τ X t))
    (F' := fun t k => Rder θ V τ X (F k) (g * oneP θ V τ X t)) (x₀ := 0) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds (0 : ℝ) zero_lt_one)
    (Filter.Eventually.of_forall fun t => (hFc _).aestronglyMeasurable)
    (integrable_of_continuous μ (hFc _))
    ((hc1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun k t ht => hC (k, t) ⟨Set.mem_univ _, ht⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k t _ =>
      GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder (hF k) hX) g t)
  have e := key.2
  simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at e
  exact e

end Compact

theorem avg_closed : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam (D := D) θ → ∀ (V : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Submodule ℂ (K → GA D V → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × GA D V => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, F k ∈ GlobalTheory.Mem.AutSpace.SmFun θ V) → (∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, (fun k => Rder θ V τ X (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, Continuous (fun x => ∫ k, F k x ∂μ) ∧ (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ) ∧ ∀ τ j, gelf θ V τ j (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, gelf θ V τ j (F k) x ∂μ := by
  intro D θ hθ V K _ _ _ _ μ _ 𝒢 hc hsm hder
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : ∀ F ∈ 𝒢, ∀ x, Continuous fun k => F k x := fun F hF x =>
    (hc F hF).comp (continuous_id.prodMk continuous_const)
  have hint : ∀ F ∈ 𝒢, ∀ x, Integrable (fun k => F k x) μ := fun F hF x =>
    integrable_of_continuous μ (hk F hF x)
  have hd : ∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ, ∀ g, HasDerivAt (fun t : ℝ => ∫ k, F k (g * oneP θ V τ X t) ∂μ)
      (∫ k, Rder θ V τ X (F k) g ∂μ) 0 := fun F hF τ X hX g =>
    hasDerivAt_avg μ hθ hX (hsm F hF) (hk F hF) (hc _ (hder F hF τ X hX)) g
  have hR : ∀ F ∈ 𝒢, ∀ τ, ∀ X ∈ lieAt V τ,
      Rder θ V τ X (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, Rder θ V τ X (F k) x ∂μ :=
    fun F hF τ X hX => funext fun g => (hd F hF τ X hX g).deriv
  have hSm : ∀ F ∈ 𝒢, (fun x => ∫ k, F k x ∂μ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := by
    intro F hF
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V {φ | ∃ F ∈ 𝒢, φ = fun x => ∫ k, F k x ∂μ} ?_ ?_ _
      ⟨F, hF, rfl⟩
    · rintro _ ⟨F, hF, rfl⟩
      exact continuous_avg μ (hc F hF)
    · rintro _ ⟨F, hF, rfl⟩ τ X hX
      exact ⟨_, ⟨_, hder F hF τ X hX, rfl⟩, hd F hF τ X hX⟩
  have hW : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      ∀ F ∈ 𝒢, (fun k => l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) ∈ 𝒢 ∧
        l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun x => ∫ k, F k x ∂μ) =
          fun x => ∫ k, (l.foldr (fun p f => Rder θ V p.1 p.2 f) (F k)) x ∂μ := by
    intro l hl F hF
    induction l with
    | nil => exact ⟨hF, rfl⟩
    | cons p l ih =>
      obtain ⟨h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
      have hp := hl p List.mem_cons_self
      refine ⟨hder _ h1 p.1 p.2 hp, ?_⟩
      simp only [List.foldr_cons]
      rw [h2]
      exact hR _ h1 p.1 p.2 hp
  have hC : ∀ F ∈ 𝒢, ∀ τ Z, (fun k => RderC θ V τ Z (F k)) ∈ 𝒢 ∧
      RderC θ V τ Z (fun x => ∫ k, F k x ∂μ) = fun x => ∫ k, RderC θ V τ Z (F k) x ∂μ := by
    intro F hF τ Z
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have m1 := hder F hF τ _ h1
    have m2 := hder F hF τ _ h2
    have e : (fun k => RderC θ V τ Z (F k)) = (fun k => Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) (F k)) +
        Complex.I • (fun k => Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) (F k)) := rfl
    refine ⟨e ▸ add_mem m1 (Submodule.smul_mem _ _ m2), ?_⟩
    have i1 := hint _ m1
    have i2 := hint _ m2
    simp only [RderC]
    rw [hR F hF τ _ h1, hR F hF τ _ h2]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i1 x) ((i2 x).const_mul _), integral_const_mul]
  have hL : ∀ τ (L : List ((GA D V → ℂ) → GA D V → ℂ)), (∀ f ∈ L, ∃ Z, f = RderC θ V τ Z) → ∀ F ∈ 𝒢,
      (fun k => L.foldr (fun f acc => f acc) (F k)) ∈ 𝒢 ∧
        L.foldr (fun f acc => f acc) (fun x => ∫ k, F k x ∂μ) =
          fun x => ∫ k, (L.foldr (fun f acc => f acc) (F k)) x ∂μ := by
    intro τ L hLZ F hF
    induction L with
    | nil => exact ⟨hF, rfl⟩
    | cons f L ih =>
      obtain ⟨h1, h2⟩ := ih fun q hq => hLZ q (List.mem_cons_of_mem _ hq)
      obtain ⟨Z, rfl⟩ := hLZ f List.mem_cons_self
      refine ⟨(hC _ h1 τ Z).1, ?_⟩
      simp only [List.foldr_cons]
      rw [h2]
      exact (hC _ h1 τ Z).2
  intro F hF
  refine ⟨continuous_avg μ (hc F hF), hSm F hF, fun l hl => (hW l hl F hF).2, fun τ j => ?_⟩
  have hmem : ∀ idx : Fin (j + 1) → Fin V.rank, ∀ f ∈ List.ofFn (fun a : Fin (j + 1) =>
      RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)), ∃ Z, f = RderC θ V τ Z := by
    intro idx f hf
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
    exact ⟨_, rfl⟩
  simp only [gelf]
  rw [Finset.sum_congr rfl fun idx _ => (hL τ _ (hmem idx) F hF).2]
  funext x
  simp only [Finset.sum_apply]
  rw [integral_finset_sum _ fun idx _ => hint _ (hL τ _ (hmem idx) F hF).1 x]

end GlobalTheory.AvgFam

end
