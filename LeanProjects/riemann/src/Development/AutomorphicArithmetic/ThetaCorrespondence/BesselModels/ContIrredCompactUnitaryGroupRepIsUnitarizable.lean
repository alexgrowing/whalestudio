import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace UpperTheory.Lit.Bur.Unitarize

theorem continuousOn_of_dual {X F : Type} [TopologicalSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] {s : Set X} {f : X → F}
    (h : ∀ l : Module.Dual ℂ F, ContinuousOn (fun x => l (f x)) s) : ContinuousOn f s := by
  let b := Module.finBasis ℂ F
  have e : f = fun x => ∑ i, b.coord i (f x) • b i := by
    funext x
    exact (b.sum_repr (f x)).symm
  rw [e]
  exact continuousOn_finset_sum _ fun i _ => (h (b.coord i)).smul continuousOn_const

theorem exists_invariant_core_of_equiv {G W E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (e : W ≃ₗ[ℂ] E) (r : G → Module.End ℂ W) (h1 : r 1 = 1) (hm : ∀ a b, r (a * b) = r a * r b)
    (hc : ∀ (w : W) (l : Module.Dual ℂ W), Continuous fun g => l (r g w)) :
    ∃ c : InnerProductSpace.Core ℂ W, ∀ g x y, c.inner (r g x) (r g y) = c.inner x y := by
  let A : G → W → E := fun g x => e (r g⁻¹ x)
  have hA : ∀ x, Continuous fun g => A g x := fun x => by
    rw [← continuousOn_univ]
    refine continuousOn_of_dual fun l => ?_
    have h := hc x (l ∘ₗ (e : W →ₗ[ℂ] E))
    exact (h.comp continuous_inv).continuousOn
  let F : W → W → G → ℂ := fun x y g => ⟪A g x, A g y⟫_ℂ
  have hF : ∀ x y, Continuous (F x y) := fun x y => (hA x).inner (hA y)
  have hI : ∀ x y, Integrable (F x y) μ := fun x y =>
    (hF x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hxx : ∀ x, ∫ g, F x x g ∂μ = ((∫ g, ‖A g x‖ ^ 2 ∂μ : ℝ) : ℂ) := fun x => by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [F]
    rw [inner_self_eq_norm_sq_to_K]
    simp
  let core : PreInnerProductSpace.Core ℂ W :=
    { inner := fun x y => ∫ g, F x y g ∂μ
      conj_inner_symm := fun x y => by
        show conj (∫ g, F y x g ∂μ) = ∫ g, F x y g ∂μ
        rw [← integral_conj]
        simp only [F, inner_conj_symm]
      re_inner_nonneg := fun x => by
        show 0 ≤ RCLike.re (∫ g, F x x g ∂μ)
        rw [hxx]
        simpa using integral_nonneg fun g => by positivity
      add_left := fun x y z => by
        show ∫ g, F (x + y) z g ∂μ = ∫ g, F x z g ∂μ + ∫ g, F y z g ∂μ
        rw [← integral_add (hI x z) (hI y z)]
        simp only [F, A, map_add, inner_add_left]
      smul_left := fun x y a => by
        show ∫ g, F (a • x) y g ∂μ = conj a * ∫ g, F x y g ∂μ
        rw [← integral_const_mul]
        simp only [F, A, map_smul, inner_smul_left] }
  refine ⟨{ core with definite := fun x hx => ?_ }, fun h x y => ?_⟩
  · by_contra hx0
    have hpos := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ)
      (f := fun g => ‖A g x‖ ^ 2) (x := 1) ((hA x).norm.pow 2) (HasCompactSupport.of_compactSpace _)
      (fun g => by positivity) (by simpa [A, h1] using hx0)
    have h0 : ∫ g, F x x g ∂μ = 0 := hx
    rw [hxx] at h0
    exact hpos.ne' (by exact_mod_cast h0)
  · show ∫ g, F (r h x) (r h y) g ∂μ = ∫ g, F x y g ∂μ
    rw [← integral_mul_left_eq_self (F x y) h⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [F, A, _root_.mul_inv_rev, hm]

theorem exists_invariant_core {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (r : G → Module.End ℂ W) (h1 : r 1 = 1) (hm : ∀ a b, r (a * b) = r a * r b)
    (hc : ∀ (w : W) (l : Module.Dual ℂ W), Continuous fun g => l (r g w)) :
    ∃ c : InnerProductSpace.Core ℂ W, ∀ g x y, c.inner (r g x) (r g y) = c.inner x y :=
  exists_invariant_core_of_equiv μ
    (LinearEquiv.ofFinrankEq W (EuclideanSpace ℂ (Fin (Module.finrank ℂ W))) (by simp)) r h1 hm hc

theorem compactSpace_UJ_allPos (k : ℕ) : CompactSpace (PI.UpqRep.UJ (PI.UpqRep.allPos k)) := by
  have hemb := PI.UpqRep.isClosedEmbeddingMatrix k (PI.UpqRep.allPos k)
  rw [← isCompact_univ_iff, hemb.1.isEmbedding.isCompact_iff, Set.image_univ, hemb.2]
  have hc : IsCompact (Set.pi Set.univ fun _ : Fin k => Set.pi Set.univ fun _ : Fin k => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (X := Matrix (Fin k) (Fin k) ℂ) hc (hemb.2 ▸ hemb.1.isClosed_range) ?_
  intro g hg i _ j _
  have hu : g ∈ Matrix.unitaryGroup (Fin k) ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (PI.HwUniqW.mem_UJset_allPos.1 hg)
  simpa using entry_norm_bound_of_unitary hu i j

theorem unitarize : ∀ {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {π : Matrix (Fin k) (Fin k) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH 1) π), ∃ (Wp : Type) (_ : NormedAddCommGroup Wp) (_ : InnerProductSpace ℂ Wp) (_ : FiniteDimensional ℂ Wp) (ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)) (T : W ≃ₗ[ℂ] Wp), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ ∧ (∀ h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∀ w, T (π h w) = ρ h (T w)) ∧ ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro k W _ _ _ π hπ
  obtain ⟨⟨h1, hm⟩, hc, hi⟩ := hπ
  have hset : PI.UpqRep.UJset (PI.UpqRep.allPos k) = Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ) :=
    Set.ext fun h => PI.HwUniqW.mem_UJset_allPos.trans GlobalTheory.BesselMapOne.mem_UH_one.symm
  rw [hset]
  have hmem : ∀ g : PI.UpqRep.UJ (PI.UpqRep.allPos k), PI.UpqRep.umat g ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ) :=
    fun g => hset ▸ g.2
  have hlift : ∀ g ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∃ u : PI.UpqRep.UJ (PI.UpqRep.allPos k),
      PI.UpqRep.umat u = g := fun g hg => by
    have hg' : g ∈ Set.range (PI.UpqRep.coeMatrixAlt (PI.UpqRep.allPos k)) := by
      rw [PI.UpqRep.range_coeMatrix]
      exact hset.ge hg
    exact hg'
  haveI := compactSpace_UJ_allPos k
  obtain ⟨c, hinv⟩ := exists_invariant_core (PI.UpqRep.muG (PI.UpqRep.allPos k))
    (fun g => π (PI.UpqRep.umat g)) h1 (fun a b => hm _ (hmem a) _ (hmem b))
    (fun w l => (hc w l).comp_continuous (PI.UpqRep.continuous_coeMatrix _) hmem)
  letI : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℂ W _ _ _ c
  letI : InnerProductSpace ℂ W := InnerProductSpace.ofCore c.toCore
  refine ⟨W, inferInstance, inferInstance, ‹_›, fun g => LinearMap.toContinuousLinearMap (π g), LinearEquiv.refl ℂ W, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · ext v
    simp [h1]
  · intro a ha b hb
    ext v
    simp [hm a ha b hb]
  · intro g hg v
    obtain ⟨u, rfl⟩ := hlift g hg
    have := hinv u v v
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) v]
    exact congrArg (fun z : ℂ => Real.sqrt (RCLike.re z)) this
  · intro v
    exact continuousOn_of_dual fun l => hc v l
  · intro h _ w
    rfl
  · intro S hS
    exact hi S hS

end UpperTheory.Lit.Bur.Unitarize

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.contIrred_compactUnitaryGroup_rep_isUnitarizable : ∀ {k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {π : Matrix (Fin k) (Fin k) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH 1) π), ∃ (Wp : Type) (_ : NormedAddCommGroup Wp) (_ : InnerProductSpace ℂ Wp) (_ : FiniteDimensional ℂ Wp) (ρ : Matrix (Fin k) (Fin k) ℂ → (Wp →L[ℂ] Wp)) (T : W ≃ₗ[ℂ] Wp), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) ρ ∧ (∀ h ∈ Formalism.QuantumDeterminants.UH (1 : Matrix (Fin k) (Fin k) ℂ), ∀ w, T (π h w) = ρ h (T w)) ∧ ∀ S : Submodule ℂ Wp, (∀ g ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  first | exact @UpperTheory.Lit.Bur.Unitarize.unitarize | exact UpperTheory.Lit.Bur.Unitarize.unitarize | (intros; apply UpperTheory.Lit.Bur.Unitarize.unitarize <;> assumption)
