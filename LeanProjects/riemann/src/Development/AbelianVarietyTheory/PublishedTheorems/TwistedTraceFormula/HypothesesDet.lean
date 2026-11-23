import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.TemperedSubrepresentationComplex
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ConclusionOfStepsOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NegNotMemSpecialLinearPartUnitaryOneOne

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open GlobalTheory.LeviFactor GlobalTheory.FlagMeas.Model
open scoped InnerProductSpace

namespace GlobalTheory.Published.TemperedComplex

variable {n a : ℕ} {ε : Fin n → Bool}

theorem isClosed_glPart {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) :
    IsClosed (glPart ε W : Set (UJ ε)) := by
  refine (isClosed_leviOne hW hj).inter ?_
  change IsClosed {g : UJ ε | ∀ y : Fin n → ℂ, (∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) →
    uMat g *ᵥ y - y ∈ W (Fin.last a)}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun y => isClosed_iInter fun _ =>
    (W _).closed_of_finiteDimensional.preimage ((continuous_uMat.matrix_mulVec continuous_const).sub continuous_const)

theorem exists_haar {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) :
    ∃ μ : Measure ↥(KG ε ⊓ glPart ε W), μ.IsHaarMeasure ∧ IsProbabilityMeasure μ := by
  have hK : IsCompact (KG ε : Set (UJ ε)) := isCompact_iff_compactSpace.2 (instCompactKG n ε)
  have : CompactSpace ↥(KG ε ⊓ glPart ε W) :=
    isCompact_iff_compactSpace.1 (hK.inter_right (isClosed_glPart hW hj))
  exact ⟨Measure.haarMeasure ⊤, inferInstance, ⟨Measure.haarMeasure_self⟩⟩

theorem exists_haar_glPart {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) :
    ∃ ν : Measure (glPart ε W), ν.IsHaarMeasure := by
  haveI : LocallyCompactSpace (glPart ε W) := (isClosed_glPart hW hj).locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

theorem isIndModel_self {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}
    (hσ : IsURepOn (mats (glPart ε W)) σ) (s : Fin a → ℂ) (μ : Measure ↥(KG ε ⊓ glPart ε W))
    [IsProbabilityMeasure μ] :
    IsIndModel (glPart ε W) (KG ε ⊓ glPart ε W) μ (indFun (glPart ε W) j W σ s) σ
      (LinearMap.proj 1 ∘ₗ Submodule.subtype _) := by
  classical
  have one : ∀ {u : UJ ε}, IsSplit ε W 0 u → u = 1 := fun hu => (existsUnique_isSplit hW 0).unique hu isSplit_one
  have hN : (1 : UJ ε) ∈ flagN ε W := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩
  have law : ∀ f ∈ indFun (glPart ε W) j W σ s, ∀ g ∈ glPart ε W, f g = σ (uMat g) (f 1) := fun f hf g hg => by
    simpa [pairing] using hf.2.2 1 hN g hg.1 0 1 isSplit_one (one_mem _) hg (one_mem _) 1 (one_mem _)
  refine ⟨Function.Surjective.denseRange fun v => ⟨⟨fun g => if g ∈ glPart ε W then σ (uMat g) v else 0,
    ?_, fun g hg => if_neg hg, fun u hu m _ x t ht h1 hm h3 g hg => ?_⟩, ?_⟩, fun f => ?_, fun y hy f f' e => ?_⟩
  · refine ((hσ.2.2 v).comp continuous_uMat.continuousOn fun g hg => ⟨g, hg, rfl⟩).congr fun g hg => if_pos hg
  · have hx : x = 0 := funext fun i => by
      have := ht.detOn_succ hW i
      rw [h3.1.2, h3.1.2, one_mul, eq_comm, Real.exp_eq_one_iff, mul_eq_zero] at this
      have hji := hj i
      exact this.resolve_left (by exact_mod_cast (by omega : j i ≠ 0))
    subst hx
    have hu1 : u = 1 := one ⟨h1.1.1, fun i y hy => by simpa using hu.1 i y hy, hu.2⟩
    rw [hu1, one ht, one_mul, mul_one]
    dsimp only
    rw [if_pos (mul_mem hm hg), if_pos hg, uMat_mul, hσ.1.2 _ ⟨m, hm, rfl⟩ _ ⟨g, hg, rfl⟩]
    simp [pairing]
  · simp [uMat_one, hσ.1.1, one_mem]
  · have : ∀ k : ↥(KG ε ⊓ glPart ε W), ‖f.1 k‖ = ‖f.1 1‖ := fun k => by
      rw [law _ f.2 _ k.2.2, hσ.2.1 _ ⟨_, k.2.2, rfl⟩]
    simp [this]
  · simpa [e] using (law _ f.2 y hy).symm

theorem conclusion_of_steps_one {W : Flag n a} (hW : IsIsoFlag ε (fun _ => 1) W)
    {π : Matrix (Fin n) (Fin n) ℂ → (ℂ →L[ℂ] ℂ)} (hπ : IsURepOn (mats (glPart ε W)) π) :
    ∃ (χ : Matrix (Fin n) (Fin n) ℂ → (ℂ →L[ℂ] ℂ)) (y : Fin a → ℝ),
      IsURepOn (mats (leviOne ε W ⊓ glPart ε W)) χ ∧
      ∀ μ : Measure ↥(KG ε ⊓ glPart ε W), μ.IsHaarMeasure → IsProbabilityMeasure μ →
        ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : InnerProductSpace ℂ X) (_ : CompleteSpace X)
          (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X))
          (ι : indFun (glPart ε W) (fun _ => 1) W χ (fun l => Complex.I * y l) →ₗ[ℂ] X),
          IsIndModel (glPart ε W) (KG ε ⊓ glPart ε W) μ _ ρ ι ∧
          ∃ T : ℂ →ₗᵢ[ℂ] X, ∀ g ∈ glPart ε W, ∀ v, T (π (uMat g) v) = ρ (uMat g) (T v) := by
  refine ⟨π, 0, by rwa [inf_eq_right.2 (glPart_le W)], fun μ _ _ => ⟨ℂ, _, _, inferInstance, π, _,
    isIndModel_self hW (fun _ => le_rfl) hπ _ μ, LinearIsometry.id, fun _ _ _ => rfl⟩⟩

theorem hypotheses_det : IsIsoFlag e2 (fun _ => 1) W2 ∧ glPart e2 W2 ≠ ⊥ ∧
    IsURepOn (mats (glPart e2 W2)) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧
    IsIrredOn (mats (glPart e2 W2)) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧
    ∃ ν : Measure (glPart e2 W2), ν.IsHaarMeasure ∧ ∀ v w : ℂ, ∀ r : ℝ, 0 < r →
      Integrable (fun g : glPart e2 W2 => ‖⟪v, ((uMat g.1).det • (1 : ℂ →L[ℂ] ℂ)) w⟫_ℂ‖ ^ (2 + r)) ν := by
  have hW : IsIsoFlag e2 (fun _ => 1) W2 := by
    convert isIsotropicFlag_unitary_one_one using 1
    funext i; rw [Subsingleton.elim i 0]; rfl
  have h := isURepOn_det (H := ℂ) e2
  have sub : mats (glPart e2 W2) ⊆ UJset e2 := by
    rintro _ ⟨g, -, rfl⟩; exact g.2
  refine ⟨hW, fun e => ?_, ⟨⟨h.1.1, fun x hx y hy => h.1.2 x (sub hx) y (sub hy)⟩, fun g hg => h.2.1 g (sub hg),
    fun v => (h.2.2 v).mono sub⟩, fun S _ _ => eq_bot_or_eq_top S, ?_⟩
  · have := GlobalTheory.LeviFactor.Model.neg_mem_generalLinearPart_unitary_one_one
    rw [e, Subgroup.mem_bot] at this
    exact GlobalTheory.LeviFactor.Model.neg_notMem_specialLinearPart_unitary_one_one (this ▸ one_mem _)
  · haveI : CompactSpace (glPart e2 W2) := isCompact_iff_compactSpace.1
      ((isCompact_iff_compactSpace.2 (instCompactKG 2 e2)).of_isClosed_subset (isClosed_glPart hW fun _ => le_rfl)
        ((glPart_le W2).trans levi_borel_le_compact))
    refine ⟨Measure.haar, inferInstance, fun v w r hr => ?_⟩
    refine Continuous.integrable_of_hasCompactSupport ?_ (isClosed_tsupport _).isCompact
    refine Continuous.rpow_const (Continuous.norm (continuous_const.inner ?_)) fun _ => Or.inr (by positivity)
    exact (h.2.2 w).comp_continuous (continuous_uMat.comp continuous_subtype_val) fun g => g.1.2

end GlobalTheory.Published.TemperedComplex

end
