import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ComplexPrincipalSeriesIrreducible
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NegNotMemSpecialLinearPartUnitaryOneOne

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.RealInd
open GlobalTheory.LeviFactor GlobalTheory.LeviFactor.Model

namespace GlobalTheory.Published.ComplexSeries

variable {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}

theorem isClosed_slPart (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) : IsClosed (slPart ε W : Set (UJ ε)) := by
  choose π hπ using fun i => (W i).subtype.exists_leftInverse_of_injective (W i).ker_subtype
  have e : ∀ i (g : UJ ε) (h : ∀ y ∈ W i, Matrix.toLin' (uMat g) y ∈ W i),
      (Matrix.toLin' (uMat g)).restrict h = π i ∘ₗ Matrix.toLin' (uMat g) ∘ₗ (W i).subtype := fun i g h => by
    ext y : 1
    exact (LinearMap.congr_fun (hπ i) ((Matrix.toLin' (uMat g)).restrict h y)).symm
  have hc : ∀ i, Continuous fun g : UJ ε => LinearMap.det (π i ∘ₗ Matrix.toLin' (uMat g) ∘ₗ (W i).subtype) := fun i => by
    let b := Module.finBasis ℂ (W i)
    simp only [← LinearMap.det_toMatrix b]
    refine Continuous.matrix_det (continuous_pi fun k => continuous_pi fun l => ?_)
    simp only [LinearMap.toMatrix_apply, LinearMap.comp_apply, Matrix.toLin'_apply]
    exact ((b.coord k ∘ₗ π i).continuous_of_finiteDimensional).comp (continuous_uMat.matrix_mulVec continuous_const)
  have : (slPart ε W : Set (UJ ε)) = (leviOne ε W : Set (UJ ε)) ∩
      (⋂ y : Fin n → ℂ, ⋂ _ : (∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0),
        {g | uMat g *ᵥ y - y ∈ W (Fin.last a)}) ∩
      ⋂ i, {g | LinearMap.det (π i ∘ₗ Matrix.toLin' (uMat g) ∘ₗ (W i).subtype) = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1, fun i => e i g (fun y hy => (h.1.1.1 i y hy).1) ▸ h.2 i _⟩,
      fun h => ⟨h.1, fun i k => e i g k ▸ h.2 i⟩⟩
  rw [this]
  refine ((isClosed_leviOne hW hj).inter (isClosed_iInter fun y => isClosed_iInter fun _ => ?_)).inter
    (isClosed_iInter fun i => isClosed_eq (hc i) continuous_const)
  exact (W _).closed_of_finiteDimensional.preimage
    ((continuous_uMat.matrix_mulVec continuous_const).sub continuous_const)

theorem exists_haar (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i) :
    ∃ μ : Measure ↥(KG ε ⊓ slPart ε W), μ.IsHaarMeasure ∧ IsProbabilityMeasure μ := by
  have hK : IsCompact (KG ε : Set (UJ ε)) := isCompact_iff_compactSpace.2 (instCompactKG n ε)
  have : CompactSpace ↥(KG ε ⊓ slPart ε W) := isCompact_iff_compactSpace.1 (hK.inter_right (isClosed_slPart hW hj))
  exact ⟨Measure.haarMeasure ⊤, inferInstance, ⟨Measure.haarMeasure_self⟩⟩

theorem exists_unit {b : ℕ} {W' : Flag n b} (hW' : IsIsoFlag ε (fun _ => 1) W') (S : Subgroup (UJ ε)) (s : Fin b → ℂ)
    (μ : Measure ↥(KG ε ⊓ S)) [IsProbabilityMeasure μ] {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}
    {ι : indFun S (fun _ => 1) W' (fun _ => (1 : ℂ →L[ℂ] ℂ)) s →ₗ[ℂ] X}
    (h : IsIndModel S (KG ε ⊓ S) μ _ ρ ι) : ∃ w : X, ‖w‖ = 1 := by
  classical
  obtain ⟨f, hf, h1, h2⟩ := exists_spherical hW' (fun _ => le_rfl) s
  obtain ⟨hc, hl⟩ := mem_indFun_top.1 hf
  have hm : (fun g => if g ∈ S then f g else 0) ∈ indFun S (fun _ => 1) W' (fun _ => (1 : ℂ →L[ℂ] ℂ)) s :=
    ⟨hc.continuousOn.congr fun g hg => if_pos hg, fun g hg => if_neg hg,
      fun u hu m hm x t ht a1 a2 a3 g hg => by
        dsimp only
        rw [if_pos (mul_mem (mul_mem (mul_mem a1 a2) a3) hg), if_pos hg, hl u hu m hm x t ht]⟩
  refine ⟨ι ⟨_, hm⟩, ?_⟩
  have := h.norm_sq ⟨_, hm⟩
  have e : ∀ k : ↥(KG ε ⊓ S), (if (k : UJ ε) ∈ S then f k else 0) = 1 := fun k => by
    rw [if_pos (show (k : UJ ε) ∈ S from k.2.2), ← one_mul k.1, h2 _ _ k.2.1, h1]
  simp only [e] at this
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by simpa using this)

def W4' : Flag 4 2 := ![⊥, Submodule.span ℂ {![1, 0, 1, 0]}, LinearMap.range emb]

theorem isIsotropicFlag_lines_unitary_two_two : IsIsoFlag e4 (fun _ => 1) W4' := by
  have h1 : Module.finrank ℂ (Submodule.span ℂ {(![1, 0, 1, 0] : Fin 4 → ℂ)}) = 1 :=
    finrank_span_singleton fun h => by simpa using congrFun h 0
  have hle : Submodule.span ℂ {(![1, 0, 1, 0] : Fin 4 → ℂ)} ≤ LinearMap.range emb :=
    (Submodule.span_singleton_le_iff_mem _ _).2 ⟨![1, 0], by ext i; fin_cases i <;> simp [emb]⟩
  refine ⟨rfl, Fin.monotone_iff_le_succ.2 fun i => ?_, fun i => ?_, isIsotropicFlag_siegel.2.2.2⟩
  · fin_cases i
    · exact bot_le
    · exact hle
  · fin_cases i
    · change Module.finrank ℂ (Submodule.span ℂ {(![1, 0, 1, 0] : Fin 4 → ℂ)}) =
        Module.finrank ℂ (⊥ : Submodule ℂ (Fin 4 → ℂ)) + 1
      rw [h1, finrank_bot]
    · change Module.finrank ℂ (LinearMap.range emb) =
        Module.finrank ℂ (Submodule.span ℂ {(![1, 0, 1, 0] : Fin 4 → ℂ)}) + 1
      rw [h1, finrank_siegel_flag]

theorem hypotheses_four : IsIsoFlag e4 ![2] W4 ∧ (∀ i, 1 ≤ (![2] : Fin 1 → ℕ) i) ∧ IsIsoFlag e4 (fun _ => 1) W4' ∧
    (∀ i, W4 i ∈ Set.range W4') ∧ W4' (Fin.last 2) = W4 (Fin.last 1) ∧
    IsURepOn (mats (leviOne e4 W4' ⊓ slPart e4 W4)) (fun _ => (1 : ℂ →L[ℂ] ℂ)) ∧
    (∃ μ : Measure ↥(KG e4 ⊓ slPart e4 W4), μ.IsHaarMeasure ∧ IsProbabilityMeasure μ) ∧ slPart e4 W4 ≠ ⊥ := by
  refine ⟨isIsotropicFlag_siegel, by simp, isIsotropicFlag_lines_unitary_two_two, fun i => ?_, rfl,
    ⟨⟨rfl, fun _ _ _ _ => rfl⟩, fun _ _ _ => rfl, fun _ => continuousOn_const⟩,
    exists_haar isIsotropicFlag_siegel (by simp), fun h => neg_mem_specialLinearPart_siegel.2 (Subgroup.mem_bot.1 (h ▸ neg_mem_specialLinearPart_siegel.1))⟩
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

theorem twistedTraceFormula_four_of_hypotheses (h : ComplexPrincipalSeriesIrreducible) (y : Fin 2 → ℝ) :
    ∃ (X : Type) (_ : NormedAddCommGroup X) (_ : InnerProductSpace ℂ X) (_ : CompleteSpace X)
      (ρ : Matrix (Fin 4) (Fin 4) ℂ → (X →L[ℂ] X)), IsIrredOn (mats (slPart e4 W4)) ρ ∧ ∃ w : X, ‖w‖ = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, ⟨μ, h7, h8⟩, -⟩ := hypotheses_four
  obtain ⟨X, _, _, _, ρ, ι, hm, hi⟩ := h 4 e4 1 _ W4 h1 h2 2 W4' h3 h4 h5 _ y h6 μ h7 h8
  exact ⟨X, _, _, inferInstance, ρ, hi, exists_unit h3 _ _ μ hm⟩

theorem conclusion_bot {b : ℕ} (W' : Flag n b) (S : Subgroup (UJ ε)) (hS : S = ⊥)
    (χ : Matrix (Fin n) (Fin n) ℂ → (ℂ →L[ℂ] ℂ)) (hχ : χ 1 = 1) (s : Fin b → ℂ) (hW' : IsIsoFlag ε (fun _ => 1) W')
    (μ : Measure ↥(KG ε ⊓ S)) [IsProbabilityMeasure μ] :
    ∃ ι : indFun S (fun _ => 1) W' χ s →ₗ[ℂ] ℂ,
      IsIndModel S (KG ε ⊓ S) μ _ (fun _ => 1) ι ∧ IsIrredOn (mats S) (fun _ => (1 : ℂ →L[ℂ] ℂ)) := by
  classical
  subst hS
  refine ⟨LinearMap.proj 1 ∘ₗ Submodule.subtype _, ⟨Function.Surjective.denseRange fun v =>
    ⟨⟨fun g => if g = 1 then v else 0, ?_, fun g hg => if_neg (by simpa using hg),
      fun u _ m _ x t ht h1 h2 h3 g hg => ?_⟩, by simp⟩, fun f => ?_, fun y hy f f' e => ?_⟩,
    fun S _ _ => eq_bot_or_eq_top S⟩
  · exact (continuousOn_const (c := v)).congr fun g hg => if_pos (by simpa using hg)
  · rw [Subgroup.mem_bot] at h1 h2 h3 hg
    subst h1 h2 h3 hg
    have hx : x = 0 := funext fun i => by
      have := ht.detOn_succ hW' i
      rw [uMat_one, detOn_one, detOn_one, one_mul, eq_comm, Real.exp_eq_one_iff] at this
      simpa using this
    simp [hx, pairing, uMat_one, hχ]
  · have : ∀ k : ↥(KG ε ⊓ ⊥), f.1 k = f.1 1 := fun k => by rw [Subgroup.mem_bot.1 k.2.2]
    simp [this]
  · rw [Subgroup.mem_bot] at hy
    simp [e, hy]

theorem pairing_rho_seven (x : ℝ) : pairing (fun _ : Fin 3 => 1) (rho 7 fun _ => 1) ![0, x, -x] = 2 * x := by
  have h1 : Finset.Iio (1 : Fin 3) = {0} := by decide
  have h2 : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
  simp [pairing, rho, Fin.sum_univ_three, h1, h2]
  ring

end GlobalTheory.Published.ComplexSeries

end
