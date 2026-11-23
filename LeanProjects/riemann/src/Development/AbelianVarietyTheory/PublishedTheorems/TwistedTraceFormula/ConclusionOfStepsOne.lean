import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.TemperedSubrepresentation

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd

namespace GlobalTheory.Published.TemperedSub

variable {n a : ℕ} {ε : Fin n → Bool}

theorem exists_haar (D : Datum ε) :
    ∃ μ : Measure ↥(KG ε ⊓ D.M), μ.IsHaarMeasure ∧ IsProbabilityMeasure μ := by
  have hK : IsCompact (KG ε : Set (UJ ε)) := isCompact_iff_compactSpace.2 (instCompactKG n ε)
  have : CompactSpace ↥(KG ε ⊓ D.M) :=
    isCompact_iff_compactSpace.1 (hK.inter_right (isClosed_leviOne D.flag D.pos))
  exact ⟨Measure.haarMeasure ⊤, inferInstance, ⟨Measure.haarMeasure_self⟩⟩

theorem isIndModel_self {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}
    (hσ : IsURepOn (mats (leviOne ε W)) σ) (s : Fin a → ℂ) (μ : Measure ↥(KG ε ⊓ leviOne ε W))
    [IsProbabilityMeasure μ] :
    IsIndModel (leviOne ε W) (KG ε ⊓ leviOne ε W) μ (indFun (leviOne ε W) j W σ s) σ
      (LinearMap.proj 1 ∘ₗ Submodule.subtype _) := by
  classical
  have one : ∀ {u : UJ ε}, IsSplit ε W 0 u → u = 1 := fun hu => (existsUnique_isSplit hW 0).unique hu isSplit_one
  have hN : (1 : UJ ε) ∈ flagN ε W := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩
  have law : ∀ f ∈ indFun (leviOne ε W) j W σ s, ∀ g ∈ leviOne ε W, f g = σ (uMat g) (f 1) := fun f hf g hg => by
    simpa [pairing] using hf.2.2 1 hN g hg 0 1 isSplit_one (one_mem _) hg (one_mem _) 1 (one_mem _)
  refine ⟨Function.Surjective.denseRange fun v => ⟨⟨fun g => if g ∈ leviOne ε W then σ (uMat g) v else 0,
    ?_, fun g hg => if_neg hg, fun u hu m hm x t ht h1 _ h3 g hg => ?_⟩, ?_⟩, fun f => ?_, fun y hy f f' e => ?_⟩
  · refine ((hσ.2.2 v).comp continuous_uMat.continuousOn fun g hg => ⟨g, hg, rfl⟩).congr fun g hg => if_pos hg
  · have hx : x = 0 := funext fun i => by
      have := ht.detOn_succ hW i
      rw [h3.2, h3.2, one_mul, eq_comm, Real.exp_eq_one_iff, mul_eq_zero] at this
      have hji := hj i
      exact this.resolve_left (by exact_mod_cast (by omega : j i ≠ 0))
    subst hx
    have hu1 : u = 1 := one ⟨h1.1, fun i y hy => by simpa using hu.1 i y hy, hu.2⟩
    rw [hu1, one ht, one_mul, mul_one]
    dsimp only
    rw [if_pos (mul_mem hm hg), if_pos hg, uMat_mul, hσ.1.2 _ ⟨m, hm, rfl⟩ _ ⟨g, hg, rfl⟩]
    simp [pairing]
  · simp [uMat_one, hσ.1.1, one_mem]
  · have : ∀ k : ↥(KG ε ⊓ leviOne ε W), ‖f.1 k‖ = ‖f.1 1‖ := fun k => by
      rw [law _ f.2 _ k.2.2, hσ.2.1 _ ⟨_, k.2.2, rfl⟩]
    simp [this]
  · simpa [e] using (law _ f.2 y hy).symm

theorem conclusion_of_steps_one (D : Datum ε) (h : D.j = fun _ => 1) :
    ∃ (b : ℕ) (W' : Flag n b), IsIsoFlag ε (fun _ => 1) W' ∧ (∀ i, D.W i ∈ Set.range W') ∧
    ∃ (U : Type) (_ : NormedAddCommGroup U) (_ : InnerProductSpace ℂ U) (_ : CompleteSpace U)
      (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (y : Fin b → ℝ), IsIrrTempered (leviOne ε W') τ ∧
      ∀ μ : Measure ↥(KG ε ⊓ D.M), μ.IsHaarMeasure → IsProbabilityMeasure μ →
        ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
          (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X))
          (ι : indFun D.M (fun _ => 1) W' τ (fun l => Complex.I * y l) →ₗ[ℂ] X),
          IsIndModel D.M (KG ε ⊓ D.M) μ _ ρ ι →
          ∃ T : D.V →ₗᵢ[ℂ] X, ∀ m ∈ D.M, ∀ v, T (D.σ (uMat m) v) = ρ (uMat m) (T v) := by
  have hW : IsIsoFlag ε (fun _ => 1) D.W := h ▸ D.flag
  refine ⟨D.a, D.W, hW, fun i => ⟨i, rfl⟩, D.V, _, _, inferInstance, D.σ, 0, D.temp, fun μ _ _ X _ _ _ ρ ι hm => ?_⟩
  obtain ⟨U, -, hU⟩ := (isIndModel_self hW (fun _ => le_rfl) D.temp.2.2.1 _ μ).unique hm
    fun _ hf _ hy => indFun_mul_right hf hy
  exact ⟨U.toLinearIsometry, fun m hm v => hU _ ⟨m, hm, rfl⟩ v⟩

theorem sphericalDatum_steps (s : ℂ) : (sphericalDatum s).j = (fun _ => 1) ∧ (sphericalDatum s).a = 1 :=
  ⟨funext fun (i : Fin 1) => by rw [Subsingleton.elim i 0]; rfl, rfl⟩

theorem pairing_rho_four (x : ℝ) : pairing (fun _ : Fin 2 => 1) (rho 4 fun _ => 1) ![x, -x] = 2 * x := by
  have h : Finset.Iio (1 : Fin 2) = {0} := by decide
  have h0 : Finset.Iio (0 : Fin 2) = ∅ := by decide
  simp [pairing, rho, Fin.sum_univ_two, h, h0]
  ring

end GlobalTheory.Published.TemperedSub

end
