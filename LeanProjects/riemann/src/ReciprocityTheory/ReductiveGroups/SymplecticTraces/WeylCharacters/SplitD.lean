import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitB
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed

noncomputable section

open Matrix Finset TensorProduct

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

theorem sp_trace_piece {Λ' μ : Fin n → ℝ} (T : KType ε Λ') (T' : KType ε μ) (hμ : μ = Λ') (R : KRep ε)
    (S : Submodule ℂ R.V) (hS : S = ⊤) (φ : T'.V ≃ₗᵢ[ℂ] S)
    (hφ : ∀ (k : KG ε) (v : T'.V), (φ (T'.op k v) : R.V) = R.op k (φ v)) (k : KG ε) :
    LinearMap.trace ℂ T.V (T.op k : T.V →ₗ[ℂ] T.V) = LinearMap.trace ℂ R.V (R.op k : R.V →ₗ[ℂ] R.V) := by
  subst hμ hS
  obtain ⟨ψ, hψ, -, -⟩ := kType_unique T T'
  let Θ : T.V ≃ₗ[ℂ] R.V := ψ.toLinearEquiv ≪≫ₗ φ.toLinearEquiv ≪≫ₗ LinearEquiv.ofTop ⊤ rfl
  have hΘ : ∀ v, Θ (T.op k v) = R.op k (Θ v) := by
    intro v
    show ((φ (ψ (T.op k v)) : R.V)) = R.op k (φ (ψ v))
    rw [hψ, hφ]
  have e : (R.op k : R.V →ₗ[ℂ] R.V) = Θ.conj (T.op k : T.V →ₗ[ℂ] T.V) := by
    ext v
    rw [LinearEquiv.conj_apply_apply]
    show R.op k v = Θ (T.op k (Θ.symm v))
    rw [hΘ, LinearEquiv.apply_symm_apply]
  rw [e, LinearMap.trace_conj']

theorem sp_trace_of_rep {Λ' : Fin n → ℝ} (T : KType ε Λ') (R : KRep ε) (x : R.V) (hx : x ≠ 0)
    (hxw : Formalism.REAL.KHighest ε R.units Λ' x)
    (huniq : ∀ (μ : Fin n → ℝ) (y : R.V), y ≠ 0 → Formalism.REAL.KHighest ε R.units μ y → ∃ c : ℂ, y = c • x)
    (k : KG ε) :
    LinearMap.trace ℂ T.V (T.op k : T.V →ₗ[ℂ] T.V) = LinearMap.trace ℂ R.V (R.op k : R.V →ₗ[ℂ] R.V) := by
  obtain ⟨m, xs, μ, h1, h2, h3, -, -, h6⟩ := compRed n ε R
  choose c hc using fun i => huniq (μ i) (xs i) (h1 i).1 (h1 i).2
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h; apply (h1 i).1; rw [hc i, h, zero_smul]
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : x ∈ (⨆ i : Fin 0, Formalism.REAL.kSpan ε R.units (xs i)) := by rw [h3]; trivial
    rw [iSup_of_empty, Submodule.mem_bot] at this
    exact hx this
  have hm1 : m ≤ 1 := by
    by_contra hm
    have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have h := h2 _ _ hne (xs ⟨0, by omega⟩) (Formalism.REAL.mem_compact_span_self (ε := ε) (F := R.units) _)
      (xs ⟨1, by omega⟩) (Formalism.REAL.mem_compact_span_self (ε := ε) (F := R.units) _)
    rw [hc, hc, inner_smul_left, inner_smul_right] at h
    refine (mul_ne_zero ((map_ne_zero _).mpr (hc0 _)) (mul_ne_zero (hc0 _) (inner_self_ne_zero.mpr hx))) h
  obtain rfl : m = 1 := by omega
  have htop : Formalism.REAL.kSpan ε R.units (xs 0) = ⊤ := by rw [← h3, iSup_unique]; rfl
  have hμ : μ 0 = Λ' := by
    funext a
    have e1 := (h1 0).2.1 a
    have e2 := hxw.1 a
    have hne : xs 0 ≠ 0 := (h1 0).1
    rw [hc 0, map_smul, e2, smul_comm] at e1
    have e3 : ((μ 0 a : ℝ) : ℂ) • xs 0 = ((Λ' a : ℝ) : ℂ) • xs 0 := by rw [hc 0]; exact e1.symm
    exact_mod_cast smul_left_injective ℂ hne e3
  obtain ⟨T', φ, -, hφ, -, -⟩ := h6 0
  exact sp_trace_piece T T' hμ R _ htop φ hφ k

end ReciprocityTheory.ChartRestriction.TR.Weyl
