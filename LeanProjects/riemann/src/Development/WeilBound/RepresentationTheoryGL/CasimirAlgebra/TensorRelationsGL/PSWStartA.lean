import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]

def mono (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) :
    Γ → ℂ :=
  fun k => (∏ τ, (κ τ k).det ^ c τ) * ∏ p, κ (lab p) k (I p) (K p)

def Mono (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (H : Set ι) : Set (Γ → ℂ) :=
  {g | ∃ (m : ℕ) (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n), (∀ p, lab p ∈ H) ∧ g = mono κ lab c I K}

theorem exists_half (bar : ι → ι) (h1 : ∀ τ, bar (bar τ) = τ) (h2 : ∀ τ, bar τ ≠ τ) :
    ∃ H : Set ι, ∀ τ, τ ∈ H ↔ bar τ ∉ H := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨{τ | e τ < e (bar τ)}, fun τ => ?_⟩
  simp only [Set.mem_setOf_eq, h1, not_lt]
  have hne : e τ ≠ e (bar τ) := fun h => h2 τ (e.injective h).symm
  constructor
  · intro h
    exact h.le
  · intro h
    exact lt_of_le_of_ne h hne

variable {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

theorem det_ne (hK : IsKD bar κ) (τ : ι) (γ : Γ) : (κ τ γ).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (hK.unit τ γ)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem mono_cont (hK : IsKD bar κ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) :
    Continuous (mono κ lab c I K) := by
  have hent : ∀ τ, Continuous fun k => κ τ k :=
    fun τ => continuous_pi fun i => continuous_pi fun j => hK.cont τ i j
  unfold mono
  refine Continuous.mul ?_ ?_
  · refine continuous_finset_prod _ fun τ _ => ?_
    exact ((hent τ).matrix_det).zpow₀ (c τ) fun k => Or.inl (det_ne hK τ k)
  · exact continuous_finset_prod _ fun p _ => hK.cont (lab p) (I p) (K p)

theorem one_mem_Mono (H : Set ι) : (1 : Γ → ℂ) ∈ Mono κ H := by
  refine ⟨0, Fin.elim0, 0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
  funext k
  simp [mono]

theorem mul_mem_Mono (hK : IsKD bar κ) (H : Set ι) {g g' : Γ → ℂ} (hg : g ∈ Mono κ H) (hg' : g' ∈ Mono κ H) :
    g * g' ∈ Mono κ H := by
  obtain ⟨m1, l1, c1, I1, K1, hl1, rfl⟩ := hg
  obtain ⟨m2, l2, c2, I2, K2, hl2, rfl⟩ := hg'
  refine ⟨m1 + m2, Fin.append l1 l2, c1 + c2, Fin.append I1 I2, Fin.append K1 K2, ?_, ?_⟩
  · intro p
    refine Fin.addCases (fun i => ?_) (fun i => ?_) p
    · simpa [Fin.append_left] using hl1 i
    · simpa [Fin.append_right] using hl2 i
  · funext k
    simp only [mono, Pi.mul_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]
    rw [show (∏ τ, (κ τ k).det ^ (c1 τ + c2 τ)) =
        (∏ τ, (κ τ k).det ^ c1 τ) * ∏ τ, (κ τ k).det ^ c2 τ by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun τ _ => zpow_add₀ (det_ne hK τ k) _ _]
    ring

def monoAlg (hK : IsKD bar κ) (H : Set ι) : Subalgebra ℂ (Γ → ℂ) :=
  (Submodule.span ℂ (Mono κ H)).toSubalgebra (Submodule.subset_span (one_mem_Mono H)) (by
    intro x y hx hy
    have := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Submodule.subset_span (mul_mem_Mono hK H ha hb))

theorem integrable_of_cont [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : MeasureTheory.Measure Γ)
    [MeasureTheory.IsFiniteMeasure μ] {f : Γ → ℂ} (hf : Continuous f) : MeasureTheory.Integrable f μ := by
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem entry_mem (hK : IsKD bar κ) {H : Set ι} (hH : ∀ τ, τ ∈ H ↔ bar τ ∉ H) (τ : ι) (i j : Fin n) :
    (fun k => κ τ k i j) ∈ Submodule.span ℂ (Mono κ H) := by
  classical
  change (fun k => κ τ k i j) ∈ monoAlg hK H
  have hent : ∀ σ ∈ H, ∀ a b : Fin n, (fun k => κ σ k a b) ∈ monoAlg hK H := by
    intro σ hσ a b
    apply Submodule.subset_span
    refine ⟨1, fun _ => σ, 0, fun _ => a, fun _ => b, fun _ => hσ, ?_⟩
    funext k
    simp [mono]
  by_cases hτ : τ ∈ H
  · exact hent τ hτ i j
  · have hσ : bar τ ∈ H := by
      by_contra h
      exact hτ ((hH τ).2 h)
    have hinv : ∀ z : ℤ, (fun k => (κ (bar τ) k).det ^ z) ∈ monoAlg hK H := by
      intro z
      apply Submodule.subset_span
      refine ⟨0, Fin.elim0, Pi.single (bar τ) z, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
      funext k
      symm
      simp only [mono, Fin.prod_univ_zero, mul_one]
      rw [Finset.prod_eq_single (bar τ)]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hadj : (fun k => (κ (bar τ) k).adjugate j i) ∈ monoAlg hK H := by
      have hfun : (fun k => (κ (bar τ) k).adjugate j i) = ∑ p : Equiv.Perm (Fin n),
          (Equiv.Perm.sign p : ℤ) • ∏ r, (fun k => ((κ (bar τ) k).updateRow i (Pi.single j 1)) (p r) r) := by
        funext k
        simp [Matrix.adjugate_apply, Matrix.det_apply, Finset.sum_apply, Finset.prod_apply, Units.smul_def]
      rw [hfun]
      refine Subalgebra.sum_mem _ fun p _ => zsmul_mem (Subalgebra.prod_mem _ fun r _ => ?_) _
      by_cases h : p r = i
      · simp only [h, Matrix.updateRow_self]
        exact Subalgebra.algebraMap_mem (monoAlg hK H) ((Pi.single j (1 : ℂ) : Fin n → ℂ) r)
      · simp only [Matrix.updateRow_ne h]
        exact hent _ hσ _ _
    have hkey : (fun k => κ τ k i j) =
        (fun k => (κ (bar τ) k).det ^ (-1 : ℤ)) * (fun k => (κ (bar τ) k).adjugate j i) := by
      funext k
      have hinvM : (κ (bar τ) k)⁻¹ = (κ (bar τ) k)ᴴ := Matrix.inv_eq_right_inv (hK.unit (bar τ) k)
      have e1 : κ τ k i j = star (κ (bar τ) k i j) := by
        have := hK.conj (bar τ) k i j
        rwa [hK.invol] at this
      have e2 : star (κ (bar τ) k i j) = ((κ (bar τ) k)ᴴ) j i := by
        simp [Matrix.conjTranspose_apply]
      rw [Pi.mul_apply, e1, e2, ← hinvM]
      simp [Matrix.inv_def, Ring.inverse_eq_inv', _root_.zpow_neg_one]
    rw [hkey]
    exact Subalgebra.mul_mem _ (hinv (-1)) hadj

end SWS

end PositivityTheory.Rg.Cz

end
