import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

noncomputable section

open Finset Matrix MeasureTheory
open scoped ContDiff NNReal ENNReal

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Smooth

variable {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem puniq_smooth_add_smul {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f)
    (hf' : Formalism.REAL.SmoothOnGV ε f') (c : ℂ) : Formalism.REAL.SmoothOnGV ε (fun x => f x + c • f' x) := by
  intro g₀ hg
  obtain ⟨U₁, F₁, o₁, m₁, c₁, e₁⟩ := hf g₀ hg
  obtain ⟨U₂, F₂, o₂, m₂, c₂, e₂⟩ := hf' g₀ hg
  refine ⟨U₁ ∩ U₂, fun x => F₁ x + c • F₂ x, o₁.inter o₂, ⟨m₁, m₂⟩,
    (c₁.mono Set.inter_subset_left).add ((c₂.mono Set.inter_subset_right).const_smul c), ?_⟩
  intro g hgU hgJ
  dsimp only
  rw [e₁ g hgU.1 hgJ, e₂ g hgU.2 hgJ]

theorem puniq_rdV_congr {φ ψ : Matrix (Fin n) (Fin n) ℂ → E} (hφ : Formalism.REAL.SmoothOnGV ε φ)
    (he : ∀ x, Formalism.REAL.inUJ ε x → ψ x = φ x) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (hX : Formalism.REAL.inG ε X) : Formalism.REAL.RdV X ψ g = Formalism.REAL.RdV X φ g := by
  have hm : ∀ t : ℝ, Formalism.REAL.inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) := by
    intro t
    have h2 := Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t
    unfold Formalism.REAL.inUJ at hg h2 ⊢
    calc (g * NormedSpace.exp ((t : ℂ) • X))ᴴ * Formalism.REAL.Jm ε * (g * NormedSpace.exp ((t : ℂ) • X))
        = (NormedSpace.exp ((t : ℂ) • X))ᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * NormedSpace.exp ((t : ℂ) • X) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hg, h2]
  show deriv (fun t : ℝ => ψ (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X))) 0
  congr 1
  funext t
  exact he _ (hm t)

theorem puniq_eabV_congr {φ ψ : Matrix (Fin n) (Fin n) ℂ → E} (hφ : Formalism.REAL.SmoothOnGV ε φ)
    (he : ∀ x, Formalism.REAL.inUJ ε x → ψ x = φ x) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (a b : Fin n) : Formalism.REAL.EabV ε a b ψ g = Formalism.REAL.EabV ε a b φ g := by
  have hc := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  simp only [Formalism.REAL.EabV, Formalism.REAL.EcV]
  rw [puniq_rdV_congr hφ he hg hc.1, puniq_rdV_congr hφ he hg hc.2.1]

theorem puniq_eabV_lin {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f)
    (hf' : Formalism.REAL.SmoothOnGV ε f') (c : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (a b : Fin n) :
    Formalism.REAL.EabV ε a b (fun x => f x + c • f' x) g =
      Formalism.REAL.EabV ε a b f g + c • Formalism.REAL.EabV ε a b f' g := by
  have hc := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  simp only [Formalism.REAL.EabV, Formalism.REAL.EcV]
  rw [(Formalism.REAL.rdLinV n ε E f f' _ _ 0 c g hf hf' hc.1 hc.1 hg).2.2,
    (Formalism.REAL.rdLinV n ε E f f' _ _ 0 c g hf hf' hc.2.1 hc.2.1 hg).2.2]
  simp only [smul_add]
  rw [smul_comm Complex.I c]
  abel

theorem puniq_eabV_smooth (a b : Fin n) {φ : Matrix (Fin n) (Fin n) ℂ → E}
    (hφ : Formalism.REAL.SmoothOnGV ε φ) : Formalism.REAL.SmoothOnGV ε (Formalism.REAL.EabV ε a b φ) := by
  have hc := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  exact puniq_smooth_add_smul (Formalism.REAL.rdSmoothV n ε E φ _ hφ hc.1)
    (Formalism.REAL.rdSmoothV n ε E φ _ hφ hc.2.1) Complex.I

theorem puniq_casimirV_lin {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : S7.SmoothOnGV ε f)
    (hf' : S7.SmoothOnGV ε f') (c : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    S7.casimirV ε (fun x => f x + c • f' x) g = S7.casimirV ε f g + c • S7.casimirV ε f' g := by
  have hsm : ∀ (a b : Fin n) {φ : Matrix (Fin n) (Fin n) ℂ → E}, Formalism.REAL.SmoothOnGV ε φ →
      Formalism.REAL.SmoothOnGV ε (Formalism.REAL.EabV ε a b φ) := fun a b _ h => puniq_eabV_smooth a b h
  have hg' : Formalism.REAL.inUJ ε g := hg
  have step : ∀ a b : Fin n,
      Formalism.REAL.EabV ε a b (Formalism.REAL.EabV ε b a (fun x => f x + c • f' x)) g =
        Formalism.REAL.EabV ε a b (Formalism.REAL.EabV ε b a f) g + c • Formalism.REAL.EabV ε a b (Formalism.REAL.EabV ε b a f') g := by
    intro a b
    rw [puniq_eabV_congr (φ := fun x => Formalism.REAL.EabV ε b a f x + c • Formalism.REAL.EabV ε b a f' x)
      (puniq_smooth_add_smul (hsm b a hf) (hsm b a hf') c) (fun x hx => puniq_eabV_lin hf hf' c hx b a) hg' a b]
    exact puniq_eabV_lin (hsm b a hf) (hsm b a hf') c hg' a b
  show (∑ a, ∑ b, Formalism.REAL.EabV ε a b (Formalism.REAL.EabV ε b a (fun x => f x + c • f' x)) g) =
    (∑ a, ∑ b, Formalism.REAL.EabV ε a b (Formalism.REAL.EabV ε b a f) g) +
      c • ∑ a, ∑ b, Formalism.REAL.EabV ε a b (Formalism.REAL.EabV ε b a f') g
  simp only [step, Finset.sum_add_distrib, Finset.smul_sum]

end Smooth

theorem puniq_schur {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (A : T.V →ₗ[ℂ] T.V)
    (hA : ∀ (k : S7.KG ε) (v : T.V), A (T.op k v) = T.op k (A v)) : ∃ c : ℂ, ∀ v, A v = c • v := by
  letI := T.instNACG
  letI := T.instIPS
  letI := T.instFD
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by
    have hw := T.w_norm
    rw [h, norm_zero] at hw
    exact zero_ne_one hw⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  refine ⟨c, fun v => ?_⟩
  have hinv : ∀ k : S7.KG ε, ∀ v ∈ Module.End.eigenspace A c,
      ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈ Module.End.eigenspace A c := by
    intro k v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have := hA k v
    simp only [S7.KType.op] at this
    rw [this, hv, map_smul]
  rcases T.irred _ hinv with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.mp hc)
  · have hv : v ∈ Module.End.eigenspace A c := by rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.mp hv

theorem puniq_kset {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g ∈ UJset ε := by
  obtain ⟨hu, hc⟩ := hg
  have hu' : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hu
    simpa [Matrix.star_eq_conjTranspose] using this
  show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hu', Matrix.one_mul]

theorem puniq_isKTypeOf_map {ε : Fin n → Bool} {H₁ H₂ : Type*} [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}
    (U : H₁ ≃ₗᵢ[ℂ] H₂) (hU : ∀ g ∈ Formalism.REAL.Kset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x))
    {μ : Fin n → ℝ} {S : Submodule ℂ H₁} (hS : Formalism.MainNotions.S.IsKTypeOf ε σ₁ μ S) :
    Formalism.MainNotions.S.IsKTypeOf ε σ₂ μ (S.map (U.toLinearEquiv : H₁ →ₗ[ℂ] H₂)) := by
  obtain ⟨hfd, hst, hmin, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  set f : H₁ →ₗ[ℂ] H₂ := (U.toLinearEquiv : H₁ →ₗ[ℂ] H₂) with hf
  have hfU : ∀ x, f x = U x := fun x => rfl
  have hback : ∀ g ∈ Formalism.REAL.Kset ε, ∀ y, σ₁ g (U.symm y) = U.symm (σ₂ g y) := by
    intro g hg y
    apply U.injective
    rw [hU g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have memS : ∀ x, f x ∈ S.map f → x ∈ S := by
    rintro x ⟨y, hy, hxy⟩
    rwa [← U.injective hxy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := hfd
    exact (U.toLinearEquiv.submoduleMap S).finiteDimensional
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ₁ g x, hst g hg x hx, hU g hg x⟩
  · intro S'' hle hst''
    have hc := hmin (S''.comap f) (fun x hx => memS x (hle hx)) (fun g hg x hx => by
      show f (σ₁ g x) ∈ S''
      rw [hfU, hU g hg]
      exact hst'' g hg _ hx)
    have hsurj : Function.Surjective f := U.surjective
    rcases hc with h | h
    · left
      rw [← Submodule.map_comap_eq_of_surjective hsurj S'', h, Submodule.map_bot]
    · right
      rw [← Submodule.map_comap_eq_of_surjective hsurj S'', h]
  · refine ⟨U v, ⟨v, hvS, rfl⟩, fun h => hv0 (U.injective (by rw [h, map_zero])), fun θ hθ => ?_⟩
    rw [← hU _ hθ, hvw θ hθ, map_smul]
  · intro μ' w hw hw0 hww
    refine hdom μ' (U.symm w) ?_ ?_ ?_
    · obtain ⟨x, hx, rfl⟩ := hw
      rw [hfU, LinearIsometryEquiv.symm_apply_apply]
      exact hx
    · intro h
      apply hw0
      rw [← U.apply_symm_apply w, h, map_zero]
    · intro θ hθ
      rw [hback _ hθ, hww θ hθ, map_smul]

theorem puniq_memLp_haar {ε : Fin n → Bool} {X : Type*} [NormedAddCommGroup X]
    (F : Matrix (Fin n) (Fin n) ℂ → X)
    (hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    (μ : Measure (S7.UJ ε)) (hμ : μ.IsHaarMeasure) : MemLp (fun g : S7.UJ ε => F (S7.toM g)) 2 μ := by
  have hF' : MemLp (fun g : S7.UJ ε => F (S7.toM g)) 2 (Measure.haar : Measure (S7.UJ ε)) := hF
  rw [MeasureTheory.Measure.isMulLeftInvariant_eq_smul μ (Measure.haar : Measure (S7.UJ ε))]
  exact hF'.smul_measure ENNReal.coe_ne_top

end ReciprocityTheory.ChartRestriction.DS
