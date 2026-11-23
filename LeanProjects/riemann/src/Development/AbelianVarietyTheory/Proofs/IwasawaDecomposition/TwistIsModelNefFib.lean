import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCompAlgebraMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TwistModel

theorem induced_twist {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y} {M : Model Y}
    {L : HermLB M.p} {k : ℕ+} {cf₀ : HeightOneSpectrum (𝓞 F) → ℝ} (h : A.Induced M L k cf₀)
    (ci : InfinitePlace F → ℝ) {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hcf : (Function.support cf).Finite) :
    ∃ L' : HermLB M.p, L'.B = L.B ∧ (A.twist ci cf).Induced M L' k (cf₀ + cf) := by
  obtain ⟨hf, r, hr, hi, hv⟩ := h
  let E := Equiv.ofBijective _ (GlobalTheory.TwistTop.bijective_comp_algebraMap F)
  have hE (σ : F →+* ℂ) : E.symm (σ.comp (algebraMap (𝓞 F) F)) = σ := E.symm_apply_apply σ
  let s (τ : 𝓞 F →+* ℂ) : ℝ := (k : ℕ) * (A.n : ℕ) * ci (InfinitePlace.mk (E.symm τ))
  have hs (τ : 𝓞 F →+* ℂ) : s ((starRingEnd ℂ).comp τ) = s τ := by
    obtain ⟨σ, rfl⟩ := E.surjective τ
    have e : (starRingEnd ℂ).comp (E σ) = E (ComplexEmbedding.conjugate σ) := rfl
    simp only [s, e, Equiv.symm_apply_apply, InfinitePlace.mk_conjugate_eq]
  refine ⟨L.shift s hs, rfl, (hf.union hcf).subset (Function.support_add _ _), r, hr,
    fun σ y y' i f h₁ h₂ h₃ => ?_, fun v e y yt i h₁ h₂ => ?_⟩
  · have e := hi σ y y' i f h₁ h₂ h₃
    change Real.exp (-(2 * (k : ℕ) * (A.n : ℕ) * (A.ci (InfinitePlace.mk σ) + ci (InfinitePlace.mk σ)))) *
      C.pn Y σ _ (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y =
      ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-((L.φ _).φ (i PUnit.unit) y' + 2 * s _))
    rw [neg_add, Real.exp_add, ← mul_assoc, ← e, mul_add, neg_add, Real.exp_add, mul_right_comm]
    simp only [s, hE, mul_assoc]
  · have e := hv v e y yt i h₁ h₂
    change ((k : ℕ) : ℝ) * (A.lg v _ y - (A.n : ℕ) * cf v) = Real.log (Ext.w _ (valAt y.1
      (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn))) - (k : ℕ) * (A.n : ℕ) * (cf₀ v + cf v)
    linear_combination e

theorem twist_isModel_nefFib : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (ci : InfinitePlace F → ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support cf).Finite → (A.IsModel → (A.twist ci cf).IsModel) ∧ (A.NefFib → (A.twist ci cf).NefFib) := by
  intro F _ _ C Y A ci cf hcf
  refine ⟨fun ⟨M, L, k, cf₀, h⟩ => ?_, fun ⟨M, L, k, cf₀, h, hN⟩ => ?_⟩
  · obtain ⟨L', -, h'⟩ := induced_twist h ci hcf
    exact ⟨M, L', k, _, h'⟩
  · obtain ⟨L', hB, h'⟩ := induced_twist h ci hcf
    refine ⟨M, L', k, _, h', ?_⟩
    unfold ArInt.NefFib at hN ⊢
    rw [hB]
    exact hN

end GlobalTheory.TwistModel
