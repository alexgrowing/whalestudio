import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharEqOneOfOpENeZero

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology

namespace GlobalTheory.RootEx

private theorem exists_open_translations {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {Φ : M → ℂ} (hΦ : Φ ∈ SB M) :
    ∃ Λ : AddSubgroup M, IsOpen (Λ : Set M) ∧ ∀ x, ∀ y ∈ Λ, Φ (x + y) = Φ x := by
  obtain ⟨K, hKo, hK⟩ := GlobalTheory.QuotInt.exists_open_stab (G := Multiplicative M)
    (F := fun x => Φ (Multiplicative.toAdd x)) hΦ
  refine ⟨{ carrier := {y | Multiplicative.ofAdd y ∈ K}
            add_mem' := fun hy hz => K.mul_mem hy hz
            zero_mem' := K.one_mem
            neg_mem' := fun hy => K.inv_mem hy }, hKo, ?_⟩
  intro x y hy
  exact hK (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) hy

theorem exists_isQuotInt_unfolding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (P P' : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P'] (π : Representation ℂ (GL n k) P) (π' : Representation ℂ (GL n' k) P') (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (_ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ)) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : IsPos ψ p π σ b) (φ : P') (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h Ψ, Ψ.1 = opE ψ ν p (om μ 1 h Φ.1) → f h = b (θ φ Ψ) (σ h F)), ∃ z, IsQuotInt ν μX μG p f z := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψc hψ1 ν _ μ hμ μX _ μG _ A _ _ σ hσ P P' _ _ _ _
    π π' θ hθ b hb φ F Φ f hf
  have hom := om_isSmoothRepresentation k (n' ⊕ Fin (c + 1)) (n ⊕ Fin c) μ hμ
  have hom' := om_isSmoothRepresentation k n' n μ hμ
  have hE := opE_SB_and_linear k n n' c p ψ hψc ν
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  have hmemΨ : ∀ h : GL (n ⊕ Fin c) k, opE ψ ν p (om μ 1 h Φ.1) ∈ SB (Matrix n n' k) :=
    fun h => hE.1 _ (hom.2.2.2.1 1 h Φ.1 Φ.2)
  have om_smul : ∀ {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (g : GL a k) (h : GL b k) (z : ℂ) (G : Matrix b a k → ℂ), om μ g h (z • G) = z • om μ g h G := by
    intro a b _ _ _ _ g h z G
    funext y
    simp only [om, Pi.smul_apply, smul_eq_mul]
    ring
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : {y : GL (n ⊕ Fin c) k | σ y F = F ∧ om μ 1 y Φ.1 = Φ.1} ∈ 𝓝 (1 : GL (n ⊕ Fin c) k) := by
      refine Filter.inter_mem ((hσ F).mem_nhds (by simp)) ?_
      have ho : IsOpen {y : GL (n ⊕ Fin c) k | om μ 1 y Φ.1 = Φ.1} :=
        (hom.2.2.2.2 Φ.1 Φ.2).preimage (continuous_const.prodMk continuous_id)
      exact ho.mem_nhds (hom.1 Φ.1)
    have hx : {y | x⁻¹ * y ∈ {y : GL (n ⊕ Fin c) k | σ y F = F ∧ om μ 1 y Φ.1 = Φ.1}} ∈ 𝓝 x := by
      have hc : Continuous fun y : GL (n ⊕ Fin c) k => x⁻¹ * y := continuous_const.mul continuous_id
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hU)
    filter_upwards [hx] with y hy
    obtain ⟨z, rfl⟩ : ∃ z, y = x * z := ⟨x⁻¹ * y, by group⟩
    simp only [inv_mul_cancel_left] at hy
    obtain ⟨h1, h2⟩ := hy
    have e1 : om μ 1 (x * z) Φ.1 = om μ 1 x Φ.1 := by
      have := hom.2.1 1 1 x z Φ.1
      rw [mul_one] at this
      rw [this, h2]
    have hσz : σ (x * z) F = σ x F := by
      rw [map_mul, Module.End.mul_apply, h1]
    rw [hf (x * z) ⟨_, hmemΨ x⟩ (by rw [e1]), hf x ⟨_, hmemΨ x⟩ rfl, hσz]
  obtain ⟨Λ, hΛo, hΛ⟩ := exists_open_translations (M := Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) Φ.2
  obtain ⟨Ω, hΩ, hΩR⟩ := opE_support_compact_mod_R k n n' c p hp1 hpc ψ hψc hψ1 ν (tsupport Φ.1) hΦ.2
    Λ hΛo
  have hsupp : ∀ h, f h ≠ 0 → ∃ r ∈ R k n c p, ∃ w ∈ Ω, h = r * w := by
    intro h hfh
    have hne : opE ψ ν p (om μ 1 h Φ.1) ≠ 0 := by
      intro h0
      apply hfh
      rw [hf h 0 (by rw [h0]; rfl)]
      simp
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hne
    exact hΩR μ Φ.1 (subset_tsupport _) hΛ (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  have hequiv : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h := by
    intro x u hu h
    let Ψ'' : SB (Matrix n n' k) := ⟨om μ 1 x (opE ψ ν p (om μ 1 h Φ.1)), hom'.2.2.2.1 1 x _ (hmemΨ h)⟩
    have m1 : om μ 1 (embX c x * u * h) Φ.1 = om μ 1 (embX c x) (om μ 1 u (om μ 1 h Φ.1)) := by
      have e1 := hom.2.1 1 1 (embX c x * u) h Φ.1
      have e2 := hom.2.1 1 1 (embX c x) u (om μ 1 h Φ.1)
      rw [mul_one] at e1 e2
      rw [e1, e2]
    have hkey : (((((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
        (ψ (-simpleSum u) : ℂ)) • Ψ'' : SB (Matrix n n' k)) : Matrix n n' k → ℂ) =
        opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) := by
      rw [m1, (opE_om_embX k n n' c p hp1 hpc ψ ν μ _).1 x,
        opE_om_target_unipotent k n n' c p hp1 hpc ψ ν μ _ u hu, om_smul, Submodule.coe_smul, smul_smul]
    have hθΨ : θ φ Ψ'' = π x (θ φ ⟨_, hmemΨ h⟩) := by
      have := hθ 1 x φ ⟨_, hmemΨ h⟩ Ψ'' rfl
      simpa using this
    rw [hf _ _ hkey, hf h ⟨_, hmemΨ h⟩ rfl, map_smul, hθΨ, map_smul, LinearMap.smul_apply, map_mul,
      map_mul, Module.End.mul_apply, Module.End.mul_apply, hb.2 x, hb.1 _ u hu, smul_eq_mul]
    have hN : 0 < nabs k (Matrix.GeneralLinearGroup.det x) := GlobalTheory.RootEx.OpELevi.nabs_pos _
    have hpow : (nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) =
        nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) *
          nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) := by
      rw [← Real.rpow_add hN]
      ring_nf
    have hψ : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
        Circle.coe_one]
    rw [hpow, Complex.ofReal_mul]
    linear_combination
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
      b (θ φ ⟨_, hmemΨ h⟩) (σ h F) * hψ
  exact (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp1 hpc ν μX μG f).2 hloc ⟨Ω, hΩ, hsupp⟩ hequiv

end GlobalTheory.RootEx
