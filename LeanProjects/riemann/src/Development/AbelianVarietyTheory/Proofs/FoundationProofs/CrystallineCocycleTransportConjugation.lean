import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LatticeConditions
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TwistedTriples

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open scoped TensorProduct

namespace GlobalTheory.TwistedSelmerCompare

theorem natCast_mem_maximalIdeal {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : ((IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  have h2 := IsLocalRing.eq_maximalIdeal h
  have h3 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h2, Ideal.mem_comap, map_natCast] at h3
  exact h3

theorem padicInt_hom_ext {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (f g : ℤ_[l] →+* O) : f = g := by
  ext z
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_iInf]
  intro n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (z.appr n : ℤ_[l]) + c * (l : ℤ_[l]) ^ n := by rw [hc]; ring
  have : f z - g z = (f c - g c) * (l : O) ^ n := by
    rw [hz]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hl n)

theorem crystallineCocycle_transport_conjugation {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K₁ K₂ L₁ L₂ : FinExt l)
    (θ : ↥(GK K₂) →* ↥(GK K₁)) (hθ : Continuous θ) (σ : GQ l)
    (hσ : ∀ g : ↥(GK K₂), (g : GQ l) = σ * (θ g : GQ l) * σ⁻¹) {k : ℕ}
    (M₁ : ↥(GK K₁) →* Matrix (Fin k) (Fin k) ↥L₁.1) (M₂ : ↥(GK K₂) →* Matrix (Fin k) (Fin k) ↥L₂.1)
    (p : ↥L₁.1 →ₗ[ℚ_[l]] ↥L₂.1)
    (hp : ∀ g (v : Fin k → ↥L₁.1), (fun j => p ((M₁ (θ g)).mulVec v j)) = (M₂ g).mulVec fun j => p (v j))
    (c : ↥(GK K₁) → Fin k → ↥L₁.1) (hc : c ∈ finiteCocycles (P.PD K₁) (matRep M₁)) :
    (fun g j => p (c (θ g) j)) ∈ finiteCocycles (P.PD K₂) (matRep M₂) := by
  obtain ⟨⟨hc1, hc2⟩, x, hx⟩ := hc
  have := L₁.2
  have hpc : Continuous p := p.continuous_of_finiteDimensional
  let q : (Fin k → ↥L₁.1) →ₗ[ℚ_[l]] (Fin k → ↥L₂.1) := LinearMap.compLeft p (Fin k)
  have hq : ∀ g v, q (matRep M₁ (θ g) v) = matRep M₂ g (q v) := fun g v => hp g v
  let T := TensorProduct.map q (P.actQ σ).toLinearMap
  have hT : ∀ g y, T (actVB (P.PD K₁) (matRep M₁) (θ g) y) = actVB (P.PD K₂) (matRep M₂) g (T y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v b =>
      change q (matRep M₁ (θ g) v) ⊗ₜ[ℚ_[l]] P.actQ σ ((P.PD K₁).actB (θ g) b) =
        matRep M₂ g (q v) ⊗ₜ[ℚ_[l]] (P.PD K₂).actB g (P.actQ σ b)
      rw [hq, P.PD_actB, P.PD_actB, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← map_mul, ← map_mul]
      congr 3
      rw [hσ g]; group
  refine ⟨⟨continuous_pi fun j => hpc.comp ((continuous_apply j).comp (hc1.comp hθ)), fun g h => ?_⟩,
    T x, fun g => ?_⟩
  · change q (c (θ (g * h))) = q (c (θ g)) + matRep M₂ g (q (c (θ h)))
    rw [map_mul, hc2, map_add, hq]
  · rw [← hT, ← map_sub, ← hx]
    change q (c (θ g)) ⊗ₜ[ℚ_[l]] (1 : P.R.B) = q (c (θ g)) ⊗ₜ[ℚ_[l]] P.actQ σ 1
    rw [map_one]

section Coef

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem toLLK_bijective (B : LocBridge l E Ω Gw O) : Function.Bijective (Br.toLLK B) := by
  refine ⟨(Br.toLLK B).injective, fun x => ?_⟩
  have := B.LL.2
  have : Algebra.IsAlgebraic ℤ_[l] ↥B.LL.1 := IsFractionRing.comap_isAlgebraic_iff.2
    (inferInstance : Algebra.IsAlgebraic ℚ_[l] ↥B.LL.1)
  obtain ⟨d, hd, hx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ_[l]) x).exists_integral_multiple
  obtain ⟨n, hn⟩ := B.eO.surjective ⟨d • x, hx⟩
  refine ⟨algebraMap O _ n / algebraMap O _ (algebraMap ℤ_[l] O d), ?_⟩
  rw [map_div₀, Br.toLLK_alg, Br.toLLK_alg, hn, B.eO_alg, ← IsScalarTower.algebraMap_apply, div_eq_iff]
  · change d • x = _
    rw [Algebra.smul_def, mul_comm]
  · rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥B.LL.1]
    simpa using hd

theorem exists_coefMap (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (f : O₀ →+* O)
    (hf : Function.Injective f) (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ φ : ↥B₀.LL.1 →ₐ[ℚ_[l]] ↥B.LL.1,
      ∀ x : FractionRing O₀, φ (Br.toLLK B₀ x) = Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf x) := by
  let e := RingEquiv.ofBijective _ (toLLK_bijective B₀)
  let φ : ↥B₀.LL.1 →+* ↥B.LL.1 := (Br.toLLK B).comp ((GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf).comp e.symm.toRingHom)
  have hφ : ∀ x, φ (Br.toLLK B₀ x) = Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf x) := fun x =>
    congrArg (fun y => Br.toLLK B (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf y)) (e.symm_apply_apply x)
  have hc : φ.comp (algebraMap ℚ_[l] ↥B₀.LL.1) = algebraMap ℚ_[l] ↥B.LL.1 := by
    refine IsFractionRing.ringHom_ext (A := ℤ_[l]) fun z => ?_
    have h := hφ (algebraMap O₀ _ (algebraMap ℤ_[l] O₀ z))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, hz, Br.toLLK_alg, Br.toLLK_alg, B.eO_alg, B₀.eO_alg,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, h]
  exact ⟨{ φ with commutes' := fun q => DFunLike.congr_fun hc q }, hφ⟩

end Coef

end GlobalTheory.TwistedSelmerCompare

end
