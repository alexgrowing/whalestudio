import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.HodgeTateFromSandwich

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Basic

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem mat_mul' {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mulVec {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {x y : Fin n → AE F E} (h : mat g *ᵥ x = y) :
    mat g⁻¹ *ᵥ y = x := by
  rw [← h, Matrix.mulVec_mulVec, ← mat_mul', inv_mul_cancel, mat_one', Matrix.one_mulVec]

theorem pair_pres (hp : IsPair B M χX χW om r s r' s') (x) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : om x Φ ∈ schA F _ :=
  (IsUWeilPair.isUSplitting hp.weil).pres x Φ hΦ

theorem pair_cont (hp : IsPair B M χX χW om r s r' s') {l} (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : Continuous fun x => l (om x Φ) :=
  (IsUWeilPair.isUSplitting hp.weil).cont l hl Φ hΦ

theorem pair_adm (hp : IsPair B M χX χW om r s r' s') (x) {l} (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) :
    l ∘ₗ om x ∈ (adeleClass F).adm (Fin n × Fin d) :=
  (IsUWeilPair.isUSplitting hp.weil).adm x l hl

theorem om_mul (om : Rep σ X W) (x y) (Φ) : om x (om y Φ) = om (x * y) Φ := by rw [map_mul]; rfl

theorem rho_om (hp : IsPair B M χX χW om r s r' s') (g h) (a : Fin n → AE F E) (b : Fin d → AE F E) (c : AE F E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    M.co.rho B.ψ (c • Matrix.vecMulVec a b) (om (g, h) Φ) =
      om (g, h) (M.co.rho B.ψ (c • Matrix.vecMulVec (mat g⁻¹ *ᵥ a) (mat h⁻¹ *ᵥ b)) Φ) := by
  rw [(IsUWeilPair.isUSplitting hp.weil).impl (g, h) _ Φ hΦ]
  congr 2
  change _ = mat g * _ * (mat h)ᵀ
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mat_mul', ← mat_mul', mul_inv_cancel, mul_inv_cancel, mat_one', mat_one',
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem rho_linear (M : Model σ X W) (ψ) (u) {ι : Type} (t : Finset ι) (c : ι → ℂ) (Φ : ι → Fn F n d) :
    M.co.rho ψ u (∑ i ∈ t, c i • Φ i) = ∑ i ∈ t, c i • M.co.rho ψ u (Φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ev_adm {κ : Type} [Fintype κ] (y : κ → AF F) : (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  classical
  refine ⟨g (fun i => (y i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem thetaSum_smul' {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem kfin_dec (hp : IsPair B M χX χW om r s r' s') {K : Subgroup (UA σ X.J)} {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hK : KFinite om K Φ) (S : Submodule ℂ (Fn F n d)) (hS : ∀ k : K, om (k.1, 1) Φ ∈ S) :
    ∃ (m : ℕ) (Ψ : Fin m → Fn F n d) (c : Fin m → K → ℂ), (∀ i, Ψ i ∈ S) ∧ (∀ i, Continuous (c i)) ∧
      ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i := by
  set V := Submodule.span ℂ (Set.range fun k : K => om (k.1, 1) Φ)
  haveI : FiniteDimensional ℂ V := hK
  let b := Module.finBasis ℂ V
  have hc : Continuous fun k : K => (⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩ : V) := by
    refine Continuous.subtype_mk (continuous_pi fun y => ?_) _
    exact (pair_cont hp (ev_adm y) hΦ).comp (continuous_subtype_val.prodMk continuous_const)
  refine ⟨_, fun i => (b i).1, fun i k => b.repr ⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩ i,
    fun i => Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hS k) (b i).2,
    fun i => (b.coord i).continuous_of_finiteDimensional.comp hc, fun k => ?_⟩
  have := congrArg Subtype.val (b.sum_repr ⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩)
  rw [Submodule.coe_sum] at this
  exact this.symm

end Basic

end PositivityTheory.ThKCT

end
