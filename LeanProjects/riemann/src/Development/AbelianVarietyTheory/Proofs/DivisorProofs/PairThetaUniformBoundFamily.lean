import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Filter Topology

noncomputable section

namespace GlobalTheory.ThetaKernelDeriv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χY χW : Chr F E} {om : Rep σ Y W}
  {r s r' s' : ℕ}

theorem pureA_add (f f' : SInf F (Fin n × Fin d)) (φ : (Fin n × Fin d → Af F) → ℂ) :
    pureA F ⇑(f + f') φ = pureA F f φ + pureA F f' φ := by
  funext x; simp [pureA, add_mul]

theorem pureA_smul (c : ℝ) (f : SInf F (Fin n × Fin d)) (φ : (Fin n × Fin d → Af F) → ℂ) :
    pureA F ⇑(c • f) φ = (c : ℂ) • pureA F f φ := by
  funext x; simp [pureA, mul_assoc, Complex.real_smul]

theorem pureA_mem (f : SInf F (Fin n × Fin d)) {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Af F)) :
    pureA F f φ ∈ schA F (Fin n × Fin d) :=
  Submodule.subset_span ⟨f, φ, hφ, rfl⟩

def thetaLinAt (hP : IsPair B M χY χW om r s r' s') {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Af F))
    (g : UA σ Y.J) (h : UA σ W.J) : SInf F (Fin n × Fin d) →ₗ[ℝ] ℂ where
  toFun f := theta om (pureA F f φ) g h
  map_add' f f' := by
    have hs := hP.weil.isUSplitting.pres
    simp only [theta, pureA_add, map_add]
    exact thetaSum_add F (hs _ _ (pureA_mem f hφ)) (hs _ _ (pureA_mem f' hφ))
  map_smul' c f := by
    simp only [theta, pureA_smul, map_smul, RingHom.id_apply]
    rw [thetaSum_smul, Complex.real_smul]

theorem hasDerivAt_theta_pureA (hB : ThetaBasic) (hP : IsPair B M χY χW om r s r' s')
    {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Af F)) (f : ℝ → SInf F (Fin n × Fin d))
    (f₁ : SInf F (Fin n × Fin d)) (hf : Tendsto (fun t : ℝ => t⁻¹ • (f t - f 0)) (𝓝[≠] 0) (𝓝 f₁)) (g : UA σ Y.J)
    (h : UA σ W.J) :
    HasDerivAt (fun t : ℝ => theta om (pureA F (f t) φ) g h) (theta om (pureA F f₁ φ) g h) 0 := by
  have hc : Continuous (thetaLinAt hP hφ g h) := (hB F E σ B n d Y W M χY χW om r s r' s' hP).2 φ hφ g h
  rw [hasDerivAt_iff_tendsto_slope]
  have e : ∀ t : ℝ, slope (fun t : ℝ => theta om (pureA F (f t) φ) g h) 0 t = thetaLinAt hP hφ g h (t⁻¹ • (f t - f 0)) := by
    intro t
    rw [slope_def_module, map_smul, map_sub, sub_zero]
    rfl
  rw [show slope (fun t : ℝ => theta om (pureA F (f t) φ) g h) 0 = fun t => thetaLinAt hP hφ g h (t⁻¹ • (f t - f 0)) from funext e]
  exact (hc.tendsto f₁).comp hf

end GlobalTheory.ThetaKernelDeriv

theorem GlobalTheory.ThetaKernelDeriv.hasDerivAt_theta_sum : KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (χY χW : Chr F E) (om : Rep σ Y W) (r s r' s' : ℕ), IsPair B M χY χW om r s r' s' → ∀ (m : ℕ) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ) (f : ℝ → Fin m → SInf F (Fin n × Fin d)) (f₁ : Fin m → SInf F (Fin n × Fin d)), (∀ i, φ i ∈ SB (Fin n × Fin d → Af F)) → (∀ i, Tendsto (fun t : ℝ => t⁻¹ • (f t i - f 0 i)) (𝓝[≠] 0) (𝓝 (f₁ i))) → ∀ g h, HasDerivAt (fun t : ℝ => theta om (∑ i, pureA F (f t i) (φ i)) g h) (theta om (∑ i, pureA F (f₁ i) (φ i)) g h) 0 := by
  intro hK F E _ _ _ _ _ σ B n d Y W M χY χW om r s r' s' hP m φ f f₁ hφ hf g h
  have hB : ThetaBasic := GlobalTheory.T.theta_basic_properties hK.base
  have hs := hP.weil.isUSplitting.pres
  have hsum : ∀ u : Fin m → SInf F (Fin n × Fin d),
      theta om (∑ i, pureA F (u i) (φ i)) g h = ∑ i, theta om (pureA F (u i) (φ i)) g h := by
    intro u
    simp only [theta, map_sum]
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simp [thetaSum]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, thetaSum_add F (hs _ _ (GlobalTheory.ThetaKernelDeriv.pureA_mem _ (hφ a)))
        (Submodule.sum_mem _ fun i _ => hs _ _ (GlobalTheory.ThetaKernelDeriv.pureA_mem _ (hφ i))), ih]
  simp_rw [hsum]
  exact HasDerivAt.fun_sum fun i _ => GlobalTheory.ThetaKernelDeriv.hasDerivAt_theta_pureA hB hP (hφ i) (fun t => f t i) (f₁ i) (hf i) g h
