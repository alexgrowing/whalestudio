import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenIntegralHaar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ConeSmallLawC

open GlobalTheory.ConeSmallLaw

theorem absE_cpow_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x y : (AE F E)ˣ) (z : ℂ) :
    ((absE F E (x * y) : ℝ) : ℂ) ^ z = ((absE F E x : ℝ) : ℂ) ^ z * ((absE F E y : ℝ) : ℂ) ^ z := by
  rw [map_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (absE F E x).2 (absE F E y).2 z

theorem absE_cpow_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : (AE F E)ˣ) (z : ℂ) : ((absE F E x : ℝ) : ℂ) ^ z ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl (Complex.ofReal_ne_zero.mpr (absE_pos x).ne')

theorem coneI_lawC : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ z : ℂ, GlobalTheory.ConeSmallCT.HasLawC G₁.W H' X.β (z + (b : ℂ) / 2) (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' he' K μK μ hK hμK hμ X om om' om₁ om₁' T T₁ Φ' hΦ' z t m hL h
  classical
  have hS : Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := by
    refine Submodule.span_le.mpr ?_ hΦ'.2
    rintro _ ⟨f, φ, hφ, hv, -, rfl⟩
    refine GlobalTheory.TensUniq.pure_mem_schA f φ hφ ?_
    filter_upwards [hv, T.geo.hM'.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨u, hu⟩ : ∃ u : (AE F E)ˣ, u = (Units.map (cA σ).toMonoidHom t)⁻¹ := ⟨_, rfl⟩
  have hν0 : ∀ l : (AE F E)ˣ, (X.ν l : ℂ) ≠ 0 := fun l => Circle.coe_ne_zero _
  have hin : ∀ k : K, (∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, m * h) Φ'))) 1 *
        (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ) =
      ((X.α t : ℂ) * (((absE F E t : ℝ) ^ ((b : ℝ) / 2) : ℝ) : ℂ)) *
        ((X.ν u : ℂ) * ((absE F E u : ℝ) : ℂ) ^ z)⁻¹ *
        ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))) 1 *
          (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ := by
    intro k
    rw [← integral_mul_right_eq_self (μ := μ) (fun l => G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l)
      (om' (k.1, h) Φ'))) 1 * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) u, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun l => ?_)
    simp only
    rw [integrand_levi hKP cfg he' T T₁ t m hL k.1 h Φ' hS l, ← hu, absE_cpow_mul, map_mul, Circle.coe_mul]
    have h1 := hν0 u
    have h2 := absE_cpow_ne_zero u z
    field_simp
  have hα := GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' T) t
  have hβ := GlobalTheory.chrX_conj_inv F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.Inhab.pairV T) t
  have hνu : X.ν u = X.α t / X.β t := by
    rw [hu, map_inv, Chars.ν, MonoidHom.div_apply, hα, hβ, inv_div_inv, inv_div]
  have hr := absE_pos t
  have habsu : ((absE F E u : ℝ) : ℂ) ^ z = (((absE F E t : ℝ) : ℂ) ^ z)⁻¹ := by
    rw [hu, map_inv, absE_cA, NNReal.coe_inv, Complex.ofReal_inv, Complex.inv_cpow]
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  show GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' z (m * h) = _
  unfold GlobalTheory.ConeSmall.coneI
  rw [integral_congr_ae (Eventually.of_forall hin), integral_const_mul]
  congr 1
  have hc0 : ((absE F E t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hz0 := absE_cpow_ne_zero t z
  rw [Complex.cpow_add _ _ hc0, show ((b : ℂ) / 2) = (((b : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hr.le, hνu, habsu, Circle.coe_div]
  have hA := Circle.coe_ne_zero (X.α t)
  have hB := Circle.coe_ne_zero (X.β t)
  field_simp

end GlobalTheory.ConeSmallLawC
