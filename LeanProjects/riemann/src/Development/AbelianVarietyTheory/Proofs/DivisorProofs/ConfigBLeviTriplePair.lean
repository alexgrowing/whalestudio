import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleDescendsToSmallerGeometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleSmallerGeometryThetaCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleSmallerGeometryEisensteinStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LawVLevi

theorem resEtaPow_div' {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] {K : Subgroup Rˣ}
    {χ₁ χ₂ : Eˣ →* Circle} {m n : ℕ} (h₁ : ResEtaPow K χ₁ m) (h₂ : ResEtaPow K χ₂ n) :
    ResEtaPow K (χ₁ / χ₂) (m + n) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]
  split_ifs
  · simp
  · have h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]

theorem isHecke_div' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ₁ χ₂ : Chr F E}
    (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩

end GlobalTheory.LawVLevi

open GlobalTheory.LawVLevi in

theorem GlobalTheory.LawVLevi.evalA_leviV : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ (t : (AE F E)ˣ) (m₀ : UA σ G.V.J), IsLevi (W₁ := X₁) H₀ t 1 m₀ → ∀ Ψ ∈ schA F (Fin a × Fin (a + (b + 2))), e₂ (om (m₀, 1) Ψ) = (((X.β / X.α) t : ℂ) * (((absE F E t : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • e₂ Ψ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev t m₀ hL Ψ hΨ
  obtain ⟨ea, hea⟩ := GlobalTheory.T.triple_descends_to_smaller_geometry hKP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁
  obtain ⟨eb, c, heb, hfac⟩ := GlobalTheory.T.triple_smaller_geometry_theta_compat hKP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev ea hea
  have hlaw := GlobalTheory.T.triple_smaller_geometry_eisenstein hKP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ hV₂ hH₀ hM₂ eb heb
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  have eV : V₁ = G.V := cfg.eV
  subst eV
  have ep : p₁ = G.p := cfg.ep
  subst ep
  have P : IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T.geo.hW, T.geo.hM, T.chars.heckeβ, isHecke_div' T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div' T.chars.resβ T.chars.resα, T.weil⟩
  have P₁ : IsPair B M₁ X.β (X.β / X.α) om₁ (a - G.p) G.p _ _ :=
    ⟨T₁.base, T₁.geo.hV, T₁.geo.hW, T₁.geo.hM, T₁.chars.heckeβ, isHecke_div' T₁.chars.heckeβ T₁.chars.heckeα,
      T₁.chars.resβ, resEtaPow_div' T₁.chars.resβ T₁.chars.resα, T₁.weil⟩
  have hL1 : IsLevi (W₁ := W₁) H' 1 1 (1 : UA σ G.W.J) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [mat]
  have hpres : om (m₀, 1) Ψ ∈ schA F (Fin a × Fin (a + (b + 2))) := (T.weil.isUSplitting).pres _ Ψ hΨ
  have key := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B a (a + (b + 2)) G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (a + b) W₁ H' a
    (a + b + 1) M₁ om₁ _ _ cfg.hH' P₁ ea hea m₀ 1 1 1 hL1 1 (Subgroup.one_mem _) Ψ hΨ
  rw [mul_one] at key
  have h1 : ((X.β 1 : ℂ) * (((absE F E 1 : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) = 1 := by simp
  rw [h1, one_smul] at key
  rw [hfac _ hpres, key, hlaw t m₀ hL _ (hea.maps Ψ hΨ), hfac Ψ hΨ, smul_comm]
