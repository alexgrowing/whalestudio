import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitBasisCompl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviLineEval

theorem resEtaPow_of_add_two {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ : Eˣ →* Circle} {n : ℕ} (h : ResEtaPow K χ (n + 2)) : ResEtaPow K χ n := by
  intro a
  rw [h a]
  simp [pow_add]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) :
    ResEtaPow K (χ / χ') (n + m) := by
  intro a
  rw [MonoidHom.div_apply, Circle.coe_div, h a, h' a]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg, inv_one, ← pow_add]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

end GlobalTheory.LeviLineEval

open GlobalTheory.LeviLineEval GlobalTheory.HermPlaneCompl in

theorem GlobalTheory.ThK.evalLine_leviV : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ eb : Fn F a (a + b) →ₗ[ℂ] Fn F n₁ (a + b), IsEv B G₁.M M₂ H₀.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H₀.x) z} eb → ∀ (t : (AE F E)ˣ) (m₀ : UA σ G₁.V.J), IsLevi (W₁ := X₁) H₀ t 1 m₀ → ∀ Φ ∈ schA F (Fin a × Fin (a + b)), eb (om₁ (m₀, 1) Φ) = (((X.β / X.α) t : ℂ) * (((absE F E t : ℝ) ^ (((a + b : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • eb Φ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ hV₂ hH₀ hM₂ eb heb t m₀ hL Φ hΦ
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  have eV : V₁ = G.V := cfg.eV
  subst eV
  have ep : p₁ = G.p := cfg.ep
  subst ep

  let M : Model σ (reS G.V V₂) W₁ := ⟨M₁.co, M₁.vac, M₁.μ, M₁.dom⟩
  have hMg : M.IsGood B.ψ := ⟨T₁.geo.hM.rat, T₁.geo.hM.vac, T₁.geo.hM.std, T₁.geo.hM.haar, T₁.geo.hM.dom⟩
  have hres : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.β / X.α) (a + b) :=
    resEtaPow_div T₁.chars.resβ T₁.chars.resα
  have hW₁ : W₁.IsSkew σ B (a + b - (G.p + q₁)) (G.p + q₁) := T₁.geo.hW
  have P : IsPair B M X.β (X.β / X.α) om₁ (a - G.p) G.p (a + b - (G.p + q₁)) (G.p + q₁) :=
    ⟨T₁.base, hV₂, hW₁, hMg, T₁.chars.heckeβ, isHecke_div T₁.chars.heckeβ T₁.chars.heckeα, T₁.chars.resβ, hres, T₁.weil⟩

  have hA : a = n₁ + 2 := hH₀.rank
  have hX₁ : X₁.IsHerm σ B (a - G.p - 1) (G.p - 1) := isHerm_compl T₁.base hV₂ hH₀
  have hresβ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range X.β n₁ := by
    have h := T₁.chars.resβ
    rw [hA] at h
    exact resEtaPow_of_add_two h
  obtain ⟨om₂, hom₂⟩ := GlobalTheory.WeilExGen.exists_isWeil hKP.base F E σ B T₁.base n₁ (a + b) X₁ W₁ _ _ _ _ hX₁ hW₁ M₂ hM₂ X.β (X.β / X.α)
    T₁.chars.heckeβ (isHecke_div T₁.chars.heckeβ T₁.chars.heckeα) hresβ hres
  have P₂ : IsPair B M₂ X.β (X.β / X.α) om₂ (a - G.p - 1) (G.p - 1) (a + b - (G.p + q₁)) (G.p + q₁) :=
    ⟨T₁.base, hX₁, hW₁, hM₂, T₁.chars.heckeβ, isHecke_div T₁.chars.heckeβ T₁.chars.heckeα, hresβ, hres, hom₂⟩
  have heb' : IsEv B M M₂ H₀.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H₀.x) z} eb :=
    ⟨heb.maps, heb.Heisenberg₂, heb.inv, heb.loc⟩
  have key := (GlobalTheory.T.adapted_plane_first_variable hKP.base F E σ B a (a + b) (reS G.V V₂) W₁ M X.β (X.β / X.α) om₁ _ _ _ _ P n₁ X₁ H₀ j₀ j₁
    M₂ om₂ _ _ hH₀ P₂).2 eb heb' 1 t 1 m₀ hL 1 (Subgroup.one_mem _) Φ hΦ
  rw [show om₂ (1, 1) = 1 from map_one om₂, Module.End.one_apply] at key
  erw [one_mul] at key
  exact key
