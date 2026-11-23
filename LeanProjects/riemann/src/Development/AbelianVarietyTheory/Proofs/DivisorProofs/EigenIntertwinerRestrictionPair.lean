import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSkewComplement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.UnipEvZero

theorem evZero_unip_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ u ∈ unip σ W H', ∀ Ψ ∈ schA F (Fin n × Fin d), e₀ (om (1, u) Ψ) = e₀ Ψ := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ he₀ χX χW om r s r' s' hP u hu Ψ hΨ
  have hW₁ := KernelZero.isSkew_complement F E σ B hP.base d d₁ W W₁ H' i₀ i₁ r' s' hP.skew hH
  have hres₁ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d₁ := by
    intro a
    rw [hP.resW a, hH.rank, pow_add, neg_one_sq, mul_one]
  obtain ⟨om₁, hom₁⟩ := GlobalTheory.WeilExGen.exists_isWeil hKP.base F E σ B hP.base n d₁ X W₁ r s (r' - 1) (s' - 1) hP.herm hW₁ M₁ hM₁ χX χW
    hP.hX hP.hW hP.resX hres₁
  have hP₁ : IsPair B M₁ χX χW om₁ r s (r' - 1) (s' - 1) :=
    ⟨hP.base, hP.herm, hW₁, hM₁, hP.hX, hP.hW, hP.resX, hres₁, hom₁⟩
  have hL : IsLevi H' 1 (1 : UA σ W₁.J) (1 : UA σ W.J) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [mat]
  have h := GlobalTheory.T.adapted_plane_second_variable hKP.base F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ (r' - 1) (s' - 1)
    hH hP₁ e₀ he₀ 1 1 1 1 hL u hu Ψ hΨ
  have h1 : om₁ (1, 1) = 1 := map_one om₁
  simpa [h1] using h

end GlobalTheory.ThK.UnipEvZero
