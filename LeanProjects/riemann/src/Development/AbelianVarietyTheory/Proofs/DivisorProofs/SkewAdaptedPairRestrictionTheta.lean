import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicEmbeddedVanishesAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDimensionBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalModelCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLagrangianSubspaceExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticInjectivePlaneCoordinatesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem exists_ratLagr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
        Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
        ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
              M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁

  have hD : ∀ p q, symp (cA σ) (-1) (incM F X.J) (incM F W.J) p q =
      (M.co.e p).1 ⬝ᵥ (M.co.e q).2 - (M.co.e q).1 ⬝ᵥ (M.co.e p).2 := M.co.form
  have hcross := GlobalTheory.T.symplectic_isotropic_embedded_vanishes_adelic F E σ n d d₁ X.J W.J H' (fun u => (hH.orth u).1)
  have hiso : ∀ a ∈ lagr M M₁ H', ∀ b ∈ lagr M M₁ H', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
    intro a ha b hb
    obtain ⟨u, hu, z, hz, hea⟩ := ha
    obtain ⟨u', hu', z', hz', heb⟩ := hb
    have ea : hat a = M.co.e (u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [← hea, LinearEquiv.apply_symm_apply]
    have eb : hat b = M.co.e (u' + incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) := by
      rw [← heb, LinearEquiv.apply_symm_apply]
    have h1 := GlobalTheory.T.symplectic_isotropic_plane_vanishes_adelic F E σ n d d₁ X.J W.J H' hH.xx u hu u' hu'
    have h2 := hcross u' hu' z
    have h3 := hcross u hu z'
    have h4 := GlobalTheory.T.symplectic_form_restricted_plane F E σ n d d₁ X.J W.J W₁.J H'.ι hH.gram z z'
    rw [M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_zero] at h4
    rw [hD] at h1 h2 h3 h4
    apply (AdeleRing.algebraMap_injective (𝓞 F) F)
    have ha1 : (fun i => algebraMap F (AF F) (a.1 i)) = (hat a).1 := rfl
    have ha2 : (fun i => algebraMap F (AF F) (a.2 i)) = (hat a).2 := rfl
    have hb1 : (fun i => algebraMap F (AF F) (b.1 i)) = (hat b).1 := rfl
    have hb2 : (fun i => algebraMap F (AF F) (b.2 i)) = (hat b).2 := rfl
    rw [RingHom.map_dotProduct, RingHom.map_dotProduct]
    simp only [Function.comp_def]
    rw [ha1, ha2, hb1, hb2, ea, eb]
    simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination h1 + h2 - h3 + h4
  refine ⟨lagr M M₁ H', hiso, ?_, ?_⟩
  ·
    have hrat := GlobalTheory.T.rational_model_coordinates F E σ n d X W M hP.good.rat
    have hrat₁ := GlobalTheory.T.rational_model_coordinates F E σ n d₁ X W₁ M₁ hP₁.good.rat
    obtain ⟨f, hf, hfe⟩ := hrat
    obtain ⟨f₁, hf₁, hfe₁⟩ := hrat₁
    have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
    obtain ⟨K, hK, hKz⟩ := GlobalTheory.T.rational_lagrangian_subspace_exists F E σ n d₁ X W₁ M₁ h2 f₁ hf₁ hfe₁
    have hinj := mul_transpose_injective F E σ n d d₁ W.J W₁.J H'.ι hH.gram
      (GlobalTheory.T.skew_determinant_ne_zero_first_space F E σ B d₁ W₁ r₁ s₁ hP₁.skew)
    refine le_antisymm ?_ ?_
    · exact GlobalTheory.T.lagrangian_dimension_bound F _ _ hiso
    · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact GlobalTheory.T.quadratic_injective_plane_coordinates F E σ n d d₁ X W W₁ M M₁ H' h2 hH.rank hH.xy (fun u => (hH.orth u).2) hinj f hf hfe K hK hKz
  ·
    intro t w hw
    obtain ⟨u, ⟨y, rfl⟩, z, hz, he⟩ := hw
    have ew : hat w = M.co.e (Matrix.vecMulVec y (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [← he, LinearEquiv.apply_symm_apply]
    refine ⟨Matrix.vecMulVec (t • y) (incV F H'.x), ⟨t • y, rfl⟩, t • z, by simp [hz], fun φ => ?_⟩
    have h0 := hcross _ ⟨t • y, rfl⟩ (t • z)
    rw [hD] at h0
    rw [Darboux.rho, Darboux.rho, schr_comp, ← map_add]
    have hs : (M.co.e (Matrix.vecMulVec (t • y) (incV F H'.x))).1 ⬝ᵥ
          (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ)).2 -
        (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ)).1 ⬝ᵥ
          (M.co.e (Matrix.vecMulVec (t • y) (incV F H'.x))).2 = 0 := by linear_combination -h0
    rw [hs, mul_zero, AddChar.map_zero_eq_one, one_smul]
    have hm : Matrix.vecMulVec (t • y) (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * (t • z) * (incM F H'.ι)ᵀ =
        t • (Matrix.vecMulVec y (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
      rw [smul_add, Matrix.smul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul]
    rw [hm, LinearEquiv.map_smul, ← ew]
    rfl

end GlobalTheory.MixedLagr

end
