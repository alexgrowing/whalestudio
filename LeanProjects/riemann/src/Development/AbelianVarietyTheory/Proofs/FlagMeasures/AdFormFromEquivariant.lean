import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForm_from_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → Function.Injective Jm → (∀ p ∈ ValC (gramC J emb) lam, ∃ ξ, Jm ξ = p) → ∀ g ∈ AdForms S emb lam, ∃ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) ∧ ∀ y : UPts σ J (FiniteAdeleRing (𝓞 F) F), g y = Jm (φ (Φ.symm (y * h0⁻¹))) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm
    hψ hK hχ hrat hint hinj hsurj g hg

  have hval : ∀ z, g z ∈ ValC (gramC J emb) lam := fun z => (Submodule.mem_inf.mp hg).2 z (Set.mem_univ z)
  have hfun := (Submodule.mem_inf.mp hg).1
  choose pre hpre using fun z => hsurj (g z) (hval z)
  refine ⟨fun x => pre (Φ x * h0), ?_, ?_⟩
  · intro γ x κ
    obtain ⟨gr, hgrU, hgr⟩ := hrat γ
    apply hinj
    rw [hpre, LinearMap.map_smulₛₗ]
    funext y
    obtain ⟨y', hy'⟩ := exists_isTr' emb gr y
    rw [Pi.smul_apply, hint γ gr hgr (pre (Φ x * h0)) y y' hy', hpre]

    have hconj : (starRingEnd ℂ) ((((ψ κ)⁻¹ : ℂˣ) : ℂ)) = ((ψ κ : ℂˣ) : ℂ) := by
      rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ κ), Complex.conj_conj]
    rw [smul_eq_mul, hconj]
    have hk : ((h0⁻¹ * Φ κ.1 * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U :=
      (hK κ.1).1 κ.2
    have hx : (Φ (ιf γ * x * κ.1) * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
        Φ (ιf γ) * (Φ x * h0) * (h0⁻¹ * Φ κ.1 * h0) := by
      simp only [map_mul]; group
    have key := hfun gr hgrU (Φ x * h0) (Φ (ιf γ * x * κ.1) * h0) ⟨_, hk⟩
      (by rw [hx, Subgroup.coe_mul, Subgroup.coe_mul, hgr]) y y' hy'
    rw [key, ← hχ κ.1 κ.2 hk]
  · intro y
    rw [hpre]
    congr 1
    simp

end GlobalTheory
