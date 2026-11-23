import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForms_of_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J → ∃ γ : Γ, (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → (∀ ξ, Jm ξ ∈ ValC (gramC J emb) lam) → ∀ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (fun y : UPts σ J (FiniteAdeleRing (𝓞 F) F) => Jm (φ (Φ.symm (y * h0⁻¹)))) ∈ AdForms S emb lam := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm hψ hK hχ hΓ hJ hV φ hφ
  refine Submodule.mem_inf.2 ⟨?_, fun x _ => hV _⟩
  intro g hg x x' κ hx y y' hy
  obtain ⟨γ, hγ⟩ := hΓ g hg
  let κ' : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩
  let k : Gf := Φ.symm (h0 * κ' * h0⁻¹)
  have hk1 : h0⁻¹ * Φ k * h0 = κ' := by
    simp only [k, MulEquiv.apply_symm_apply]; group
  have hy1 : ((h0⁻¹ * Φ k * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U := by
    rw [hk1]; exact κ.2
  have hk : k ∈ K := (hK k).2 hy1
  have hc : ((ψ ⟨k, hk⟩ : ℂˣ) : ℂ) = ((S.chi κ : ℂˣ) : ℂ) := by
    rw [hχ k hk hy1]
    congr 2
    apply Subtype.ext
    show ((h0⁻¹ * Φ k * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
      GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = κ.1
    rw [hk1]
  have hx' : x' = Φ (ιf γ) * x * κ' := by
    apply Subtype.ext
    rw [hx, ← hγ]; rfl
  have hdec : Φ.symm (x' * h0⁻¹) = ιf γ * Φ.symm (x * h0⁻¹) * ((⟨k, hk⟩ : K) : Gf) := by
    apply Φ.injective
    simp only [k, map_mul Φ, MulEquiv.apply_symm_apply, hx']
    group
  have hconj : (starRingEnd ℂ) (((ψ ⟨k, hk⟩)⁻¹ : ℂˣ) : ℂ) = ((ψ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
    rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ _), Complex.conj_conj]
  show Jm (φ (Φ.symm (x' * h0⁻¹))) y = (S.chi κ : ℂ) * Jm (φ (Φ.symm (x * h0⁻¹))) y'
  rw [hdec, hφ, LinearMap.map_smulₛₗ, hconj, hc, Pi.smul_apply, smul_eq_mul, hJ γ g hγ _ y y' hy]

end GlobalTheory
