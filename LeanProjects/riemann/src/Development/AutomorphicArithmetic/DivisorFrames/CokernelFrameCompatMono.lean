import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.Twist (resM)

private theorem hom_ext_frame {X : Scheme.{0}} {F G : X.Modules} {κ : Type} [Fintype κ] {e : κ → Γ(F, ⊤)}
    (he : IsFrame e) {φ ψ : F ⟶ G} (h : ∀ i, φ.app ⊤ (e i) = ψ.app ⊤ (e i)) : φ = ψ := by
  ext V s
  refine congr($((he.basis le_top).ext (f₁ := QCoh.appLinear φ V) (f₂ := QCoh.appLinear ψ V)
    fun i => ?_) s)
  rw [IsFrame.basis_apply]
  exact (Twist.app_resM φ _ _).trans ((congrArg _ (h i)).trans (Twist.app_resM ψ _ _).symm)

theorem UpperTheory.cokernel_frame_compat_mono :
    ∀ (X : Scheme.{0}) (E A A' : X.Modules) (u : A ⟶ E) (v : A' ⟶ E) (m r : ℕ) (e : Fin m ⊕ Fin r → Γ(E, ⊤))
        (a : Fin m → Fin r → Γ(X, ⊤)), Mono u → Mono v → IsFrame e →
        IsFrame (fun k => (cokernel.π u).app ⊤ (e (Sum.inr k))) →
        (∀ i, (cokernel.π u).app ⊤ (e (Sum.inl i)) = ∑ k, a i k • (cokernel.π u).app ⊤ (e (Sum.inr k))) →
        IsFrame (fun k => (cokernel.π v).app ⊤ (e (Sum.inr k))) →
        (∀ i, (cokernel.π v).app ⊤ (e (Sum.inl i)) = ∑ k, a i k • (cokernel.π v).app ⊤ (e (Sum.inr k))) →
        ∃ φ : A ≅ A', φ.hom ≫ v = u := by
  intro X E A A' u v m r e a hu hv he fu au fv av
  have key : cokernel.π u ≫ (IsFrame.iso fu fv).hom = cokernel.π v := by
    refine hom_ext_frame he fun i => ?_
    rw [← QCoh.app_app]
    rcases i with i | k
    · rw [au, av]
      refine (map_sum (QCoh.appLinear (IsFrame.iso fu fv).hom ⊤) _ _).trans
        (Finset.sum_congr rfl fun k _ => ?_)
      rw [map_smul]
      exact congrArg _ (IsFrame.iso_hom_app fu fv k)
    · exact IsFrame.iso_hom_app fu fv k
  have h1 : u ≫ cokernel.π v = 0 := by
    rw [← key, ← Category.assoc, cokernel.condition, zero_comp]
  have h2 : v ≫ cokernel.π u = 0 := by
    rw [← cancel_mono (IsFrame.iso fu fv).hom, Category.assoc, key, cokernel.condition, zero_comp]
  have hf := Abelian.monoLift_comp v u h1
  have hg := Abelian.monoLift_comp u v h2
  exact ⟨⟨Abelian.monoLift v u h1, Abelian.monoLift u v h2,
    by rw [← cancel_mono u, Category.assoc, hg, hf, Category.id_comp],
    by rw [← cancel_mono v, Category.assoc, hf, hg, Category.id_comp]⟩, hf⟩
