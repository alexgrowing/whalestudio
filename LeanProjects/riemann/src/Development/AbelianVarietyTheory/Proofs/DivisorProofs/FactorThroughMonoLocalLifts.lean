import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBasis

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.CoverHom

theorem exists_factor_of_affineCover : ∀ (X : Scheme.{0}) (F E G : X.Modules) [F.IsQuasicoherent] [E.IsQuasicoherent] [G.IsQuasicoherent] (u : F ⟶ G) (ι : E ⟶ G) [Mono ι] (I : Type) (V : I → X.Opens), (∀ i, IsAffineOpen (V i)) → (∀ x : X, ∃ i, x ∈ V i) → (∀ i (s : Γ(F, V i)), ∃ s' : Γ(E, V i), ι.app _ s' = u.app _ s) → ∃ v : F ⟶ E, v ≫ ι = u := by
  intro X F E G _ _ _ u ι _ I V hV hx h
  have hc : iSup V = ⊤ := top_unique fun x _ => Opens.mem_iSup.2 (hx x)
  have hcov : IsOpenCover V := hc
  have h0 : u ≫ cokernel.π ι = 0 := by
    refine (GlobalTheory.QCoh.hom_eq_zero_iff_affineCover V hcov hV (u ≫ cokernel.π ι)).2 fun i s => ?_
    exact (GlobalTheory.QCoh.exact_cokernel_π_app ι (hV i) (u.app _ s)).2 (h i s)
  exact ⟨Abelian.monoLift ι u h0, Abelian.monoLift_comp ι u h0⟩

end GlobalTheory.CoverHom
