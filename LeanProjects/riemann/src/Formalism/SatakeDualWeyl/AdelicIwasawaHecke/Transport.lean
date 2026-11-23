import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem transport_cT_map {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) {m p : Type} (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem transport_bc_mem {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n]
    [DecidableEq n] (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  rw [transport_cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem transport_symm_comp {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A ≃+* B) (h : (φ : A →+* B).comp σ = σ'.comp φ) :
    (φ.symm : B →+* A).comp σ' = σ.comp φ.symm := by
  ext x
  have h1 := RingHom.congr_fun h (φ.symm x)
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h1 ⊢
  rw [← h1, RingEquiv.symm_apply_apply]

theorem unitary_group_transport : Formalism.UG.UJTransport := by
  intro A B _ _ n _ _ σ σ' φ h J
  have hs := transport_symm_comp σ σ' φ h
  refine ⟨{ toFun := fun g => ⟨bc (φ : A →+* B) g, transport_bc_mem σ σ' φ h J g g.2⟩
            invFun := fun g => ⟨bc (φ.symm : B →+* A) g, by
              have hm := transport_bc_mem σ' σ (φ.symm : B →+* A) hs (J.map φ) g g.2
              have hJ : (J.map φ).map (φ.symm : B →+* A) = J := by ext i j; simp
              rwa [hJ] at hm⟩
            left_inv := fun g => by
              apply Subtype.ext; apply Units.ext; ext i j; simp [bc]
            right_inv := fun g => by
              apply Subtype.ext; apply Units.ext; ext i j; simp [bc]
            map_mul' := fun a b => by
              apply Subtype.ext; simp }, fun g => rfl⟩

theorem split_group_points : Formalism.UG.SplitPts := by
  intro F E _ _ _ n _ _ σ J R _ _ φ hφ
  have hc : (φ : E ⊗[F] R →+* R × R).comp (sigR σ R) = (swapR R).comp φ := RingHom.ext hφ
  obtain ⟨e, he⟩ := unitary_group_transport (E ⊗[F] R) (R × R) n (sigR σ R) (swapR R) φ hc
    (J.map (inclE (F := F) R))
  exact ⟨e, he⟩

end Formalism.UG.P
