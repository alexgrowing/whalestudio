import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACR

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CR2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem U_swap (f f' : Fin (r + 1) → V) :
    Submodule.span E (Set.range (Sum.elim f' f)) = Submodule.span E (Set.range (Sum.elim f f')) := by
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.union_comm]

theorem Zhat_swap (f f' : Fin (r + 1) → V) :
    H.Zhat f' f = ((M.L.cj.toRingEquiv.toRingHom).mapMatrix (H.Zhat f f'))ᵀ := by
  ext a b
  simp only [HermSp.Zhat, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact H.h_herm _ _

theorem om'_swap (f f' : Fin (r + 1) → V) : H.om' f' f = H.om f f' := by
  unfold HermSp.om' HermSp.om
  rw [Zhat_swap, ← Matrix.adjugate_transpose, ← RingHom.map_adjugate]
  simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem det_Zhat_swap_unit (f f' : Fin (r + 1) → V) (h : IsUnit (H.Zhat f f').det) :
    IsUnit (H.Zhat f' f).det := by
  rw [Zhat_swap, Matrix.det_transpose, ← RingHom.map_det]
  exact h.map _

theorem cond_second_of_iso (g₁ g₁' g₂ g₂' : Fin (r + 1) → V) (T₁ T₂ : F) (hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H g₁ T₁)
    (hF₂ : Formalism.MainNotions.ThinScalesBound.FrameK H g₂ T₂) (hZ₁ : IsUnit (H.Zhat g₁ g₁').det) (χ : H.Wb g₁ ≃ₗ[E] H.Wb g₂) (κ : E)
    (hz : χ (H.mkW g₁ ⟨g₁ (Fin.last r), z_mem_perpX H hF₁⟩) = H.mkW g₂ ⟨g₂ (Fin.last r), z_mem_perpX H hF₂⟩)
    (ho : χ (H.mkW g₁ ⟨H.om' g₁ g₁', om'_mem_perpX H _ _⟩) = κ • H.mkW g₂ ⟨H.om' g₂ g₂', om'_mem_perpX H _ _⟩) :
    ∀ u ∈ Submodule.span E (Set.range (Sum.elim g₁ g₁')), ∀ hu : u ∈ H.perp (H.X g₁),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim g₂ g₂')), ∃ hu' : u' ∈ H.perp (H.X g₂),
        χ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩ := by
  intro u hu hup
  obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
  let zP₁ : ↥(H.perp (H.X g₁)) := ⟨g₁ (Fin.last r), z_mem_perpX H hF₁⟩
  let oP₁ : ↥(H.perp (H.X g₁)) := ⟨H.om' g₁ g₁', om'_mem_perpX H _ _⟩
  let zP₂ : ↥(H.perp (H.X g₂)) := ⟨g₂ (Fin.last r), z_mem_perpX H hF₂⟩
  let oP₂ : ↥(H.perp (H.X g₂)) := ⟨H.om' g₂ g₂', om'_mem_perpX H _ _⟩
  have h1 : H.mkW g₁ ⟨u, hup⟩ = H.mkW g₁ (β • zP₁ + γ • oP₁) := by
    apply mkW_eq_of_sub_mem
    show u - (β • g₁ (Fin.last r) + γ • H.om' g₁ g₁') ∈ H.X g₁
    rw [hxe]
    convert hx using 1
    abel
  refine ⟨((β • zP₂ + (γ * κ) • oP₂ : ↥(H.perp (H.X g₂))) : V), ?_, (β • zP₂ + (γ * κ) • oP₂).2, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
      (Submodule.smul_mem _ _ (om'_mem_U H g₂ g₂'))
  · rw [h1]
    simp only [map_add, map_smul]
    rw [show χ (H.mkW g₁ zP₁) = H.mkW g₂ zP₂ from hz, show χ (H.mkW g₁ oP₁) = κ • H.mkW g₂ oP₂ from ho, smul_smul]
    show _ = H.mkW g₂ (β • zP₂ + (γ * κ) • oP₂)
    rw [map_add, map_smul, map_smul]

end CR2

end Formalism.L2.SG.LsDatumA
