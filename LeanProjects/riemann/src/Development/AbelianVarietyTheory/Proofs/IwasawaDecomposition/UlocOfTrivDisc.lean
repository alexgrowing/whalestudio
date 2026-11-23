import Mathlib
import Formalism.LocalToGlobal.HermitianForms.DefsGH
import Formalism.LocalToGlobal.Columns.RecLevelLocT

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem uloc_of_triv_disc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (_ : (T : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ levelVL σ J v S.Lb)
    (_ : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb),
    x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad S v hT x hx hy
  have hL : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    unfold Formalism.UG.levelVL Formalism.UG.level at hx
    exact hx.2
  have hLi : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb :=
    (stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)).inv_mem hL
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    unfold Formalism.UG.latS
    apply Submodule.span_mono
    apply Set.image_mono
    intro z hz
    exact Submodule.subset_span (S.Lb_int z hz)
  have hfw : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hy'
    have h2 := Submodule.add_mem _ (hsub (hy y hy')) hy'
    rwa [sub_add_cancel] at h2
  have hbw : ∀ y, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) →
      y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hw
    have hd := hy _ hw
    have hi := hsub ((hLi _).1 hd)
    have key : y = (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y -
        ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
            ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) -
            (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) := by
      have hinv : ∀ u, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ u) = u := by
        intro u
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Matrix.mulVec_sub, hinv, hinv, sub_sub_cancel]
    rw [key]
    exact Submodule.sub_mem _ hw hi
  rw [S.UlocAlt v hT, Subgroup.mem_inf]
  refine ⟨hx, ⟨?_, ?_⟩⟩
  · show ∀ y, y ∈ _ ↔ _
    exact fun y => ⟨hfw y, hbw y⟩
  · intro z
    have h0 := S.fT_L v hT
      (⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F), hfw z z.2⟩ - z)
      (by
        show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F) -
          (z : Fin n → E ⊗[F] v.adicCompletion F) ∈ _
        exact hy z z.2)
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end GlobalTheory
