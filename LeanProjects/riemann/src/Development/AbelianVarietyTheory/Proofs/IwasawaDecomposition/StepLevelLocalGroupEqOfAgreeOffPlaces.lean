import Mathlib
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

noncomputable section

namespace GlobalTheory

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}

theorem stepLevel_uloc_le_of_agree {bad bad' : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F)))
    (hQ : ∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → x ∈ S.U → x ∈ S'.U)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Q) : S.Uloc v ≤ S'.Uloc v := by
  intro h hh
  have hx1 : bc (prV (E := E) v) (Formalism.UG.P.afsplitU v h 1) = h := Formalism.UG.P.afsplit_right1 v h 1
  have hxw : ∀ w, w ≠ v → bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h 1) = 1 := by
    intro w hw
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
      Units.val_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxU : Formalism.UG.P.afsplitU v h 1 ∈ S.U := by
    rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v σ J h 1 (S.Uloc_le v hh) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · rw [hw, hx1]; exact hh
    · rw [hxw w hw]; exact one_mem _
  have hxQ : ∀ w ∈ Q, bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h 1) = 1 :=
    fun w hw => hxw w (fun he => hv (he ▸ hw))
  have h2 := ((S'.U_eq _).mp (hQ _ hxQ hxU)).2 v
  rwa [hx1] at h2

end

theorem stepLevel_uloc_eq_of_agree : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad bad' : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (S' : StepLevel F E σ J T f bad') (Q : Set (HeightOneSpectrum (𝓞 F))),
    (∀ x, (∀ v ∈ Q, bc (prV (E := E) v) x = 1) → (x ∈ S.U ↔ x ∈ S'.U)) → ∀ v, v ∉ Q → S.Uloc v = S'.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad bad' S S' Q hQ v hv
  exact le_antisymm (stepLevel_uloc_le_of_agree S S' Q (fun x hx => (hQ x hx).mp) v hv)
    (stepLevel_uloc_le_of_agree S' S Q (fun x hx => (hQ x hx).mpr) v hv)

end GlobalTheory
