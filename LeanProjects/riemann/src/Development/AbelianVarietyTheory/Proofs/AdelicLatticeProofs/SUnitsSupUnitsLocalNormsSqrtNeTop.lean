import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowLeIndexLocalNormsSqrtExtensionStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem normSub_id_le_normSub {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F) :
    normSub (RingHom.id F) δ ≤ normSub φ δ := by
  intro x hx
  obtain ⟨a, b, hab⟩ := (mem_normSub _ _ x).1 hx
  refine (mem_normSub _ _ x).2 ⟨φ a, φ b, ?_⟩
  have hab' : (x : F) = a ^ 2 - δ * b ^ 2 := hab
  rw [hab']
  simp [map_sub, map_mul, map_pow]

theorem normSub_id_le_locNorm (F : Type) [Field F] [NumberField F] (δ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    normSub (RingHom.id F) δ ≤ locNorm F δ S :=
  le_inf (le_iInf₂ fun _ _ => normSub_id_le_normSub _ δ)
    (le_iInf fun _ => normSub_id_le_normSub _ δ)

theorem sUnits_sup_locNorm_ne_top : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by
  intro F _ _ δ S hS hδ hsq htop
  obtain ⟨hne, hle⟩ := GlobalTheory.T.two_mul_relIndex_normSub_sUnits_le F δ S hS hδ hsq
  obtain ⟨-, hge⟩ := GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension F (δ : F) S δ.ne_zero
  have h1 : (locNorm F δ S).index = (locNorm F δ S).relIndex (sUnits F S) := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have h2 : (locNorm F δ S).relIndex (sUnits F S) ≤
      (normSub (RingHom.id F) (δ : F)).relIndex (sUnits F S) :=
    Subgroup.relIndex_le_of_le_left (normSub_id_le_locNorm F δ S) hne
  omega

end GlobalTheory.QNorm
