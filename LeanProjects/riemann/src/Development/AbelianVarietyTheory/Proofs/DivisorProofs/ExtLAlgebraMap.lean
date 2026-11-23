import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivationExtensionBasicOpen

noncomputable section
set_option autoImplicit false

namespace GlobalTheory.LogDerProj

def logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) :
    Submodule A (Derivation ℤ A A) where
  carrier := {D | (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J}
  zero_mem' := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  add_mem' := fun {D D'} h h' =>
    ⟨fun a => by simp [h.1 a, h'.1 a], fun g hg => add_mem (h.2 g hg) (h'.2 g hg)⟩
  smul_mem' := fun r D h =>
    ⟨fun a => by simp [h.1 a], fun g hg => Ideal.mul_mem_left _ r (h.2 g hg)⟩

theorem mem_logSub {k A : Type} [CommRing k] [CommRing A] (φ : k →+* A) (J : Ideal A) (D : Derivation ℤ A A) :
    D ∈ logSub φ J ↔ (∀ a, D (φ a) = 0) ∧ ∀ g ∈ J, D g ∈ J := Iff.rfl

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S]
include f

def ext (D : Derivation ℤ R R) : Derivation ℤ S S :=
  Classical.choose (GlobalTheory.LogDerLoc.exists_extension (B := S) f D)

theorem ext_algebraMap (D : Derivation ℤ R R) (r : R) :
    ext (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  Classical.choose_spec (GlobalTheory.LogDerLoc.exists_extension (B := S) f D) r

theorem der_ext (D₁ D₂ : Derivation ℤ S S) (h : ∀ r, D₁ (algebraMap R S r) = D₂ (algebraMap R S r)) :
    D₁ = D₂ := by
  ext y
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) y
  have hu : IsUnit (algebraMap R S t) := IsLocalization.map_units S t
  have e' : y * algebraMap R S t = algebraMap R S r := e
  have h1 := congrArg D₁ e'
  have h2 := congrArg D₂ e'
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1 h2
  rw [h r, h t] at h1
  have : algebraMap R S t * D₁ y = algebraMap R S t * D₂ y := by linear_combination h1 - h2
  exact hu.mul_left_cancel this

def extL : Derivation ℤ R R →ₗ[R] Derivation ℤ S S where
  toFun := ext f
  map_add' D D' := der_ext f _ _ fun r => by
    rw [ext_algebraMap, Derivation.add_apply, Derivation.add_apply, ext_algebraMap, ext_algebraMap, map_add]
  map_smul' c D := der_ext f _ _ fun r => by
    rw [ext_algebraMap, RingHom.id_apply, Derivation.smul_apply, Derivation.smul_apply, ext_algebraMap,
      smul_eq_mul, map_mul, Algebra.smul_def]

theorem extL_algebraMap (D : Derivation ℤ R R) (r : R) :
    extL (S := S) f D (algebraMap R S r) = algebraMap R S (D r) :=
  ext_algebraMap f D r

variable {k : Type} [CommRing k]

def res (φ : k →+* R) (J : Ideal R) :
    logSub φ J →ₗ[R] (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R where
  toFun D := ⟨extL f D.1, fun a => by
      rw [RingHom.comp_apply, extL_algebraMap, D.2.1 a, map_zero],
    GlobalTheory.LogDerLoc.map_mem_map (algebraMap R S) D.1 (extL f D.1) (extL_algebraMap f D.1) J D.2.2⟩
  map_add' D D' := Subtype.ext (map_add (extL (S := S) f) D.1 D'.1)
  map_smul' c D := Subtype.ext (map_smul (extL (S := S) f) c D.1)

theorem res_apply (φ : k →+* R) (J : Ideal R) (D : logSub φ J) (r : R) :
    (res (S := S) f φ J D).1 (algebraMap R S r) = algebraMap R S (D.1 r) :=
  ext_algebraMap f D.1 r

end GlobalTheory.LogDerProj
