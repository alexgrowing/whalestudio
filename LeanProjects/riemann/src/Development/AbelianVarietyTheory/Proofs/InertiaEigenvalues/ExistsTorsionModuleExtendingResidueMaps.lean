import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup

open CategoryTheory GlobalTheory.SelFun

namespace GlobalTheory.SelFun

theorem exists_factor_of_injective {Λ : Type} [CommRing Λ] {X Y J : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] [AddCommGroup J] [Module Λ J] (hJ : Module.Injective Λ J)
    (g : X →ₗ[Λ] Y) (ψ : X →ₗ[Λ] J) (h : LinearMap.ker g ≤ LinearMap.ker ψ) :
    ∃ u : Y →ₗ[Λ] J, ∀ x, u (g x) = ψ x := by
  have hi : Function.Injective ((LinearMap.ker g).liftQ g le_rfl) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨u, hu⟩ := hJ.out ((LinearMap.ker g).liftQ g le_rfl) hi ((LinearMap.ker g).liftQ ψ h)
  refine ⟨u, fun x => ?_⟩
  simpa using hu (Submodule.Quotient.mk x)

def powTorsion {Λ : Type} [CommRing Λ] (I : Ideal Λ) (J : Type) [AddCommGroup J] [Module Λ J] : Submodule Λ J where
  carrier := {b | ∃ n : ℕ, ∀ x ∈ I ^ n, x • b = 0}
  zero_mem' := ⟨0, fun x _ => smul_zero x⟩
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, fun x hx => ?_⟩
    rw [smul_add, hn x (Ideal.pow_le_pow_right (Nat.le_add_right n m) hx),
      hm x (Ideal.pow_le_pow_right (Nat.le_add_left m n) hx), add_zero]
  smul_mem' := by
    rintro c a ⟨n, hn⟩
    exact ⟨n, fun x hx => by rw [smul_comm, hn x hx, smul_zero]⟩

theorem residue_smul_eq_zero {Λ : Type} [CommRing Λ] [IsLocalRing Λ] (x : Λ) (hx : x ∈ IsLocalRing.maximalIdeal Λ)
    (a : IsLocalRing.ResidueField Λ) : x • a = 0 := by
  rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff x).2 hx, zero_mul]

theorem exists_torsion_extension (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] (P : Type) [AddCommGroup P]
    [Module Λ P] [Module.Finite Λ P] (N : Submodule Λ P) :
    ∃ (B : ModuleCat.{0} Λ) (f : IsLocalRing.ResidueField Λ →ₗ[Λ] B), Tors Λ B ∧ Function.Injective f ∧
      ∀ φ : N →ₗ[Λ] IsLocalRing.ResidueField Λ, ∃ u : P →ₗ[Λ] B, u ∘ₗ N.subtype = f ∘ₗ φ := by
  let k := ModuleCat.of Λ (IsLocalRing.ResidueField Λ)
  let J := Injective.under k
  let ι : IsLocalRing.ResidueField Λ →ₗ[Λ] J := (Injective.ι k).hom
  have hι : Function.Injective ι := (ModuleCat.mono_iff_injective (Injective.ι k)).1 inferInstance
  have hJ : Module.Injective Λ J := Module.injective_module_of_injective_object Λ J (inj := Injective.injective_under k)
  let m := IsLocalRing.maximalIdeal Λ
  have hmem : ∀ a, ι a ∈ powTorsion m J := fun a =>
    ⟨1, fun x hx => by rw [← map_smul, residue_smul_eq_zero x (by rwa [pow_one] at hx), map_zero]⟩
  refine ⟨ModuleCat.of Λ (powTorsion m J), ι.codRestrict _ hmem, ?_, ?_, ?_⟩
  · rintro ⟨b, n, hn⟩
    exact ⟨n, fun x hx => Subtype.ext (hn x hx)⟩
  · intro a b hab
    exact hι (congrArg Subtype.val hab)
  · intro φ
    obtain ⟨n, hn⟩ := Ideal.exists_pow_inf_eq_pow_smul m N
    have h1 := hn (n + 1) (Nat.le_succ n)
    rw [Nat.add_sub_cancel_left, pow_one] at h1
    let K : Submodule Λ P := m ^ (n + 1) • ⊤
    have hK : K ⊓ N ≤ m • N := by
      rw [show K ⊓ N = _ from h1]
      exact Submodule.smul_mono le_rfl inf_le_right
    have hker : LinearMap.ker (K.mkQ ∘ₗ N.subtype) ≤ LinearMap.ker (ι ∘ₗ φ) := by
      intro y hy
      have hy1 : (y : P) ∈ K := by simpa using hy
      have hy2 : (y : P) ∈ m • N := hK ⟨hy1, y.2⟩
      have hy3 : y ∈ (m • ⊤ : Submodule Λ N) := by
        rwa [Submodule.mem_smul_top_iff]
      have : φ y = 0 := by
        refine Submodule.smul_induction_on (p := fun y => φ y = 0) hy3 ?_ ?_
        · intro r hr z _
          rw [map_smul, residue_smul_eq_zero r hr]
        · intro a b ha hb
          rw [map_add, ha, hb, add_zero]
      simp [this]
    obtain ⟨u, hu⟩ := exists_factor_of_injective hJ _ _ hker
    have hu2 : ∀ p, (u ∘ₗ K.mkQ) p ∈ powTorsion m J := fun p =>
      ⟨n + 1, fun x hx => by
        rw [← map_smul]
        have : K.mkQ (x • p) = 0 :=
          (Submodule.Quotient.mk_eq_zero K).2 (Submodule.smul_mem_smul hx Submodule.mem_top)
        rw [LinearMap.comp_apply, this, map_zero]⟩
    refine ⟨(u ∘ₗ K.mkQ).codRestrict _ hu2, ?_⟩
    ext y
    exact hu y

end GlobalTheory.SelFun
