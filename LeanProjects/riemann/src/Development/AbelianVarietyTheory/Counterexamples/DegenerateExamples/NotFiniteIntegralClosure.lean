import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

noncomputable section

namespace GlobalTheory.GoodProjectorTest

open Formalism.BasicNotions Formalism.MainNotions

def noPar (D : D7) : D7 :=
  { D with
    ntypes := { D.ntypes with
      Par := PEmpty
      labPar := fun _ σ => σ.elim
      labPar_monic := fun _ σ => σ.elim
      locPar := fun σ => σ.elim
      locPar_dim := fun σ => σ.elim
      labPar_def := fun _ σ => σ.elim
      MtPar := fun _ _ σ => σ.elim
      AmbPar := fun _ σ => σ.elim }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat
    nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    bc_tie := D.bc_tie
    rbar_tie := D.rbar_tie
    mtpar_tie := fun _ σ => σ.elim }

def withAmb (D : D7) (S : ∀ μ, D.ntypes.Par → Submodule ℂ (D.what₂.Amb μ)) : D7 :=
  { D with
    ntypes := { D.ntypes with AmbPar := S }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat
    nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    bc_tie := D.bc_tie
    rbar_tie := D.rbar_tie
    mtpar_tie := D.mtpar_tie }

def AlgebraPart (D : D7) : Prop :=
  (∀ g : G0g D.nd, D.ntypes.e0.coeff g ∈ D.ntypes.Qchi) ∧
  (∀ g : G0g D.nd, IsIntegral ℤ ((Nat.card (G0g D.nd) : ℂ) * D.ntypes.e0.coeff g)) ∧
  (∀ a : MonoidAlgebra ℂ (G0g D.nd), D.ntypes.e0 * a = a * D.ntypes.e0) ∧
  (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) (MM : AddSubgroup V),
    (∀ a : ℂ, IsIntegral ℤ a → ∀ x ∈ MM, a • x ∈ MM) → (∀ g, ∀ x ∈ MM, ρ g x ∈ MM) →
    let e := ρ.asAlgebraHom D.ntypes.e0
    let c : ℂ := (Nat.card (G0g D.nd) : ℂ)
    (∀ x ∈ MM, c • e x ∈ MM ∧ c • e x ∈ LinearMap.range e) ∧
    (∀ y ∈ MM, y ∈ LinearMap.range e → ∃ x ∈ MM, e x = y) ∧
    (∀ x ∈ MM, ∃ u ∈ MM, ∃ z ∈ MM, u ∈ LinearMap.range e ∧
      z ∈ LinearMap.range (LinearMap.id - e) ∧ c • x = u + z))

theorem not_finite_integralClosure : ¬ Module.Finite ℤ (integralClosure ℤ ℂ) := by
  intro hf
  haveI : IsNoetherianRing (integralClosure ℤ ℂ) := isNoetherian_of_tower ℤ inferInstance
  have h2 : (2 : integralClosure ℤ ℂ) ≠ 0 := two_ne_zero
  have hu : ¬ IsUnit (2 : integralClosure ℤ ℂ) := by
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : (2 : ℂ) * (b : ℂ) = 1 := congrArg (Subtype.val) hb
    have hbq : (b : ℂ) = algebraMap ℚ ℂ (1 / 2) := by
      simp only [one_div, map_inv₀, map_ofNat]; field_simp; linear_combination hb'
    have hi : IsIntegral ℤ (algebraMap ℚ ℂ (1 / 2)) := hbq ▸ b.2
    rw [isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at hi
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    have hz' : (2 * z : ℚ) = 1 := by simp at hz; rw [hz]; norm_num
    have : (2 * z : ℤ) = 1 := by exact_mod_cast hz'
    omega
  obtain ⟨p, hp, -⟩ := WfDvdMonoid.exists_irreducible_factor hu h2
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (p : ℂ)
  replace hs := hs.symm
  have hsi : IsIntegral ℤ s := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [pow_two, hs]; exact p.2
  have hp' : p = (⟨s, hsi⟩ : integralClosure ℤ ℂ) * ⟨s, hsi⟩ := Subtype.ext hs.symm
  have : IsUnit (⟨s, hsi⟩ : integralClosure ℤ ℂ) := by
    rcases hp.isUnit_or_isUnit hp' with h | h <;> exact h
  exact hp.not_isUnit (hp' ▸ this.mul this)

theorem lattice_eq_bot {V : Type} [AddCommGroup V] [Module ℂ V] (MM : AddSubgroup V)
    (hs : ∀ a : ℂ, IsIntegral ℤ a → ∀ x ∈ MM, a • x ∈ MM) (hfg : Module.Finite ℤ MM) : MM = ⊥ := by
  by_contra hne
  obtain ⟨⟨x, hx⟩, hx0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).1 hne
  have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  let f : integralClosure ℤ ℂ →+ MM :=
    { toFun := fun a => ⟨(a : ℂ) • x, hs a a.2 x hx⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp [add_smul]) }
  have hinj : Function.Injective f.toIntLinearMap := by
    intro a b hab
    have : (a : ℂ) • x = (b : ℂ) • x := congrArg Subtype.val hab
    exact Subtype.ext (smul_left_injective ℂ hx0' this)
  exact not_finite_integralClosure (Module.Finite.of_injective _ hinj)

def ParOnto (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Sig : List (Part D.naut.CG)),
    N.IsBCV D.nd D.naut i P (N.twistIso D.nd D.naut (Sig ++ [N.muPart D.nd D.naut i]) D.naut.etaTinv) →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (N.isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r) →
    ∃ σ : D.ntypes.Par, ∀ w, N.isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ w

end GlobalTheory.GoodProjectorTest
