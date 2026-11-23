import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetBasic

open MvPolynomial

variable {S : Type} [Field S] {ρ : Type}

theorem jet_const_add_nil (m : ℕ) (x : Jet S ρ m) :
    ∃ c : S, ∃ n : Jet S ρ m, IsNilpotent n ∧ x = algebraMap S (Jet S ρ m) c + n := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨MvPolynomial.constantCoeff P, Ideal.Quotient.mk _ (P - C (MvPolynomial.constantCoeff P)), ?_, ?_⟩
  · refine ⟨m + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (sub_const_mem_orig P) _
  · rw [map_sub, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]
    ring

theorem isLocalRing_jet (m : ℕ) : IsLocalRing (Jet S ρ m) := by
  haveI : Nontrivial (Jet S ρ m) := (jetAug : Jet S ρ m →ₐ[S] S).toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨c, n, hn, rfl⟩ := jet_const_add_nil m x
  by_cases hc : c = 0
  · right
    subst hc
    rw [map_zero, zero_add]
    convert hn.neg.isUnit_add_right_of_commute isUnit_one (Commute.one_right _) using 1
    ring
  · left
    convert hn.isUnit_add_right_of_commute ((isUnit_iff_ne_zero.2 hc).map (algebraMap S (Jet S ρ m))) (Commute.all _ _) using 1
    ring

theorem ker_trunc_sq (m : ℕ) :
    RingHom.ker (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ^ 2 = ⊥ := by
  have hle : RingHom.ker (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ≤
      Ideal.map (Ideal.Quotient.mk (orig S ρ ^ (m + 1 + 1))) (orig S ρ ^ (m + 1)) := by
    intro x hx
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker] at hx
    have hP : P ∈ orig S ρ ^ (m + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    exact Ideal.mem_map_of_mem _ hP
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle 2).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul]
  refine (Ideal.map_mono (Ideal.pow_le_pow_right (show m + 1 + 1 ≤ (m + 1) * 2 by omega))).trans ?_
  rw [Ideal.map_quotient_self]

theorem jet_zero_const :
    (Algebra.ofId S (Jet S ρ 0)).comp (jetAug : Jet S ρ 0 →ₐ[S] S) = AlgHom.id S (Jet S ρ 0) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro r
  have h0 : (Ideal.Quotient.mk (orig S ρ ^ (0 + 1)) (X r)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
    exact X_mem_orig r
  show algebraMap S (Jet S ρ 0) ((jetAug : Jet S ρ 0 →ₐ[S] S) (Ideal.Quotient.mk (orig S ρ ^ (0 + 1)) (X r))) =
    Ideal.Quotient.mk (orig S ρ ^ (0 + 1)) (X r)
  rw [h0, map_zero, map_zero]

theorem jet_basic : ∀ {S : Type} [Field S] {ρ : Type} (m : ℕ),
    IsLocalRing (Jet S ρ m) ∧ RingHom.ker (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ^ 2 = ⊥ ∧
    (Algebra.ofId S (Jet S ρ 0)).comp (jetAug : Jet S ρ 0 →ₐ[S] S) = AlgHom.id S (Jet S ρ 0) :=
  fun m => ⟨isLocalRing_jet m, ker_trunc_sq m, jet_zero_const⟩

end GlobalTheory.JetBasic
