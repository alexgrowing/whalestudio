import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ArithTrdeg

theorem trdeg_functionField_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D) :
    Algebra.trdeg ℤ X.functionField = D := by
  have hft := DimCoheight.finiteType_of_isAmb (MixHt.isAmb_of_isArithVar h)
  have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat

  have key : ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      ringKrullDim Γ(X, U) =
        ((Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) : WithBot ℕ∞) := by
    intro U hU hne
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    have : CharZero Γ(X, U) :=
      ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hc0
    have hinj : Function.Injective (algebraMap ℤ Γ(X, U)) := RingHom.injective_int _
    have : FaithfulSMul ℤ Γ(X, U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one _ hinj,
      ← DimCoheight.trdeg_eq_of_isFractionRing ℤ Γ(X, U) X.functionField]
  have hdim : ((Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) : WithBot ℕ∞) =
      ((D + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← h.dim_eq]
    apply le_antisymm
    · obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
      have hU : IsAffineOpen U := hU
      rw [← key U hU ⟨⟨_, hxU⟩⟩, ← Published.dim_affineOpen hU]
      exact topologicalKrullDim_subspace_le X (U : Set X)
    · refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      have hU : IsAffineOpen U := hU
      refine ⟨(U : Set X), U.isOpen, hyU, ?_⟩
      rw [Published.dim_affineOpen hU, key U hU ⟨⟨y, hyU⟩⟩]
  have h2 : Cardinal.toENat (Algebra.trdeg ℤ X.functionField) = D := by
    have h3 : (Cardinal.toENat (Algebra.trdeg ℤ X.functionField) + 1 : ℕ∞) = ((D : ℕ∞) + 1) := by
      exact_mod_cast hdim
    exact (WithTop.add_right_cancel (ENat.one_ne_top) h3)
  exact Cardinal.toENat_eq_natCast.1 h2

theorem isTranscendenceBasis_functionField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    (∃ x : Fin D → X.functionField, IsTranscendenceBasis ℤ x) ∧
      ∀ x : Fin D → X.functionField, AlgebraicIndependent ℤ x → IsTranscendenceBasis ℤ x := by
  intro k _ X _ p D h
  have htr := trdeg_functionField_eq h
  refine ⟨?_, fun x hx => hx.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr]; simp)⟩
  have : FaithfulSMul ℤ X.functionField := by
    have : CharZero X.functionField := by
      have hc0 : CharZero Γ(X, ⊤) := (flat_int_iff_charZero _).1 h.flat
      exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 hc0
    exact (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective_int _)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ X.functionField
  have hcard := hs.cardinalMk_eq_trdeg
  rw [htr] at hcard
  have : Finite s := Cardinal.lt_aleph0_iff_finite.1 (by rw [hcard]; exact Cardinal.natCast_lt_aleph0)
  have : Fintype s := Fintype.ofFinite s
  have e : s ≃ Fin D := Fintype.equivFinOfCardEq (by
    rw [Cardinal.mk_fintype] at hcard; exact_mod_cast hcard)
  exact ⟨_, hs.comp_equiv e.symm⟩

end GlobalTheory.ArithTrdeg
