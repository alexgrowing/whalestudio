import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem preimage_fromSpecStalk_eq_constFn {k : Type} [Field k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) :
    (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom = Cartier.constFn p := by
  ext a
  have n := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k)).inv a))
    (Scheme.ΓSpecIso_naturality (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)))
  simp only [Spec.map_preimage, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at n
  rw [← n]
  have hid : (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ≤ ⊤))
      = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rw [hid, CommRingCat.id_apply, Iso.inv_hom_id_apply]
  have e2 : Scheme.Hom.appLE p ⊤ ⊤ (by simp) = Scheme.Hom.appTop p := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  simp only [Cartier.constFn, Cartier.fnOf, algX, e2, RingHom.comp_apply]

theorem isLocModel_locRing_and_exists_trBasis {k : Type} [Field k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ) (x : X) (hn : topologicalKrullDim X = n) :
    IsLocModel (Cartier.constFn p) (locRing x) ∧
      ∃ z : Fin n → X.functionField, TrBasis (Cartier.constFn p) z := by
  refine ⟨isLocModel_locRing x, ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : (U : Set X).Nonempty := ⟨x, hxU⟩
  obtain ⟨d, h₁, h₂⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen k p hU hne
  have e₁ := GlobalTheory.OpenDim.topologicalKrullDim_open k p U hne
  have e₂ : topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have hdn : d = n := by
    have : ((d : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by rw [← h₁, ← e₂, e₁, hn]
    exact_mod_cast this
  subst hdn
  rw [preimage_fromSpecStalk_eq_constFn] at h₂
  letI := (Cartier.constFn p).toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k X.functionField
  have hc : Cardinal.mk s = (d : Cardinal) := hs.cardinalMk_eq_trdeg.trans h₂
  have hfin : Fintype s := (Cardinal.lt_aleph0_iff_fintype.mp (hc ▸ Cardinal.nat_lt_aleph0 d)).some
  have hcard : Fintype.card s = d := by
    have := hc; rw [Cardinal.mk_fintype] at this; exact_mod_cast this
  let e : Fin d ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (e i : X.functionField), ?_⟩
  unfold TrBasis
  exact hs.comp_equiv e

end GlobalTheory.FieldPair
