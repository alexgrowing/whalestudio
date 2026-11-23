import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.CurvePID

theorem coheight_le_one {X : Scheme.{0}} (hd : topologicalKrullDim X = 1) (x : X) :
    Order.coheight x ≤ 1 := by
  have e : topologicalKrullDim X = Order.krullDim X :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
  have := Order.coheight_le_krullDim x
  rw [← e, hd] at this
  exact_mod_cast this

theorem finite_of_isClosed {X : Scheme.{0}} [IsIntegral X] [NoetherianSpace X]
    (hd : topologicalKrullDim X = 1) {s : Set X} (hs : IsClosed s) (hη : genericPoint X ∉ s) :
    s.Finite := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine hS.sUnion fun t ht => ?_
  obtain ⟨x, hx⟩ := QuasiSober.sober (hi t ht) (hc t ht)
  have hne : x ≠ genericPoint X := by
    rintro rfl
    exact hη ⟨t, ht, hx.mem⟩
  refine (Set.finite_singleton x).subset fun y hy => ?_
  by_contra hyx
  have h1 : y < x := lt_of_le_not_ge (show x ⤳ y from hx.specializes hy) fun h =>
    hyx ((show y ⤳ x from h).antisymm (hx.specializes hy)).eq
  have h2 : x < genericPoint X := lt_of_le_not_ge (show _ ⤳ x from genericPoint_specializes x)
    fun h => hne ((show x ⤳ _ from h).antisymm (genericPoint_specializes x)).eq
  have h3 := coheight_le_one hd y
  have h4 : Order.coheight x < Order.coheight y :=
    Order.coheight_strictAnti h1 ((coheight_le_one hd x).trans_lt (by simp))
  have h5 : Order.coheight (genericPoint X) < Order.coheight x :=
    Order.coheight_strictAnti h2 ((coheight_le_one hd _).trans_lt (by simp))
  exact absurd (h4.trans_le h3) (not_lt.2 (Order.one_le_iff_pos.2 (zero_le.trans_lt h5)))

theorem isIntegrallyClosed_stalk {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [LocallyOfFinitePresentation f] {x : X} (hx : x ∈ f.smoothLocus) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    simp
  have hn := (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (f.smoothLocus.ι ≫ f)
    (fun y => by
      have hf : IsField ((Spec (.of k)).presheaf.stalk y) := by
        have : Ring.KrullDimLE 0 ((Spec (.of k)).presheaf.stalk y) :=
          krullDimLE_of_coheight_le (by
            have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
            exact (Order.coheight_eq_zero.2 (fun b _ => (Subsingleton.elim b y).le)).le)
        exact Ring.KrullDimLE.isField_of_isDomain
      let := hf.toField
      exact ⟨inferInstance, inferInstance⟩) ⟨x, hx⟩).2
  exact IsIntegrallyClosed.of_equiv (f.smoothLocus.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv

theorem finite_not_isPrincipalIdealRing : ∀ (κ : Type) [Field κ] [CharZero κ] (C : Scheme.{0}) [Algebra κ Γ(C, ⊤)] [IsIntegral C], IsProjCurve κ C → {x : C | ¬ IsPrincipalIdealRing (C.presheaf.stalk x)}.Finite := by
  intro κ _ _ C _ _ hC
  have := hC.isNoetherian
  have := hC.isProperCurve.isProper
  let f : C ⟶ Spec (.of κ) := strHom κ C
  have : IsProper f := this
  have : LocallyOfFinitePresentation f := inferInstance
  have hη : genericPoint C ∈ f.smoothLocus := f.genericPoint_mem_smoothLocus_of_perfectField
  refine (finite_of_isClosed hC.dim_eq f.smoothLocus.2.isClosed_compl fun h => h hη).subset
    fun x hx hU => hx ?_
  have hn := isIntegrallyClosed_stalk f hU
  have h1 : Ring.KrullDimLE 1 (C.presheaf.stalk x) :=
    krullDimLE_of_coheight_le (coheight_le_one hC.dim_eq x)
  have h3 : IsIntegrallyClosed (C.presheaf.stalk x) ∧ ∀ P : Ideal (C.presheaf.stalk x),
      P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal _ :=
    ⟨hn, fun P h0 hP => IsLocalRing.eq_maximalIdeal
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P h0 hP)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (C.presheaf.stalk x)).out 0 3).mpr h3

end GlobalTheory.CurvePID
