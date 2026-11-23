import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mem_mul_eq_zero_of_algebraMap_eq_zero {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] (M : Submonoid R) [IsLocalization M S] :
    ∃ f ∈ M, ∀ a : R, algebraMap R S a = 0 → f * a = 0 := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker (algebraMap R S)) :
    (RingHom.ker (algebraMap R S)).FG)
  have hk : ∀ a ∈ s, ∃ m : M, (m : R) * a = 0 := by
    intro a ha
    have : a ∈ RingHom.ker (algebraMap R S) := hs ▸ Submodule.subset_span ha
    exact (IsLocalization.map_eq_zero_iff M S a).1 this
  choose! m hm using hk
  refine ⟨∏ a ∈ s, (m a : R), Submonoid.prod_mem _ fun a _ => (m a).2, ?_⟩
  have key : ∀ a ∈ Submodule.span R (s : Set R), (∏ a ∈ s, (m a : R)) * a = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem b hb =>
        rw [← Finset.prod_erase_mul _ _ hb, _root_.mul_assoc, hm b hb, mul_zero]
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add, hb, hc, add_zero]
    | smul r b _ hb => rw [smul_eq_mul, _root_.mul_left_comm, hb, mul_zero]
  intro a ha
  exact key a (hs ▸ ha)

theorem exists_affineOpen_isIntegrallyClosed_charZero (X : Scheme.{0})
    (hN : Geo.Tor.IsNormalScheme X) (hL : IsLocallyNoetherian X)
    (h0 : ∀ x : X, CharZero (X.residueField x)) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧
      IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := X.presheaf.algebra_section_stalk (U := V) ⟨x, hxV⟩
  haveI := hV.isLocalization_stalk ⟨x, hxV⟩
  obtain ⟨f, hfM, hf⟩ := exists_mem_mul_eq_zero_of_algebraMap_eq_zero (R := Γ(X, V))
    (S := X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  have hU : IsAffineOpen (X.basicOpen f) := hV.basicOpen f
  have hxU : x ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f x hxV]
    exact IsLocalization.map_units (X.presheaf.stalk x) ⟨f, hfM⟩

  letI : Algebra Γ(X, V) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  let g : Γ(X, X.basicOpen f) →+* X.presheaf.stalk x := (X.presheaf.germ _ x hxU).hom
  have hcomp : ∀ a : Γ(X, V), g (algebraMap Γ(X, V) Γ(X, X.basicOpen f) a) =
      algebraMap Γ(X, V) (X.presheaf.stalk x) a := fun a =>
    X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le f)) x hxU a
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨⟨r, m⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers f) σ
    have hr : algebraMap Γ(X, V) (X.presheaf.stalk x) r = 0 := by
      rw [← hcomp, ← hrm, map_mul, hσ, zero_mul]
    have hfr := congrArg (algebraMap Γ(X, V) Γ(X, X.basicOpen f)) (hf r hr)
    rw [map_mul, map_zero] at hfr
    have hu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen f) f) :=
      IsLocalization.map_units Γ(X, X.basicOpen f) ⟨f, Submonoid.mem_powers f⟩
    have hr0 := hu.mul_right_eq_zero.1 hfr
    have hmu : IsUnit (algebraMap Γ(X, V) Γ(X, X.basicOpen f) (m : Γ(X, V))) :=
      IsLocalization.map_units Γ(X, X.basicOpen f) m
    rw [hr0] at hrm
    exact hmu.mul_left_eq_zero.1 hrm
  haveI : IsDomain (X.presheaf.stalk x) := (hN x).1
  haveI hD : IsDomain Γ(X, X.basicOpen f) := hinj.isDomain g
  haveI : CharZero (X.residueField x) := h0 x
  have hcz : CharZero Γ(X, X.basicOpen f) := by
    refine ⟨fun a b hab => ?_⟩
    have := congrArg ((X.residue x).hom.comp g) hab
    simp only [map_natCast] at this
    exact Nat.cast_injective this
  have hIC : IsIntegrallyClosed Γ(X, X.basicOpen f) := by
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp ↦ ?_
    let P : Spec Γ(X, X.basicOpen f) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec P ∈ X.basicOpen f := hU.range_fromSpec.le ⟨P, rfl⟩
    letI : Algebra Γ(X, X.basicOpen f) (X.presheaf.stalk (hU.fromSpec P)) :=
      X.presheaf.algebra_section_stalk (U := X.basicOpen f) ⟨_, hy⟩
    have h : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) :=
      hU.isLocalization_stalk' P hy
    haveI := (hN (hU.fromSpec P)).1
    haveI := (hN (hU.fromSpec P)).2
    exact IsIntegrallyClosed.of_equiv (R := X.presheaf.stalk (hU.fromSpec P))
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hU.fromSpec P))
        (Localization.AtPrime p)).toRingEquiv
  exact ⟨⟨X.basicOpen f, hU⟩, hxU, hD, IsLocallyNoetherian.component_noetherian ⟨_, hU⟩, hIC, hcz⟩

end GlobalTheory
