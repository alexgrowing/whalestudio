import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFunctionsExistsGlobalFunctionOfThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ClosedFibreConn

open Classical in

theorem idem_eq_of_basicOpen {X : Scheme.{0}} {e e' : Γ(X, ⊤)} (he : e * e = e) (he' : e' * e' = e')
    (h : (X.basicOpen e : Set X) = X.basicOpen e') : e = e' := by
  have key : ∀ (a : Γ(X, ⊤)) (x : X) (hx : x ∈ (⊤ : X.Opens)), a * a = a →
      (X.presheaf.germ ⊤ x hx).hom a = if x ∈ X.basicOpen a then 1 else 0 := by
    intro a x hx ha
    have hg : (X.presheaf.germ ⊤ x hx).hom a * (X.presheaf.germ ⊤ x hx).hom a = (X.presheaf.germ ⊤ x hx).hom a := by
      rw [← map_mul, ha]
    split_ifs with hxa
    · have hu := (X.mem_basicOpen a x hx).1 hxa
      exact hu.mul_left_cancel (hg.trans (_root_.mul_one _).symm)
    · rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ((X.presheaf.germ ⊤ x hx).hom a) with h1 | h1
      · exact absurd ((X.mem_basicOpen a x hx).2 h1) hxa
      · have h0 : (X.presheaf.germ ⊤ x hx).hom a * (1 - (X.presheaf.germ ⊤ x hx).hom a) = 0 := by
          rw [mul_sub, _root_.mul_one, hg, sub_self]
        exact h1.mul_left_eq_zero.1 h0
  refine TopCat.Presheaf.section_ext X.sheaf ⊤ e e' fun x hx => ?_
  change (X.presheaf.germ ⊤ x hx).hom e = (X.presheaf.germ ⊤ x hx).hom e'
  rw [key e x hx he, key e' x hx he']
  have : (x ∈ X.basicOpen e) ↔ (x ∈ X.basicOpen e') := by
    change x ∈ (X.basicOpen e : Set X) ↔ x ∈ (X.basicOpen e' : Set X); rw [h]
  simp only [this]

theorem eq_zero_of_germ_closedFibre {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (f : X ⟶ Sp A)
    (hf : IsClosedMap f) (t : Γ(X, ⊤))
    (h : ∀ x, f x = closedPoint A → (X.presheaf.germ ⊤ x trivial).hom t = 0) : t = 0 := by
  let Z : Set X := {y | (X.presheaf.germ ⊤ y trivial).hom t = 0}
  have hZ : IsOpen Z := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨W, hW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq X.presheaf y (show y ∈ (⊤ : X.Opens) from trivial) (show y ∈ (⊤ : X.Opens) from trivial) t 0
      (hy.trans (map_zero _).symm)
    refine ⟨W, fun y' hy' => ?_, W.isOpen, hW⟩
    have e₁ := TopCat.Presheaf.germ_res_apply X.presheaf iU y' hy' t
    have e₂ := TopCat.Presheaf.germ_res_apply X.presheaf iV y' hy' 0
    exact e₁.symm.trans ((congrArg _ e').trans (e₂.trans (map_zero _)))
  have hall : ∀ y, y ∈ Z := by
    by_contra hne
    obtain ⟨y, hy⟩ := not_forall.1 hne
    have hc : IsClosed (f '' Zᶜ) := hf _ hZ.isClosed_compl
    obtain ⟨y', hy', e⟩ := (IsLocalRing.specializes_closedPoint (R := A) (f y)).mem_closed hc ⟨y, hy, rfl⟩
    exact hy' (h y' e)
  exact TopCat.Presheaf.section_ext X.sheaf ⊤ t 0 fun y hy => (hall y).trans (map_zero _).symm

theorem thick_apply_eq (A : Type) [CommRing A] [IsLocalRing A] (e : ℕ)
    (z : Spec (CommRingCat.of (A ⧸ maximalIdeal A ^ (e + 1)))) : thick A (maximalIdeal A) e z = closedPoint A := by
  apply PrimeSpectrum.ext
  show Ideal.comap _ _ = maximalIdeal A
  have := z.isPrime
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime _ z.asIdeal).ne_top) fun x hx => ?_
  show (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (e + 1)))).hom x ∈ z.asIdeal
  refine z.2.mem_of_pow_mem (e + 1) ?_
  rw [← map_pow, CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hx _)]
  exact z.asIdeal.zero_mem

theorem isPreconnected_closedFibre : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A], IsAdicComplete (maximalIdeal A) A → ∀ (X : Scheme.{0}) (f : X ⟶ Sp A), IsProper f → PreconnectedSpace X → _root_.IsPreconnected {x : X | f x = closedPoint A} := by
  intro A _ _ _ hA X f hf hX
  haveI := hf
  rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_clopen]
  intro C hC
  let Y : Over (Sp A) := Over.mk f
  have hfst : ∀ e (y : (thickObj A (maximalIdeal A) e Y).left),
      f (pullback.fst Y.hom (thick A (maximalIdeal A) e) y) = closedPoint A := by
    intro e y
    rw [← Scheme.Hom.comp_apply]
    change (pullback.fst Y.hom (thick A (maximalIdeal A) e) ≫ Y.hom) y = _
    rw [pullback.condition, Scheme.Hom.comp_apply]
    exact thick_apply_eq A e _
  let D : ∀ e, Set (thickObj A (maximalIdeal A) e Y).left := fun e =>
    {y | (⟨pullback.fst Y.hom (thick A (maximalIdeal A) e) y, hfst e y⟩ : {x : X | f x = closedPoint A}) ∈ C}
  have hD : ∀ e, IsClopen (D e) := fun e =>
    hC.preimage ((pullback.fst Y.hom (thick A (maximalIdeal A) e)).continuous.subtype_mk (fun y => hfst e y))
  choose g hg hgD using fun e => GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen _ (D e) (hD e)
  have hcomp : ∀ e, thickMap A (maximalIdeal A) e Y ≫ pullback.fst Y.hom (thick A (maximalIdeal A) (e + 1)) =
      pullback.fst Y.hom (thick A (maximalIdeal A) e) := fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hcompat : ∀ e, (thickMap A (maximalIdeal A) e Y).appTop.hom (g (e + 1)) = g e := by
    intro e
    refine idem_eq_of_basicOpen (by rw [← map_mul, hg]) (hg e) ?_
    rw [← Scheme.preimage_basicOpen_top, hgD e]
    ext y
    change thickMap A (maximalIdeal A) e Y y ∈ ((thickObj A (maximalIdeal A) (e + 1) Y).left.basicOpen (g (e + 1)) : Set _) ↔ y ∈ D e
    rw [hgD (e + 1)]
    simp only [D, Set.mem_setOf_eq, ← Scheme.Hom.comp_apply, hcomp]
  obtain ⟨s, hs⟩ := GlobalTheory.T.formalFunctions_exists_globalFunction_of_thickenings A (maximalIdeal A) hA Y hf g hcompat
  haveI : IsProper Y.hom := hf
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have ht : s * s - s = 0 := by
    refine eq_zero_of_germ_closedFibre f f.isClosedMap _ fun x hx => ?_
    refine GlobalTheory.FormalValue.germ_eq_zero_of_thickenings (maximalIdeal A) Y ⊤ (s * s - s) (fun e => ?_) x trivial ?_
    · change (pullback.fst Y.hom (thick A (maximalIdeal A) e)).appTop.hom (s * s - s) = 0
      rw [map_sub, map_mul, hs e, hg e, sub_self]
    · change maximalIdeal A ≤ (f x).asIdeal
      rw [hx]; exact le_rfl
  have hs2 : s * s = s := sub_eq_zero.1 ht
  have hB : IsClopen (X.basicOpen s : Set X) :=
    ⟨GlobalTheory.PairingLocus.isClosed_basicOpen (X := X) hs2, (X.basicOpen s).isOpen⟩
  have hne : (maximalIdeal A ^ (0 + 1)) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal A).ne_top
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨z₀⟩ : Nonempty (PrimeSpectrum (A ⧸ maximalIdeal A ^ (0 + 1))) := inferInstance
  have hC' : C = {c | c.1 ∈ (X.basicOpen s : Set X)} := by
    ext c
    obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.hom) (g := thick A (maximalIdeal A) 0)
      c.1 z₀ (c.2.trans (thick_apply_eq A 0 z₀).symm)
    have e1 : c ∈ C ↔ y ∈ D 0 := by
      change c ∈ C ↔ (⟨_, hfst 0 y⟩ : {x : X | f x = closedPoint A}) ∈ C
      rw [show (⟨_, hfst 0 y⟩ : {x : X | f x = closedPoint A}) = c from Subtype.ext hy]
    rw [e1, ← hgD 0, ← hs 0, ← Scheme.preimage_basicOpen_top]
    change pullback.fst Y.hom (thick A (maximalIdeal A) 0) y ∈ X.basicOpen s ↔ _
    rw [hy]; rfl
  rcases isClopen_iff.1 hB with h | h
  · left; rw [hC', h]; rfl
  · right; rw [hC', h]; rfl

end GlobalTheory.ClosedFibreConn
