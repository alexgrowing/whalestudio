import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem eq_of_germ_comp {R : Type} [CommRing R] [IsLocalRing R] {z z' : Spec (CommRingCat.of R) ⟶ X}
    {U : X.Opens} (hU : IsAffineOpen U) (h : z (IsLocalRing.closedPoint R) ∈ U)
    (h' : z' (IsLocalRing.closedPoint R) ∈ U)
    (e : X.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo z =
      X.presheaf.germ U _ h' ≫ Scheme.stalkClosedPointTo z') : z = z' := by
  have key : ∀ (t : Spec (CommRingCat.of R) ⟶ X) (ht : t (IsLocalRing.closedPoint R) ∈ U),
      t = Spec.map (X.presheaf.germ U _ ht ≫ Scheme.stalkClosedPointTo t) ≫ hU.fromSpec := by
    intro t ht
    rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk ht]
    exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk t).symm
  rw [key z h, key z' h', e]

theorem val_int {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (hz : genPt ξ ⤳ centre z) {A : Type} (s : Finset A) (f : A → Ω) (g : A → R)
    (h : ∀ i ∈ s, ValAt ξ z (f i) (g i)) : ValAt ξ z (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootHt.ArchB.val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact RootHt.ArchB.val_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique

open GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PointUnique in

theorem GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ q : X, genPt ξ ⤳ q) → ∀ (z z' : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ y z' w → z = z' := by
  intro X Ω _ ξ K _ J y T _ hall z z' w hz hz'
  have hξ := T.gen
  have h := hall (centre z)
  have h' := hall (centre z')
  choose c hc using hz.1
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have in1 := RootHt.ArchB.in_chart (c := c) h hz hc0
  have in2 := RootHt.ArchB.in_chart (c := c) h' hz' hc0
  obtain ⟨x, hx⟩ : ∃ x : ((k : K) → J k) → Ω, x = fun c' => ∏ k, y ⟨k, c' k⟩ := ⟨_, rfl⟩
  rw [← hx] at T in1 in2
  have hxc : x c ≠ 0 := in1.1
  obtain ⟨U, hU, hUm⟩ := T.affine c hxc
  have hzU : centre z ∈ U := (hUm _).2 ⟨h, in1⟩
  have hzU' : centre z' ∈ U := (hUm _).2 ⟨h', in2⟩

  have hval : ∀ (t : Spec (CommRingCat.of ℂ) ⟶ X), CoordsAt ξ y t w → ∀ (k : K) (i : J k),
      ValAt ξ t (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩ / w ⟨k, c k⟩) := by
    intro t ht k i
    obtain ⟨-, h2⟩ := ht.2 k (c k) (hc k)
    obtain ⟨r, hr, e⟩ := h2 i
    rw [e, mul_div_assoc, div_self (hc0 k), _root_.mul_one]
    exact hr
  have hrat : ∀ j : (k : K) → J k, x j / x c = ∏ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ := fun j => by
    rw [hx]
    exact (Finset.prod_div_distrib _ _).symm
  have key : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ r : ℂ, ValAt ξ z a r ∧ ValAt ξ z' a r := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      refine ⟨∏ k, w ⟨k, j k⟩ / w ⟨k, c k⟩, ?_, ?_⟩
      · simp only [hrat]
        exact val_prod h _ _ _ fun k _ => hval z hz k (j k)
      · simp only [hrat]
        exact val_prod h' _ _ _ fun k _ => hval z' hz' k (j k)
    | algebraMap n =>
      refine ⟨(n : ℂ), ?_, ?_⟩
      · simpa using val_int h n
      · simpa using val_int h' n
    | add a b _ _ ha hb =>
      obtain ⟨r, h1, h2⟩ := ha
      obtain ⟨s, h3, h4⟩ := hb
      exact ⟨r + s, RootHt.ArchB.val_add h1 h3, RootHt.ArchB.val_add h2 h4⟩
    | mul a b _ _ ha hb =>
      obtain ⟨r, h1, h2⟩ := ha
      obtain ⟨s, h3, h4⟩ := hb
      exact ⟨r * s, RootHt.ArchB.val_mul h1 h3, RootHt.ArchB.val_mul h2 h4⟩
  refine eq_of_germ_comp hU hzU hzU' ?_
  ext s
  have hgm : ∀ (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U),
      genMap ξ p (X.presheaf.germ U p.1 hp s) = genMap ξ q (X.presheaf.germ U q.1 hq s) :=
    fun p q hp hq => GlobalTheory.CompanionTheory.Ar.genMap_germ_eq_genMap_germ ξ U p q hp hq s
  have ha : genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    refine (T.ring c hxc _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hUm _).2 ⟨p.2, hp⟩
    rw [hgm ⟨centre z, h⟩ p hzU hpU]
    exact ⟨_, rfl⟩
  obtain ⟨r, h1, h2⟩ := key _ ha
  have e1 : ValAt ξ z (genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s))
      ((Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U (centre z) hzU s)) := ⟨h, _, rfl, rfl⟩
  have e2 : ValAt ξ z' (genMap ξ ⟨centre z, h⟩ (X.presheaf.germ U (centre z) hzU s))
      ((Scheme.stalkClosedPointTo z').hom (X.presheaf.germ U (centre z') hzU' s)) :=
    ⟨h', _, (hgm ⟨centre z', h'⟩ ⟨centre z, h⟩ hzU' hzU), rfl⟩
  exact (RootHt.ArchB.val_unique hξ e1 h1).trans (RootHt.ArchB.val_unique hξ h2 e2)
