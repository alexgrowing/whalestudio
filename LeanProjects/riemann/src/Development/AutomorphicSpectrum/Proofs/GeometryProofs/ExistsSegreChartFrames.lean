import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundleStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ_eq {U : X.Opens} (g : Γ(X, U)) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) :
    genMap ξ p (X.presheaf.germ U p.1 hp g) = genMap ξ q (X.presheaf.germ U q.1 hq g) := by
  have key : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.2 hr) g) := by
    intro r hr
    show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes r.2 (X.presheaf.germ U r.1 hr g)) = _
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hr r.2 g)
  rw [key p hp, key q hq]

theorem unitAt_of_isUnit {p : Cpt ξ} {s : X.presheaf.stalk p.1} (hs : IsUnit s) :
    unitAt ξ p (genMap ξ p s) := by
  have hu : IsUnit (genMap ξ p s) := hs.map (genMap ξ p)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hu.ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, Units.inv_mul, map_one]

theorem isUnit_of_unitAt (hξ : IsCptGen ξ) {p : Cpt ξ} {s : X.presheaf.stalk p.1}
    (h : unitAt ξ p (genMap ξ p s)) : IsUnit s := by
  obtain ⟨h0, _, t, ht⟩ := h
  refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
  rw [map_mul, ht, map_one, mul_inv_cancel₀ h0]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem inFrameDomain_of_unitAt (hT : CoordTie ℤ ξ (segreCoord y)) {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (hz : CoordsAt ξ y z w) (h : genPt ξ ⤳ centre z) {c : (k : K) → J k} {f : Ω}
    (hc : InChart ξ (segreCoord y) c ⟨centre z, h⟩) (hf : unitAt ξ ⟨centre z, h⟩ f) :
    InFrameDomain y c f w := by
  let gv : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, h⟩
  let ev : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have hinj : Function.Injective gv := hT.gen.inj ⟨centre z, h⟩
  constructor
  · choose d hd using hz.1
    have key : ∀ k, ∃ (r : ℂ) (s : X.presheaf.stalk (centre z)),
        gv s = y ⟨k, c k⟩ / y ⟨k, d k⟩ ∧ ev s = r ∧ w ⟨k, c k⟩ = r * w ⟨k, d k⟩ := by
      intro k
      obtain ⟨r, ⟨_, s, hs, hv⟩, hw⟩ := (hz.2 k (d k) (hd k)).2 (c k)
      exact ⟨r, s, hs, hv, hw⟩
    choose r s hs hv hw using key
    obtain ⟨t, ht⟩ : ∃ t, gv t = segreCoord y d / segreCoord y c := hc.2 d
    have hxd : segreCoord y d ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => (hz.2 k (d k) (hd k)).1
    have hxc : segreCoord y c ≠ 0 := hc.1
    have hone : t * ∏ k, s k = 1 := by
      refine hinj ?_
      rw [map_mul, map_prod, ht, map_one]
      simp only [hs]
      rw [Finset.prod_div_distrib]
      change segreCoord y d / segreCoord y c * (segreCoord y c / segreCoord y d) = 1
      field_simp
    have hval := congrArg ev hone
    rw [map_mul, map_prod, map_one] at hval
    simp only [hv] at hval
    have hr : ∏ k, r k ≠ 0 := right_ne_zero_of_mul_eq_one hval
    intro k
    rw [hw k]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.1 hr k (Finset.mem_univ k)) (hd k).ne_zero
  · obtain ⟨s, hs⟩ : ∃ s, gv s = f := hf.2.1
    obtain ⟨t, ht⟩ : ∃ t, gv t = f⁻¹ := hf.2.2
    have hone : s * t = 1 := by
      refine hinj ?_
      rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf.1]
    have hval := congrArg ev hone
    rw [map_mul, map_one] at hval
    exact ⟨ev s, (GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w h hz f _).1 ⟨h, s, hs, rfl⟩,
      left_ne_zero_of_mul_eq_one hval⟩

variable {F : Type} [AddCommGroup F] [Module Ω F] {r : ℕ} {W : ChartBundle ℤ (segreCoord y) r F} {L : Lat ξ F}

theorem exists_frames_on_chart (hT : CoordTie ℤ ξ (segreCoord y)) (hV : L.IsVB r ⊤)
    (hC : L.IsChartOf (segreCoord y) W.lat) (c : (k : K) → J k) (hc : segreCoord y c ≠ 0) :
    ∃ S : Set (Ω × (Fin r → F)), S.Finite ∧ (∀ a ∈ S, IsFrameOver y W c a.1 a.2) ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → ∃ a ∈ S, unitAt ξ p a.1 := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have loc : ∀ q : U, ∃ (g : Γ(X, U)) (b : Fin r → F), q.1 ∈ X.basicOpen g ∧
      ∀ p : Cpt ξ, p.1 ∈ X.basicOpen g → L.IsFrameAt b p := by
    intro q
    obtain ⟨h, -⟩ := (hmem q.1).1 q.2
    obtain ⟨V, hqV, b, -, hb⟩ := hV ⟨q.1, h⟩ (Set.mem_univ _)
    obtain ⟨g, hgV, hqg⟩ := hU.exists_basicOpen_le (V := V) ⟨q.1, hqV⟩ q.2
    exact ⟨g, b, hqg, fun p hp => hb p (Set.mem_univ _) (hgV hp)⟩
  choose g b hq hfr using loc
  have hsp : ∀ q : U, genPt ξ ⤳ q.1 := fun q => ((hmem q.1).1 q.2).1
  have hpU : ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → p.1 ∈ U :=
    fun p hp => (hmem p.1).2 ⟨p.2, hp⟩
  let v : U → Ω := fun q => genMap ξ ⟨q.1, hsp q⟩ (X.presheaf.germ U q.1 q.2 (g q))
  have hv : ∀ (q : U) (p : Cpt ξ) (hp : p.1 ∈ U), v q = genMap ξ p (X.presheaf.germ U p.1 hp (g q)) :=
    fun q p hp => genMap_germ_eq (g q) ⟨q.1, hsp q⟩ p q.2 hp
  have hunit : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → p.1 ∈ X.basicOpen (g q) → unitAt ξ p (v q) := by
    intro q p hp hb
    rw [hv q p hp]
    exact unitAt_of_isUnit ((Scheme.mem_basicOpen _ _ _ hp).1 hb)
  have hbasic : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → unitAt ξ p (v q) → p.1 ∈ X.basicOpen (g q) := by
    intro q p hp hu
    rw [hv q p hp] at hu
    exact (Scheme.mem_basicOpen _ _ _ hp).2 (isUnit_of_unitAt hT.gen hu)
  have hcov : (U : Set X) ⊆ ⋃ q : U, (X.basicOpen (g q) : Set X) :=
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hq _⟩
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover _ (fun q => (X.basicOpen (g q)).isOpen) hcov
  refine ⟨(fun q => (v q, b q)) '' (↑t : Set _), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    have hne : v q ≠ 0 := (hunit q ⟨q.1, hsp q⟩ q.2 (hq q)).1
    have hring : v q ∈ chartRing ℤ (segreCoord y) c :=
      (hT.ring c hc (v q)).2 fun p hp => ⟨_, (hv q p (hpU p hp)).symm⟩
    exact (GlobalTheory.T.segre_chart_bundle X Ω ξ K J y F r W L hT hV hC c (v q) (b q) hc hring hne).2
      fun p hp hu => hfr q p (hbasic q p (hpU p hp) hu)
  · intro p hp
    obtain ⟨q, hqt, hqp⟩ := Set.mem_iUnion₂.1 (ht (hpU p hp))
    exact ⟨_, ⟨q, hqt, rfl⟩, hunit q p (hpU p hp) hqp⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrames

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem exists_frames_cover_mcPts : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F : Type) [AddCommGroup F] [Module Ω F] (r : ℕ) (W : ChartBundle ℤ (segreCoord y) r F) (L : Lat ξ F), CoordTie ℤ ξ (segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (segreCoord y) W.lat → ∃ (m : ℕ) (ch : Fin m → (k : K) → J k) (fr : Fin m → Ω) (b : Fin m → Fin r → F), (∀ i, IsFrameOver y W (ch i) (fr i) (b i)) ∧ ∀ w ∈ mcPts (mCoordIdeal y), ∃ i, InFrameDomain y (ch i) (fr i) w := by
  classical
  intro X Ω _ ξ K _ J _ y F _ _ r W L hT hV hC
  have hloc := fun c : {c : (k : K) → J k // segreCoord y c ≠ 0} =>
    ChartFrames.exists_frames_on_chart (W := W) (L := L) hT hV hC c.1 c.2
  choose S hfin hframe hcov using hloc
  let T : Set (((k : K) → J k) × Ω × (Fin r → F)) :=
    ⋃ c, (fun a : Ω × (Fin r → F) => (c.1, a.1, a.2)) '' S c
  have hTfin : T.Finite := Set.finite_iUnion fun c => (hfin c).image _
  haveI := hTfin.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨m, fun i => (e.symm i).1.1, fun i => (e.symm i).1.2.1, fun i => (e.symm i).1.2.2, ?_, ?_⟩
  · have hall : ∀ t ∈ T, IsFrameOver y W t.1 t.2.1 t.2.2 := by
      intro t ht
      obtain ⟨c, a, ha, rfl⟩ := Set.mem_iUnion.1 ht
      exact hframe c a ha
    exact fun i => hall _ (e.symm i).2
  · intro w hw
    obtain ⟨z, h, hz⟩ := (GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT w).1 hw
    obtain ⟨c, hc⟩ := hT.cover ⟨centre z, h⟩
    obtain ⟨a, ha, hu⟩ := hcov ⟨c, hc.1⟩ ⟨centre z, h⟩ hc
    have hmem : (c, a.1, a.2) ∈ T := Set.mem_iUnion.2 ⟨⟨c, hc.1⟩, a, ha, rfl⟩
    refine ⟨e ⟨_, hmem⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ChartFrames.inFrameDomain_of_unitAt hT hz h hc hu

end GlobalTheory.CompanionTheory.Ar
