import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieSurjLocal

theorem map_surjective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G B : Over (Sp R)) [GrpObj G] [GrpObj B] [IsCommMonObj G] [IsCommMonObj B] (q : G ⟶ B) [IsMonHom q], Smooth q.left → ∀ u : TanM (𝟙 (Sp R)) B, ∃ v : TanM (𝟙 (Sp R)) G, tv v ≫ q = tv u := by
  intro R _ _ G B _ _ _ _ q _ hsm u
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  let π : CommRingCat.of (DualNumber R) ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
  have hπ : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']⟩
  have hu : Spec.map π ≫ (tv u).left = η[B].left := GlobalTheory.RayBasis.isTangent_pt u
  have h0 : η[G].left ≫ q.left = Spec.map π ≫ (tv u).left :=
    (congrArg (·.left) (IsMonHom.one_hom q)).trans hu.symm
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    GlobalTheory.exists_isAffineOpen_pair q.left (η[G].left (IsLocalRing.closedPoint R)) (O := ⊤) trivial
  obtain ⟨x, hx, hq⟩ := GlobalTheory.exists_lift_of_smooth_of_isAffineOpen q.left hU hV hVU π
    (tv u).left η[G].left h0
    (GlobalTheory.range_subset_opens_of_isLocalRing _ (by
      have : IsLocalHom π.hom := .of_surjective _ hπ
      have e : q.left (η[G].left (IsLocalRing.closedPoint R)) =
        (tv u).left (Spec.map π (IsLocalRing.closedPoint R)) := congr($h0 (IsLocalRing.closedPoint R))
      rw [← Spec_closedPoint (f := π), ← e]
      exact hVU hxV))
    (GlobalTheory.range_subset_opens_of_isLocalRing _ hxV) (by
      intro R' S _ _ _ _ _ _ p hp φ
      have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
      have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
        convert hn using 1
        exact Ideal.ext fun b => Eq.congr_left (hp b)
      exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
        Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩)
  let xo : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G :=
    Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w (tv u))
  have hz : smT (𝟙 (Sp R)) 0 xo = 1 := by
    apply Over.OverMorphism.ext
    rw [smT_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
    show spMap _ ≫ x = (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _) ≫ _
    rw [Category.comp_id, ← hx, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    ext <;> simp [π, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT xo hz, Over.OverMorphism.ext hq⟩

end GlobalTheory.LieSurjLocal
