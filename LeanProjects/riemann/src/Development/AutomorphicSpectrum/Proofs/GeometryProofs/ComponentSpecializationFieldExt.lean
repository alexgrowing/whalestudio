import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

theorem lieValAt_spMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (hξ : IsCptGen ξ) {F F' : Type} [Field F]
    [Field F'] (f : F →+* F') {z : Sp F ⟶ X} {z' : Sp F' ⟶ X} (hz : spMap f ≫ z = z') {e : V}
    {w : epsAt z ⟶ G} {w' : epsAt z' ⟶ G} (hw : w'.left = spMap (dualMap f) ≫ w.left) (h : M.ValAt z e w) :
    M.ValAt z' e w' := by
  letI : Algebra F F' := f.toAlgebra
  subst hz
  obtain ⟨hc, v, hext, hw0⟩ := h
  have hbot : ∀ x : PrimeSpectrum F, x.asIdeal = ⊥ := fun x =>
    (Ideal.eq_bot_or_top _).resolve_right x.isPrime.ne_top
  have hp : (spMap f) (IsLocalRing.closedPoint F') = IsLocalRing.closedPoint F :=
    PrimeSpectrum.ext ((hbot _).trans (hbot _).symm)
  have hcen : GlobalTheory.CompanionTheory.Ar.centre (spMap f ≫ z) = GlobalTheory.CompanionTheory.Ar.centre z := by
    change z ((spMap f) (IsLocalRing.closedPoint F')) = z (IsLocalRing.closedPoint F)
    rw [hp]
  have hc' : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre (spMap f ≫ z) := hcen ▸ hc
  exact GlobalTheory.CompanionTheory.Ar.LieFib.valAt_base M z hc hc' v hext w' w hw hw0

theorem isValFam_spMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (y : Sp F ⟶ Xo.XF c) (y' : Sp F' ⟶ Xo.XF c), y' = spMap f ≫ y → ∀ (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (v' : Vecs y' n), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsValFam Z y b v → IsValFam Z y' b v' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F F' _ _ f y y' hy n b v v' hv' hv
  subst hy
  simp only [GlobalTheory.CompanionTheory.Ar.Flat.Rep.IsValFam] at hv ⊢
  intro i
  obtain ⟨u, hval, t, ht1, ht2, ht3⟩ := hv i
  have hzz : spMap f ≫ (y ≫ Y.j) = (spMap f ≫ y) ≫ Y.j := (Category.assoc _ _ _).symm
  refine ⟨GlobalTheory.CompanionTheory.Ar.LieTangent.epsBase f hzz ≫ u, ?_, ?_⟩
  · exact lieValAt_spMap Z.M Z.gen f hzz rfl hval
  · simp only [GlobalTheory.CompanionTheory.Ar.Flat.SameVec]
    refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ t, ?_, ?_, ?_⟩
    · rw [Category.assoc, ht1]
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
      rw [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieTangent.spec_dual_alg, Category.assoc]
    · rw [Category.assoc, ht2, hv' i]
    · rw [Category.assoc, ht3]
      try rfl

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
