import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLieImg IsLinHom IsThGen IsHeckeIsog)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLieBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem epsMul_comp_epsMul {R : Type} [CommRing R] (a b : R) :
    (epsMul a).comp (epsMul b) = epsMul (a * b) :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul, mul_smul]

theorem epsMul_one' {R : Type} [CommRing R] : epsMul (1 : R) = RingHom.id _ :=
  RingHom.ext fun z => by
    ext <;> simp [epsMul]

theorem spMap_epsMul_cancel {R : Type} [CommRing R] {u : R} (hu : IsUnit u) {Z : Scheme.{0}}
    {f g : Sp (DualNumber R) ⟶ Z} (h : spMap (epsMul u) ≫ f = spMap (epsMul u) ≫ g) : f = g := by
  obtain ⟨u, rfl⟩ := hu
  have e : spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) = 𝟙 _ := by
    rw [GlobalTheory.Frames.ChgBC.spMap_comp_ring, epsMul_comp_epsMul, Units.inv_mul, epsMul_one',
      GlobalTheory.Frames.ChgBC.spMap_id]
  calc f = spMap (epsMul ((u⁻¹ : Rˣ) : R)) ≫ spMap (epsMul (u : R)) ≫ f := by
        rw [← Category.assoc, e, Category.id_comp]
    _ = g := by rw [h, ← Category.assoc, e, Category.id_comp]

end GlobalTheory.HeckeLieBC

namespace GlobalTheory.HeckeLieBC

open GlobalTheory.HeckeFrCompare (toFib_fst toFib_snd)

theorem lieImg_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (T Ω : Type) [CommRing T] [CommRing Ω] (χ : T →+* Ω) (x x' : Sp T ⟶ Xo.X)
    (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') (p : ℕ)
    (v w : Sp (DualNumber T) ⟶ Xo.univ.t.G.left) (w₁ : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left),
    IsUnit (p : Ω) → IsFib χ Ψ Ψ₁ → IsLieImg p Ψ v w → IsLieImg p Ψ₁ (spMap (dualMap χ) ≫ v) w₁ →
      w₁ = spMap (dualMap χ) ≫ w := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ p v w w₁ hp hF hL hL₁
  obtain ⟨pm, pm', hc, hc', hcomm, -⟩ := hF
  obtain ⟨-, -, a, ha, hw⟩ := hL
  obtain ⟨-, -, a₁, ha₁, hw₁⟩ := hL₁

  have hfib : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ ≫ pm =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.toFib x (spMap (algebraMap T (DualNumber T))) a := by
    apply GlobalTheory.Frames.ChgBC.gx_ext
    · rw [Category.assoc, hc.2.1, toFib_snd, Category.assoc, toFib_snd, ha₁, ha]
    · rw [Category.assoc, hc.2.2, GlobalTheory.HeckeFrCompare.toFib_fst_assoc, Category.assoc, toFib_fst,
        GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_alg]
  have hpush : GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ₁ (spMap (algebraMap Ω (DualNumber Ω))) a₁ =
      spMap (dualMap χ) ≫ GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push Ψ (spMap (algebraMap T (DualNumber T))) a := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori.push
    rw [← hc'.2.1, reassoc_of% hcomm, reassoc_of% hfib]
  apply spMap_epsMul_cancel hp
  rw [hw₁, hpush, ← hw, ← Category.assoc, ← Category.assoc, GlobalTheory.Frames.ChgBC.spMap_comp_ring,
    GlobalTheory.Frames.ChgBC.spMap_comp_ring, GlobalTheory.Frames.ChgBC.dualMap_eps, map_natCast]

end GlobalTheory.HeckeLieBC
