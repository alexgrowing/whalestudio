import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor
import ReciprocityTheory.CommutativeAlgebra.PowerSeriesPresentations.PresentationStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

variable {R : Type} [CommRing R] [IsDomain R]

theorem gm_jK_unitOn (w : Rˣ) (z : (TK R).left) :
    gm (toUnit (TK R)).left z ⊤ (unitOn w) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)) := by
  have e : (toUnit (TK R)).left = 𝟙 _ ≫ jK R := by simp
  rw [e, ← gm_pull (𝟙 _) (jK R) z ⊤ trivial]
  congr 1
  apply Units.ext
  have := congrArg (fun q => q.hom (w : R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

theorem tauCoord_mul_unit {Q : Data R} {a b : Q.X} {k : (FractionRing R)ˣ} (h : Q.TauCoord a b k) (w : Rˣ) :
    Q.TauCoord a b (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := by
  obtain ⟨u, hu, hv⟩ := h
  let ρ : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ := unitOn w⁻¹
  refine ⟨⟨fun j => res le_top ρ * u.s j⟩, fun i j => ?_, fun z J hJ => ?_⟩
  · show res _ (res le_top ρ * u.s i) = _ * res _ (res le_top ρ * u.s j)
    rw [map_mul, map_mul, InhTate.res_res, InhTate.res_res, hu i j]
    exact mul_left_comm _ _ _
  · rw [hv z J hJ]
    have hm := hJ.mem (lamPts (Q.c a) (Q.c b)) (toUnit (TK R)).left
    show _ = _ * gm _ z _ (res le_top ρ * u.s _)
    erw [MonoidHom.map_mul, gm_res _ z le_top hm]
    have e3 : gm (toUnit (TK R)).left z ⊤ ρ =
        (gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)))⁻¹ := by
      rw [← gm_jK_unitOn, ← MonoidHom.map_inv]
      exact congrArg _ (MonoidHom.map_inv _ _)
    have e4 : unitOn (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) =
        unitOn k * unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := MonoidHom.map_mul _ _ _
    rw [e3, e4, MonoidHom.map_mul]
    have : val u (toUnit (TK R)).left z J = gm (toUnit (TK R)).left z _ (u.s _) := rfl
    rw [this, _root_.mul_assoc, mul_inv_cancel_left]
    rfl

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut
