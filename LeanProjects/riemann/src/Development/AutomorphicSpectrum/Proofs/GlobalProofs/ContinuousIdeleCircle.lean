import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

def ideleCircle (χ : HChar E) (hu : IsUnitary χ) : GroundTheory.Global.IdeleGroup E →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ), by simp [Submonoid.unitSphere, hu x]⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul]
    rfl

theorem continuous_ideleCircle (χ : HChar E) (hu : IsUnitary χ) : Continuous (ideleCircle χ hu) :=
  Continuous.subtype_mk (Units.continuous_val.comp χ.2.1) _

def toHecke (χ : HChar E) (hu : IsUnitary χ) : GroundTheory.Global.HeckeCharacter E where
  toMonoidHom := QuotientGroup.lift (GroundTheory.Global.IdeleGroup.diagonal E).range (ideleCircle χ hu) (by
    rintro _ ⟨k, rfl⟩
    rw [MonoidHom.mem_ker]
    ext
    have := χ.2.2 k
    show ((χ.1 (Neutral.B1.diagUnits E k) : ℂˣ) : ℂ) = 1
    rw [this]; rfl)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (GroundTheory.Global.IdeleGroup.diagonal E).range).continuous_iff.2
    (continuous_ideleCircle χ hu)

theorem coe_toIdele (χ : HChar E) (hu : IsUnitary χ) (x : GroundTheory.Global.IdeleGroup E) :
    (((toHecke χ hu).toIdele x : Circle) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) := rfl

theorem coe_localComponent (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    (((toHecke χ hu).localComponent v x : Circle) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) := rfl

theorem toHecke_inv (χ : HChar E) (hu : IsUnitary χ) (hu' : IsUnitary χ⁻¹) : toHecke χ⁻¹ hu' = (toHecke χ hu)⁻¹ := by
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  show (((toHecke χ⁻¹ hu').toIdele x : Circle) : ℂ) = ((((toHecke χ hu).toIdele x)⁻¹ : Circle) : ℂ)
  rw [coe_toIdele, Circle.coe_inv, coe_toIdele]
  exact Units.val_inv_eq_inv_val (χ.1 x)

end GlobalTheory.CompanionTheory.HeckeBridge
