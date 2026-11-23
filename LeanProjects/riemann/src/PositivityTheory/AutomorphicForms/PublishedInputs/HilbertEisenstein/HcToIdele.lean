import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.LocalFields.LocalZetaGauss
import GroundTheory.LocalFields.LocalZeta
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchInt
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.UnitaryTransvectionZeroSecondMemClosure
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
import GroundTheory.GlobalFields.WeilGroups.QuasiCharacterDecomposition

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection

open Classical in

def finK (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : F) (b : (Af F)ˣ) : ℂ :=
  if (∀ w, Valued.v (pLoc F w ((b : Af F) * (yf : Af F))) ≤ WithZero.exp (-(c w : ℤ))) ∧
      (∀ w, Valued.v (pLoc F w (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ)) ≤
        WithZero.exp ((c w : ℤ) + dd w))
  then ((finiteAdelicChar F (((b⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ) : Circle) : ℂ) else 0

def ωF (ω : HChar F) (b : (Af F)ˣ) : ℂ := ((ω.1 (ofFinite b) : ℂˣ) : ℂ)

def qc (ω : HChar F) : QuasiCharacter F where
  toMonoidHom := QuotientGroup.lift _ ω.1 (by
    rintro _ ⟨a, rfl⟩
    exact ω.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ω.2.1

theorem norm_qc (ω : HChar F) (h : IsOfFinOrder ω) (c : GroundTheory.Global.IdeleClassGroup F) :
    ‖((qc ω c : ℂˣ) : ℂ)‖ = 1 := by
  induction c using QuotientGroup.induction_on with
  | H x => exact L2.norm_omega_eq_one h x

def hc (ω : HChar F) (h : IsOfFinOrder ω) : HeckeCharacter F := QuasiCharacter.toUnitary (qc ω) (norm_qc ω h)

theorem hc_toIdele (ω : HChar F) (h : IsOfFinOrder ω) (x : IdeleGroup F) :
    (((hc ω h).toIdele x : Circle) : ℂ) = ((ω.1 x : ℂˣ) : ℂ) := rfl

def xiF (ξ : Fˣ) : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom ξ

def ordAt (b : (Af F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : ℤ := ord (pLoc F v (b : Af F))

open Classical in

def locF (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (yf : (Af F)ˣ) (ξ : F) (v : HeightOneSpectrum (𝓞 F))
    (a : (v.adicCompletion F)ˣ) : ℂ :=
  (if Valued.v ((a : v.adicCompletion F) * pLoc F v (yf : Af F)) ≤ WithZero.exp (-(c v : ℤ)) ∧
      Valued.v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * algebraMap F (v.adicCompletion F) ξ) ≤
        WithZero.exp ((c v : ℤ) + dd v)
    then (localAdelicChar F v (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) ξ) : ℂ) else 0) * ((ω.loc v a : ℂˣ) : ℂ)⁻¹

def cst (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if c v = 0 then ((ω.val v : ℂˣ) : ℂ) ^ (-dd v) else
    ∫ x in ordShell (v.adicCompletion F) (-((c v : ℤ) + dd v)), ((ω.loc v x : ℂˣ) : ℂ) *
      (localAdelicChar F v (x : v.adicCompletion F) : ℂ) ∂multHaar (v.adicCompletion F)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 GroundTheory.Automorphic.GodementSection

def InvSubst : Prop := ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (f : (v.adicCompletion F)ˣ → ℂ) (t : (v.adicCompletion F)ˣ),
    (Integrable f (multHaar (v.adicCompletion F)) ↔
      Integrable (fun x => f (t * x⁻¹)) (multHaar (v.adicCompletion F))) ∧
    ∫ a, f a ∂multHaar (v.adicCompletion F) = ∫ x, f (t * x⁻¹) ∂multHaar (v.adicCompletion F)

def LocInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (yf : (Af F)ˣ) (ξ : Fˣ) (v : HeightOneSpectrum (𝓞 F)),
    Integrable (locF ω c yf (ξ : F) v) (multHaar (v.adicCompletion F)) ∧
    ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F) =
      ((ω.loc v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ξ) : ℂˣ) : ℂ)⁻¹ *
        if ordAt (xiF ξ * yf) v + dd v < 0 then 0 else
          cst ω c v * ∑ j ∈ Finset.range ((ordAt (xiF ξ * yf) v + dd v).toNat + 1), chiW ω c v ^ j

def OmegaProd : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (b : (Af F)ˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w ∉ S, c w = 0 ∧ IsIntegralUnitAt b w) →
    ωF ω b = ∏ v ∈ S, ((ω.loc v (finUnitAt v b) : ℂˣ) : ℂ)

def FinSplit : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (yf : (Af F)ˣ) (ξ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w ∉ S, c w = 0 ∧ dd w = 0 ∧ IsIntegralUnitAt yf w ∧ IsIntegralUnitAt (xiF ξ) w) →
    (∀ v, Integrable (locF ω c yf (ξ : F) v) (multHaar (v.adicCompletion F))) →
    Integrable (fun b => finK c yf (ξ : F) b * (ωF ω b)⁻¹) (finiteIdeleMeasure F) ∧
      ∫ b, finK c yf (ξ : F) b * (ωF ω b)⁻¹ ∂finiteIdeleMeasure F =
        ∏ v ∈ S, ∫ a, locF ω c yf (ξ : F) v a ∂multHaar (v.adicCompletion F)

def OmegaPos : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ ξ : Fˣ, (∀ v, 0 < reAt v (ξ : F)) → ωF ω (xiF ξ) = 1

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
