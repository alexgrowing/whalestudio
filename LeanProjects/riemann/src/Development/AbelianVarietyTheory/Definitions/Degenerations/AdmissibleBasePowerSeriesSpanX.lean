import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PelSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.PelModel

theorem ne_top_of_admissibleBase {R : Type} [CommRing R] {I : Ideal R} (h : AdmBase R I) : I ≠ ⊤ := by
  rintro rfl
  haveI := h.2.1
  haveI := h.2.2.2
  exact not_subsingleton R (IsHausdorff.subsingleton (inferInstance : IsHausdorff (⊤ : Ideal R) R))

theorem admissibleBase_powerSeries_span_X : AdmBase (PowerSeries ℚ) (Ideal.span {PowerSeries.X}) := admissibleBase_powerSeries ℚ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
  (I : Ideal R)

def zeroTriple : SAB H (Sp R) :=
  { GlobalTheory.Models.Inhab.zeroTriple H (Sp R) with
    PP := (UnifZero.zeroPre R I).LG
    cub := (UnifZero.zeroPre R I).cubG
    sym := PrimNorm.isSymmetric_of_hasGen _ ⟨UU.unitGen _ _, UU.unitGen_isGen _ _⟩
    adj := (GlobalTheory.Models.Inhab.zeroTriple H (Sp R)).adj
    prim := (GlobalTheory.Models.Inhab.zeroTriple H (Sp R)).prim }

def zeroU [IsHausdorff I R] : Unif I (UnifZero.zeroData R I) (Inh.zeroPolAV (Sp (FractionRing R))) (zeroTriple H R I).G :=
  ⟨UnifZero.zeroPre R I, fun k _ => UnifZero.expBij k⟩

theorem zeroU_LG [IsHausdorff I R] : (zeroU H R I).LG = (zeroTriple H R I).PP := rfl

theorem exists_hyp (h : AdmBase R I) : ∃ (t : SAB H (Sp R)) (D : DegData R I) (A : PolAV (Sp (FractionRing R)))
    (U : Unif I D A t.G), U.LG = t.PP := by
  haveI := h.2.2.2
  exact ⟨_, _, _, zeroU H R I, rfl⟩

def zeroP [IsHausdorff I R] : PELUnif I (zeroTriple H R I) :=
  letI := H.starRing
  letI : Module (𝓞 E) (UnifZero.zeroData R I).toPre.X := inferInstanceAs (Module (𝓞 E) PUnit)
  { D := UnifZero.zeroData R I
    mod := inferInstanceAs (Module (𝓞 E) PUnit)
    oD := ToricData.toricOAct (fun _ => 1) (𝓞 E) (fun _ _ _ => rfl)
    A := Inh.zeroPolAV _
    oA := Inh.zeroOAct (𝓞 E) _
    U := zeroU H R I
    bundle := rfl
    lin := ⟨fun _ => toUnit_unique _ _,
      fun e _ => (UnifZero.isTerminalPullback (thick R I e)).hom_ext _ _,
      fun e _ => ⟨𝟙 _, fun χ => by
        obtain rfl : χ = 0 := rfl
        exact (UnifZero.res_pullU_eq_one _ _ (UnifZero.charUnit_zero _ _)).trans (UnifZero.charUnit_zero _ _).symm,
        (UnifZero.isTerminalPullback (thick R I e)).hom_ext _ _⟩⟩
    w0 := ToricData.psi_weight_zero_linear_combination _ (𝓞 E) _ _ (fun _ => by simp [ToricData.polar]) }

theorem apply_zero (h : PelSt) : ∃ (t : SAB GlobalTheory.HostModel.host (Sp (PowerSeries ℚ)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso := by
  haveI : CharZero (PowerSeries ℚ) := algebraRat.charZero _
  obtain ⟨t, D, A, U, hU⟩ := exists_hyp GlobalTheory.HostModel.host _ _ (admissibleBase_powerSeries_span_X)
  obtain ⟨P, -, -, -, hP⟩ := h _ _ _ _ (admissibleBase_powerSeries_span_X) t D A U hU
  exact ⟨t, P, hP⟩

end GlobalTheory.LN.PelModel
end
