import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.NrmLCharpoly

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

open PositivityTheory.Rg.Tf.Loc (twConj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem transl_eq {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹ =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x) := by
  have h := congrArg (GeneralLinearGroup.map (pFin E)) (adeleqof_twist translAd_holds hu d x)
  simp only [map_mul, map_inv, adeleqof_pFin_thetaGL, adeleqof_pFin_ratGL] at h
  rw [map_mul (ratF E n), map_inv]
  exact h

private theorem transl_norm {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) *
        thF E n (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (nrm d) * GeneralLinearGroup.map (pFin E) x := by
  rw [transl_eq hu]
  set c := GeneralLinearGroup.map (pFin E) x
  set r := ratF E n (d * u⁻¹) with hr0
  set s := ratF E n (thE E n (d * u⁻¹)) with hs0
  have hr : thF E n r = s := by
    rw [hr0, hs0, GlobalTheory.EulerTw.Comm.thF_ratF]
  rw [← poleq_norm E n u hu d, map_mul (ratF E n), ← hr0, ← hs0, map_mul, map_mul, map_inv,
    GlobalTheory.EulerTw.Comm.thF_thF, hr]
  group

private theorem transl_charpoly (w : Pl E) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    (GeneralLinearGroup.map (pLoc E w) ((gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) *
        thF E n (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹))).val.charpoly =
      (nrm d).val.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  rw [transl_norm hu, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  rw [← Matrix.charpoly_map]
  rfl

private theorem sep_of {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    {w : Pl E} (hwS : w ∈ S) (hsp : IsSplitAt w)
    (hreg : ∀ y z, φ₁ w y ≠ 0 → φ₂ w z ≠ 0 → ((y * z).1.val.charpoly * (y * z).2.val.charpoly).Separable)
    (y : Gf E a b) (hne : finFn S φ₁ φ₂ y ≠ 0) :
    (GeneralLinearGroup.map (pLoc E w) (y.1 * thF E a y.1)).val.charpoly.Separable ∧
      (GeneralLinearGroup.map (pLoc E w) (y.2 * thF E b y.2)).val.charpoly.Separable := by
  have hf := GlobalTheory.CompanionTheory.SuppFinTw.factors_ne h₁ h₂ y hne w hwS
  have hs := hreg (atW w y) (atW w (thP E a b y)) hf.1 (hf.2 hsp)
  have e₁ : (atW w y * atW w (thP E a b y)).1 = GeneralLinearGroup.map (pLoc E w) (y.1 * thF E a y.1) :=
    (map_mul _ _ _).symm
  have e₂ : (atW w y * atW w (thP E a b y)).2 = GeneralLinearGroup.map (pLoc E w) (y.2 * thF E b y.2) :=
    (map_mul _ _ _).symm
  rw [e₁, e₂] at hs
  exact ⟨Polynomial.Separable.of_mul_left hs, Polynomial.Separable.of_mul_right hs⟩

theorem _root_.UpperTheory.Zero.ConvolutionTheory.EB.regS : RegS := by
  intro E _ _ _ a b S u₁ u₂ hu₁ hu₂ φ₁ φ₂ h₁ h₂ hw
  obtain ⟨w, hwS, hsp, hreg⟩ := hw
  refine ⟨fun d x h₂' hne => ?_, fun d x h₁' hne => ?_⟩
  · have hs := (sep_of h₁ h₂ hwS hsp hreg _ hne).1
    simp only [Prod.fst_mul, Prod.fst_inv] at hs
    rw [transl_charpoly w hu₁] at hs
    exact (Polynomial.separable_map _).1 hs
  · have hs := (sep_of h₁ h₂ hwS hsp hreg _ hne).2
    simp only [Prod.snd_mul, Prod.snd_inv] at hs
    rw [transl_charpoly w hu₂] at hs
    exact (Polynomial.separable_map _).1 hs

end UpperTheory.Zero.ConvolutionTheory.EB

end
