import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalConjExpansionAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)
theorem GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  intro _ D X X0 Y S YS Z c w j _ τ _ ζ Φ Φ' hC n a f hΦ
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls.base_of_tie (i := j) X.geo.fw
  have hso : (X.geo.O j).s0 = res X.core (sg0 _ X.A3.A) :=
    (sOv_eq X.core.toCore (X.geo.O j).c' (X.geo.O j).hle).trans hb.1.symm
  have hev := GlobalTheory.PlaceRead.evaluates_of_lunif X.geo.fw X.unif j (sg0 _ X.A3.A) hb.2.1 hb.2.2
  let cf : NX.FmK S ((j : ℕ) + 1) → X.core.cuspA ((j : ℕ) + 1) (wtA (X.geo.κ j)) (X.geo.κ j).n := fun g =>
    (X.geo.fw.e j).symm ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩
  have hread : ∀ (g : NX.FmK S ((j : ℕ) + 1)) h,
      (lieFac (X.core.Q.Dw ((j : ℕ) + 1)) (xiR D) (wtA (X.geo.κ j)) : ℂ) *
      (X.geo.O j).phi (X.core.cE ((j : ℕ) + 1) (X.geo.O j).s0) (cf g : X.core.R ((j : ℕ) + 1)) h =
        evW YS X.geo.v₀ j g.val h := by
    intro g h
    rw [phi_cE X.core X.R.toRealDat X.geo.O j]
    refine Eq.trans ?_ ((congrFun (hev (cf g)) h).symm.trans ?_)
    · exact congrFun (GlobalTheory.LiftRatObj.phiC_congr X.core hso (X.geo.O j).hV hb.2.2 _ _) h
    · have he : X.geo.fw.e j (cf g) = ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩ := LinearEquiv.apply_symm_apply _ _
      exact congrArg (fun x : (X.R.FW j).WK => (X.R.HW j (sg0 D X.A3.A)).e ((X.R.FW j).j (sg0 D X.A3.A) x.val)
        (X.geo.v₀ j (sg0 D X.A3.A)) h) he
  have h1 : Expands (X.geo.O j) (X.geo.κ j) Φ a fun k => cf (f k) := fun h => by
    rw [hΦ, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (hread _ _).symm
  have h2 := hC.2 n a _ h1
  funext h
  rw [h2 h, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact (congrArg (fun z => ζ * τ (a k) * z) (hread (f k) h)).trans (mul_assoc _ _ _)
end
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_conj_expansion_of_third_layer : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  first | exact @_root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer | exact _root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer | (intros; apply _root_.GlobalTheory.PlaceRead.conj_expansion_evaluation_weight_of_third_layer <;> assumption)
end
end
