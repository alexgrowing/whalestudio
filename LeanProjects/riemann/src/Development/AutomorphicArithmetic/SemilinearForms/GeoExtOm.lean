import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsEnl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedDataCoefficientMapInjective

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000
open GlobalTheory.Mem.R3.Rw.GeoTies

namespace UpperTheory.Mem.GeoExt

theorem exists_omOver : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
    ∀ (core' : CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
      HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c → HEq core'.Q.Dw z.core.Q.Dw →
      HEq core'.Q.Xo z.core.Q.Xo → HEq core'.x₀ z.core.x₀ → HEq core'.iota z.core.iota →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
      (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
      GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSide z Wt' R' →
    ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1))
      (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
      TieIn core' R'.toRealDat κ' v₀' →
      ∃ O' : ∀ i', OMDat core'.toCore R'.toRealDat i' Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0),
        (∀ i', OMPins core' R'.toRealDat κ' v₀' O' i') ∧
        ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → OmOver (z.geo.O i) (O' i') := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS core' alg' eH el ec eD eX ex eι Xg tr R' cG' hP hL hB hW κ' v₀' ht
  obtain ⟨O', k1, k2⟩ := OmExt.exists_omPins_enl z hE hf hp hS core' eH el ec eD eX ex eι R' cG' hP hL hB hW.1 κ' v₀' ht
  refine ⟨O', k1, fun i i' hi => ?_⟩
  have k3 := (k2 i i' hi).2
  have eHV := (hW.2 i i' hi).2.2.1
  obtain ⟨-, -, -, -, -, -, eβV, -, -, ePg, -, -, hcV, -⟩ := hW.1
  have e1 := (hcV i i' hi).1
  have e2 := (hcV i i' hi).2.2.1
  have e3 := (hcV i i' hi).2.2.2.1
  have h1 := hP.char.base.lev
  have hinj := OmExt.normalisedData_coefficientMap_injective (z.geo.O i) (z.geo.pins i).1 (z.geo.pins i).2
  clear hcV hP hL hB hS hW k1 k2
  obtain ⟨hPre, -, -, hLL⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  exact (by with_unfolding_all exact ((OmExt.omOver_of_isBCOf (w.st Z) _ (((Eq.refl B.toPre))) z.core core' z.R.toRealDat R'.toRealDat eH el ec eD eX ePg eβV
    z.pins.char.base.lev h1 i i' hi e1 e2 e3 eHV (z.geo.O i) (O' i') (z.geo.pins i).2 hinj k3) : _))

end UpperTheory.Mem.GeoExt

end
