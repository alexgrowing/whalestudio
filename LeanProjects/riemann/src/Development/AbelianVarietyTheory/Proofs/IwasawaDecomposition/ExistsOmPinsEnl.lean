import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBcStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapExtensionOverEnlargedBaseStatement

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

set_option maxHeartbeats 4000000 in

theorem exists_omPins_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
    ∀ (core' : CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
      HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c → HEq core'.Q.Dw z.core.Q.Dw →
      HEq core'.Q.Xo z.core.Q.Xo → HEq core'.x₀ z.core.x₀ → HEq core'.iota z.core.iota →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
      (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
      Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1))
      (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
      TieIn core' R'.toRealDat κ' v₀' →
      ∃ O' : ∀ i', OMDat core'.toCore R'.toRealDat i' Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0),
        (∀ i', OMPins core' R'.toRealDat κ' v₀' O' i') ∧
        ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev ∧
          IsBCOf (O' i') (v₀' i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)) (z.geo.O i)
            (z.geo.v₀ i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) (z.geo.κ i) (iotaW z.core i)
            (z.core.x₀ ((i : ℕ) + 1) (z.geo.O i).s0)
            (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
              (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS core' alg' eH el ec eD eX ex eι Xg tr R' cG' hP hL hB hW κ' v₀' ht
  have hc := GlobalTheory.T.exists_coefficientMap_extension_over_enlarged_base z hE hf hp hS R' cG' hP hL hB hW
  have a1 : HEq R'.C.mu0 f'.mu0 ∧ HEq R'.C.eta f'.eta := by
    have e := hL.C
    rw [w'.C_eq] at e
    rw [e]
    exact ⟨HEq.rfl, HEq.rfl⟩
  have a2 : HEq z.R.C.mu0 f.mu0 ∧ HEq z.R.C.eta f.eta := by
    have e := z.lev.C
    rw [w.C_eq] at e
    rw [e]
    exact ⟨HEq.rfl, HEq.rfl⟩
  obtain ⟨-, -, eβW, -, -, -, eβV, -, -, ePg, eG, -, hcV, -⟩ := hW
  have hcV' := fun i i' hi => (⟨(hcV i i' hi).1, (hcV i i' hi).2.2.1, (hcV i i' hi).2.2.2.1⟩ : _ ∧ _ ∧ _)
  have h1 := hP.char.base.lev
  have h2 := hP.char.base.models
  have h3 := hP.char.base.fam.tie
  clear hcV hP hL hB hS
  obtain ⟨hPre, -, -, hLL⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  have key := fun i => exists_bc_stages (w.st Z) _ ((by with_unfolding_all exact ((Eq.refl B.toPre) :))) hLL z.core core' z.R.toRealDat R'.toRealDat eH el ec eD eX ex eι
    ePg eβV eβW eG (a1.1.trans a2.1.symm) (a1.2.trans a2.2.symm) z.pins.char.base.lev z.pins.char.base.models.HV z.geo.fw.kap h1 h2 h3 ht
    i i rfl (hcV' i i rfl).1 (hcV' i i rfl).2.1 (hcV' i i rfl).2.2 (z.geo.O i) (z.geo.pins i).1 (z.geo.pins i).2 _ (hc i i rfl)
  choose O' k1 k2 k3 using key
  refine ⟨(by with_unfolding_all exact (O' :)), fun i => (by with_unfolding_all exact ((And.intro (k1 i) (k2 i)) :)), fun i i' hi => ?_⟩
  obtain rfl : i = i' := Fin.ext hi
  exact (by with_unfolding_all exact ((And.intro (k3 i).lev (k3 i)) :))

end GlobalTheory.Mem.R3.Rw.OmExt

end
