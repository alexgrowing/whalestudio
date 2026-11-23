import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGlStatement
open UpperTheory.V.Af UpperTheory.V.Af.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tw_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (s : ℝ) (L : List (WD h)) :
    (sumList L).lpTw s = sumList (L.map fun x => x.lpTw s) := by
  induction L with
  | nil =>
    change (WD.lpZero h).lpTw s = WD.lpZero h
    rw [WD.lpZero, WD.lpTw_mk]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | cons x L ih =>
    change (x.lpSum (sumList L)).lpTw s = (x.lpTw s).lpSum (sumList (L.map fun x => x.lpTw s))
    rw [WD.lpTw_sum, ih]

theorem UpperTheory.total_reciprocity :
    HypothesesH → RecTot := by
  intro H E Ω _ _ _ _ _ _ n c a d hn P w ρ σ _ hP hS τ e A h rc hrc
  have L := H.litN.loc
  have h1 := GlobalTheory.FormDict.RecTLaws.locProd_eq hrc hn σ τ e
  have h2 : ∀ i, rc (cls (ParLaws.toRep (σ i))) = sumList ((List.range (d i)).map fun k : ℕ =>
      (rc (cls (ParLaws.toRep (ρ i)))).lpTw (((d i : ℝ) - 1) / 2 - k)) := fun i => by
    have hd : ∑ _ : Fin (d i), a i = d i * a i := by simp
    exact GlobalTheory.T.local_langlands_speh_product _ _ _ w _ _ hrc (GlobalTheory.T.generic_unitary_dual_gl L.unit L.sq L.gen L.multi L.cos) L.cos (a i) (d i) _ hd (ρ i) (σ i)
      (hS i).1 (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E (a i) (P i) w (ρ i) (hP i))
      (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd (ρ i) (σ i) (hS i).2.2)
  rw [rec_algNorm hrc]
  change _ = (rc (cls (ParLaws.toRep τ))).lpTw _
  rw [h1, tw_sumList, List.map_ofFn]
  refine congrArg sumList (congrArg List.ofFn (funext fun i => ?_))
  rw [Function.comp_apply, h2, tw_sumList, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  refine congrArg sumList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, WD.lpTw_add]
  refine congrArg₂ WD.lpTw rfl ?_
  simp only [ex]
  push_cast
  ring
