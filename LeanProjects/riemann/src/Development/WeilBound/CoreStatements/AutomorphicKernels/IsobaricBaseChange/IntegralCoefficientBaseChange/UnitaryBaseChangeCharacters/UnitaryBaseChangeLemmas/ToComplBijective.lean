import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace PositivityTheory.BCUSide.HermitianLocalForms

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

theorem eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) :
    ∀ u : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v → u = w := fun u hu => by
  by_contra h
  exact hw ⟨u, h, hu.trans hv.symm⟩

omit [IsCMField E] in

theorem toCompl_bijective {w : Pl E} (hw : ¬ IsSplitAt w) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) : Function.Bijective (GlobalTheory.LFun.toCompl hv) := by
  classical
  have huniq := eq_of_not_split hw hv
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, GlobalTheory.LFun.InertChart.toCompl_surjective hv⟩
  have h1 := GlobalTheory.AutFunCompare.map_tensNU_self _ _ (GlobalTheory.AdelicU.singleFin_mul v)
    (GlobalTheory.AdelicU.evalV_singleFin_self v) y
  have h2 : GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E
      (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU _ (GlobalTheory.AdelicU.singleFin_mul v) y) = 0 :=
    FiniteAdeleRing.ext _ fun u => by
      by_cases e : u.under (𝓞 (maximalRealSubfield E)) = v
      · rw [GlobalTheory.LFun.finAdEquiv_apply e, h1]
        obtain rfl := huniq u e
        exact hy
      · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _
          (GlobalTheory.AdelicU.evalV_singleFin_ne e), map_zero]
        rfl
  rw [← h1, (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).injective).1 h2, map_zero]

def locJ (_hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) :
    w.adicCompletion E ≃+* v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E :=
  (RingEquiv.ofBijective (GlobalTheory.LFun.toCompl hv) (toCompl_bijective hw hv)).symm

theorem locJ_symm_apply (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    (y : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :
    (locJ hU w hw v hv).symm y = GlobalTheory.LFun.toCompl hv y := rfl

theorem locJ_algebraMap (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v) (e : E) :
    locJ hU w hw v hv (algebraMap E _ e) = 1 ⊗ₜ e := by
  refine (locJ hU w hw v hv).symm_apply_eq.1 ?_ |>.symm
  rw [locJ_symm_apply]
  have h := GlobalTheory.LFun.toCompl_tmul hv 1 e
  rw [map_one, one_mul] at h
  exact h

theorem locJ_cj (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    (x : w.adicCompletion E) :
    locJ hU w hw v hv (cj w x) = Algebra.TensorProduct.map
      (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
      ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E)
      (locJ hU w hw v hv x) := by
  have hmain := GlobalTheory.ConjAtPlace.main E hU w
  have hσ := (hmain.2.2.2.1 hw).1
  have hF : ∀ a, cj w (GlobalTheory.LFun.complMap hv a) = GlobalTheory.LFun.complMap hv a := by
    have := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      (hmain.1.comp (GlobalTheory.LFun.InertChart.continuous_complMap hv)) (GlobalTheory.LFun.InertChart.continuous_complMap hv)
      (funext fun x => by
        simp only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))
    exact fun a => congrFun this a
  have hcomp : ∀ y, cj w (GlobalTheory.LFun.toCompl hv y) = GlobalTheory.LFun.toCompl hv
      (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
        ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [GlobalTheory.LFun.toCompl_tmul, hF, hσ]
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨y, rfl⟩ := (locJ hU w hw v hv).symm.surjective x
  rw [RingEquiv.apply_symm_apply, locJ_symm_apply, hcomp, ← locJ_symm_apply hU w hw v hv,
    RingEquiv.apply_symm_apply]

def locPhi (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) {r : ℕ} (Q : SelfRecip E r) :
    (w.adicCompletion E)[X] →+* v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] Fld Q :=
  eval₂RingHom ((inclBase Q (v.adicCompletion (maximalRealSubfield E))).toRingHom.comp
    (locJ hU w hw v hv).toRingHom) ((1 : v.adicCompletion (maximalRealSubfield E)) ⊗ₜ alpha Q)

theorem locPhi_atPl (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (hv : w.under (𝓞 (maximalRealSubfield E)) = v) {r : ℕ} (Q : SelfRecip E r) (p : E[X]) :
    locPhi hU w hw v hv Q (atPl w p) =
      (1 : v.adicCompletion (maximalRealSubfield E)) ⊗ₜ (AdjoinRoot.mk Q.1 p : Fld Q) := by
  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (inclBase Q k).toRingHom.comp (locJ hU w hw v hv).toRingHom
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e := by
    intro e
    change inclBase Q k (locJ hU w hw v hv (algebraMap E _ e)) = _
    rw [locJ_algebraMap]
    simp [inclBase]
  have e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q)) := RingHom.ext fun e => hι1 e
  change eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _
  rw [eval₂_map, e]
  refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
  change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
  rw [← aeval_def]
  congr 1
  exact AdjoinRoot.aeval_eq p

end PositivityTheory.BCUSide.HermitianLocalForms
