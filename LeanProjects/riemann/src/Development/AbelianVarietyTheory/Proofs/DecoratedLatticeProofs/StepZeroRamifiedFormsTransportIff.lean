import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RamZero

open GlobalTheory.Mem.Col2.TwAtStd

theorem levelZero_classTransport_values {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ)
    (c : (I.stp u I.mu0 0).Cl) :
    (I.rec7 l Z).e0Tw u a ψ₀ (I.eCls0 l u a c) = ψ₀ c := by
  show ψ₀ ((I.eCls0 l u a).symm (I.eCls0 l u a c)) = ψ₀ c
  rw [Equiv.symm_apply_apply]

theorem mram_iff_ramT : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Law0 l → ∀ (u : B.Word) (a : I.ι) (ψ₀ : ((I.rec7 l Z).mem u).C.cls 0 → ((I.rec7 l Z).mem u).C.Y 0 → ℂ), ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram ↔ GlobalTheory.AdForm.RamT (I := I) (l := l) (u := u) (a := a) 0 ((I.rec7 l Z).e0Tw u a ψ₀) := by
  intro B X I hI l Z _ u a ψ₀
  have hval := levelZero_classTransport_values I l Z u a ψ₀
  have e1 := mem_Fi_of_free (I.stp u I.mu0 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (l.lev u I.mu0).free0 ψ₀
  have e2 := mem_Fi_of_free (I.stp u a 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (l.lev u a).free0
    ((I.rec7 l Z).e0Tw u a ψ₀)
  have hFi : ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mu0 ↔ (I.rec7 l Z).e0Tw u a ψ₀ ∈ (I.fm l u a).Fi 0 := by
    refine e1.trans (Iff.trans ⟨fun h c' => ?_, fun h c => ?_⟩ e2.symm)
    · obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
      have := h c
      rw [← hval c] at this
      exact this
    · have := h (I.eCls0 l u a c)
      rw [hval c] at this
      exact this
  have hN : ∀ (v : ((I.rec7 l Z).mem u).A.vT) (c : (I.stp u I.mu0 0).Cl),
      ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT 0 v s (I.eCls0 l u a c)
        ((I.rec7 l Z).e0Tw u a ψ₀ ((I.fm l u a).dil 0 v s (I.eCls0 l u a c))) = ((I.rec7 l Z).mem u).A.Nm v ψ₀ c := by
    intro v c
    have eR : ∀ c' : ((I.rec7 l Z).mem u).C.cls 0, ((I.rec7 l Z).mem u).A.Nm v ψ₀ c' =
        ∑ s, (((I.rec7 l Z).fm u).dilT 0 v s c') (ψ₀ (((I.rec7 l Z).fm u).dil 0 v s c')) := fun c' => by
      unfold ColumnsAtT.Nm
      rw [LinearMap.sum_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => ((I.rec7 l Z).fm u).rhoT_dil v x ψ₀ c'
    rw [eR c]
    letI := (I.atT l u a).FvFin v
    letI := (I.atT l u a).FvDec v
    rw [finsum_eq_sum_of_fintype]
    refine Fintype.sum_equiv (Equiv.refl _) _ _ fun s => ?_
    show (I.atIn u a).dilT B.fields.emb B.embLL 0 v s (I.eCls0 l u a c)
        ((I.rec7 l Z).e0Tw u a ψ₀ ((I.atIn u a).dil 0 v s (I.eCls0 l u a c))) =
      (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v s c (ψ₀ ((I.atIn u I.mu0).dil 0 v s c))
    rw [dil_eCls0 B X I hI l u a v s c, dilT_eCls0 B X I hI l u a v s c, hval]
  unfold ColumnsAtT.Mram GlobalTheory.AdForm.RamT
  rw [Submodule.mem_inf, Submodule.mem_iInf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hFi.1 h1, fun v c' => ?_⟩
    obtain ⟨c, rfl⟩ := (I.eCls0 l u a).surjective c'
    refine (hN v c).trans ?_
    exact congrFun (LinearMap.mem_ker.1 (h2 v)) c
  · rintro ⟨h1, h2⟩
    exact ⟨hFi.2 h1, fun v => LinearMap.mem_ker.2 (funext fun c => (hN v c).symm.trans (h2 v (I.eCls0 l u a c)))⟩

end GlobalTheory.RamZero

end
