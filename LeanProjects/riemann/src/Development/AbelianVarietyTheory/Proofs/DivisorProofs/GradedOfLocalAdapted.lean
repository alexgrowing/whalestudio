import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameImageSpansGenericStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFramesFiltrationGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSpanSubmoduleSectionSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationGradedProjectionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationLiftProjectionCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationGradedShortExactStatement

set_option autoImplicit false

noncomputable section

open NumberField CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.TrueGeo
open GlobalTheory.LieVB (omega)
open GlobalTheory.LocM (tanEv)
open Formalism.MainNotions.DIV.Cons (intO)
open scoped Classical
open GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM)

namespace GlobalTheory.GrFilt

theorem isGraded_of_locAdapted : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {ι : Type} [Fintype ι] {L : X.Modules} {g : ℕ}
    {E E' : ι → X.Modules} {r : ι → ℕ} (hL : VMetric p L g) {m : ℕ} (o : ι ≃ Fin m) (h : ∀ a, VMetric p (E a) (r a))
    (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a), (∀ a, Mono (u a)) →
    (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ LocAdapted r (fun a => (o a : ℕ)) T u V) → OrthEmb hL h T → IsGraded hL o h u := by
  intro k _ X _ p ι _ L g E E' r hL m o h T u hu hloc hT
  set o' : ι → ℕ := fun a => (o a : ℕ) with ho'
  have ho : Function.Injective o' := Fin.val_injective.comp o.injective
  have hgen : GenSpanEq r o' T u := fun V f hf f' hf' c hc hA hV k =>
    GlobalTheory.T.adapted_frames_filtration_generic o' ho T u f hf f' hf' c hc hA hV (fun a => GlobalTheory.T.frame_image_spans_generic_stalk (u a) (hu a) (f a) (f' a) (hf a) (hf' a) hV) k
  have hmem : FrameMem r o' T u := fun k V f hf f' hf' c hc hA V' hV' a => by
    have := GlobalTheory.T.generic_span_submodule_section_sum c hc (fun z => o' z.1 < k) (genSpan o' T k) (fun hV => hgen V f hf f' hf' c hc hA hV k) V' hV' a
    simpa only [not_lt, filtSub] using this
  have hP (k : ℕ) {V : X.Opens} {f : ∀ a, Fin (r a) → Γ(E a, V)} (hf : ∀ a, IsFrame (f a)) {f' : ∀ a, Fin (r a) → Γ(E' a, V)}
      {hf' : ∀ a, IsFrame (f' a)} {c : (Σ a, Fin (r a)) → Γ(L, V)} {hc : IsFrame c} (hA : AdaptedAt o' T u f f' hf' c hc) :
      ∀ (V' : X.Opens) (h : V' ≤ V) (a : (Σ a, Fin (r a)) → Γ(X, V')),
        (∑ z, a z • resM L h (c z)) ∈ (filtSub o' T k).sec V' ↔ ∀ z, ¬ (o' z.1 < k) → a z = 0 := fun V' h a => by
    simpa only [not_lt] using hmem k V f hf f' hf' c hc hA V' h a
  choose κ hκ using GlobalTheory.T.filtration_graded_projection_exists o' ho T u hu hloc hmem hgen
  have hvb (k : ℕ) : IsVB (filtSub o' T k).toMod (Fintype.card {z : Σ a, Fin (r a) // o' z.1 < k}) := fun x => by
    obtain ⟨V, hx, f, hf, f', hf', c, hc, hA⟩ := hloc x
    obtain ⟨t, ht, -⟩ := exists_isFrame_subP (filtSub o' T k) c hc _ (hP k hf hA)
    exact ⟨V, t ∘ (Fintype.equivFin _).symm, hx, ht.comp_equiv _⟩
  have hsub (k : ℕ) : IsSubbundle (filtSub o' T k).incl := ⟨inferInstance, Fintype.card {z : Σ a, Fin (r a) // ¬ o' z.1 < k},
    fun x => by
      obtain ⟨V, hx, f, hf, f', hf', c, hc, hA⟩ := hloc x
      obtain ⟨e, he⟩ := exists_isFrame_cokernelP (filtSub o' T k) c hc _ (hP k hf hA)
      exact ⟨V, e, hx, he⟩⟩
  have hex := fun b => GlobalTheory.T.filtration_graded_short_exact o' ho T u hloc hmem b (κ b) (hκ b)
  refine ⟨fun i => (filtSub o' T i).toMod, fun i => (filtSub o' T i).incl, fun i => stepMap o' T i, κ, fun a => liftT o' T a,
    fun a => (hex a).choose, fun i => ⟨hsub i, _, hvb i⟩, ?_, ?_, fun i => rfl, fun a => (hex a).choose_spec,
    fun a => GlobalTheory.T.filtration_lift_projection_comp o' ho T u hloc hmem a (κ a) (hκ a), hT⟩
  · have := hvb 0
    rw [show Fintype.card {z : Σ a, Fin (r a) // o' z.1 < 0} = 0 from by simp] at this
    exact isVB_zero_iff.1 this
  · refine isIso_of_frames (ι := {z : Σ a, Fin (r a) // o' z.1 < m}) _ fun x => ?_
    obtain ⟨V, hx, f, hf, f', hf', c, hc, hA⟩ := hloc x
    obtain ⟨t, ht, hct⟩ := exists_isFrame_subP (filtSub o' T m) c hc _ (hP m hf hA)
    refine ⟨V, t, hx, ht, ?_⟩
    have e : (fun i => (filtSub o' T m).incl.app V (t i)) = c ∘ (Equiv.subtypeUnivEquiv fun z => (o z.1).isLt) :=
      funext hct
    change IsFrame fun i => (filtSub o' T m).incl.app V (t i)
    rw [e]
    exact hc.comp_equiv _

end GlobalTheory.GrFilt

end
