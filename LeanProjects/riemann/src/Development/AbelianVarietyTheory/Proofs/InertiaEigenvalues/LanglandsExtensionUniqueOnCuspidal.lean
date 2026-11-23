import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LangExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  haveI : LeftCommutative (WD.lpSum (h := h)) :=
    ⟨fun a b c => by rw [← WD.lpSum_assoc, WD.lpSum_comm a b, WD.lpSum_assoc]⟩
  exact hp.foldr_eq _

theorem charZero_adicCompletion : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

end GlobalTheory.LocLanglands.LangExt

open GlobalTheory.LocLanglands.LangExt in

theorem GlobalTheory.LocLanglands.exists_isLExt : LanglandsExhaustionGL → LanglandsMultisegments → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (r : IrrGL (w.adicCompletion E) → WD h), (∃ rc, IsLExt r rc) ∧ ∀ rc, IsLExt r rc → ∀ x : IrrGL (w.adicCompletion E), x.IsCusp → rc x = r x := by
  intro hX hM E Ω _ _ _ _ _ A w h r
  haveI : CharZero (w.adicCompletion E) := charZero_adicCompletion
  refine ⟨⟨fun x => segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList, ?_⟩, ?_⟩
  · intro l x hl
    have hm := Classical.choose_spec (hX (w.adicCompletion E) x)
    have he := (hM (w.adicCompletion E)).1 _ _ x hm hl
    show segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList = segSum r l
    unfold segSum
    apply sumList_perm
    apply List.Perm.map
    apply Multiset.coe_eq_coe.1
    rw [Multiset.coe_toList]
    exact he
  · intro rc hrc x hx
    have h1 := hrc [.single x hx] x (single_spec hx).2.2.2
    rw [h1]
    change (((r x).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp h 1)).lpSum (WD.lpZero h) = r x
    rw [WD.lpSum_zero]
    have h2 := (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (r x)).1
    have h3 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
    rw [h3]
    exact h2

end
