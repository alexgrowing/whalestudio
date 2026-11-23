import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.AlgebraTools.jqRec :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (ε : EpsFamily A) (rc : IrrGL (w.adicCompletion E) → WD h), Laws a ha ε rc → ∀ (n : ℕ) (π : IrrRep (GL (Fin n) (w.adicCompletion E))) (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsSubquotient π.ρ (prinSeries ψ) → ∀ σ : Weil h, (rc (cls π)).charPol σ = ∏ i, (X - C ((ψ i (a σ) : ℂˣ) : ℂ)) := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc L n π ψ hψ hs σ
  have H := GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries (k := w.adicCompletion E) ⟨π.V, π.ρ, π.smooth, π.irr⟩ hψ hs
  have H1 := (hasSupport_of_isCuspSupport H).of_equiv (equivRep π)
  have H2 := L.supp (cls π) _ H1 σ
  rw [H2, Multiset.map_map, Finset.prod_eq_multiset_prod]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  show (rc (IrrGL.ofChar (ψ i) (hψ i))).charPol σ = _
  rw [L.one]
  rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp
