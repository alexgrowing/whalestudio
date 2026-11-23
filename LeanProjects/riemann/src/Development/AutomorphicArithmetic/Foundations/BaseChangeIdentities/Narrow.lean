import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.BaseChangeIsobaricNOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivOfIsSubquotient
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TwoAtCharZero

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcN

namespace UpperTheory.BaseChangeIdentities

structure IsBaseChangeU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : Submodule ℂ (UA E n → ℂ)) {c : ℕ}
    {N : Fin c → ℕ} (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    (m : Fin c → (E →+* ℂ) → Multiset ℂ) : Prop where
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, CsdAsc (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  unram : ∀ w, IsUnramU π w → GlobalTheory.LGrp.IsSpherical (locProd h w (σ · w)) (GlobalTheory.LFun.KGL w n)
  inert : ∀ (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
    (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → IsUnramInv ϖ s q →
    ∀ α, HasSatAt π w s ϖ q α → GlobalTheory.LFun.HasSatGL w (locProd h w (σ · w)) (GlobalTheory.LGrp.bcParam n α)
  split : ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w))
  weight : ∀ τ lam, HasWeightAt π τ lam → ∑ i, m i τ = infOfWeight lam

def DefiniteN : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i)))
        (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ), IsBaseChangeU π h V σ m

def AscComp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∀ (a : ℕ) (π : CuspSub E a), a = N → IsNormalised π →
      ∃ V : Submodule ℂ (Sm E N), IsDiscrete V ∧ AscEmb V π 1) ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → AscEmb V π d → HasSpehComp V π d

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.BaseChangeBridge in

theorem definiteN_of : BaseChangeIsobaricN → DefiniteN := by
  intro hBC E _ _ _ hun n hn π hπ
  obtain ⟨c, N, h, V, σ, m, P, H⟩ := hBC E hun n hn π hπ
  refine ⟨c, N, h, V, σ, m, ?_⟩
  have hirr : ∀ w, (locProd h w (σ · w)).IsIrreducible := fun w =>
    (UpperTheory.Lit.Mix.multiProd_at (@UpperTheory.Lit.Mix.twoAt_charZero _ _ _ _ _ (charZero_of_injective_algebraMap (algebraMap E _).injective)) (GlobalTheory.SmGL.stdBlocks N h)
      (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
      (fun i => GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E (N i) (V i) (H.discrete i) w (σ i w)
        (H.loc i w)))
  exact
    { pos := H.pos
      discrete := H.discrete
      csd := H.csd
      loc := H.loc
      inf := H.inf
      unram := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isSpherical_of_equiv e he (H.unram w hw)
      inert := fun w s ϖ q hs hq α hα => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact hasSatGL_of_equiv e he (H.inert w s ϖ q hs hq α hα)
      split := fun w hw => by
        obtain ⟨e, he⟩ := exists_equiv_of_isSubquotient (P w).irred (hirr w) (H.sub w)
        exact isCompAlong_of_equiv e he (hirr w) (H.split w hw)
      weight := H.weight }

theorem bridge : BaseChangeIsobaricN → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → DefiniteN :=
  fun h _ => definiteN_of h

end UpperTheory.BaseChangeIdentities

end
