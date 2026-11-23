import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IsSubquotientOfHasSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Hi
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.RR

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion L)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion L) → WD h}

theorem charPol_supp (H : LawsV a ha ε rc) (x : IrrGL (w.adicCompletion L)) {n : ℕ} (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) (hs : HasSupport x.rep (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i))) (g : Weil h) :
    (rc x).charPol g = ∏ j, (X - C (ω j (a g) : ℂ)) := by
  rw [H.supp x _ hs g, Multiset.map_map, Finset.prod_eq_multiset_prod]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  show (rc (IrrGL.ofChar (ω i) (hω i))).charPol g = _
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

theorem ps_alg (H : LawsV a ha ε rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) (hs : IsSubquotient σ.ρ (PS ω)) (s : Weil h) :
    (rc (algNorm σ)).charPol s = ∏ j, (X - C (ω j (a s) : ℂ)) := by
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion L) (((n : ℂ) - 1) / 2)) :=
    fun i => (hω i).mul (isSmoothChar_absPow _)
  have e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  have e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i) := fun i =>
    IrrGL.tw_ofChar _ _ _ _
  let τ : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, σ.ρ, σ.smooth, σ.irred⟩
  have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hμ τ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  simp only [Multiset.map_map, Function.comp_def, ← e1, IrrGL.nu_nu, e0, IrrGL.nu_zero] at h2
  exact charPol_supp H (algNorm σ) ω hω h2 s

theorem ps_cls (H : LawsV a ha ε rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ)
    (hψ : ∀ i, IsSmoothChar (ψ i)) (hs : IsSubquotient σ.ρ (prinSeries ψ)) :
    rc (algNorm σ) = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (n : ℝ)) / 2) ∧
      ∀ s, (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol s = ∏ j, (X - C (ψ j (a s) : ℂ)) := by
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  let τ : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, σ.ρ, σ.smooth, σ.irred⟩
  exact ⟨H.nu_eq _ _, charPol_supp H _ ψ hψ
    ((hasSupport_of_isSubquotient_prinSeries _ n _ hψ τ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred))⟩

end UpperTheory.V.Z.Win.RR
