import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.OfStar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecT
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalStar
open scoped commutatorElement
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]
omit [IsCMField E] [Fact l.Prime] in
theorem star_guard'_alt {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (k : NcW (rc (algNorm σ))) :
    (IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ UpperTheory.GalStar.Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ)) := by
  first | (have hOpn := UpperTheory.One.M.opn _ (hrc); obtain ⟨_, _, _, H⟩ := hOpn) | obtain ⟨_, _, _, -, H⟩ := hrc
  have e : (rc (algNorm σ)).lpDim = a := H.dim _
  have := star_guard k
  rwa [e] at this
theorem isGalU_of_props_alt {π : CuspSub E a} (χ : HChar (maximalRealSubfield E)) {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ} (H : PropsB _root_.UpperTheory.One.M.recT π ι r wt HT) :
    _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT :=
  ⟨H.cont, H.ss, fun w hl A h rc hrc σ hσ => aw_of_away (H.away w hl A h rc hrc σ hσ), H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj =>
      have k := H.above P AI T w A h O Bw hj
      ⟨fun ⟨σ, hσ, rc, hrc, n⟩ => (k.nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).1,
        fun ⟨σ, hσ, rc, hrc, n⟩ => (k.nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).2.2.1, fun σ hσ hs => (k.crys σ hσ hs).1⟩⟩
theorem pairU_of_star_alt (H : Row0b _root_.UpperTheory.One.M.recT) : _root_.UpperTheory.GalS.PairUAlt := fun E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hp => by
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, _root_.UpperTheory.GalS.isGalU_of_props_alt χ k⟩
theorem carU_of_star_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (H : Row0b _root_.UpperTheory.One.M.recT) : _root_.UpperTheory.GalS.CarUAlt := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha π hc hr
  have hpol := isPolarized_of_isCsd hc
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a (by omega) π _ hr
    ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E _) (hGK E a _) hpol.dual⟩
  refine ⟨r, wt, HT, _root_.UpperTheory.GalS.isGalU_of_props_alt _ k, fun P AI T w _ A h O _ _ _ Bw hj σ hσ rc hrc n => ?_⟩
  have b := ((k.above P AI T w A h O Bw hj).nice σ hσ rc hrc (_root_.UpperTheory.GalS.star_guard'_alt hrc n) n.2.1).2.2.2
  exact ⟨b.dim, fun _ => (away_nice b n).1, fun _ _ => (away_nice b n).2⟩
theorem field_of_starFull_alt (_ : _root_.UpperTheory.Zero.LLC.RecTExists) (_ : GlobalTheory.Published.LocalConverseGL)
    (_ : GlobalTheory.Published.LanglandsExhaustionGL) (H : _root_.UpperTheory.One.M.Row) : _root_.UpperTheory.GalS.PairUAlt := _root_.UpperTheory.GalS.pairU_of_star_alt H
theorem ofDual_star_alt (hGK : GlobalTheory.Published.GelfandKazhdanDual) (H : _root_.UpperTheory.One.M.Row) : _root_.UpperTheory.GalS.CarUAlt := _root_.UpperTheory.GalS.carU_of_star_alt hGK H
end UpperTheory.GalS
end
end
