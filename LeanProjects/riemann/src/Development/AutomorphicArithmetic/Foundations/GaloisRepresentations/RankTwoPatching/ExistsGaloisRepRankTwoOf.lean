import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolarizedOfCyclicConjugates
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DualBaseChangeOfFrobeniusChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConjugatesAgree
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakePolarizationOfCuspidalTransfer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.SV

theorem galRS_iso {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {π : TR.CuspSub F n}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRS π ι r wt HT)
    (hs : IsSSRep r') (hi : RepIso r r') : IsGalRS π ι r' wt HT := by
  obtain ⟨p, hp⟩ := id hi
  have hp' : ∀ s, p * r s = r' s * p := fun s => by rw [hp, inv_mul_cancel_right]
  have ew : ∀ (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      wdOf h hw ι r' = wdOf h hw ι r := fun w hw A h =>
    ((isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)).of_conj hw p fun g => hp' _).wdOf_eq hw
  have hc : ∀ (A : ValuationSubring Ω) (g : ↥(Dec (F := F) A)), r'.comp (Dec (F := F) A).subtype g =
      p * r.comp (Dec (F := F) A).subtype g * p⁻¹ := fun A g => hp g
  refine ⟨continuous_of_iso H.cont hi, hs, H.plain, fun w σ hσ hP => ⟨fun A h rc hrc => ⟨fun hl => ?_, fun O _ _ _ Bw hj g => ?_⟩,
    fun A h O _ _ _ Bw hj => ?_⟩, fun w hw B hB => (H.frob w hw B hB).of_iso hi,
    fun w hw A h m => ew w hw A h ▸ H.ratio w hw A h m, H.weights, H.weights_sym, fun w A h O _ _ _ Bw hj σ hσ hS => ?_⟩
  · exact (((H.loc w σ hσ hP).1 A h rc hrc).1 hl).of_conj hl p fun g => hp' _
  · obtain ⟨a1, a2⟩ := ((H.loc w σ hσ hP).1 A h rc hrc).2 O Bw hj g
    exact ⟨ExLib.isPstAt_conj (Loc.PP l) Bw p (hc A) a1, ExLib.wdAt_conj (Loc.PP l) ι Bw h hj p (hc A) ▸ a2⟩
  · obtain ⟨k1, -, -, k4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l (Loc.PP l) F Ω O _ Bw n _ _ p (hc A)
    obtain ⟨a1, a2⟩ := (H.loc w σ hσ hP).2 A h O Bw hj
    exact ⟨k1 a1, fun τ LL' τ' hτ => k4 τ _ (a2 τ LL' τ' hτ)⟩
  · obtain ⟨-, k2, -, -⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l (Loc.PP l) F Ω O _ Bw n _ _ p (hc A)
    exact k2 (H.crys w A h O Bw hj σ hσ hS)

end UpperTheory.Gal.SV
