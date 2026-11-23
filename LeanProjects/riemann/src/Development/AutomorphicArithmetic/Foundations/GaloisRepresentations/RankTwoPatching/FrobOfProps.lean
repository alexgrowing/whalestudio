import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ExistenceOfGaloisRepresentationsOfHyp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.UnrAtOfIsoTwist
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.ExLib
open private UpperTheory.V.Af.exists_sign from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ExistenceOfGaloisRepresentationsOfHyp

namespace UpperTheory.Gal.SV

theorem rowB (h : RowT) : UpperTheory.GalStar.Row0b fun h rc => IsRecT h rc := by
  first | exact h | exact UpperTheory.GalStar.Row0.row0b _ h

theorem propsB_iso {Rc : UpperTheory.GalStar.RecNotion} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {m : ℕ}
    [NumberField E] [IsAlgClosure E Ω] [IsCMField E] {π : CuspSub E m}
    {ι : Qbar l ≃+* ℂ} {r r' : G E Ω →* GL (Fin m) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : UpperTheory.GalStar.PropsB Rc π ι r wt HT) (hs : IsSSRep r') (h : RepIso r r') :
    UpperTheory.GalStar.PropsB Rc π ι r' wt HT := by
  have hc := continuous_of_iso H.cont h
  obtain ⟨g, hg⟩ := h
  have hg' : ∀ s, g * r s = r' s * g := fun s => by rw [hg, inv_mul_cancel_right]
  have ew : ∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w),
      wdOf h hw ι r' = wdOf h hw ι r := fun w hw A h =>
    ((isWDOf_wdOf (h := h) hw ι (Units.continuous_val.comp H.cont)).of_conj hw g fun s => hg' _).wdOf_eq hw
  refine ⟨hc, hs, fun w hw A h rc hrc σ hσ => ew w hw A h ▸ H.away w hw A h rc hrc σ hσ, H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj => ?_⟩
  have Ha := H.above P AI T w A h O Bw hj
  have e : ∀ s : ↥(Dec (F := E) A), r'.comp (Dec (F := E) A).subtype s = g * r.comp (Dec (F := E) A).subtype s * g⁻¹ :=
    fun s => hg s
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l P E Ω O _ Bw m _ _ g e
  refine ⟨fun σ hσ hf => ?_, fun σ hσ rc hrc h1 h2 => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := Ha.crys σ hσ hf
    exact ⟨c2 a1, c1 a2, fun τ L τ' hτ => c4 _ _ (a3 τ L τ' hτ)⟩
  · obtain ⟨a1, a2, a3, a4⟩ := Ha.nice σ hσ rc hrc h1 h2
    exact ⟨c1 a1, isPstAt_conj P Bw g e a2, fun τ L τ' hτ => c4 _ _ (a3 τ L τ' hτ), wdAt_conj P ι Bw h hj g e ▸ a4⟩

def ExCS : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub F n) (χ : HChar (maximalRealSubfield F)), (CG.mk π).IsRegAlg →
    (∀ v v' : InfinitePlace (maximalRealSubfield F), χ.locInf v (-1) = χ.locInf v' (-1)) →
    GlobalTheory.ContraPair.DualIsConjBy π (compNorm F χ) →
    ∃ (χ' : HChar (maximalRealSubfield F)) (r : G F Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ),
      compNorm F χ' = compNorm F χ ∧ UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) π ι r wt HT ∧ AttC ι r π ∧
      ∀ r' : G F Ω →* GL (Fin n) (Qbar l), Continuous r' → AttC ι r' π → UpperTheory.GalStar.PropsB (fun h rc => IsRecT h rc) π ι r' wt HT

end UpperTheory.Gal.SV
