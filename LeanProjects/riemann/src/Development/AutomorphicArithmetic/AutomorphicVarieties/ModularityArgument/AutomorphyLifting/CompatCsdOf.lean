import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcross
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatCsd

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def AAcross2 : Prop :=
  HypothesesH → RowT → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
    Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ r : G ℚ Ω →* GL (Fin n) (Qbar l), (∀ v : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → PotUnl r v) →
    Continuous r → IsAutomorphicOverImagQuad ι r → (∃ θ, IsAlgChar ι θ ∧ DualTw r θ) → IneAb r → Flagged r →
    IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) →
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → WitAQ ι r

variable {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

theorem WitA.iso' [IsCMField F] (e : RepIso r r') (h : WitA ι r) : WitA ι r' :=
  have u : ∀ {r r' : G F Ω →* GL (Fin n) (Qbar l)}, RepIso r r' → ∀ v, (Unl1 r v → Unl1 r' v) ∧ (PotUnl r v → PotUnl r' v) :=
    fun e _ => ⟨fun k A hA => (k A hA).imp fun _ j => ⟨j.1.of_iso e, j.2⟩, fun k A hA => (k A hA).imp fun _ j => ⟨j.1.of_iso e, j.2⟩⟩
  ⟨fun v hv k => (u e v).2 (h.1 v hv ((u e.symm' v).1 k)), fun π hreg ha =>
    (h.2 π hreg (attC_iso e.symm' ha)).imp fun _ ht v hv => ht v (hv.imp id (u e.symm' v).2)⟩

theorem ParAtT.congr {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 E)} {p p' : Gu.Par Ω w}
    (H : ParAtT ι r w p) (e : ∀ A h rc, IsRecT h rc → p A h rc = p' A h rc) : ParAtT ι r w p' :=
  fun A h rc hrc => e A h rc hrc ▸ H A h rc hrc

def CompatCsdT : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n), Continuous r →
    (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → AttC ι r π → ∀ w σ, π.IsLocComp w σ → LocGlobT ι r w σ

end UpperTheory.V.Z.Win
