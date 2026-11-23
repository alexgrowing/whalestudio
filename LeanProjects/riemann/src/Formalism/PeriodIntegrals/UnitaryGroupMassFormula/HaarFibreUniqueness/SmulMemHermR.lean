import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA

noncomputable section

namespace PI.OmFibreUniq.W.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.VolStabSW PI.VolStabSW.SdUniqW PI.AdicCompletionValuation
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (a : ℕ)

theorem sigR_algebraMap (c : R) : sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R _ c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem smul_mem_HermR (c : R) (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (hS : S ∈ HermR R σ a) :
    c • S ∈ HermR R σ a := by
  intro i j
  have h := hS i j
  simp only [Matrix.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, h, sigR_algebraMap]

instance hermSMul : SMul R (HermR R σ a) :=
  ⟨fun c S => ⟨c • (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)), smul_mem_HermR R σ a c S S.2⟩⟩

theorem coe_herm_smul (c : R) (S : HermR R σ a) :
    ((c • S : HermR R σ a) : Matrix (Fin a) (Fin a) (R ⊗[F] E)) = c • (S : Matrix _ _ _) := rfl

instance hermModule : Module R (HermR R σ a) :=
  Function.Injective.module R (HermR R σ a).subtype Subtype.val_injective (fun _ _ => rfl)

instance hermContSMul [TopologicalSpace R] [IsTopologicalRing R] :
    ContinuousSMul R (HermR R σ a) :=
  ⟨by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩

instance hermSC [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    [FiniteDimensional F E] : SecondCountableTopology (HermR R σ a) := by
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  exact TopologicalSpace.Subtype.secondCountableTopology _

end HermMod

def PsiNT : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)),
    IsCharAF F ψ → IsStdChar ψ → NumberField.IsTotallyReal F → ∃ y, psiV F ψ v y ≠ 1

def AbsSd : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ0 : Fv F v → ℂ),
    Continuous ψ0 → (∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s) → (∀ r, ‖ψ0 r‖ = 1) → (∃ y, ψ0 y ≠ 1) →
    ∀ {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
      [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → Fv F v),
      (∀ x x' y, B (x + x') y = B x y + B x' y) → (∀ (c : Fv F v) x y, B (c • x) y = c * B x y) →
      (∀ x y, B x y = B y x) → (∀ x, Continuous (B x)) →
      ∀ {ι : Type} [Fintype ι] (β β' : ι → V),
        (∀ x, x = ∑ j, B x (β' j) • β j) → (∀ y, y = ∑ j, B (β j) y • β' j) →
        ∃ μ : Measure V, SelfDual μ (fun x y => ψ0 (B x y))

def BRFacts : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ),
    IsCMExt F E σ → IsHermND σ J →
    (∀ x x' y : TupV (E := E) v n a,
      BR (Fv F v) σ J (x + x') y = BR (Fv F v) σ J x y + BR (Fv F v) σ J x' y) ∧
    (∀ (c : Fv F v) (x y : TupV (E := E) v n a), BR (Fv F v) σ J (c • x) y = c * BR (Fv F v) σ J x y) ∧
    (∀ x y : TupV (E := E) v n a, BR (Fv F v) σ J x y = BR (Fv F v) σ J y x) ∧
    (∀ x : TupV (E := E) v n a, Continuous (BR (Fv F v) σ J x))

def FrameW : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ),
    IsCMExt F E σ → IsHermND σ J →
    ∃ (ι : Type) (_ : Fintype ι) (β β' : ι → TupV (E := E) v n a),
      (∀ x, x = ∑ j, BR (Fv F v) σ J x (β' j) • β j) ∧
      (∀ y, y = ∑ j, BR (Fv F v) σ J (β j) y • β' j)

def HermFacts : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ), IsCMExt F E σ →
    (∀ x x' y : HermR (Fv F v) σ a,
      pairHerm (Fv F v) σ a (x + x') y = pairHerm (Fv F v) σ a x y + pairHerm (Fv F v) σ a x' y) ∧
    (∀ (c : Fv F v) (x y : HermR (Fv F v) σ a),
      pairHerm (Fv F v) σ a (c • x) y = c * pairHerm (Fv F v) σ a x y) ∧
    (∀ x y : HermR (Fv F v) σ a, pairHerm (Fv F v) σ a x y = pairHerm (Fv F v) σ a y x) ∧
    (∀ x : HermR (Fv F v) σ a, Continuous (pairHerm (Fv F v) σ a x))

def FrameH : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ), IsCMExt F E σ →
    ∃ (ι : Type) (_ : Fintype ι) (β β' : ι → HermR (Fv F v) σ a),
      (∀ x, x = ∑ j, pairHerm (Fv F v) σ a x (β' j) • β j) ∧
      (∀ y, y = ∑ j, pairHerm (Fv F v) σ a (β j) y • β' j)

theorem sdEx_of (hP : PsiNT) (hA : AbsSd) (hWf : BRFacts) (hW : FrameW) (hHf : HermFacts)
    (hH : FrameH) : SdEx := by
  intro F E _ _ _ _ _ σ n J ψ v a hS
  obtain ⟨hCM, hJ, hψ, hstd⟩ := hS
  have hc : Continuous (psiV F ψ v) := continuous_psiV ψ hψ.1 v
  have hadd := psiV_add ψ v
  have hn : ∀ r, ‖psiV F ψ v r‖ = 1 := fun r => hψ.2.1 _
  have hnt := hP ψ v hψ hstd hCM.1
  constructor
  · obtain ⟨ι, _, β, β', h1, h2⟩ := hW σ J v a hCM hJ
    obtain ⟨ha, hs, hsym, hcont⟩ := hWf σ J v a hCM hJ
    obtain ⟨μ, hμ⟩ := hA v _ hc hadd hn hnt (BR (Fv F v) σ J) ha hs hsym hcont β β' h1 h2
    exact ⟨μ, hμ⟩
  · obtain ⟨ι, _, β, β', h1, h2⟩ := hH σ v a hCM
    obtain ⟨ha, hs, hsym, hcont⟩ := hHf σ v a hCM
    obtain ⟨μ, hμ⟩ := hA v _ hc hadd hn hnt (pairHerm (Fv F v) σ a) ha hs hsym hcont β β' h1 h2
    exact ⟨μ, hμ⟩

end PI.OmFibreUniq.W.Sd
