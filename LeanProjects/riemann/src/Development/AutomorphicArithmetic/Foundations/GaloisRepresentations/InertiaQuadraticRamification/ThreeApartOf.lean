import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def QuadDisj : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : Set (HeightOneSpectrum (𝓞 F)))
    (N : Subgroup (G F Ω)), (∀ u ∉ T, ∀ A : ValuationSubring Ω, IsPlaceOver A u → Ine (F := F) A ≤ N) →
    ∀ Q : QCM F Ω, RamOff T Q → GlobalTheory.AboveL.SolvDisj ↥Q.K N

def AllUnr : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (T : Set (HeightOneSpectrum (𝓞 Y)))
    (Q : QCM Y Ω), Step1 T Q → ∀ w : HeightOneSpectrum (𝓞 ↥Q.K),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield ↥Q.K)) w.asIdeal

def Double : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))) (Q : QCM E Ω), Step0 T Q → ∀ t ∈ T,
    ∃ w₁ w₂ : HeightOneSpectrum (𝓞 ↥Q.K), w₁.under (𝓞 E) = t ∧ w₂.under (𝓞 E) = t ∧ GlobalTheory.Cong.Apart w₁ w₂

def ApartUp : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M],
    (∀ w₁ w₂ : HeightOneSpectrum (𝓞 M), GlobalTheory.Cong.Apart (w₁.under (𝓞 K)) (w₂.under (𝓞 K)) → GlobalTheory.Cong.Apart w₁ w₂) ∧
    ∀ v : HeightOneSpectrum (𝓞 K), ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v

def ThreeApart : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T₁ : Set (HeightOneSpectrum (𝓞 E))) (Q₁ : QCM E Ω), Step0 T₁ Q₁ →
    ∀ (T₂ : Set (HeightOneSpectrum (𝓞 ↥Q₁.K))) (Q₂ : QCM ↥Q₁.K Ω), Step0 T₂ Q₂ → ∀ t ∈ T₁,
    (∀ w : HeightOneSpectrum (𝓞 ↥Q₁.K), w.under (𝓞 E) = t → w ∈ T₂) →
    ∀ (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra ↥Q₂.K M],
    ∃ w : Fin 3 → HeightOneSpectrum (𝓞 M), (∀ i, (((w i).under (𝓞 ↥Q₂.K)).under (𝓞 ↥Q₁.K)).under (𝓞 E) = t) ∧
      ∀ i j, i ≠ j → GlobalTheory.Cong.Apart (w i) (w j)

def SatSplit : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra K M]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)), IsPlaceOver A v → IsPlaceOver A w →
    (∀ g ∈ Dec (F := K) A, Fixes M g) → ∀ (a : ℕ) (π : CuspSub K a) (P : CuspSub M a),
    UpperTheory.CBC.SplitLift (UpperTheory.CBC.Cusp.cx π) (UpperTheory.CBC.Cusp.cx P) → ∀ B, (CG.mk π).HasSat v B → (CG.mk P).HasSat w B

def GoodOf : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (l a : ℕ)
    (π : CuspSub Y a) (T : Set (HeightOneSpectrum (𝓞 Y))),
    (∀ u ∉ T, ((l : ℕ) : 𝓞 Y) ∉ u.asIdeal ∧ ∃ B, (CG.mk π).HasSat u B) → ∀ Q : QCM Y Ω, Step1 T Q →
    ∀ P : CuspSub ↥Q.K a, UpperTheory.CBC.SplitLift (UpperTheory.CBC.Cusp.cx π) (UpperTheory.CBC.Cusp.cx P) → GlobalTheory.GalCut.Good l P

theorem threeApart_of (h1 : Double) (h2 : ApartUp) : ThreeApart := by
  intro E Ω _ _ _ _ _ _ T₁ Q₁ s₁ T₂ Q₂ s₂ t ht hT M _ _ _ _
  obtain ⟨a, b, ha, hb, hab⟩ := h1 E Ω T₁ Q₁ s₁ t ht
  obtain ⟨x, y, hx, hy, hxy⟩ := h1 ↥Q₁.K Ω T₂ Q₂ s₂ a (hT a ha)
  obtain ⟨z, hz⟩ := (h2 ↥Q₁.K ↥Q₂.K).2 b
  have hxz : GlobalTheory.Cong.Apart x z := (h2 ↥Q₁.K ↥Q₂.K).1 x z (by rw [hx, hz]; exact hab)
  have hyz : GlobalTheory.Cong.Apart y z := (h2 ↥Q₁.K ↥Q₂.K).1 y z (by rw [hy, hz]; exact hab)
  choose up hup using (h2 ↥Q₂.K M).2
  refine ⟨fun i => up (![x, y, z] i), fun i => ?_, fun i j hij => (h2 ↥Q₂.K M).1 _ _ ?_⟩
  · rw [hup]
    fin_cases i
    · simpa [hx] using ha
    · simpa [hy] using ha
    · simpa [hz] using hb
  · rw [hup, hup]
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hxy | exact hxz | exact hyz | exact hxy.symm | exact hxz.symm | exact hyz.symm

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
