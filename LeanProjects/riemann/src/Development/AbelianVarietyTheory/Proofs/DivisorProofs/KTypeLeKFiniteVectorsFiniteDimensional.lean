import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStabIffIsKStableOnFiniteVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactHighestWeightUniqueOfIrreducibleStatement
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.kTypeInKFinite : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → S ≤ D ∧ FiniteDimensional ℂ (S.comap D.subtype) ∧ KStab ε E (S.comap D.subtype) ∧ (∀ ν : Fin n → ℝ, ∀ x ∈ S.comap D.subtype, x ≠ 0 → KHighest ε E ν x → ν = μ) := by
  intro n ε H _ _ σ D E hH hU hI hK μ S hS
  have hSD : S ≤ D := fun v hv => (hK.mem v).2 ⟨S, hS.1, hv, hS.2.1⟩
  haveI : FiniteDimensional ℂ S := hS.1
  have hmap : (S.comap D.subtype).map D.subtype = S := by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hSD
  haveI hFD : FiniteDimensional ℂ (S.comap D.subtype) :=
    LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hSD).symm
  have hStab : KStab ε E (S.comap D.subtype) := by
    rw [GlobalTheory.T.kStab_iff_isKStableOn_finite_vectors n ε H σ D E hH hU hI hK _ hFD, hmap]; exact hS.2.1
  have hinj := Submodule.map_injective_of_injective (f := D.subtype) Subtype.val_injective
  have hirr : ∀ L' ≤ S.comap D.subtype, KStab ε E L' → L' = ⊥ ∨ L' = S.comap D.subtype := by
    intro L' hL' hst
    haveI : FiniteDimensional ℂ L' := Submodule.finiteDimensional_of_le hL'
    have hK' := (GlobalTheory.T.kStab_iff_isKStableOn_finite_vectors n ε H σ D E hH hU hI hK L' inferInstance).1 hst
    have hle : L'.map D.subtype ≤ S := hmap ▸ Submodule.map_mono hL'
    rcases hS.2.2.1 _ hle hK' with h | h
    · left; apply hinj; rw [h, Submodule.map_bot]
    · right; apply hinj; rw [h, hmap]
  obtain ⟨v, hv0, hvS, hvh⟩ := hK.hw μ S hS
  have hKR : KRel ε E := fun a b c d _ _ => hK.gl a b c d
  have hKU : KUnit ε E := fun a b h x y => by rw [hK.unit a b x y]; simp [Formalism.REAL.sgn, h]
  refine ⟨hSD, hFD, hStab, ?_⟩
  exact GlobalTheory.T.compactHighestWeight_unique_of_irreducible n ε D E hKR hKU _ hFD hStab hirr μ v hvS hv0 hvh
