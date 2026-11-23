import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory

theorem exists_finset_sum_translate_fixed {G X : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : X) (hx : IsOpen {g | ρ g x = x}) :
    ∃ s : Finset G, (∀ g ∈ s, g ∈ K) ∧ s.Nonempty ∧
      ∀ k ∈ K, ρ k (∑ g ∈ s, ρ g x) = ∑ g ∈ s, ρ g x := by
  classical
  have hmul : ∀ (a b : G) (y : X), ρ (a * b) y = ρ a (ρ b y) := fun a b y => by
    rw [map_mul, Module.End.mul_apply]
  have hinv : ∀ (a : G) (y : X), ρ a⁻¹ (ρ a y) = y := fun a y => by
    rw [← hmul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ (a : G) (y : X), ρ a (ρ a⁻¹ y) = y := fun a y => by
    rw [← hmul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun i : K => (fun g => (i : G)⁻¹ * g) ⁻¹' {g | ρ g x = x})
    (fun i => hx.preimage (continuous_const.mul continuous_id))
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, show ρ (k⁻¹ * k) x = x by
      rw [inv_mul_cancel, map_one, Module.End.one_apply]⟩)
  let F : Finset X := t.image (fun i : K => ρ (i : G) x)
  have hFmem : ∀ y, y ∈ F ↔ ∃ k ∈ K, ρ k x = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
      refine Finset.mem_image.2 ⟨i, hi, ?_⟩
      have h1 : ρ ((i : G)⁻¹ * k) x = x := hki
      calc ρ (i : G) x = ρ (i : G) (ρ ((i : G)⁻¹ * k) x) := by rw [h1]
        _ = ρ k x := by rw [← hmul, mul_inv_cancel_left]
  let f : X → G := fun y => if h : ∃ k ∈ K, ρ k x = y then h.choose else 1
  have hf : ∀ y ∈ F, f y ∈ K ∧ ρ (f y) x = y := by
    intro y hy
    have h := (hFmem y).1 hy
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine ⟨F.image f, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hg
    exact (hf y hy).1
  · exact Finset.Nonempty.image ⟨x, (hFmem x).2 ⟨1, K.one_mem, by
      rw [map_one, Module.End.one_apply]⟩⟩ f
  · have hsum : ∑ g ∈ F.image f, ρ g x = ∑ y ∈ F, y := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun y hy => (hf y hy).2)
      · intro y hy y' hy' h
        rw [← (hf y hy).2, ← (hf y' hy').2]
        exact congrArg (fun g => ρ g x) h
    intro k hk
    rw [hsum, map_sum]
    refine Finset.sum_nbij' (fun y => ρ k y) (fun y => ρ k⁻¹ y) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro y hy
      obtain ⟨k', hk', rfl⟩ := (hFmem y).1 hy
      exact (hFmem _).2 ⟨k * k', K.mul_mem hk hk', hmul _ _ _⟩
    · intro y hy
      obtain ⟨k', hk', rfl⟩ := (hFmem y).1 hy
      exact (hFmem _).2 ⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', hmul _ _ _⟩
    · intro y _
      exact hinv k y
    · intro y _
      exact hinv' k y

end GlobalTheory
