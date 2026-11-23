import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.TorSB

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem psi_isLocallyConstant {ψ : AddChar F Circle} (hψ : IsStd ψ) :
    IsLocallyConstant fun r : F => ((ψ r : Circle) : ℂ) := by
  have h := isTrivialOn_addCharConductor hψ.1 hψ.2.1
  rw [hψ.2.2] at h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (valBall F 0 : Set F),
    (isOpen_valBall 0).preimage (continuous_id.sub continuous_const), ?_, fun y hy => ?_⟩
  · show x - x ∈ valBall F 0
    rw [sub_self]
    exact (valBall F 0).zero_mem
  · have h1 : ψ (y - x) = 1 := h _ hy
    have h2 : y = x + (y - x) := by ring
    show ((ψ y : Circle) : ℂ) = ((ψ x : Circle) : ℂ)
    rw [h2, AddChar.map_add_eq_mul, h1, mul_one]

theorem indicator_isLocallyConstant {X : Type} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    {f : X → ℂ} (hf : IsLocallyConstant f) : IsLocallyConstant (S.indicator f) := by
  have h := (LocallyConstant.indicator (⟨f, hf⟩ : LocallyConstant X ℂ) hS).isLocallyConstant
  have e : S.indicator f = ((LocallyConstant.indicator (⟨f, hf⟩ : LocallyConstant X ℂ) hS) : X → ℂ) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, LocallyConstant.indicator_of_mem _ hS hx]
      rfl
    · rw [Set.indicator_of_notMem hx, LocallyConstant.indicator_of_notMem _ hS hx]
  rw [e]
  exact h

theorem torF_mem (n : ℕ) : torF F n ∈ schwartzBruhat F := by
  have hcont : Continuous fun x : F => x - 1 := continuous_id.sub continuous_const
  have hcl : IsClopen ({x : F | x - 1 ∈ valBall F (n : ℤ)} : Set F) :=
    ⟨(isClosed_valBall (n : ℤ)).preimage hcont, (isOpen_valBall (n : ℤ)).preimage hcont⟩
  have hK : IsCompact ({x : F | x - 1 ∈ valBall F (n : ℤ)} : Set F) := by
    have : ({x : F | x - 1 ∈ valBall F (n : ℤ)} : Set F) =
        (fun y : F => y + 1) '' (valBall F (n : ℤ) : Set F) := by
      ext x
      constructor
      · intro hx
        exact ⟨x - 1, hx, by ring⟩
      · rintro ⟨y, hy, rfl⟩
        show y + 1 - 1 ∈ valBall F (n : ℤ)
        simpa using hy
    rw [this]
    exact (isCompact_valBall (n : ℤ)).image (continuous_id.add continuous_const)
  refine ⟨indicator_isLocallyConstant hcl (IsLocallyConstant.const (1 : ℂ)), ?_⟩
  exact HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _

theorem torG_mem {ψ : AddChar F Circle} (hψ : IsStd ψ) (n : ℕ) : torG ψ n ∈ schwartzBruhat F := by
  have hcl : IsClopen (valBall F (-(n : ℤ)) : Set F) :=
    ⟨isClosed_valBall _, isOpen_valBall _⟩
  refine ⟨indicator_isLocallyConstant hcl (psi_isLocallyConstant hψ), ?_⟩
  exact HasCompactSupport.intro (isCompact_valBall (-(n : ℤ)))
    fun x hx => Set.indicator_of_notMem hx _

theorem pt_mem {f g : F → ℂ} (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    Ad3.SchwartzSpaceL2.pt f g ∈ GodementSectionLocal.schwartzBruhat2 F := by
  refine GodementSectionLocal.mem_schwartzBruhat2.2
    ⟨(hf.1.comp_continuous (continuous_apply 0)).mul (hg.1.comp_continuous (continuous_apply 1)), ?_⟩
  refine HasCompactSupport.intro
    ((hf.2.isCompact.prod hg.2.isCompact).image (Homeomorph.finTwoArrow (X := F)).symm.continuous)
    fun x hx => ?_
  by_contra hne
  refine hx ⟨(x 0, x 1), ⟨subset_tsupport _ fun h => hne ?_, subset_tsupport _ fun h => hne ?_⟩, ?_⟩
  · simp [Ad3.SchwartzSpaceL2.pt, h]
  · simp [Ad3.SchwartzSpaceL2.pt, h]
  · ext j
    fin_cases j <;> simp

theorem tor_schwartzBruhat : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ n : ℕ, 1 ≤ n →
  torF F n ∈ schwartzBruhat F ∧ torG ψ n ∈ schwartzBruhat F ∧ Ad3.SchwartzSpaceL2.pt (torF F n) (torG ψ n) ∈ GodementSectionLocal.schwartzBruhat2 F := by
  intro F _ _ _ _ _ _ ψ hψ n _
  exact ⟨torF_mem n, torG_mem hψ n, pt_mem (torF_mem n) (torG_mem hψ n)⟩

end GlobalTheory.CompanionTheory.TorSB
