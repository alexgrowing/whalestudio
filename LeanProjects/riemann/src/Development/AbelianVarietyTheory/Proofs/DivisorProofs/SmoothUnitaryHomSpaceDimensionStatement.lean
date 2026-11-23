import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothUnitaryHomSpaceDimension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_unitary_hom_space_dimension : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ν α : kˣ →* ℂˣ), GlobalTheory.KSplit.IsSmU ν → GlobalTheory.KSplit.IsSmU α →
    ∀ (U V V' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
      (π : Representation ℂ (GL (Fin d) k) U) (ρ : Representation ℂ (GL (Fin n) k) V) (ρ' : Representation ℂ (GL (Fin n) k) V'),
      π.IsIrreducible → GlobalTheory.PRep.IsAdmissible π → ρ.IsIrreducible → ρ'.IsIrreducible →
      ∀ (P : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] U →ₗ[ℂ] V) (P' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] U →ₗ[ℂ] V'),
        P ≠ 0 → P' ≠ 0 →
        (∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Ψ Ψ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)),
          (Ψ' : Matrix (Fin n) (Fin d) k → ℂ) = GlobalTheory.SplitFlip.omB ν α g h Ψ → ∀ u, P Ψ' (π h u) = ρ g (P Ψ u)) →
        (∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Ψ Ψ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)),
          (Ψ' : Matrix (Fin n) (Fin d) k → ℂ) = GlobalTheory.SplitFlip.omB ν α g h Ψ → ∀ u, P' Ψ' (π h u) = ρ' g (P' Ψ u)) →
        Nonempty (ρ.Equiv ρ') := by
  first | exact @GlobalTheory.HoweFlipPair.uniq | exact GlobalTheory.HoweFlipPair.uniq | (intros; apply GlobalTheory.HoweFlipPair.uniq <;> assumption)
