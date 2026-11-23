import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftIdempotentAdicComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicCompleteStatement

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem existsUnique_idempotent_sharp {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.U)
    (he : IsIdempotentElem e) : ∃! e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = e := by
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  haveI hcA : IsAdicComplete (Ideal.span {A.pi ^ 1}) A.A := by
    rw [pow_one]; exact A.compl
  haveI hcA' : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
  haveI hcU : IsAdicComplete (Ideal.span {(l : A.U)}) A.U := GlobalTheory.T.untilt_adic_complete A
  have hmemker : ∀ x y : A.A, A.aToU1 x = A.aToU1 y →
      Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y := by
    intro x y h
    apply Ideal.Quotient.eq.2
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub, h, sub_self]
  have hsharp_idem : ∀ x : A.A, IsIdempotentElem x → IsIdempotentElem (A.sharp x) := fun x hx =>
    hx.map A.sharp
  have hU := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift (l : A.U) 1 one_ne_zero
    (Ideal.Quotient.mk _ e) (he.map (Ideal.Quotient.mk _))
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk _ e)
  have haid : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) a) := by
    have : A.aToU1 (a * a) = A.aToU1 a := by
      rw [map_mul, ha]
      exact congrArg _ he |>.trans rfl
    have h2 := hmemker _ _ this
    rw [map_mul] at h2
    exact h2
  obtain ⟨e₀, ⟨he₀, hmk⟩, huniq⟩ := GlobalTheory.CompanionTheory.IdemLift.existsUnique_idempotent_lift A.pi 1 one_ne_zero
    (Ideal.Quotient.mk _ a) haid
  have hcong : ∀ x y : A.A, Ideal.Quotient.mk (Ideal.span {A.pi ^ 1}) x = Ideal.Quotient.mk _ y →
      A.aToU1 x = A.aToU1 y := by
    intro x y h
    have h3 := Ideal.Quotient.eq.1 h
    rw [pow_one, ← hker, RingHom.mem_ker, map_sub] at h3
    exact sub_eq_zero.1 h3
  refine ⟨e₀, ⟨he₀, ?_⟩, ?_⟩
  · refine hU.unique ⟨hsharp_idem _ he₀, ?_⟩ ⟨he, rfl⟩
    rw [← A.sharpMap_eq, hcong _ _ hmk, ha]
  · rintro e₁ ⟨he₁, hs₁⟩
    refine huniq e₁ ⟨he₁, ?_⟩
    rw [← hmk]
    apply hmemker
    have hs₀ : A.sharp e₀ = e := hU.unique ⟨hsharp_idem _ he₀, by
      rw [← A.sharpMap_eq, hcong _ _ hmk, ha]⟩ ⟨he, rfl⟩
    rw [A.sharpMap_eq, A.sharpMap_eq, hs₁, hs₀]

end GlobalTheory.CompanionTheory.Untilt
