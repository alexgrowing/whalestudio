import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase

set_option autoImplicit false

noncomputable section

open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.ExpFrame

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

theorem exists_unif_dvd (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (l : ℕ)
    (hl : l ≠ 0) (hu : ¬ IsUnit ((l : ℕ) : O)) :
    ∃ (ϖ : O) (n : ℕ), Irreducible ϖ ∧ ϖ ∣ (l : O) ∧ (l : O) ∣ ϖ ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h0 : ((l : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  refine ⟨ϖ, n, hϖ, ?_, hn.dvd⟩
  rcases n with _ | n
  · exact absurd (hn.isUnit_iff.2 (by simp)) hu
  · exact (dvd_pow_self ϖ n.succ_ne_zero).trans hn.symm.dvd

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

open GlobalTheory.ExpTie

section Sub

variable {ι : Type} {N : ℕ} {lam : ι → ℕ → ℕ} (X : HidaSetting ι N lam) (ϖ : X.O)

abbrev Red : Type := NablaT X.O N lam ⧸ scaleSub X.A (NablaT X.O N lam) ϖ

abbrev SimpIx : Type :=
  Σ E : Submodule X.A (Red X ϖ), {N' : Submodule X.A E // IsSimpleModule X.A (E ⧸ N')}

abbrev SimpMod (μ : SimpIx X ϖ) : Type := μ.1 ⧸ μ.2.1

variable {X ϖ}

theorem exists_simpMod (Gm : Type) [AddCommGroup Gm] [Module X.A Gm] [IsSimpleModule X.A Gm]
    (h : IsSubquot X.A (Red X ϖ) Gm) :
    ∃ μ : SimpIx X ϖ, Nonempty (Gm ≃ₗ[X.A] SimpMod X ϖ μ) := by
  obtain ⟨E, ψ, hψ⟩ := h
  let e := ψ.quotKerEquivOfSurjective hψ
  haveI : IsSimpleModule X.A (E ⧸ LinearMap.ker ψ) := IsSimpleModule.congr e
  exact ⟨⟨E, LinearMap.ker ψ, inferInstance⟩, ⟨e.symm⟩⟩

end Sub

end GlobalTheory.ExpModel

namespace GlobalTheory.ExpModel

section SubF

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
  (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))]
  [IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (m : Ideal F.T) [m.IsPrime] (ϖ : F.O)

abbrev modA (μ : SimpIx (F.setting lam jK m) ϖ) : Module (alg F.O N lam) (SimpMod (F.setting lam jK m) ϖ μ) :=
  (inferInstance : Module (F.setting lam jK m).A (SimpMod (F.setting lam jK m) ϖ μ))

end SubF

end GlobalTheory.ExpModel

end
