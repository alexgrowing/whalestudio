import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
import Formalism.PadicSubsetSums.StableGradedCounts.CentralIdempotentsSumOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSimpleModuleOfFinrankEnd
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys.ZSum

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem zIdem_eq_centralIdem (τ : FDRep ℂ Γ) : zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

theorem zIdem_eq_charIdem' (τ : FDRep ℂ Γ) : zIdem τ = PI.CharIdem.charIdem τ := by
  unfold zIdem PI.CharIdem.charIdem
  rfl

theorem isIrreducible_of_simple (τ : FDRep ℂ Γ) (h : Simple τ) : Representation.IsIrreducible τ.ρ := by
  haveI := h
  have hc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero hc
  apply GlobalTheory.AbsIrrDescent.isIrreducible_of_norm_one
  have hs := FDRep.char_orthonormal τ τ
  rw [if_pos ⟨Iso.refl _⟩, inv_mul_eq_one₀ hc] at hs
  exact hs.symm

theorem isIrr_of_simple (τ : FDRep ℂ Γ) (h : Simple τ) : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr τ.ρ :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.isIrr_of_isIrreducible _ (isIrreducible_of_simple τ h)

theorem isIrreducible_of_isIrr {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ Γ W)
    (h : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr σ) : σ.IsIrreducible := by
  obtain ⟨hnt, hW⟩ := h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule e
    exact (bot_ne_top : (⊥ : Submodule ℂ W) ≠ ⊤) h1
  · rcases hW U.toSubmodule (fun g x hx => U.apply_mem_toSubmodule g hx) with h1 | h1
    · left; exact Subrepresentation.toSubmodule_injective h1
    · right; exact Subrepresentation.toSubmodule_injective h1

theorem zIdem_eq_of_iso {τ τ' : FDRep ℂ Γ} (i : τ ≅ τ') : zIdem τ = zIdem τ' := by
  have h1 : τ.character = τ'.character := FDRep.char_iso i
  have h2 : Module.finrank ℂ τ = Module.finrank ℂ τ' := (FDRep.isoToLinearEquiv i).finrank_eq
  change ∑ γ : Γ, MonoidAlgebra.single γ ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * τ.character γ⁻¹) =
    ∑ γ : Γ, MonoidAlgebra.single γ ((Module.finrank ℂ τ' : ℂ) / Fintype.card Γ * τ'.character γ⁻¹)
  rw [h1, h2]

theorem zIdem_eq_of_equiv (τ τ' : FDRep ℂ Γ) (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) :
    zIdem τ = zIdem τ' := by
  have h2 : Module.finrank ℂ τ = Module.finrank ℂ τ' := φ.finrank_eq
  have h1 : ∀ g, LinearMap.trace ℂ τ' (τ'.ρ g) = LinearMap.trace ℂ τ (τ.ρ g) := by
    intro g
    have : τ'.ρ g = φ.conj (τ.ρ g) := by
      ext x; simp [LinearEquiv.conj_apply, hφ]
    rw [this, LinearMap.trace_conj']
  unfold zIdem
  simp only [h1, h2]

theorem zIdem_ne_zero (τ : FDRep ℂ Γ) (h : Simple τ) : zIdem τ ≠ 0 := by
  intro h0
  have ha := (orthogonalCentral Γ τ τ h h).1
  rw [← zIdem_eq_charIdem', h0, map_zero] at ha
  obtain ⟨hnt, -⟩ := isIrr_of_simple τ h
  obtain ⟨v, hv⟩ := exists_ne (0 : τ)
  exact hv (by simpa using (LinearMap.congr_fun ha v).symm)

theorem zIdem_mul_self (τ : FDRep ℂ Γ) (h : Simple τ) : zIdem τ * zIdem τ = zIdem τ := by
  have := (orthogonalCentral Γ τ τ h h).2.2.1
  rw [zIdem_eq_charIdem']; exact this

theorem zIdem_mul_of_ne (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ') (hne : zIdem τ ≠ zIdem τ') :
    zIdem τ * zIdem τ' = 0 := by
  have := (orthogonalCentral Γ τ τ' h h').2.2.2.2 ⟨fun i => hne (zIdem_eq_of_iso i)⟩
  rw [zIdem_eq_charIdem', zIdem_eq_charIdem']; exact this

end GlobalTheory.SerOSys.ZSum

namespace GlobalTheory.SerOSys.ZSum

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem zIdem_set_finite :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite := by
  set S := {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}
  have hli : LinearIndependent ℂ (fun z : S => (z : MonoidAlgebra ℂ Γ)) := by
    rw [linearIndependent_iff']
    intro s c hs j hj
    obtain ⟨τ, hτ, hτz⟩ := j.2
    have hmul := congrArg (· * (j : MonoidAlgebra ℂ Γ)) hs
    simp only [Finset.sum_mul, zero_mul, smul_mul_assoc] at hmul
    rw [Finset.sum_eq_single j] at hmul
    · rw [← hτz, zIdem_mul_self τ hτ] at hmul
      exact (smul_eq_zero.1 hmul).resolve_right (zIdem_ne_zero τ hτ)
    · intro i _ hij
      obtain ⟨σ, hσ, hσz⟩ := i.2
      have hne : zIdem σ ≠ zIdem τ := by
        rw [hσz, hτz]; exact fun e => hij (Subtype.ext e)
      rw [← hσz, ← hτz, zIdem_mul_of_ne σ τ hσ hτ hne, smul_zero]
    · intro hn; exact absurd hj hn
  exact Set.finite_coe_iff.1 hli.finite

theorem zIdem_set_finsum :
    ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := by
  classical
  set S := {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z} with hS
  have hfin : S.Finite := zIdem_set_finite
  letI : Fintype S := hfin.fintype
  choose τ hτ hτz using fun z : S => z.2
  have key := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_sum_one Γ S (fun z => (τ z : Type)) (fun z => (τ z).ρ)
    (fun z => isIrr_of_simple (τ z) (hτ z))
    (fun i j ⟨φ, hφ⟩ => Subtype.ext ((hτz i).symm.trans ((zIdem_eq_of_equiv (τ i) (τ j) φ hφ).trans (hτz j))))
    (fun W _ _ _ σ hσ => by
      haveI := isIrreducible_of_isIrr σ hσ
      have hs : Simple (FDRep.of σ) := PI.GreenLabelSurjWork.simple_of_irr σ
      let i : S := ⟨zIdem (FDRep.of σ), FDRep.of σ, hs, rfl⟩
      obtain ⟨e, he⟩ := repIso_of_zIdem_eq_of_simple (FDRep.of σ) (τ i) hs (hτ i) (hτz i).symm
      exact ⟨i, e, fun g x => he g x⟩)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_subtype hfin.toFinset (fun x => Set.Finite.mem_toFinset hfin) (fun z => z), ← key]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← zIdem_eq_centralIdem, hτz z]

end GlobalTheory.SerOSys.ZSum

namespace GlobalTheory.SerOSys

theorem zIdem_finite_and_finsum_eq_one : ∀ (Γ : Type) [Group Γ] [Fintype Γ],
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 :=
  fun _ _ _ => ⟨ZSum.zIdem_set_finite, ZSum.zIdem_set_finsum⟩

end GlobalTheory.SerOSys
