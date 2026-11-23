import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadEltIdemCentral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffOneRealOfIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenInfKerLeOfSemidirectSplitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubGoodIdempotentEqBadTupleSumsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightUpperUnitriangularIdempotentIndepCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem bad_part_le_locShare : ∀ (D : D7) (Γ V : Type) [Group Γ] [Finite Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G0g D.nd) (ι : G0g D.nd →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D P lam ψ → ∀ (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup (G0g D.nd)), (∀ k, IsHalf D k (H k)) → ∀ (n : Fin 2 → ℕ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → ∀ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) → ∃ S : ∀ k : Fin 2, Finset (Tup D k), (∀ k, ∀ t ∈ S k, ¬ goodAt D k t) ∧ (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) : ℝ) ≤ c * (locShare D (fun k _ => eUk D k (ψ₀ k)) 0 (S 0) + locShare D (fun k _ => eUk D k (ψ₀ k)) 1 (S 1)) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  intro D Γ V _ _ _ _ _ π ι hs ρ P lam ψ hW lamb hlamb H hH n c hemb hn ψ₀ hψ₀
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  haveI : Finite (G0g D.nd) := Finite.of_injective ι (fun a b h => by
    have := congrArg π h; rwa [hs.1, hs.1] at this)
  letI : Fintype (G0g D.nd) := Fintype.ofFinite _
  obtain ⟨S, hbad, hsplit⟩ := GlobalTheory.T.one_sub_goodIdempotent_eq_badTupleSums D
  have hloc : ∀ k, locShare D (fun k' v => eUk D k' (ψ ⟨k', v⟩)) k (S k) =
      locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) := by
    intro k
    unfold locShare
    refine Finset.sum_congr rfl fun t _ => Finset.prod_congr rfl fun v _ => ?_
    exact GlobalTheory.T.weight_upperUnitriangularIdempotent_indep_character D k _ _ (hW.1 ⟨k, v⟩) (hψ₀ k) (t v)
  refine ⟨S, hbad, ?_⟩
  have key := GlobalTheory.T.finrank_eigen_inf_ker_le_of_semidirect_split (G0g D.nd) Γ V π ι hs ρ P lam lamb hlamb H n D.ntypes.e0
    (fun k => badElt D k (S k)) (fun k => locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k)) c hemb hn
    (fun k => (GlobalTheory.BadCount.IdemCen.badElt_idem_central D k (S k)).1)
    (fun k a => (GlobalTheory.BadCount.IdemCen.badElt_idem_central D k (S k)).2 a)
    (by simpa using hsplit)
    (fun k g hg => (GlobalTheory.BadCount.badElt_mul_lvlIdem D P lam ψ hW k (S k) (H k) (hH k)).1 g hg)
    (fun k => by rw [← hloc k]; exact (GlobalTheory.BadCount.badElt_mul_lvlIdem D P lam ψ hW k (S k) (H k) (hH k)).2)
  simpa using key

end GlobalTheory.BadCount
