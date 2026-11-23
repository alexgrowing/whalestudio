import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthGeFinrankOfSemilinearSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDieudonneModFrobeniusDifferentialsStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem colength_range_map_ge (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) :
    (Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (Module.finrank k (G.dual.Lie ⧸ LinearMap.range (lieMap H.dual G.dual (dualHom G H q))) : ℕ∞) ≤
        Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) := by
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  obtain ⟨hfin, -⟩ := rigExt_field_of_charP p k hp G
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials p T k
  have hred : ∀ m : T.M H, T.red G (T.map q m) = rigExtMap q (T.red H m) := fun m => by
    show T.base.red G trivial (T.base.smap trivial trivial (SemiHom.ofHom q) m) = _
    rw [T.base.red_smap, SemiHom.ofHom_rig]
  constructor
  · haveI : Module.Finite k G.omega :=
      Module.Finite.of_injective G.rigOfOmega (G.rigOfOmega_injective_of_eq_zero hp)
    obtain ⟨-, hsurj, -, hsemi, hnat⟩ := hθ G
    let Q := LinearMap.range (omegaMap G H q)
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M G) (G.omega ⧸ Q) (WittVector.frobeniusEquiv p k)
      (Q.mkQ.toAddMonoidHom.comp (θ G)) (Q.mkQ_surjective.comp hsurj) (fun a n => ?_)
      (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (θ G (WittVector.frobenius a • n)) = WittVector.constantCoeff a • Q.mkQ (θ G n)
      rw [hsemi, LinearMap.map_smul]
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (θ G (T.map q m)) = 0
      rw [hnat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩
  · haveI : Module.Finite k G.dual.Lie := Module.Finite.of_surjective (G.rigToLie hp) (G.rigToLie_surjective hp)
    let Q := LinearMap.range (lieMap H.dual G.dual (dualHom G H q))
    refine (GlobalTheory.T.length_ge_finrank_of_semilinear_surjective p k (T.M G) (G.dual.Lie ⧸ Q) (RingEquiv.refl _)
      ((Q.mkQ ∘ₗ G.rigToLie hp).toAddMonoidHom.comp (T.red G).toAddMonoidHom)
      ((Q.mkQ_surjective.comp (G.rigToLie_surjective hp)).comp (T.base.red_surjective G trivial))
      (fun a n => ?_) (LinearMap.range (T.map q))).1 ?_
    · show Q.mkQ (G.rigToLie hp (T.red G (a • n))) = WittVector.constantCoeff a • Q.mkQ (G.rigToLie hp (T.red G n))
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.map_smul]
    · rintro _ ⟨m, rfl⟩
      show Q.mkQ (G.rigToLie hp (T.red G (T.map q m))) = 0
      rw [hred, rigToLie_rigExtMap, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩

end GlobalTheory.Dieu
