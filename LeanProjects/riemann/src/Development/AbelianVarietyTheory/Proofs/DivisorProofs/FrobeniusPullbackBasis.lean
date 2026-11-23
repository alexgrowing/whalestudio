import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

variable {R R' M N : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R' N]

theorem basis_of_liftSemi_bijective {ι : Type} (f : M →ₛₗ[algebraMap R R'] N)
    (hf : Function.Bijective (liftSemi f)) (b : Module.Basis ι R M) :
    LinearIndependent R' (fun j => f (b j)) ∧
      Submodule.span R' (Set.range fun j => f (b j)) = ⊤ := by
  let c := (Algebra.TensorProduct.basis R' b).map (LinearEquiv.ofBijective _ hf)
  have e : (fun j => f (b j)) = c := funext fun j => by
    simp [c, Algebra.TensorProduct.basis_apply]
  rw [e]
  exact ⟨c.linearIndependent, c.span_eq⟩

theorem span_range_of_liftSemi_surjective (f : M →ₛₗ[algebraMap R R'] N)
    (hf : Function.Surjective (liftSemi f)) : Submodule.span R' (Set.range f) = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨y, rfl⟩ := hf z
  induction y with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)
  | tmul r m => exact Submodule.smul_mem _ r (Submodule.subset_span ⟨m, rfl⟩)

theorem flat_of_injective_of_isBezout [IsDomain R] [IsBezout R] [IsDomain R']
    (hi : Function.Injective (algebraMap R R')) : Module.Flat R R' :=
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hi
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)

theorem flat_frobRing {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
    (h : (p : R) = 0) : @Module.Flat R R _ _ (frobRing h).toAlgebra.toModule :=
  @flat_of_injective_of_isBezout R R _ _ (frobRing h).toAlgebra _ _ _
    ((injective_iff_map_eq_zero (frobRing h)).2 fun r hr =>
      (pow_eq_zero_iff hp.out.ne_zero).1 ((frobRing_apply h r).symm.trans hr))

end PDiv

namespace PDivGroup

theorem SemiHom.range_rigOfOmega_eq_span {p : ℕ} {R R' : Type} [CommRing R] [CommRing R']
    {σ : R →+* R'} {G : PDivGroup p R} {G' : PDivGroup p R'} (s : SemiHom σ G' G)
    (hs : Submodule.span R' (Set.range s.omega) = ⊤) :
    LinearMap.range G'.rigOfOmega =
      Submodule.span R' (s.rig '' (LinearMap.range G.rigOfOmega : Set G.RigExt)) := by
  rw [LinearMap.range_eq_map G'.rigOfOmega, ← hs, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, rfl⟩, s.rig_rigOfOmega w⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨_, ⟨w, rfl⟩, (s.rig_rigOfOmega w).symm⟩

theorem rigExt_frobTwist : GlobalTheory.Published.BarsottiTateDieudonne.WittModule → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (h : (p : R) = 0) (G : PDivGroup p R), (∀ (n : ℕ) (b : Module.Basis (Fin n) R G.RigExt), LinearIndependent R (fun j => (frobProj h G).rig (b j)) ∧ Submodule.span R (Set.range fun j => (frobProj h G).rig (b j)) = ⊤) ∧ LinearMap.range (frobTwist h G).rigOfOmega = Submodule.span R ((frobProj h G).rig '' (LinearMap.range G.rigOfOmega : Set G.RigExt)) := by
  intro _ p _ R _ _ _ h G
  refine ⟨fun n b => ?_, (frobProj h G).range_rigOfOmega_eq_span ?_⟩
  · exact @basis_of_liftSemi_bijective R R _ _ _ _ (frobRing h).toAlgebra _ _ _ _ _ _
      (@liftSemi_rig_bijective p R R _ _ G _ (frobRing h).toAlgebra h (Or.inl (flat_frobRing h))) b
  · exact @span_range_of_liftSemi_surjective R R _ _ _ _ (frobRing h).toAlgebra _ _ _ _ _
      (@T.omega_baseChange_bijective_of_p_eq_zero p R _ G R _ (frobRing h).toAlgebra h).2

end PDivGroup

end GlobalTheory
