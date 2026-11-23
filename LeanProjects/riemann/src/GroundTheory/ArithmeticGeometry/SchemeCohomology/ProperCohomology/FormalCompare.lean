import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalTower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules) (q : ℕ)

lemma formalτ_mem_formalQ (n : ℕ) (y : Sheaf.H.{u} (modulesAb (idealPow I F (n + 2))) (q + 1))
    (hy : y ∈ formalQ I F q (n + 1)) :
    H.linearMap A (idealPowSucc I F (n + 1)) (q + 1) y ∈ formalQ I F q n := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨formalτE I F q n x, formalδ_naturality I F q n x⟩

def formalτQ (n : ℕ) : formalQ I F q (n + 1) →ₗ[A] formalQ I F q n :=
  (H.linearMap A (idealPowSucc I F (n + 1)) (q + 1)).restrict (formalτ_mem_formalQ I F q n)

abbrev formalτP : ∀ n, (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q (n + 1)) →ₗ[A]
    (Sheaf.H.{u} (modulesAb F) q ⧸ formalK I F q n) :=
  quotTower (formalK I F q) (formalK_antitone I F q)

lemma formalι_comm (n : ℕ) :
    (formalτE I F q n).comp (formalι I F q (n + 1)) = (formalι I F q n).comp (formalτP I F q n) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Sheaf.H.map.{u} (modulesAbMap (quotPowMap I F n)) q
      (Sheaf.H.map.{u} (modulesAbMap (quotPowπ I F (n + 1))) q h) =
    Sheaf.H.map.{u} (modulesAbMap (quotPowπ I F n)) q h
  rw [← Sheaf.H.map_comp_apply, ← modulesAbMap_comp, quotPowπ_map]

lemma formalπ_comm (n : ℕ) :
    (formalτQ I F q n).comp (formalπ I F q (n + 1)) = (formalπ I F q n).comp (formalτE I F q n) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  exact (formalδ_naturality I F q n x).symm

lemma surjective_formalτP (n : ℕ) : Function.Surjective (formalτP I F q n) := by
  intro x
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk h, rfl⟩

variable {I F q}

theorem mem_range_formalβ_of_mem_towerLimit {c : ℕ}
    (hQ : ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0)
    {x : ∀ n, Sheaf.H.{u} (modulesAb (quotPow I F n)) q} (hx : x ∈ towerLimit (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q) (formalτE I F q))
    (n : ℕ) : x n ∈ LinearMap.range (formalβ I F q n) := by
  obtain ⟨p, hp⟩ := (bijective_towerLimitMap (formalτP I F q) (formalτE I F q) (formalτQ I F q)
    (formalι I F q) (formalπ I F q) (formalι_comm I F q) (formalπ_comm I F q)
    (formalι_injective I F q) (range_formalι I F q) hQ).2 ⟨x, hx⟩
  obtain ⟨h, hh⟩ := Submodule.Quotient.mk_surjective _ (p.1 n)
  refine ⟨h, ?_⟩
  have := congrArg (fun y => y.1 n) hp
  simp only at this
  rw [← this]
  change formalβ I F q n h = formalι I F q n (p.1 n)
  rw [← hh]
  rfl

theorem range_towerComp_formalτE_eq {c : ℕ} (hQ : ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0)
    (n k : ℕ) (hk : c ≤ k) :
    LinearMap.range (towerComp (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q) (formalτE I F q) n k) = LinearMap.range (formalβ I F q n) := by
  rw [range_towerComp_eq_of_exact (formalτP I F q) (formalτE I F q) (formalτQ I F q)
    (formalι I F q) (formalπ I F q) (formalι_comm I F q) (formalπ_comm I F q)
    (range_formalι I F q) (surjective_formalτP I F q) hQ n k hk, formalι, Submodule.range_liftQ]

end

end GroundTheory.Arith.SchemeCoh
