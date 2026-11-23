import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.GlobalGen
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.PSpaceFinite
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ModulesAbExact
import GroundTheory.ArithmeticGeometry.SchemeCohomology.SheafH
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.SerrePAux
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {n : ℕ}
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (projectiveSpace A n).toTopCat) AddCommGrpCat.{u})]

attribute [local instance] algebraOfOver

theorem serre_step (p : ℕ)
    (ih : ∀ R : (projectiveSpace A n).Modules, IsCoherent R →
      Module.Finite A (Sheaf.H.{w'} (modulesAb R) (p + 1)) ∧
      ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → Subsingleton (Sheaf.H.{w'} (modulesAb (twist R q)) (p + 1)))
    (G : (projectiveSpace A n).Modules) (hG : IsCoherent G) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb G) p) ∧
      (0 < p → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        Subsingleton (Sheaf.H.{w'} (modulesAb (twist G q)) p)) := by
  have := hG.1
  obtain ⟨q₀, hq₀⟩ := exists_generatingSections_twist G hG
  obtain ⟨σ, hσ⟩ := hq₀ q₀ le_rfl
  have : Finite σ.I := hσ.finite
  let ψ : freeP A n σ.I ⟶ twist G q₀ := σ.π
  have : Epi ψ := σ.epi
  have hK : IsCoherent (kernel ψ) := isCoherent_kernel ψ (isCoherent_freeP σ.I)
  let S : ShortComplex (projectiveSpace A n).Modules :=
    ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)
  have hS : S.ShortExact := ⟨S.exact_of_f_is_kernel (kernelIsKernel ψ)⟩
  have hSk : ∀ k : ℤ, (S.map (twistEquiv (A := A) (n := n) k).functor).ShortExact := fun k =>
    shortExact_tensorEquiv _ hS
  have eK : ∀ k : ℤ, (S.map (twistEquiv (A := A) (n := n) k).functor).X₁ ≅ twist (kernel ψ) k :=
    fun k => eqToIso (twistEquiv_obj k _)
  have eG : ∀ k : ℤ, (S.map (twistEquiv (A := A) (n := n) k).functor).X₃ ≅ twist G (q₀ + k) :=
    fun k => eqToIso (twistEquiv_obj k _) ≪≫ twistTwistIso G q₀ k
  constructor
  · have h1 : Module.Finite A (Sheaf.H.{w'}
        (modulesAb (S.map (twistEquiv (A := A) (n := n) (-q₀)).functor).X₁) (p + 1)) :=
      have := (ih _ (isCoherent_twist hK (-q₀))).1
      Module.Finite.equiv (H.linearEquivOfIso A (eK (-q₀)) (p + 1)).symm
    have h2 : Module.Finite A (Sheaf.H.{w'}
        (modulesAb (S.map (twistEquiv (A := A) (n := n) (-q₀)).functor).X₂) p) :=
      finite_H_twist_free σ.I (-q₀) p
    have h3 := finite_H_X₃ A (hSk (-q₀)) p
    have e : (S.map (twistEquiv (A := A) (n := n) (-q₀)).functor).X₃ ≅ G :=
      eG (-q₀) ≪≫ eqToIso (congrArg (twist G) (add_neg_cancel (q₀ : ℤ))) ≪≫ twistZero G
    exact Module.Finite.equiv (H.linearEquivOfIso A e p)
  · intro hp
    obtain ⟨q₁, hq₁⟩ := (ih (kernel ψ) hK).2
    refine ⟨q₀ + q₁, fun q hq => ?_⟩
    have h1 : Subsingleton (Sheaf.H.{w'}
        (modulesAb (S.map (twistEquiv (A := A) (n := n) ((q - q₀ : ℕ) : ℤ)).functor).X₁) (p + 1)) :=
      have := hq₁ (q - q₀) (by omega)
      (H.linearEquivOfIso A (eK ((q - q₀ : ℕ) : ℤ)) (p + 1)).toEquiv.subsingleton
    have h2 : Subsingleton (Sheaf.H.{w'}
        (modulesAb (S.map (twistEquiv (A := A) (n := n) ((q - q₀ : ℕ) : ℤ)).functor).X₂) p) :=
      subsingleton_H_twist_free σ.I (Int.natCast_nonneg _) hp
    have h3 := subsingleton_H_X₃ (hSk ((q - q₀ : ℕ) : ℤ)) p
    have e : (S.map (twistEquiv (A := A) (n := n) ((q - q₀ : ℕ) : ℤ)).functor).X₃ ≅ twist G q :=
      eG _ ≪≫ eqToIso (congrArg (twist G) (by omega))
    exact (H.linearEquivOfIso A e p).symm.toEquiv.subsingleton

theorem serre_all (d : ℕ) : ∀ p : ℕ, n < p + d →
    ∀ G : (projectiveSpace A n).Modules, IsCoherent G →
      Module.Finite A (Sheaf.H.{w'} (modulesAb G) p) ∧
      (0 < p → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        Subsingleton (Sheaf.H.{w'} (modulesAb (twist G q)) p)) := by
  induction d with
  | zero =>
    intro p hp G hG
    have := hG.1
    have : Subsingleton (Sheaf.H.{w'} (modulesAb G) p) := subsingleton_H_of_lt G (by omega)
    exact ⟨Module.Finite.of_finite, fun _ =>
      ⟨0, fun q _ => subsingleton_H_of_lt (twist G q) (by omega)⟩⟩
  | succ d ih =>
    intro p hp G hG
    exact serre_step p (fun R hR => ⟨(ih (p + 1) (by omega) R hR).1,
      (ih (p + 1) (by omega) R hR).2 (Nat.succ_pos p)⟩) G hG

theorem finite_H (G : (projectiveSpace A n).Modules) (hG : IsCoherent G) (p : ℕ) :
    Module.Finite A (Sheaf.H.{w'} (modulesAb G) p) :=
  (serre_all (n + 1) p (by omega) G hG).1

theorem exists_subsingleton_H_twist (G : (projectiveSpace A n).Modules) (hG : IsCoherent G) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ p : ℕ, 0 < p →
      Subsingleton (Sheaf.H.{w'} (modulesAb (twist G q)) p) := by
  have h : ∀ p : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → 0 < p →
      Subsingleton (Sheaf.H.{w'} (modulesAb (twist G q)) p) := fun p => by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · exact ⟨0, fun _ _ h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨q₀, hq₀⟩ := (serre_all (n + 1) p (by omega) G hG).2 hp
      exact ⟨q₀, fun q hq _ => hq₀ q hq⟩
  choose f hf using h
  refine ⟨∑ p ∈ Finset.range (n + 1), f p, fun q hq p hp => ?_⟩
  by_cases hpn : p ≤ n
  · exact hf p q (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))) hq) hp
  · have := hG.1
    exact subsingleton_H_of_lt (twist G q) (by omega)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
