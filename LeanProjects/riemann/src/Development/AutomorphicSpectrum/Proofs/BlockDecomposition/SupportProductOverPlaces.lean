import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.ProdSupp

variable {F : Type} [Field F] [NumberField F] {d β : F}

def place (u : Pl F) (x : Q d β (Kp u)) : Q d β (AF F) :=
  ⟨inc u x.re, inc u x.imI, inc u x.imJ, inc u x.imK⟩

theorem q_ext_places {x y : Q d β (AF F)} (h : ∀ u : Pl F, qmap (proj u) x = qmap (proj u) y) :
    x = y := by
  refine QuaternionAlgebra.ext (adele_ext fun u => ?_) (adele_ext fun u => ?_)
    (adele_ext fun u => ?_) (adele_ext fun u => ?_)
  · exact congrArg QuaternionAlgebra.re (h u)
  · exact congrArg QuaternionAlgebra.imI (h u)
  · exact congrArg QuaternionAlgebra.imJ (h u)
  · exact congrArg QuaternionAlgebra.imK (h u)

theorem qmap_star {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (f : R →ₐ[F] R') (x : Q d β R) : qmap f (star x) = star (qmap f x) := by
  ext <;> simp [qmap]

theorem qmap_place_same (u : Pl F) (x : Q d β (Kp u)) : qmap (proj u) (place u x) = x := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> exact proj_inc_same u _

theorem qmap_place_ne {u u' : Pl F} (h : u' ≠ u) (x : Q d β (Kp u)) :
    qmap (proj u') (place u x) = 0 := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> exact proj_inc_ne h _

def atPlace (u : Pl F) (y : Q d β (Kp u)) : Q d β (AF F) := 1 + place u (y - 1)

theorem qmap_atPlace_same (u : Pl F) (y : Q d β (Kp u)) : qmap (proj u) (atPlace u y) = y := by
  rw [atPlace, map_add, map_one, qmap_place_same]
  abel

theorem qmap_atPlace_ne {u u' : Pl F} (h : u' ≠ u) (y : Q d β (Kp u)) :
    qmap (proj u') (atPlace u y) = 1 := by
  rw [atPlace, map_add, map_one, qmap_place_ne h, add_zero]

theorem atPlace_mem_suppAt (u : Pl F) {y : Q d β (Kp u)} (hy : qn y = 1) :
    atPlace u y ∈ SuppAt d β {u} := by
  refine ⟨adele_ext fun u' => ?_, fun u' hu' => qmap_atPlace_ne hu' y⟩
  rw [← qn_qmap, map_one]
  by_cases h : u' = u
  · subst h
    rw [qmap_atPlace_same, hy]
  · rw [qmap_atPlace_ne h, qn_one]

theorem suppAt_empty_eq_one {g : Q d β (AF F)} (hg : g ∈ SuppAt d β (∅ : Set (Pl F))) : g = 1 :=
  q_ext_places fun u => by rw [hg.2 u (Set.notMem_empty u), map_one]

theorem exists_mul_of_mem_insert {u : Pl F} {T : Set (Pl F)} {g : Q d β (AF F)}
    (hg : g ∈ SuppAt d β (insert u T)) :
    ∃ g' ∈ SuppAt d β T, ∃ h ∈ SuppAt d β {u}, g = g' * h := by
  have hy : qn (qmap (proj u) g) = 1 := by rw [qn_qmap, hg.1, map_one]
  have hh := atPlace_mem_suppAt u hy
  set h := atPlace u (qmap (proj u) g) with hdef
  refine ⟨g * star h, ⟨?_, fun u' hu' => ?_⟩, h, hh, ?_⟩
  · rw [qn_mul, qn_star, hg.1, hh.1, one_mul]
  · rw [map_mul, qmap_star]
    by_cases e : u' = u
    · subst e
      rw [hdef, qmap_atPlace_same, mul_star_eq, hy, map_one]
    · rw [hdef, qmap_atPlace_ne e, hg.2 u' (by simp [e, hu']), star_one, one_mul]
  · rw [mul_assoc, star_mul_eq, hh.1, map_one, mul_one]

theorem suppAt_subset_of_places :
    ∀ {F : Type} [Field F] [NumberField F] (d β : F) (N : Set (Q d β (AF F))), (1 : Q d β (AF F)) ∈ N →
      (∀ x ∈ N, ∀ y ∈ N, x * y ∈ N) → (∀ u : Pl F, SuppAt d β {u} ⊆ N) →
      ∀ T : Finset (Pl F), SuppAt d β (T : Set (Pl F)) ⊆ N := by
  intro F _ _ d β N h1 hmul hu T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    rw [Finset.coe_empty] at hg
    rw [suppAt_empty_eq_one hg]
    exact h1
  | insert u T _ ih =>
    intro g hg
    rw [Finset.coe_insert] at hg
    obtain ⟨g', hg', h, hh, rfl⟩ := exists_mul_of_mem_insert hg
    exact hmul _ (ih hg') _ (hu u hh)

end GlobalTheory.CompanionTheory.PlaneSA.ProdSupp
