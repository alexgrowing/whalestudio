import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.CombMul

theorem pt_sum_ofFn {S : Scheme.{0}} {G : Over S} [GrpObj G] {F : Type} [Field F] {x : Sp F ⟶ S} {V : Type}
    [AddCommGroup V] [Module F V] (M : LieModel G x V) : ∀ {n : ℕ} (u : Fin n → V),
    M.pt (∑ i, u i) = (List.ofFn fun i => M.pt (u i)).prod
  | 0, u => by simp [M.pt_zero]
  | n + 1, u => by
    rw [Fin.sum_univ_succ, M.add, pt_sum_ofFn M (fun i => u i.succ), List.ofFn_succ, List.prod_cons]

theorem isComb_pt_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] {F : Type} [Field F] {x : Sp F ⟶ S} {V : Type}
    [AddCommGroup V] [Module F V] (M : LieModel G x V) {n : ℕ} (c : Fin n → F) (e : Fin n → V)
    (w : epsAt x ⟶ G) : IsComb c (fun i => M.pt (e i)) w ↔ w = M.pt (∑ i, c i • e i) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u = fun i => M.pt (c i • e i) :=
      funext fun i => Over.OverMorphism.ext ((hu i).trans (M.smul _ _).symm)
    rw [pt_sum_ofFn, h]
  · rintro rfl
    exact ⟨fun i => M.pt (c i • e i), fun i => M.smul _ _, pt_sum_ofFn M _⟩

theorem isComb_mul : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (m n k : ℕ) (v : Fin n → (epsAt x ⟶ G)) (u : Fin m → (epsAt x ⟶ G)) (w : Fin k → (epsAt x ⟶ G)) (A : Matrix (Fin k) (Fin m) F) (C : Matrix (Fin m) (Fin n) F), (∀ i, IsTanAt G x (v i)) → (∀ i, IsComb (C i) v (u i)) → (∀ i, IsComb (A i) u (w i)) → ∀ i, IsComb ((A * C) i) v (w i) := by
  intro S G _ _ F _ x m n k v u w A C hv hu hw i
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨e, rfl⟩ : ∃ e : Fin n → E, v = fun i => M.pt (e i) := by
    choose e he using fun i => M.onto (v i) (hv i)
    exact ⟨e, funext fun i => (he i).symm⟩
  obtain rfl : u = fun j => M.pt (∑ l, C j l • e l) :=
    funext fun j => (isComb_pt_iff M (C j) e (u j)).1 (hu j)
  have hwi := (isComb_pt_iff M (A i) _ (w i)).1 (hw i)
  rw [isComb_pt_iff, hwi]
  congr 1
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.Ar.CombMul
