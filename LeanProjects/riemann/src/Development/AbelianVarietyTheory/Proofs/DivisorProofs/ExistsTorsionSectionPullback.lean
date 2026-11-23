import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

theorem GlobalTheory.grpPullback_lift_torsion : ∀ (S S' : Scheme.{0}) (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (T : Over S') (w : Over.mk (T.hom ≫ f) ⟶ G),
      ∃ σ : T ⟶ G', σ.left ≫ φ = w.left ∧ ∀ k : ℕ, w ^ k = 1 → σ ^ k = 1 := by
  intro S S' G' _ G _ f φ h T w
  have uniq : ∀ a b : T ⟶ G', a.left ≫ φ = b.left ≫ φ → a = b := by
    intro a b e
    ext
    exact h.1.hom_ext e (by rw [Over.w a, Over.w b])
  let push : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w x])
  have push_left : ∀ x : T ⟶ G', (push x).left = x.left ≫ φ := fun x => rfl
  have hmul : ∀ x y : T ⟶ G', push (x * y) = push x * push y := by
    intro x y
    ext
    exact (h.2 T x y (push x) (push y) rfl rfl).symm
  have hone : push 1 = 1 := by
    have e : push 1 * push 1 = push 1 := by rw [← hmul, _root_.mul_one]
    simpa using e
  have hpow : ∀ (x : T ⟶ G') (k : ℕ), push (x ^ k) = push x ^ k := by
    intro x k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, pow_succ, hmul, ih]
  let σ : T ⟶ G' := Over.homMk (h.1.lift w.left T.hom (by simpa using Over.w w)) (h.1.lift_snd _ _ _)
  have hσ : σ.left ≫ φ = w.left := h.1.lift_fst _ _ _
  have hpσ : push σ = w := by ext; exact hσ
  refine ⟨σ, hσ, fun k hk => uniq _ _ ?_⟩
  rw [← push_left, ← push_left, hpow, hpσ, hk, hone]
