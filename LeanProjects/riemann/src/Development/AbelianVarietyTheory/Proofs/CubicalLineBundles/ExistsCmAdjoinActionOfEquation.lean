import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

private theorem okAct_group_identity {A : Type*} [CommGroup A] (i w : A) (k m n m' n' : ℤ) :
    i ^ (m * m' - n * n' * k) * w ^ (m * n' + n * m' + n * n') =
      (i ^ m * w ^ n) ^ m' * (w ^ m * (w * i ^ (-k)) ^ n) ^ n' := by
  have h1 : m * m' - n * n' * k = m * m' + (-k) * n * n' := by ring
  rw [h1]
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

theorem exists_okAct_of_equation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (W : G ⟶ G), IsMonHom W → (W ≫ W) * (𝟙 G) ^ ((1 + H.d) / 4) = W → ∃ a : OAct (OK H) G, a.act (wK H) = W ∧ ∀ m n : ℤ, a.act ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := by
  intro E _ _ _ H S G _ _ W hW hEq
  obtain ⟨-, hco, -, hsq, -⟩ := OK_isDedekindDomain_and_projective E H
  set k : ℕ := (1 + H.d) / 4 with hk
  choose c hc hcu using hco
  have hcoord : ∀ m n : ℤ, c ((m : OK H) + (n : OK H) * wK H) = (m, n) := fun m n =>
    (hcu _ (m, n) rfl).symm
  have hWW : W ≫ W = W * (𝟙 G) ^ (-(k : ℤ)) := by
    rw [zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    exact hEq
  let F : OK H → (G ⟶ G) := fun a => (𝟙 G) ^ (c a).1 * W ^ (c a).2
  have hF : ∀ m n : ℤ, F ((m : OK H) + (n : OK H) * wK H) = (𝟙 G) ^ m * W ^ n := fun m n => by
    simp only [F, hcoord]
  have hex : ∀ a : OK H, ∃ m n : ℤ, a = (m : OK H) + (n : OK H) * wK H := fun a => ⟨_, _, hc a⟩
  refine ⟨⟨F, fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩, ?_, hF⟩
  · have h1 := Serre.isMonHom_zpow (𝟙 G) (c a).1
    have h2 := Serre.isMonHom_zpow W (c a).2
    exact Serre.isMonHom_mul _ _
  · have := hF 1 0
    simpa using this
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : OK H) + (n : OK H) * wK H) * ((m' : OK H) + (n' : OK H) * wK H) =
        ((m * m' - n * n' * (k : ℤ) : ℤ) : OK H) + ((m * n' + n * m' + n * n' : ℤ) : OK H) * wK H := by
      push_cast
      linear_combination ((n : OK H) * (n' : OK H)) * hsq
    rw [e, hF, hF, hF]
    simp only [MonObj.comp_mul, GrpObj.comp_zpow, MonObj.mul_comp, GrpObj.zpow_comp, Category.comp_id,
      Category.id_comp, hWW]
    exact okAct_group_identity _ _ _ _ _ _ _
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : OK H) + (n : OK H) * wK H) + ((m' : OK H) + (n' : OK H) * wK H) =
        ((m + m' : ℤ) : OK H) + ((n + n' : ℤ) : OK H) * wK H := by
      push_cast
      ring
    rw [e, hF, hF, hF, zpow_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _
  · have := hF 0 1
    simpa using this

end GlobalTheory.CM
