import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LatticeBlocks
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyCl

theorem value_of_normalAt {κ : Rule} (hH : Homog (fun _ => 1) κ) (hT : ThetaOne κ) (x : KeyIn ℂ)
    {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ} (hab : KeyPow.charHalf x.P.g a b)
    (hc : c ≠ 0) (hM : M.det ≠ 0) (h : KeyPow.NormalAt x τ M a b c) : (κ ℂ x : ℂ) = M.det ^ 4 / c ^ 8 := by
  have key := KeyPow.value_at_normalForm (fun _ => 1) 0 (κ ℂ) x.P.g a b (Nat.zero_le _)
    (fun P hg rig hr th hth v hv th' hth' v' hv' a M _ h₁ h₂ =>
      hH ℂ P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂)
    (fun z hz σ hN => by
      obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (KeyPow.normalAt_one_iff z σ _ _).1 hN
      exact hT z u σ _ _ h₁ h₂ (fun i => hab.1 _) (fun i => hab.2 _) h₃ h₄ h₅ h₆)
    x rfl τ M c hc hM h
  simpa only [_root_.pow_one] using key

theorem value_pow_complex : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ →
    ∀ (x y : KeyIn ℂ) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ ℂ y = κ ℂ x ^ j := by
  intro κ hH hT x y j hp
  obtain ⟨⟨τ, M, a, b, c, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x
  have hre : ∀ f : Fin x.P.g → ℂ, (∀ i, f i = 0 ∨ f i = 1 / 2) → (fun k => ((f k).re : ℂ)) = f := by
    intro f hf
    funext k
    rcases hf k with h | h <;> rw [h] <;> norm_num
  have ha := hre a hab.1
  have hb := hre b hab.2
  obtain ⟨e, τ', M', hdet, hN'⟩ := KeyPow.normalAt_pow x y j τ M (fun k => (a k).re) (fun k => (b k).re) c hp
    (by rw [ha, hb]; exact hN)
  have hx := value_of_normalAt hH hT x hab hc hM hN
  have hy := value_of_normalAt hH hT y
    ⟨fun p => by rw [congrFun ha (e.symm p).2]; exact hab.1 _,
      fun p => by rw [congrFun hb (e.symm p).2]; exact hab.2 _⟩
    (pow_ne_zero j hc) (by rw [hdet]; exact pow_ne_zero j hM) hN'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hy, hx, hdet, div_pow, ← _root_.pow_mul, ← _root_.pow_mul, ← _root_.pow_mul,
    ← _root_.pow_mul, mul_comm j 4, mul_comm j 8]

end GlobalTheory.KeyCl
