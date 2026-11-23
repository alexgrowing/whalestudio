import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaGL

theorem kerGL_mul_right_KGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g k : GL (Fin r) (w.adicCompletion E), k ∈ KGL w r → φ (g * k) = φ g := by
  intro E _ _ w r N z φ hφ g k hk
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
  have hm := mem_Ov_of_isUnifV hϖ
  obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ hm hϖ g
  obtain ⟨t, ht⟩ : ∃ t : GL (Fin r) (w.adicCompletion E), t = k₁⁻¹ * g * k₂⁻¹ := ⟨_, rfl⟩
  have hg : g = k₁ * t * k₂ := by rw [ht]; group
  have htv : t.1 = Matrix.diagonal fun i => ϖ ^ a i := by
    calc t.1 = ((k₁⁻¹ : GL (Fin r) (w.adicCompletion E)).1 * k₁.1) * Formalism.UG.diagPow E w ϖ a *
          (k₂.1 * (k₂⁻¹ : GL (Fin r) (w.adicCompletion E)).1) := by
          rw [ht, Units.val_mul, Units.val_mul, e]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]; rfl
  rw [hg, mul_assoc (k₁ * t) k₂ k, hφ ϖ hϖ a t htv k₁ hk₁ (k₂ * k) (mul_mem hk₂ hk), hφ ϖ hϖ a t htv k₁ hk₁ k₂ hk₂]

end GlobalTheory.ZetaGL
