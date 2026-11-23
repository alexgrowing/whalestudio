import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOne
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership

namespace GlobalTheory.Core.SignFrame

theorem isInU_inFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F)
    (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E)), IsSignFrame σ J ε b →
    ∀ g : GArch σ J w, IsInU ε (inFrame σ J τ b g) := by
  intro F E _ _ _ _ _ σ hc n J w τ ε b hb g
  set ρ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ
  set φ := infEmb τ
  set G : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E) := (matHom w.Completion σ J g).1
  have hG : cT ρ G * JR w.Completion J * G = JR w.Completion J := g.2
  have hφ : ∀ x, φ (ρ x) = star (φ x) := fun x => (infEmb_sigR hc τ x).symm
  have hinv' : b.1 * (b⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set D : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E) := Matrix.diagonal fun i => if ε i then 1 else -1
  have hD : cT ρ b.1 * JR w.Completion J * b.1 = D := hb
  have hS : D.map φ = signMat ε := by
    simp only [D, signMat, Matrix.diagonal_map (map_zero φ)]
    congr 1; funext i; split_ifs <;> simp

  have key : cT ρ ((b⁻¹).1 * G * b.1) * D * ((b⁻¹).1 * G * b.1) = D := by
    have hcb : cT ρ (b⁻¹).1 * cT ρ b.1 = 1 := by rw [← cT_mul, hinv', cT_one]
    rw [← hD]
    calc cT ρ ((b⁻¹).1 * G * b.1) * (cT ρ b.1 * JR w.Completion J * b.1) * ((b⁻¹).1 * G * b.1)
        = cT ρ b.1 * cT ρ G * (cT ρ (b⁻¹).1 * cT ρ b.1) * JR w.Completion J * (b.1 * (b⁻¹).1) * G * b.1 := by
          simp only [cT_mul, Matrix.mul_assoc]
      _ = cT ρ b.1 * (cT ρ G * JR w.Completion J * G) * b.1 := by
          rw [hcb, hinv']; simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      _ = cT ρ b.1 * JR w.Completion J * b.1 := by rw [hG]
  have hval : inFrame σ J τ b g = ((b⁻¹).1 * G * b.1).map φ := rfl
  unfold IsInU
  rw [hval, ← hS, ← GlobalTheory.Core.Rk.IwArch.map_cT ρ φ hφ, ← Matrix.map_mul, ← Matrix.map_mul, key]

end GlobalTheory.Core.SignFrame
