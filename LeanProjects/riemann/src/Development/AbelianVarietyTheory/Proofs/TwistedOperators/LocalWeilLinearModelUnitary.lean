import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalUnramifiedVector
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.UnitWShapeSplit

open GlobalTheory.UnitWShape

theorem shape_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → (∀ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ∀ Y, ι φ₁ Y = c * ι φ (Y * (((mat h).map (piW t))⁻¹)ᵀ)) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v t ι hι h hh
  obtain ⟨S, hSB, huniq, hlin, hcomm⟩ := exists_localOp hP F E σ B a a' G X om om' hTr v h hh
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := heisW B G X om om' hTr v t h S hSB hcomm
  obtain ⟨hT0, hM0, hST, hSM⟩ := hA ι hι
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  set ht := (mat h).map (piW t) with hht
  have hdet : IsUnit ht.det := by
    have h1 : IsUnit (mat h).det := (Units.isUnit h.1).map Matrix.detMonoidHom
    have h2 := h1.map (piW t)
    rw [RingHom.map_det] at h2
    exact h2
  have hsb := fun (w : (Fin a × Fin (a + a') → Fv F v) × (Fin a × Fin (a + a') → Fv F v))
    (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) (hφ : φ ∈ SB _) => GlobalTheory.SchrSB.schr_mem_SB B.ψ hTr.base.std.1 v w φ hφ
  have hL2 : ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ y ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ c : ℂ,
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (c • x + y)) (Y * htᵀ)) = c • (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S x) (Y * htᵀ)) + fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S y) (Y * htᵀ) := by
    intro x hx y hy c
    funext Y
    simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have hT2 : ∀ C, ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x) = (fun Y => ι x (Y + C)) ∧
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C) x)) (Y * htᵀ)) = fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S x) ((Y + C) * htᵀ) := by
    intro C x hx
    refine ⟨hsb _ x hx, hT0 C x hx, ?_⟩
    funext Y
    simp only [hST C x hx, Matrix.add_mul]
  have hM2 : ∀ l, ∀ x ∈ SB (Fin a × Fin (a + a') → Fv F v),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x ∈ SB (Fin a × Fin (a + a') → Fv F v) ∧
      ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x) = (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι x Y) ∧
      (fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => ι (S (schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l) x)) (Y * htᵀ)) =
        fun Y : Matrix (Fin a) (Fin (a + a')) (Fv F v) => GlobalTheory.LatVac.psiAt B.ψ v (l Y) * ι (S x) (Y * htᵀ) := by
    intro l x hx
    refine ⟨hsb _ x hx, hM0 l x hx, ?_⟩
    funext Y
    simp only [hSM l x hx, Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one,
      Matrix.mul_one]
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι
    (fun x Y => ι (S x) (Y * htᵀ)) hbij hL2
    (fun C => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wT C)) (fun l => schr (GlobalTheory.LatVac.psiAt B.ψ v) (wM l)) hT2 hM2
  refine ⟨c, fun φ hφ φ₁ _ hAct Y => ?_⟩
  rw [huniq φ hφ φ₁ hAct]
  have e := congrFun (hc φ hφ) (Y * (ht⁻¹)ᵀ)
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rwa [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one,
    Matrix.mul_one] at e

end GlobalTheory.UnitWShapeSplit
