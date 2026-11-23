import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.CommVac

theorem commVac : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ}
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')) (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → CfgA B G G₁ H H' →
    ∀ (v : Pl F) (γ : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)), At (evFin F v) γ → γ ∈ iso0 (F := F) (b + 2) H' →
      γ ∈ latAtV G.V G.W v → ∀ u : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ)
          (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) (G.M.vac v)) =
        GlobalTheory.LatVac.psiAt B.ψ v (evFin F v (symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) γ u)) •
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' hX hC v γ hγat hγiso hγlat u
  obtain ⟨hSB, -, θ, -, hact⟩ := hX.geo.hM.vac v
  obtain ⟨y, rfl⟩ := hγiso
  have hg : ∑ j, ∑ l, incV F H'.x j * incM F G.W.J j l * cA σ (incV F H'.x l) = 0 := by
    have e : ∑ j, ∑ l, incV F H'.x j * incM F G.W.J j l * cA σ (incV F H'.x l) =
        inclR (F := F) (AF F) (form σ G.W.J H'.x H'.x) := by
      have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun _ => rfl
      simp only [form, dotProduct, Matrix.mulVec, incV, incM, Matrix.map_apply, hc, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e, hC.hH'.xx, map_zero]
  have h0 : hTens (cA σ) (incM F G.V.J) (incM F G.W.J) (Matrix.vecMulVec y (incV F H'.x))
      (Matrix.vecMulVec y (incV F H'.x)) = 0 := by
    unfold hTens
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ∀ j, ∑ l, Matrix.vecMulVec y (incV F H'.x) i j * incM F G.V.J i k * incM F G.W.J j l *
        cA σ (Matrix.vecMulVec y (incV F H'.x) k l) =
        (y i * incM F G.V.J i k * cA σ (y k)) * ∑ l, incV F H'.x j * incM F G.W.J j l * cA σ (incV F H'.x l) := by
      intro j
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Matrix.vecMulVec_apply, map_mul]
      ring
    simp only [this, ← Finset.mul_sum, hg, mul_zero]
  have hfix : schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (Matrix.vecMulVec y (incV F H'.x))) (G.M.vac v)
      = G.M.vac v := by
    apply GlobalTheory.TensUniq.eq_of_tens_eq v (G.M.vac v) _ _ hSB
    intro r hr
    rw [← GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v _ hγat _ r hr, hact _ hγlat r hr]
    simp only [GlobalTheory.WeilM.symp, h0, mul_zero, map_zero, AddChar.map_zero_eq_one, one_smul]
  rw [GlobalTheory.VacLoc.schr_comm, hfix]
  congr 2
  rw [G.M.co.form]
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, dotProduct, map_sub, map_sum, map_mul]

end GlobalTheory.CommVac
