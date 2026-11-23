import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section
namespace GlobalTheory.FrameScale

theorem vecMul_entry {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (x : k) (q r : Fin c) (m : ι)
    (hb : ∀ i, b i m = x * φ (a i r)) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = x * φ ((Formalism.UG.cT σ a * g * a) q r) := by
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, hb, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameScale
end

theorem GlobalTheory.FrameScale.clauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m)
  (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
  (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : k) (e : ℕ), ϖ ≠ 0 → Function.Injective j →
  (∀ r i, β.b i (j r) = ϖ ^ (e * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) →
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) →
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1)) •
      (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (j ⟨q.1, by omega⟩) 1) ∧
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (2 * σ + 1 - q.1)) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) *
      (if q.1 = σ then -1 else 1))⁻¹ • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
      Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1) := by
  intro D _ T L _ _ sc G W _ _ F hF σ h' k _ _ _ _ p β j ϖ e hϖ hj hb hout
  have hne : (-D.host.xi0) ≠ 0 := neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hc : p.pr (incA D (-D.host.xi0)) ≠ 0 := ((hne.isUnit.map (incA D)).map p.pr).ne_zero
  have hc' : p.pr (incA D (star (-D.host.xi0))) ≠ 0 :=
    (((star_ne_zero.2 hne).isUnit.map (incA D)).map p.pr).ne_zero
  have hcol : ∀ (q : Fin (σ + 1)) i, xFB F σ h' i q = incA D ((-D.host.xi0) ^ (q.1 + 1)) * incA D ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩) := by
    intro q i
    have := congrFun (GlobalTheory.CharXFB.xFB_col F hF σ h' q) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    rfl
  have key : ∀ m, β.b' *ᵥ (fun i => β.b i m) = Pi.single m 1 := by
    intro m
    have : (fun i => β.b i m) = β.b *ᵥ Pi.single m 1 := by
      funext i; simp [Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have hv : (fun i => p.pr (xFB F σ h' i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * (ϖ ^ (e * (q.1 + 1)))⁻¹) • fun i => β.b i (j ⟨q.1, by omega⟩) := by
      funext i
      rw [hcol]
      simp only [map_mul, map_pow, Pi.smul_apply, smul_eq_mul, hb]
      field_simp
    rw [hv, Matrix.mulVec_smul, key, smul_smul]
    convert one_smul k _
    rw [inv_pow]
    field_simp
  · have hv : (fun i => p.pr (cA D (xFB F σ h' i q))) = p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) •
        fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩))) := by
      funext i
      rw [hcol]
      simp only [map_mul, GlobalTheory.DualPairCheck.cA_incA, star_pow, map_pow, Pi.smul_apply, smul_eq_mul]
    have hsm : ∀ (x : k) (u : Fin (G.V (.grid (2 * σ + 2) 0)).rank → k)
        (M : Matrix (Fin (G.V (.grid (2 * σ + 2) 0)).rank) (Fin (G.V (.grid (2 * σ + 2) 0)).rank) k),
        (x • u) ᵥ* M = x • (u ᵥ* M) := by
      intro x u M
      funext m
      simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hg := (G.colDec (2 * σ + 2) (by omega) h').gram
    have hw : ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩)))) ᵥ*
        (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
        (ϖ ^ (e * (2 * σ + 1 - q.1)) * (if q.1 = σ then -1 else 1)) • Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1 := by
      funext m
      by_cases hm : m ∈ Set.range j
      · obtain ⟨r, rfl⟩ := hm
        refine (GlobalTheory.FrameScale.vecMul_entry (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * σ + 2) (by omega) h').a _ β.b _ ⟨q.1, by omega⟩ r (j r) (hb r)).trans ?_
        rw [hg]
        simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, RingHom.coe_comp, Function.comp_apply]
        by_cases hr : r = ⟨2 * σ - q.1, by omega⟩
        · subst hr
          have e1 : 2 * σ - q.1 + 1 = 2 * σ + 1 - q.1 := by omega
          rw [Pi.single_eq_same, if_pos (by simp only; omega), e1]
          by_cases hq : q.1 = σ
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hq]
            simp
          · rw [if_neg (fun h => hq (by have := congrArg Fin.val h; simp only at this; omega)), if_neg hq]
            simp
        · rw [Pi.single_eq_of_ne (hj.ne hr), if_neg (fun h => hr (Fin.ext (by simp only; omega)))]
          simp
      · rw [hout m hm ⟨q.1, by omega⟩, Pi.smul_apply, Pi.single_eq_of_ne (fun h => hm ⟨_, h.symm⟩), smul_zero]
    have hs : (if q.1 = σ then (-1 : k) else 1) ≠ 0 := by split_ifs <;> norm_num
    rw [hv, hsm, hw, smul_smul, smul_smul]
    refine (congrArg (· • Pi.single (j ⟨2 * σ - q.1, by omega⟩) (1 : k)) ?_).trans (one_smul k _)
    field_simp
