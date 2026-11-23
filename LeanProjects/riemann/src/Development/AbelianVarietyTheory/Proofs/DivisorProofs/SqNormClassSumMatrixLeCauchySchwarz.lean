import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAtInvNatSmulSelf

noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mat_opOf_apply {F F' : GFam K} (M : GFam.Mat F F') (hF : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) (b' : F'.β)
    (d' : F'.D b') :
    ((M.opOf hF s φ b' : (F'.mem b').EqFun) : F'.D b' → F'.V) d' =
      ∑ b, (M b b').appOf (hF b) (s b) (φ b : (F.mem b).D → F.V) d' := by
  simp only [GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem step_le (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t h h' : ℝ)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hh' : 0 ≤ h') (hp : ∀ b, PosAt ((Q.F i).mem b) v) (hp' : ∀ b, PosAt ((Q.F (i + 1)).mem b) v)
    (hc : ∀ b, (Nat.card ((Q.F i).mem b).Cl : ℝ) ≤ h) (hc' : ∀ b, (Nat.card ((Q.F (i + 1)).mem b).Cl : ℝ) ≤ h')
    (hk : ∀ b b' d d', OpLe ((Q.F i).mem b) ((Q.F (i + 1)).mem b') v ((Q.kk i b b').k d d') t) (φ : (Q.F i).Forms) :
    (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (Fintype.card (Q.F (i + 1)).β : ℝ) * h * h' * t *
        (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
  have hN : (famIpAt (Q.F i) (Q.hF i) v φ φ).re =
      ∑ b, (((Q.F i).mem b).ipAt (Q.hF i b) v (φ b : ((Q.F i).mem b).D → (Q.F i).V) (φ b : ((Q.F i).mem b).D → (Q.F i).V)).re := by
    unfold famIpAt
    rw [Complex.re_sum]
  have hN0 : 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
    rw [hN]
    exact Finset.sum_nonneg fun b _ => ipAt_self_nonneg _ v _ (hp b) _
  have hB : ∀ b' d', (((Q.F (i + 1)).mem b').pairAt v ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')
      ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by
    intro b' d'
    have e := mat_opOf_apply (Q.kk i) (Q.hF i) (fun b => ((Q.F i).mem b).outSec) φ b' d'
    change ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d') = _ at e
    rw [e]
    refine (pairAt_sum_le ((Q.F (i + 1)).mem b') v (hp' b') _ _).trans ?_
    rw [Finset.card_univ, hN, Finset.mul_sum _ _ t, Finset.mul_sum _ _ h]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity)
    refine (appOf_le v (Q.kk i b b') (Q.hF i b) (hp b) (hp' b') t ht _ d' fun d => hk b b' d d').trans ?_
    exact mul_le_mul_of_nonneg_right (hc b) (mul_nonneg ht (ipAt_self_nonneg _ v _ (hp b) _))
  have hB0 : 0 ≤ (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by positivity
  calc (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re
      ≤ ∑ _b' : (Q.F (i + 1)).β, h' * ((Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re))) := by
        rw [famIpAt, Complex.re_sum]
        refine Finset.sum_le_sum fun b' _ => ?_
        exact (ipAt_self_le _ v _ (hp' b') _ _ (hB b')).trans (mul_le_mul_of_nonneg_right (hc' b') hB0)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end GlobalTheory.ColNorms.SumBound
