import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecMulEntry

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.FrameZero

theorem vecMul_row {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (q : Fin c) (m : ι) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = ((Formalism.UG.cT σ a * g).map φ * b) q m := by
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring
private theorem mulVec_col_eq_single_of_mul_eq_one {k m n : Type} [Field k] [Fintype m] [DecidableEq n] (b : Matrix m n k)
    (b' : Matrix n m k) (hb : b' * b = 1) (j : n) : (b' *ᵥ fun i => b i j) = Pi.single j 1 := by
  funext i
  show ∑ l, b' i l * b l j = _
  rw [← Matrix.mul_apply, hb, Matrix.one_apply, Pi.single_apply]
private theorem cA_incA_eq_incA_sig (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := rfl
end GlobalTheory.FrameZero

theorem GlobalTheory.FrameZero.xclauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∃ s t : Fin (σ + 1) → k, (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (κ ⟨q.1, by omega⟩) 1) ∧
    (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) := by
  unfold GlobalTheory.AscFin.OnStd All
  intro D _ T L μ0 _ sc G _ M _ F hF σ h v _ k _ _ _ _ p β ϖ κ _ _ _ hirr hinj hb hperp
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hϖ : (ϖ : k) ≠ 0 := fun h0 => hirr.ne_zero (Subtype.ext h0)
  have hx0 : p.pr (incA D (-D.host.xi0)) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero)
  have hx1 : p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr ((map_ne_zero _).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero))
  have hx : ∀ i (q : Fin (σ + 1)), xZero (F.dJ (σ + 1) h) i q = incA D ((-D.host.xi0) ^ (q.1 + 1) *
      (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩) := by
    intro i q
    show incA D ((F.dJ (σ + 1) h).e i q) = _
    rw [he]
    rfl
  refine ⟨fun q => (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) *
      ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹)⁻¹,
    fun q => (p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) *
      (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)))⁻¹, ?_, ?_⟩
  · intro q
    have hcol : (fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹) •
          fun i => β.b i (κ ⟨q.1, by omega⟩) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hb, hx, map_mul, map_mul, map_pow, map_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ)]
    dsimp only
    rw [hcol, Matrix.mulVec_smul, mulVec_col_eq_single_of_mul_eq_one _ _ β.b'b, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx0) (inv_ne_zero (pow_ne_zero _ hϖ))), one_smul]
  · intro q
    have hrow : (fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) =
        p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) •
          fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
            ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩)) := by
      funext i
      rw [hx, cA_incA_eq_incA_sig]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, RingHom.comp_apply]
    have key : ∀ r : Fin (2 * (σ + 1) + 1 - 1), ∑ j, p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram)
            ⟨q.1, by omega⟩ j)) * ((ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) *
          p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a j r))) =
        (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram *
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a) ⟨q.1, by omega⟩ r)) := by
      intro r
      rw [Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul]
      ring
    have hN : ((fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
          ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩))) ᵥ*
          ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) =
        (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)) •
          Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1 := by
      funext m
      refine (GlobalTheory.FrameZero.vecMul_row (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
        (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a (G.V (.grid (2 * (σ + 1) + 1) 0)).gram β.b
        ⟨q.1, by omega⟩ m).trans ?_
      by_cases hm : m ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hm
        rw [Matrix.mul_apply]
        simp only [hb, Matrix.map_apply, RingHom.comp_apply]
        rw [key, (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).gram, antiDiagonalSignGramMatrix]
        split_ifs with h1 h3
        · exfalso
          have h4 := congrArg Fin.val h3
          simp only at h1 h4
          omega
        · have hrv : r.1 = 2 * (σ + 1) - 1 - q.1 := by simp only at h1; omega
          rw [map_one, map_one, mul_one, Pi.smul_apply, Pi.single_apply,
            if_pos (congrArg κ (Fin.ext hrv)), smul_eq_mul, mul_one, hrv]
        · rw [map_zero, map_zero, mul_zero, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
          intro hk
          have h4 := congrArg Fin.val (hinj hk)
          simp only at h1 h4
          omega
      · rw [Pi.smul_apply, Pi.single_apply, if_neg (fun e => hm ⟨_, e.symm⟩), smul_zero]
        exact hperp m hm _
    dsimp only
    rw [hrow, Matrix.smul_vecMul, hN, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx1) (pow_ne_zero _ hϖ)), one_smul]
