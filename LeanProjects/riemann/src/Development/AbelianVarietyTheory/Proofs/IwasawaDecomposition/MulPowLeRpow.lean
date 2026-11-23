import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramBoundedByHodgeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatePointGramStatement

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Topology ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.MuExp

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem quad_nonneg {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) (v : Fin m → ℂ) :
    0 ≤ (star v ⬝ᵥ M *ᵥ v).re :=
  h.posSemidef.re_dotProduct_nonneg v

theorem quad_map_conj {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    (star (fun i => starRingEnd ℂ (v i)) ⬝ᵥ M.map (starRingEnd ℂ) *ᵥ (fun i => starRingEnd ℂ (v i))).re =
      (star v ⬝ᵥ M *ᵥ v).re := by
  have h : star (fun i => starRingEnd ℂ (v i)) ⬝ᵥ M.map (starRingEnd ℂ) *ᵥ (fun i => starRingEnd ℂ (v i)) =
      starRingEnd ℂ (star v ⬝ᵥ M *ᵥ v) := by
    simp [dotProduct, mulVec, map_sum, Finset.mul_sum]
  rw [h, Complex.conj_re]

variable (x : ToroidalCompactificationData s)

def Bd (σ : κ.c.F →+* ℂ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ y : CxPts (genStr s.T.Z) σ, ¬ LiesIn y (genBd s.T.Z) → ∀ (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z))
    (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ),
    (star v ⬝ᵥ x.gram y g τ *ᵥ v).re ≤ C * x.r σ y ^ k * (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ∧
      (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ≤ C * x.r σ y ^ k * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re

theorem one_le_r (σ : κ.c.F →+* ℂ) (y : CxPts (genStr s.T.Z) σ) : 1 ≤ x.r σ y := by
  have h1 := x.exp_le_r σ y
  have h2 := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem mul_pow_le {C C' r : ℝ} {k k' : ℕ} (hC : C ≤ C') (hC' : 0 ≤ C') (hk : k ≤ k') (hr : 1 ≤ r) :
    C * r ^ k ≤ C' * r ^ k' := by
  have hp : r ^ k ≤ r ^ k' := pow_le_pow_right₀ hr hk
  have hp0 : 0 ≤ r ^ k := by positivity
  by_cases hc : 0 ≤ C
  · exact mul_le_mul hC hp hp0 (hc.trans hC)
  · push_neg at hc
    exact (mul_nonpos_of_nonpos_of_nonneg hc.le hp0).trans (by positivity)

theorem Bd.mono {σ : κ.c.F →+* ℂ} {C C' : ℝ} {k k' : ℕ} (h : Bd x σ C k) (hC : C ≤ C') (hC' : 0 ≤ C')
    (hk : k ≤ k') : Bd x σ C' k' := fun y hy g τ v => by
  have hC0 := mul_pow_le hC hC' hk (one_le_r x σ y)
  have q0 := quad_nonneg (x.gram_posDef g τ) v
  have q1 := quad_nonneg ((x.hodge σ).pos y g τ) v
  obtain ⟨a, b⟩ := h y hy g τ v
  exact ⟨a.trans (mul_le_mul_of_nonneg_right hC0 q1), b.trans (mul_le_mul_of_nonneg_right hC0 q0)⟩

theorem exists_bd_good (σ : κ.c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb κ.c σ) : ∃ (C : ℝ) (k : ℕ), Bd x σ C k := by
  have : CompactSpace (CxPts (genStr s.T.Z) σ) :=
    CxPts.compactSpace σ (ProjSpace.isProjOver_pullback_snd _ s.T.Z.proj)
  have hl := GlobalTheory.T.gram_bounded_by_hodge D A N j S κ s x σ hσ
  choose U hU C k hb using hl
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U fun y _ => hU y
  refine ⟨∑ y ∈ t, |C y|, ∑ y ∈ t, k y, fun y hy g τ v => ?_⟩
  obtain ⟨y₀, hy₀, hyU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  have hC0 := mul_pow_le (C := C y₀) (C' := ∑ y ∈ t, |C y|) (k := k y₀) (k' := ∑ y ∈ t, k y)
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun y => |C y|) (fun _ _ => abs_nonneg _) hy₀))
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) hy₀) (one_le_r x σ y)
  have q0 := quad_nonneg (x.gram_posDef g τ) v
  have q1 := quad_nonneg ((x.hodge σ).pos y g τ) v
  obtain ⟨a, b⟩ := hb y₀ y hyU hy g τ v
  exact ⟨a.trans (mul_le_mul_of_nonneg_right hC0 q1), b.trans (mul_le_mul_of_nonneg_right hC0 q0)⟩

theorem exists_bd (σ : κ.c.F →+* ℂ) : ∃ (C : ℝ) (k : ℕ), Bd x σ C k := by
  by_cases hσ : Formalism.L2.PjFree.GoodEmb κ.c σ
  · exact exists_bd_good x σ hσ
  have h1 : Formalism.L2.PjFree.GoodEmb κ.c ((starRingEnd ℂ).comp σ) := by
    simpa only [Formalism.L2.PjFree.goodOf, if_neg hσ] using Formalism.L2.PjFree.goodEmb_goodOf κ.c σ
  obtain ⟨C, k, hb⟩ := exists_bd_good x _ h1
  refine ⟨C, k, fun y hy g τ v => ?_⟩
  obtain ⟨y', hy', hr, hg⟩ := GlobalTheory.T.conjugate_point_gram D A N j S κ s x σ hσ y
  obtain ⟨g', hg'⟩ := hg g
  obtain ⟨a, b⟩ := hb y' (fun h => hy (hy'.1 h)) g' τ (fun i => starRingEnd ℂ (v i))
  rw [(hg' τ).1, (hg' τ).2, quad_map_conj, quad_map_conj, hr] at a b
  exact ⟨a, b⟩

theorem exists_bd_all : ∃ (C : ℝ) (k : ℕ), 1 ≤ C ∧ ∀ σ, Bd x σ C k := by
  choose C k hb using exists_bd x
  refine ⟨1 + ∑ σ, |C σ|, ∑ σ, k σ, le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _),
    fun σ => (hb σ).mono x ?_ ?_ ?_⟩
  · exact (le_abs_self _).trans ((Finset.single_le_sum (f := fun σ => |C σ|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ)).trans (le_add_of_nonneg_left zero_le_one))
  · exact add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · exact Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)

theorem mul_pow_le_rpow {C r : ℝ} (k : ℕ) (hC : 1 ≤ C) (hr : Real.exp 1 ≤ r) :
    C * r ^ k ≤ r ^ ((k : ℝ) + Real.log C) := by
  have hr0 : 0 < r := (Real.exp_pos 1).trans_le hr
  have hlr : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hr
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  rw [Real.rpow_add hr0, Real.rpow_natCast, mul_comm C]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.rpow_def_of_pos hr0]
  calc C = Real.exp (Real.log C) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp (Real.log r * Real.log C) := Real.exp_le_exp.2 (le_mul_of_one_le_left hlC hlr)

end GlobalTheory.ShFam.MuExp

namespace GlobalTheory.ShFam.ToroidalCompactificationData

open GlobalTheory.ShFam.MuExp

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem exists_isMuExp (x : ToroidalCompactificationData s) : ∃ C, x.IsMuExp C := by
  obtain ⟨C, k, hC, hb⟩ := exists_bd_all x
  refine ⟨(k : ℝ) + Real.log C, add_nonneg (Nat.cast_nonneg k) (Real.log_nonneg hC), fun σ y hy g τ v => ?_⟩
  obtain ⟨a, b⟩ := hb σ y hy g τ v
  have hr := x.exp_le_r σ y
  have hr0 : 0 < x.r σ y := (Real.exp_pos 1).trans_le hr
  have hm := mul_pow_le_rpow k hC hr
  have q0 := quad_nonneg (x.gram_posDef g τ) v
  have q1 := quad_nonneg ((x.hodge σ).pos y g τ) v
  have hp : 0 < x.r σ y ^ ((k : ℝ) + Real.log C) := Real.rpow_pos_of_pos hr0 _
  have e : x.r σ y ^ (-((k : ℝ) + Real.log C)) * x.r σ y ^ ((k : ℝ) + Real.log C) = 1 := by
    rw [← Real.rpow_add hr0, neg_add_cancel, Real.rpow_zero]
  have hn : 0 < x.r σ y ^ (-((k : ℝ) + Real.log C)) := Real.rpow_pos_of_pos hr0 _
  refine ⟨?_, b.trans (mul_le_mul_of_nonneg_right hm q0)⟩
  have a' := a.trans (mul_le_mul_of_nonneg_right hm q1)
  calc x.r σ y ^ (-((k : ℝ) + Real.log C)) * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re
      ≤ x.r σ y ^ (-((k : ℝ) + Real.log C)) * (x.r σ y ^ ((k : ℝ) + Real.log C) *
        (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re) := mul_le_mul_of_nonneg_left a' hn.le
    _ = (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re := by rw [← mul_assoc, e, one_mul]

theorem isMuExp_muExp' (x : ToroidalCompactificationData s) : x.IsMuExp x.muExp := x.isMuExp_muExp x.exists_isMuExp

end GlobalTheory.ShFam.ToroidalCompactificationData
