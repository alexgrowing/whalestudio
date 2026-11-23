import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem fourierBesselBasePoint_castSucc_column (i : Fin B.V.rank) (j : Fin σ) : x0 B i (Fin.castSucc j) = B.d.jX i j := by
  simp [x0, xLast, Fin.snoc_castSucc]

theorem fourierBesselBasePoint_last_column (i : Fin B.V.rank) : x0 B i (Fin.last σ) = (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i := by
  simp [x0, xLast, Fin.snoc_last]

theorem mul_fourierBesselBasePoint_castSucc_column {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) (j : Fin σ) :
    (M ⬝ x0 B) i (Fin.castSucc j) = (M ⬝ B.d.jX) i j := by
  simp only [Matrix.mul_apply, fourierBesselBasePoint_castSucc_column]

theorem mul_fourierBesselBasePoint_last_column {m : ℕ} (M : Mx D m B.V.rank) (i : Fin m) :
    (M ⬝ x0 B) i (Fin.last σ) = (M *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ))) i := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, fourierBesselBasePoint_last_column]

theorem fourierBesselBasePoint_mul_eq (U : Mx D (σ + 1) (σ + 1)) (i : Fin B.V.rank) (j : Fin (σ + 1)) :
    (x0 B ⬝ U) i j = ∑ k : Fin σ, B.d.jX i k * U (Fin.castSucc k) j +
      (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) i * U (Fin.last σ) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [fourierBesselBasePoint_castSucc_column, fourierBesselBasePoint_last_column]

theorem besselAnisotropicEmbedding_fixes_basePoint (h : GA D B.A) : mt B.V (embA B.d B.o h) ⬝ x0 B = x0 B := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_fourierBesselBasePoint_last_column, fourierBesselBasePoint_last_column, embA_apply, Matrix.mulVec_mulVec, B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mulVec_mulVec, vecB, ratV_mulVec,
      Matrix.mulVec_mulVec (ratV B.ζ), show rat B.o.iB = B.o.jB from rfl, B.o.emb_jB, mt_one, Matrix.mul_one]
  · rw [mul_fourierBesselBasePoint_castSucc_column, embA_apply, B.d.wittDecomp_anisotropicEmbedding_inclX, fourierBesselBasePoint_castSucc_column]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem upSum_succ (U : Mx D (σ + 1) (σ + 1)) :
    upSum U = upSum (fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j)) +
      ell D σ ⬝ᵥ (fun i => U (Fin.castSucc i) (Fin.last σ)) := by
  have h1 : ∀ j : Fin σ, ¬ (j.1 = σ + 1) := fun j => by omega
  have h2 : ¬ (σ = σ + 1) := by omega
  simp only [upSum, ell, dotProduct, Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last, h1, h2, if_false,
    Finset.sum_const_zero, add_zero, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : σ = i.1 + 1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem besselFlagProjection_mul_fourierBesselBasePoint_apply (i : Fin σ) (k : Fin (σ + 1)) : (B.d.pX ⬝ x0 B) i k = if k = Fin.castSucc i then 1 else 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [mul_fourierBesselBasePoint_last_column, Matrix.mulVec_mulVec, B.d.pX_j0, Matrix.zero_mulVec, if_neg (Fin.castSucc_lt_last i).ne']
    rfl
  · rw [mul_fourierBesselBasePoint_castSucc_column, B.d.pX_jX, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e).symm)]

theorem besselFlagProjection_mul_basePoint_mul_apply (U : Mx D (σ + 1) (σ + 1)) (i : Fin σ) (k : Fin (σ + 1)) :
    (B.d.pX ⬝ (x0 B ⬝ U)) i k = U (Fin.castSucc i) k := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [besselFlagProjection_mul_fourierBesselBasePoint_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem simpleSum_eq_upSum {n : GA D B.V} {U : Mx D (σ + 1) (σ + 1)} (e : mt B.V n ⬝ x0 B = x0 B ⬝ U) :
    simpleSum B.d (vecB B.o B.ζ) n = upSum U := by
  have hb : blockX B.d n = fun i j : Fin σ => U (Fin.castSucc i) (Fin.castSucc j) := by
    ext i j
    have h := mul_fourierBesselBasePoint_castSucc_column B (B.d.pX ⬝ mt B.V n) i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc] at h
    rw [blockX, ← besselFlagProjection_mul_basePoint_mul_apply B U i, ← e, h]
  have hc : coefX B.d (vecB B.o B.ζ) n = fun i => U (Fin.castSucc i) (Fin.last σ) := by
    ext i
    have h := mul_fourierBesselBasePoint_last_column B (B.d.pX ⬝ mt B.V n) i
    rw [Matrix.mul_assoc] at h
    rw [coefX, ← besselFlagProjection_mul_basePoint_mul_apply B U i, ← e, h, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [simpleSum, hb, hc, upSum_succ]

theorem psiBes_eq_psiUni (ψ : AddChar (AF D.host.F) ℂ) {n : GA D B.V} (h : GA D B.A) (u : UX D (σ + 1))
    (e : mt B.V (n * embA B.d B.o h) ⬝ x0 B = x0 B ⬝ u.1.1) :
    psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 := by
  rw [mt_mul, Matrix.mul_assoc, besselAnisotropicEmbedding_fixes_basePoint] at e
  rw [psiBes, simpleSum_eq_upSum B e, map_one, one_mul, psiUni]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

theorem vecB_ne : vecB B.o B.ζ ≠ 0 := by
  have hζ : B.ζ ≠ 0 := fun h => B.line.2 (by rw [h]; simp)
  intro h
  apply hζ
  have := congrArg (B.o.qB *ᵥ ·) h
  simpa [vecB, Matrix.mulVec_mulVec, B.o.qB_iB] using this

theorem exists_form : ∃ r₀ : Fin B.V₀.rank → D.host.E, ratV r₀ ⬝ᵥ ratV (vecB B.o B.ζ) = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, vecB B.o B.ζ k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact vecB_ne B (funext hc)
  refine ⟨Pi.single k (vecB B.o B.ζ k)⁻¹, ?_⟩
  rw [dotProduct, Finset.sum_eq_single k]
  · simp only [ratV, Pi.single_eq_same, ← map_mul, inv_mul_cancel₀ hk, map_one]
  · intro l _ hl
    simp only [ratV, Pi.single_eq_of_ne hl, map_zero, zero_mul]
  · exact fun h => absurd (Finset.mem_univ k) h

theorem vecMulVec_mulVec' {m k : ℕ} (w : Fin m → AE D) (r v : Fin k → AE D) (hr : r ⬝ᵥ v = 1) :
    vecMulVec w r *ᵥ v = w := by
  ext i
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum] at hr ⊢
  rw [hr, mul_one]

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB.UniRad

variable {D : D7} {σ : ℕ} (B : BesLev D σ)

def blk (U : Mx D (σ + 1) (σ + 1)) : Mx D σ σ := fun i j => U (Fin.castSucc i) (Fin.castSucc j)

theorem det_blk {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    (blk U).det = 1 := by
  have hT : (blk U).BlockTriangular id := fun i j h => (hU _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h)
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one fun i _ => (hU (Fin.castSucc i) (Fin.castSucc i)).2

def blkU {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    GL (Fin σ) (AE D) :=
  Matrix.nonsingInvUnit (blk U) (by rw [det_blk hU]; exact isUnit_one)

theorem blkU_val {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    (blkU hU).1 = blk U := rfl

theorem blkU_mem {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1) :
    blkU hU ∈ upperUni σ (AE D) := fun i j =>
  ⟨fun h => (hU (Fin.castSucc i) (Fin.castSucc j)).1 (Fin.castSucc_lt_castSucc_iff.2 h),
    (hU (Fin.castSucc i) (Fin.castSucc i)).2⟩

def blkQ (γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E) : Matrix (Fin σ) (Fin σ) D.host.E :=
  fun i j => γ (Fin.castSucc i) (Fin.castSucc j)

theorem blk_rat (γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E) : blk (rat γ : Mx D (σ + 1) (σ + 1)) = rat (blkQ γ) := rfl

theorem blkU_rat {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1)
    {γ : Matrix (Fin (σ + 1)) (Fin (σ + 1)) D.host.E} (hγ : rat γ = U) :
    (blkU hU).1 ∈ ratMx D σ σ ∧ ((blkU hU)⁻¹).1 ∈ ratMx D σ σ := by
  have ha1 : (blkU hU).1 = rat (blkQ γ) := by rw [blkU_val, ← hγ, blk_rat]
  have hdet : (blkQ γ).det = 1 := by
    apply incA_injective
    rw [map_one, RingHom.map_det]
    have e : (incA D).mapMatrix (blkQ γ) = blk U := by rw [← hγ, blk_rat]; rfl
    rw [e, det_blk hU]
  have e : rat (blkQ γ)⁻¹ ⬝ (blkU hU).1 = 1 := by
    rw [ha1, ← rat_mul, Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one), rat_one]
  refine ⟨by rw [ha1]; exact rat_mem _, ?_⟩
  have hinv : ((blkU hU)⁻¹).1 = rat (blkQ γ)⁻¹ := by
    calc ((blkU hU)⁻¹).1 = (rat (blkQ γ)⁻¹ ⬝ (blkU hU).1) ⬝ ((blkU hU)⁻¹).1 := by rw [e, Matrix.one_mul]
      _ = rat (blkQ γ)⁻¹ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [hinv]; exact rat_mem _

theorem rat_vecMulVec {m k : ℕ} (w : Fin m → D.host.E) (r : Fin k → D.host.E) :
    (rat (vecMulVec w r) : Mx D m k) = vecMulVec (ratV w) (ratV r) := by
  ext i j
  simp only [rat, Matrix.map_apply, vecMulVec_apply, ratV, map_mul]

theorem besselFlagElement_mul_basePoint_eq_basePoint_mul {U : Mx D (σ + 1) (σ + 1)} (hU : ∀ i j : Fin (σ + 1), (j < i → U i j = 0) ∧ U i i = 1)
    (a : GL (Fin σ) (AE D)) (ha : a.1 = blk U) (b : Mx D σ B.V₀.rank)
    (hbz : a.1 *ᵥ (b *ᵥ ratV (vecB B.o B.ζ)) = fun i => U (Fin.castSucc i) (Fin.last σ)) :
    mt B.V (B.d.levi a * B.d.nB b) ⬝ x0 B = x0 B ⬝ U := by
  have hX : mt B.V (B.d.levi a * B.d.nB b) ⬝ B.d.jX = B.d.jX ⬝ a.1 := by
    rw [mt_mul, Matrix.mul_assoc, B.d.nB_jX, B.d.levi_jX]
  have h0 : mt B.V (B.d.levi a * B.d.nB b) ⬝ B.d.j0 = B.d.j0 + B.d.jX ⬝ (a.1 ⬝ b) := by
    rw [mt_mul, Matrix.mul_assoc, B.d.nB_j0, Matrix.mul_add, B.d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, B.d.levi_jX,
      Matrix.mul_assoc]
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [mul_fourierBesselBasePoint_last_column, fourierBesselBasePoint_mul_eq, Matrix.mulVec_mulVec, h0, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hbz, Pi.add_apply, (hU (Fin.last σ) (Fin.last σ)).2, mul_one]
    exact add_comm _ _
  · rw [mul_fourierBesselBasePoint_castSucc_column, fourierBesselBasePoint_mul_eq, hX, (hU (Fin.last σ) (Fin.castSucc j)).1 (Fin.castSucc_lt_last j), mul_zero, add_zero,
      Matrix.mul_apply, ha]
    rfl

theorem exists_flag (u : UX D (σ + 1)) :
    ∃ n ∈ flagN B.d, mt B.V n ⬝ x0 B = x0 B ⬝ u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V) := by
  have hU : ∀ i j : Fin (σ + 1), (j < i → u.1.1 i j = 0) ∧ u.1.1 i i = 1 := u.2
  obtain ⟨r₀, hr⟩ := exists_form B
  obtain ⟨c, hc⟩ : ∃ c : Fin σ → AE D, c = fun i => u.1.1 (Fin.castSucc i) (Fin.last σ) := ⟨_, rfl⟩
  have hbz : (blkU hU).1 *ᵥ (vecMulVec (((blkU hU)⁻¹).1 *ᵥ c) (ratV r₀) *ᵥ ratV (vecB B.o B.ζ)) = c := by
    rw [vecMulVec_mulVec' _ _ _ hr, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hc] at hbz
  refine ⟨_, mul_mem (B.d.levi_mem_NFlag (blkU_mem hU)) (B.d.nB_mem_NFlag _),
    besselFlagElement_mul_basePoint_eq_basePoint_mul B hU (blkU hU) (blkU_val hU) _ hbz, fun hq => ?_⟩
  obtain ⟨γ, hγ⟩ := mem_ratMx.1 hq.1
  have hr' := blkU_rat hU hγ
  have hc' : c = ratV (fun i => γ (Fin.castSucc i) (Fin.last σ)) := by
    rw [hc]; ext i; simp only [ratV, ← hγ, rat, Matrix.map_apply]
  obtain ⟨δ, hδ⟩ := mem_ratMx.1 hr'.2
  have hbq : vecMulVec (((blkU hU)⁻¹).1 *ᵥ c) (ratV r₀) ∈ ratMx D σ B.V₀.rank := by
    rw [← hδ, hc', ← ratV_mulVec, ← rat_vecMulVec]
    exact rat_mem _
  rw [hc] at hbq
  exact mul_mem (B.d.levi_mem_GQ hr'.1 hr'.2) (B.d.nB_mem_GQ hbq)

end GlobalTheory.Unf.FB.UniRad

namespace GlobalTheory.Unf.FB

theorem uniRad_surj_psi : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), (∀ u : UX D (σ + 1), ∃ n ∈ flagN B.d, mt B.V n ⬝ x0 B = x0 B ⬝ u.1.1 ∧ (u ∈ UXQ D (σ + 1) → n ∈ GQ B.V)) ∧ ∀ (ψ : AddChar (AF D.host.F) ℂ), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (u : UX D (σ + 1)), mt B.V (n * embA B.d B.o h) ⬝ x0 B = x0 B ⬝ u.1.1 → psiBes ψ B.d 1 (vecB B.o B.ζ) n = psiUni ψ u.1 :=
  fun _ _ B => ⟨UniRad.exists_flag B, fun ψ _ _ h u e => UniRad.psiBes_eq_psiUni B ψ h u e⟩

end GlobalTheory.Unf.FB

end
