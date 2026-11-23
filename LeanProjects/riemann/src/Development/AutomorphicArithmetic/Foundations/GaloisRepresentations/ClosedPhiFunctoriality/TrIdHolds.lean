import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trId_holds :
    TrId := by
  intro l _ B _ u zb hz s d d' m t t' c pv p θ Pi e e' V V' h1 h2 lam
  have hscal : ∀ (z : ℤ_[l]) (x : Om l), u (lam (zOm l z * x)) = zb z * u (lam x) := by
    intro z x
    have hx : zOm l z * x = (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • x := by
      rw [Algebra.smul_def]
      rfl
    rw [hx, map_smul, smul_eq_mul, map_mul, hz]
  have hk : ∀ k, ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (c k * t' j k)) = s * u (lam (c k * pv k)) := by
    intro k
    simpa using h2 k (lam ∘ₗ LinearMap.mulLeft ↥(MaximalUnramifiedExtension l) (c k))
  have hE : (fun i => zb ((Pi *ᵥ e' - e) i)) = Pi.map zb *ᵥ (fun j => zb (e' j)) - fun i => zb (e i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hX : (V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ (fun i => zb ((Pi *ᵥ e' - e) i)) =
      V *ᵥ (fun i => zb (e i)) - Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j)) := by
    rw [hE, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    abel
  have hA := h1 lam
  have hS1 : ∑ i, ((V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ fun i => zb ((Pi *ᵥ e' - e) i)) i * u (lam (t i)) =
      s * u (lam p) - ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
    rw [hX, ← hA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [_root_.Pi.sub_apply]
    ring
  have hS2 : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k)) =
      ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) - ∑ k, s * u (lam (c k * pv k)) := by
    have ha : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ i, zb (Pi i j) * u (lam (t i)) =
        ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
      generalize (V' *ᵥ fun i => zb (e' i)) = w
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hb : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ k, u (lam (c k * t' j k)) = ∑ k, s * u (lam (c k * pv k)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => hk k
    rw [← ha, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sub, map_sum, hscal, mul_sub]
  have hS3 : s * u (lam (θ - ∑ k, c k * pv k)) = s * u (lam θ) - ∑ k, s * u (lam (c k * pv k)) := by
    simp only [map_sub, map_sum, mul_sub, Finset.mul_sum]
  rw [hS1, hS2, hS3, map_sub, map_sub, mul_sub]
  ring
