import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Unimod

theorem hform_frame {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J B : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform σ J (B *ᵥ x) (B *ᵥ y) = ∑ i, σ (x i) * ((Formalism.UG.cT σ B * J * B) *ᵥ y) i := by
  have h1 : ∀ (u w : Fin n → R), Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := fun u w => by
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : (fun i => σ ((B *ᵥ x) i)) = (B.map σ) *ᵥ (fun i => σ (x i)) := funext fun i => RingHom.map_mulVec σ B x i
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.UG.cT, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec]
  rfl

theorem gram_int {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (O : Subring R) (hσ : ∀ z ∈ O, σ z ∈ O)
    (J B C H' : Matrix (Fin n) (Fin n) R) (L : (Fin n → R) → Prop) (hBC : B * C = 1)
    (hH : Formalism.UG.cT σ B * J * B * H' = 1)
    (hf : ∀ y, (∀ i, y i ∈ O) ↔ L (B *ᵥ y)) (hd : ∀ y, L y ↔ ∀ x, L x → Formalism.UG.hform σ J x y ∈ O) :
    (∀ i j, (Formalism.UG.cT σ B * J * B) i j ∈ O) ∧ ∀ i j, H' i j ∈ O := by
  have hs : ∀ i k : Fin n, (Pi.single i 1 : Fin n → R) k ∈ O := fun i k => by
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  constructor
  · intro i j
    have h := (hd _).1 ((hf _).1 (hs j)) _ ((hf _).1 (hs i))
    rw [hform_frame, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h
    simpa using h
  · intro i j
    have h : L (B *ᵥ (H' *ᵥ Pi.single j 1)) := by
      refine (hd _).2 fun x hx => ?_
      have e : x = B *ᵥ (C *ᵥ x) := by rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
      have hz : ∀ k, (C *ᵥ x) k ∈ O := (hf _).2 (e ▸ hx)
      rw [e, hform_frame]
      refine sum_mem fun k _ => mul_mem (hσ _ (hz k)) ?_
      rw [Matrix.mulVec_mulVec, hH, Matrix.one_mulVec]
      exact hs j k
    simpa using (hf _).2 h i

theorem compFin_cA {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_gram {D : D7} (A : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (b : Mx D A.rank A.rank) :
    (adj b * gA A * b).map (compFin D.host.F D.host.E v) =
      Formalism.UG.cT (sigR _ D.sp.cm.sig) (b.map (compFin D.host.F D.host.E v)) * JR (Fv D.host.F v) A.gram *
        b.map (compFin D.host.F D.host.E v) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  funext i j; exact compFin_cA v _

theorem gram_unimodular : ∀ (D : D7) (A : HSp D) (b : GL (Fin A.rank) (AE D)), IsLatticeFrame (frameLat A) b → ∃ Hm : GL (Fin A.rank) (AE D), Hm.1 = adj b.1 * gA A * b.1 ∧ IntGL Hm := by
  intro D A b hb
  have h1 : adj b.1 * adj (b⁻¹).1 = 1 := by
    rw [← adj_mul, Units.inv_mul, adj_one]
  have h2 : adj (b⁻¹).1 * adj b.1 = 1 := by
    rw [← adj_mul, Units.mul_inv, adj_one]
  let Hm : GL (Fin A.rank) (AE D) :=
    (⟨adj b.1, adj (b⁻¹).1, h1, h2⟩ * ⟨gA A, giA A, gA_mul_giA A, giA_mul_gA A⟩ * b : (Mx D A.rank A.rank)ˣ)
  have hH : Hm.1 = adj b.1 * gA A * b.1 := rfl
  have key := fun v : HeightOneSpectrum (𝓞 D.host.F) =>
    gram_int (sigR _ D.sp.cm.sig) (intLoc D.host.F D.host.E v) (fun z hz => sigR_mem_intLoc _ hz)
      (JR (Fv D.host.F v) A.gram) (b.1.map (compFin D.host.F D.host.E v)) ((b⁻¹).1.map (compFin D.host.F D.host.E v))
      ((Hm⁻¹).1.map (compFin D.host.F D.host.E v)) (fun y => y ∈ latLoc D.host.F (frameLat A) v)
      (by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← map_gram, ← hH, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (hb v) (fun y => by
        have := SelfDual.isSelfDualAt_frameLat D A v
        exact (SetLike.ext_iff.1 this) y)
  refine ⟨Hm, hH, fun i j v => ?_, fun i j v => (key v).2 i j⟩
  have := (key v).1 i j
  rw [← map_gram, ← hH] at this
  exact this

end GlobalTheory.StdUnn.Unimod
