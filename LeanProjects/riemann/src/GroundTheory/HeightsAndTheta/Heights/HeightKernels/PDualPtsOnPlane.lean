import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualProjApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace DualPointsOnPlane

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T]

theorem smul_mem_dualLattice (α : 𝓞 K) {φ : Fin i → K} (hφ : φ ∈ dualLattice F) :
    (α : K) • φ ∈ dualLattice F := by
  intro x hx
  obtain ⟨a, ha⟩ := hφ x hx
  refine ⟨α * a, ?_⟩
  rw [map_mul, ha, smul_dotProduct, smul_eq_mul]

def mulMat (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s t : T) : ℤ :=
  b.repr ⟨(α : K) • (b s : Fin i → K), smul_mem_dualLattice α (b s).2⟩ t

theorem mulMat_sum (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s : T) (j : Fin i) :
    ∑ t, (mulMat b α s t : K) * (b t : Fin i → K) j = (α : K) * (b s : Fin i → K) j := by
  have h := b.sum_repr ⟨(α : K) • (b s : Fin i → K), smul_mem_dualLattice α (b s).2⟩
  have h2 := congrArg (fun v : dualLattice F => (v : Fin i → K) j) h
  simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
    zsmul_eq_mul, smul_eq_mul] at h2
  exact h2

omit [Fintype T] in

theorem recover_spec (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (Z : T → ℂ) (t : T) :
    Z t = ∑ p : (K →+* ℂ) × Fin i, p.1 ((b t : Fin i → K) p.2) * dualRecover b hb Z p := by
  have h := (LinearEquiv.ofBijective (Matrix.mulVecLin (dualEmbMatrix b)) hb).apply_symm_apply Z
  rw [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply] at h
  conv_lhs => rw [← h]
  rfl

theorem mulMat_recover (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (α : 𝓞 K) (Z : T → ℂ) (s : T) :
    ∑ t, (mulMat b α s t : ℂ) * Z t =
      ∑ p : (K →+* ℂ) × Fin i, p.1 ((b s : Fin i → K) p.2) * (p.1 α * dualRecover b hb Z p) := by
  calc ∑ t, (mulMat b α s t : ℂ) * Z t
      = ∑ t, ∑ p : (K →+* ℂ) × Fin i,
          (mulMat b α s t : ℂ) * (p.1 ((b t : Fin i → K) p.2) * dualRecover b hb Z p) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [recover_spec b hb Z t, Finset.mul_sum]
    _ = ∑ p : (K →+* ℂ) × Fin i,
          (∑ t, (mulMat b α s t : ℂ) * p.1 ((b t : Fin i → K) p.2)) * dualRecover b hb Z p := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have h := congrArg p.1 (mulMat_sum b α s p.2)
        simp only [map_sum, map_mul, map_intCast] at h
        rw [h]
        ring

def quad (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s r : T) : MRing (dualBlocks T) :=
  X ⟨(), s⟩ * ∑ t, C (mulMat b α r t) * X ⟨(), t⟩ - (∑ t, C (mulMat b α s t) * X ⟨(), t⟩) * X ⟨(), r⟩

theorem quad_mem (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K) (s r : T) :
    quad b α s r ∈ dualIdeal b := by
  have hlin : ∀ u, ∑ t, (mulMat b α u t : MvPolynomial (Fin i) K) *
      ∑ j, C ((b t : Fin i → K) j) * X j = C (α : K) * ∑ j, C ((b u : Fin i → K) j) * X j := by
    intro u
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum b α u j)
    simp only [map_sum, map_mul, map_intCast] at h
    rw [← mul_assoc, ← h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hS : ∀ u, ∑ t, (mulMat b α u t : ProjField K i) * dualLatticeCoord b ⟨(), t⟩ =
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) * dualLatticeCoord b ⟨(), u⟩ := by
    intro u
    have h := congrArg (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) (hlin u)
    simpa only [dualLatticeCoord, map_sum, map_mul, map_intCast] using h
  have hsum : ∀ u, mConeMap (dualLatticeCoord b) (∑ t, C (mulMat b α u t) * X ⟨(), t⟩) =
      MvPolynomial.C (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) *
        dualLatticeCoord b ⟨(), u⟩) * MvPolynomial.X () := by
    intro u
    rw [← hS u, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
    ring
  show quad b α s r ∈ RingHom.ker (mConeMap (dualLatticeCoord b))
  rw [RingHom.mem_ker]
  simp only [quad, map_sub, map_mul, hsum]
  simp only [mConeMap, aeval_X]
  ring

theorem eval_quad (z : (Σ _ : Unit, T) → ℂ) (b : Module.Basis T ℤ (dualLattice F)) (α : 𝓞 K)
    (s r : T) : eval z (map (Int.castRingHom ℂ) (quad b α s r)) =
      z ⟨(), s⟩ * ∑ t, (mulMat b α r t : ℂ) * z ⟨(), t⟩ -
        (∑ t, (mulMat b α s t : ℂ) * z ⟨(), t⟩) * z ⟨(), r⟩ := by
  simp [quad]

theorem agree (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ)
    (hz : z ∈ mcPts (dualIdeal b)) (α : 𝓞 K) (p q : (K →+* ℂ) × Fin i)
    (hp : dualRecover b hb (fun t => z ⟨(), t⟩) p ≠ 0) (hq : dualRecover b hb (fun t => z ⟨(), t⟩) q ≠ 0) :
    p.1 α = q.1 α := by
  obtain ⟨s0, hs0⟩ := hz.1 ()
  obtain ⟨Z, hZ⟩ : ∃ Z : T → ℂ, Z = fun t => z ⟨(), t⟩ := ⟨_, rfl⟩
  have hZt : ∀ t, z ⟨(), t⟩ = Z t := fun t => by rw [hZ]
  rw [← hZ] at hp hq
  rw [hZt] at hs0
  have hrel : ∀ s r, Z s * ∑ t, (mulMat b α r t : ℂ) * Z t =
      (∑ t, (mulMat b α s t : ℂ) * Z t) * Z r := by
    intro s r
    have h := hz.2 _ (quad_mem b α s r)
    rw [eval_quad] at h
    simp only [hZt] at h
    exact sub_eq_zero.mp h
  have hL : ∀ r, ∑ t, (mulMat b α r t : ℂ) * Z t =
      ((∑ t, (mulMat b α s0 t : ℂ) * Z t) / Z s0) * Z r := by
    intro r
    rw [div_mul_eq_mul_div, eq_div_iff hs0]
    linear_combination hrel s0 r
  set lam := (∑ t, (mulMat b α s0 t : ℂ) * Z t) / Z s0
  have hw : (fun p : (K →+* ℂ) × Fin i => p.1 α * dualRecover b hb Z p) = lam • dualRecover b hb Z := by
    apply hb.1
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    funext s
    show ∑ p : (K →+* ℂ) × Fin i, p.1 ((b s : Fin i → K) p.2) * (p.1 α * dualRecover b hb Z p) =
      ∑ p : (K →+* ℂ) × Fin i, p.1 ((b s : Fin i → K) p.2) * (lam * dualRecover b hb Z p)
    rw [← mulMat_recover, hL s, recover_spec b hb Z s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hp' := congrFun hw p
  have hq' := congrFun hw q
  simp only [Pi.smul_apply, smul_eq_mul] at hp' hq'
  rw [mul_right_cancel₀ hp hp', mul_right_cancel₀ hq hq']

end DualPointsOnPlane

open DualPointsOnPlane in

theorem DualPtsOnPlane.proof : DualPtsOnPlane.Statement := by
  intro K _ _ i F T _ _ b hb z hz
  obtain ⟨s0, hs0⟩ := hz.1 ()
  obtain ⟨p0, hp0⟩ : ∃ p, dualRecover b hb (fun t => z ⟨(), t⟩) p ≠ 0 := by
    by_contra hne
    simp only [ne_eq, not_exists, not_not] at hne
    exact hs0 ((recover_spec b hb (fun t => z ⟨(), t⟩) s0).trans (by simp [hne]))
  refine ⟨p0.1, fun τ hτ j => ?_⟩
  by_contra hne
  apply hτ
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
  ext α
  exact agree b hb z hz α (τ, j) p0 hne hp0

end

end GroundTheory.Heights₂.Heights
