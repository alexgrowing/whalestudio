import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ProjProjApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace ProjectivePointsOnPlane

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def mulMat (α : 𝓞 K) (m n : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) : ℤ :=
  (RingOfIntegers.basis K).repr (α * RingOfIntegers.basis K m) n

theorem mulMat_sum (α : 𝓞 K) (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ∑ n, (mulMat α m n : K) * integralBasis K n = (α : K) * integralBasis K m := by
  have h := congrArg (algebraMap (𝓞 K) K) ((RingOfIntegers.basis K).sum_repr
    (α * RingOfIntegers.basis K m))
  simp only [map_sum, map_mul, zsmul_eq_mul, map_intCast] at h
  simpa only [integralBasis_apply, mulMat, RingOfIntegers.coe_eq_algebraMap] using h

open scoped Classical in

theorem embComp_recon (u : (K →+* ℂ) → Fin i → ℂ) (τ : K →+* ℂ) :
    embComp τ (fun q : ProjIdx K i => ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * u σ q.2) = u τ := by
  set b := canonicalEmbedding.latticeBasis K
  have hd : ∀ σ : K →+* ℂ, ∑ m, b.repr (Pi.single τ 1) m * σ (integralBasis K m) =
      if σ = τ then 1 else 0 := by
    intro σ
    have h := congrFun (b.sum_repr (Pi.single τ 1)) σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b, canonicalEmbedding.latticeBasis_apply,
      canonicalEmbedding.apply_at, Pi.single_apply] at h
    exact h
  funext j
  calc embComp τ (fun q : ProjIdx K i => ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * u σ q.2) j
      = ∑ m, ∑ σ : K →+* ℂ, b.repr (Pi.single τ 1) m * (σ (integralBasis K m) * u σ j) := by
        simp only [embComp, Finset.mul_sum]; rfl
    _ = ∑ σ : K →+* ℂ, (∑ m, b.repr (Pi.single τ 1) m * σ (integralBasis K m)) * u σ j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = u τ j := by
        rw [Finset.sum_congr rfl fun σ _ => congrArg (· * u σ j) (hd σ)]
        simp

def lin (α : 𝓞 K) (Z : ProjIdx K i → ℂ) : ProjIdx K i → ℂ :=
  fun q => ∑ n, (mulMat α q.1 n : ℂ) * Z (n, q.2)

theorem lin_eq (α : 𝓞 K) (Z : ProjIdx K i → ℂ) (q : ProjIdx K i) :
    lin α Z q = ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * (σ (α : K) * embComp σ Z q.2) := by
  calc lin α Z q
      = ∑ n, ∑ σ : K →+* ℂ, (mulMat α q.1 n : ℂ) * (σ (integralBasis K n) * embComp σ Z q.2) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← sum_emb_embComp Z n q.2, Finset.mul_sum]
    _ = ∑ σ : K →+* ℂ, (∑ n, (mulMat α q.1 n : ℂ) * σ (integralBasis K n)) * embComp σ Z q.2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun n _ => by ring
    _ = _ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        have h := congrArg σ (mulMat_sum α q.1)
        simp only [map_sum, map_mul, map_intCast] at h
        rw [h]
        ring

theorem embComp_lin (α : 𝓞 K) (Z : ProjIdx K i → ℂ) (τ : K →+* ℂ) :
    embComp τ (lin α Z) = τ (α : K) • embComp τ Z := by
  have h : lin α Z = fun q : ProjIdx K i =>
      ∑ σ : K →+* ℂ, σ (integralBasis K q.1) * (fun σ j => σ (α : K) * embComp σ Z j) σ q.2 :=
    funext fun q => lin_eq α Z q
  rw [h]
  exact embComp_recon (fun σ j => σ (α : K) * embComp σ Z j) τ

def lform (α : 𝓞 K) (q : ProjIdx K i) : MRing (projBlocks K i) :=
  ∑ n, C (mulMat α q.1 n) * X ⟨(), (n, q.2)⟩

def quad (α : 𝓞 K) (p q : ProjIdx K i) : MRing (projBlocks K i) :=
  X ⟨(), p⟩ * lform α q - lform α p * X ⟨(), q⟩

theorem quad_mem (α : 𝓞 K) (p q : ProjIdx K i) : quad α p q ∈ projSpaceIdeal K i := by
  have hlin : ∀ u : ProjIdx K i, ∑ n, (mulMat α u.1 n : MvPolynomial (Fin i) K) *
      (C (integralBasis K n) * X u.2) = C (α : K) * (C (integralBasis K u.1) * X u.2) := by
    intro u
    have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum α u.1)
    simp only [map_sum, map_mul, map_intCast] at h
    rw [← mul_assoc, ← h, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hS : ∀ u : ProjIdx K i, ∑ n, (mulMat α u.1 n : ProjField K i) * projSpaceCoord K i ⟨(), (n, u.2)⟩ =
      algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) * projSpaceCoord K i ⟨(), u⟩ := by
    intro u
    have h := congrArg (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) (hlin u)
    simpa only [projSpaceCoord, map_sum, map_mul, map_intCast] using h
  have hsum : ∀ u : ProjIdx K i, mConeMap (projSpaceCoord K i) (lform α u) =
      MvPolynomial.C (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (C (α : K)) *
        projSpaceCoord K i ⟨(), u⟩) * MvPolynomial.X () := by
    intro u
    rw [← hS u, lform, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
    ring
  show quad α p q ∈ RingHom.ker (mConeMap (projSpaceCoord K i))
  rw [RingHom.mem_ker]
  simp only [quad, map_sub, map_mul, hsum]
  simp only [mConeMap, aeval_X]
  ring

theorem eval_quad (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (α : 𝓞 K) (p q : ProjIdx K i) :
    eval z (map (Int.castRingHom ℂ) (quad α p q)) =
      z ⟨(), p⟩ * lin α (fun r => z ⟨(), r⟩) q - lin α (fun r => z ⟨(), r⟩) p * z ⟨(), q⟩ := by
  simp [quad, lform, lin]

theorem agree (z : (Σ _ : Unit, ProjIdx K i) → ℂ) (hz : z ∈ mcPts (projSpaceIdeal K i)) (α : 𝓞 K)
    (σ τ : K →+* ℂ) (j l : Fin i) (hσ : embComp σ (fun q => z ⟨(), q⟩) j ≠ 0)
    (hτ : embComp τ (fun q => z ⟨(), q⟩) l ≠ 0) : σ (α : K) = τ (α : K) := by
  obtain ⟨q0, hq0⟩ := hz.1 ()
  set Z : ProjIdx K i → ℂ := fun q => z ⟨(), q⟩ with hZ
  have hrel : ∀ p q, Z p * lin α Z q = lin α Z p * Z q := by
    intro p q
    have h := hz.2 _ (quad_mem α p q)
    rw [eval_quad] at h
    exact sub_eq_zero.mp h
  have hL : lin α Z = (lin α Z q0 / Z q0) • Z := by
    funext r
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hq0]
    linear_combination hrel q0 r
  have key : ∀ ρ : K →+* ℂ, ρ (α : K) • embComp ρ Z = (lin α Z q0 / Z q0) • embComp ρ Z := by
    intro ρ
    rw [← embComp_lin, ← embComp_smul, ← hL]
  have h1 := congrFun (key σ) j
  have h2 := congrFun (key τ) l
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [mul_right_cancel₀ hσ h1, mul_right_cancel₀ hτ h2]

end ProjectivePointsOnPlane

open ProjectivePointsOnPlane in

theorem ProjPtsOnPlane.proof : ProjPtsOnPlane.Statement := by
  intro K _ _ i z hz
  obtain ⟨⟨m0, j0⟩, hq0⟩ := hz.1 ()
  obtain ⟨σ, j, hσ⟩ : ∃ (σ : K →+* ℂ) (j : Fin i), embComp σ (fun q => z ⟨(), q⟩) j ≠ 0 := by
    by_contra hne
    simp only [ne_eq, not_exists, not_not] at hne
    exact hq0 ((sum_emb_embComp (fun q => z ⟨(), q⟩) m0 j0).symm.trans (by simp [hne]))
  refine ⟨σ, fun τ hτ => ?_⟩
  funext l
  by_contra hne
  apply hτ
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K))
  ext α
  exact agree z hz α τ σ l j hne hσ

end

end GroundTheory.Heights₂.Heights
