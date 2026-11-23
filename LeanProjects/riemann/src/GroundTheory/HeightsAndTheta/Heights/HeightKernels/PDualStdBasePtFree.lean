import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.SingleMemDualLatticeStandard
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOnPlane
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

namespace StandardDualBasePointFree

open DualPointsOnPlane

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in

theorem coord_integral (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (c : T) (j : Fin i) :
    ∃ α : 𝓞 K, (α : K) = (b c : Fin i → K) j := by
  obtain ⟨α, hα⟩ := (b c).2 (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨α, hα.trans (dotProduct_single_one _ _)⟩

omit [DecidableEq T] in

theorem mConeMap_lin {Ω : Type} [Field Ω] (y : (Σ _ : Unit, T) → Ω) (a : T → ℤ) :
    mConeMap y (∑ t, C (a t) * X ⟨(), t⟩ : MRing (dualBlocks T)) =
      MvPolynomial.C (∑ t, (a t : Ω) * y ⟨(), t⟩) * MvPolynomial.X () := by
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [mConeMap, aeval_X, map_mul, map_intCast, eq_intCast]
  ring

end StandardDualBasePointFree

open StandardDualBasePointFree DualPointsOnPlane in

theorem DualStdBasePtFree.proof : DualStdBasePtFree.Statement := by
  intro K _ _ i T _ _ b k₂ c
  cases k₂
  refine ⟨2, ?_⟩
  have hprod : (∏ k : Unit, (X ⟨k, c k⟩ : MRing (dualBlocks T))) = X ⟨(), c ()⟩ := Fintype.prod_unique _
  rw [hprod]
  choose α hα using coord_integral b (c ())
  let am := algebraMap (MvPolynomial (Fin i) K) (ProjField K i)
  let y := dualLatticeCoord b
  let L : Fin i → MRing (dualBlocks T) := fun j => ∑ s, C (mulMat b (α j) (c ()) s) * X ⟨(), s⟩

  have hA : ∀ j, ∑ t, (dualStdCoordMat b () j t : ProjField K i) * y ⟨(), t⟩ = am (X j) := by
    intro j
    have hpoly : ∑ t, (dualStdCoordMat b () j t : MvPolynomial (Fin i) K) *
        ∑ l, C ((b t : Fin i → K) l) * X l = X j := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hc : ∀ l, ∑ t, (dualStdCoordMat b () j t : K) * (b t : Fin i → K) l = (Pi.single j (1 : K) : Fin i → K) l := by
        intro l
        have h := congrFun (dualStdCoordMat_sum b j) l
        simpa only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul] using h
      have hc' : ∀ l, ∑ t, (dualStdCoordMat b () j t : MvPolynomial (Fin i) K) * (C ((b t : Fin i → K) l) * X l) =
          C ((Pi.single j (1 : K) : Fin i → K) l) * X l := by
        intro l
        rw [← hc l, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [map_mul, map_intCast]
        ring
      simp only [hc']
      rw [Finset.sum_eq_single j (fun l _ hl => by simp [hl]) (by simp)]
      simp
    have h := congrArg am hpoly
    simpa only [am, y, dualLatticeCoord, map_sum, map_mul, map_intCast] using h

  have hS : ∀ j, ∑ s, (mulMat b (α j) (c ()) s : ProjField K i) * y ⟨(), s⟩ =
      am (C (α j : K)) * y ⟨(), c ()⟩ := by
    intro j
    have hlin : ∑ t, (mulMat b (α j) (c ()) t : MvPolynomial (Fin i) K) *
        ∑ l, C ((b t : Fin i → K) l) * X l = C (α j : K) * ∑ l, C ((b (c ()) : Fin i → K) l) * X l := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h := congrArg (C : K → MvPolynomial (Fin i) K) (mulMat_sum b (α j) (c ()) l)
      simp only [map_sum, map_mul, map_intCast] at h
      rw [← mul_assoc, ← h, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    have h := congrArg am hlin
    simpa only [am, y, dualLatticeCoord, map_sum, map_mul, map_intCast] using h

  have hy : y ⟨(), c ()⟩ = ∑ j, am (C (α j : K)) * am (X j) := by
    simp only [y, am, dualLatticeCoord, map_sum, map_mul, hα]
  have key : X ⟨(), c ()⟩ ^ 2 - ∑ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩ * L j ∈ dualIdeal b := by
    show _ ∈ RingHom.ker (mConeMap (dualLatticeCoord b))
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_sum]
    have hl : ∀ j, mConeMap (dualLatticeCoord b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩) =
        MvPolynomial.C (am (X j)) * MvPolynomial.X () := by
      intro j
      rw [← hA j]
      exact mConeMap_lin _ _
    have hL : ∀ j, mConeMap (dualLatticeCoord b) (L j) =
        MvPolynomial.C (am (C (α j : K)) * y ⟨(), c ()⟩) * MvPolynomial.X () := by
      intro j
      rw [← hS j]
      exact mConeMap_lin _ _
    have hX : mConeMap (dualLatticeCoord b) (X ⟨(), c ()⟩ : MRing (dualBlocks T)) =
        MvPolynomial.C (y ⟨(), c ()⟩) * MvPolynomial.X () := by
      simp only [mConeMap, aeval_X, y]
    simp only [map_mul, map_pow, hl, hL, hX]
    symm
    calc ∑ j, MvPolynomial.C (am (X j)) * MvPolynomial.X () *
          (MvPolynomial.C (am (C (α j : K))) * MvPolynomial.C (y ⟨(), c ()⟩) * MvPolynomial.X ())
        = MvPolynomial.C ((∑ j, am (C (α j : K)) * am (X j)) * y ⟨(), c ()⟩) * MvPolynomial.X () ^ 2 := by
          rw [Finset.sum_mul, map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [map_mul]
          ring
      _ = _ := by
          rw [← hy, map_mul]
          ring
  have hQ : ∑ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩ * L j ∈
      Ideal.span (Set.range fun j : PBlk i () => linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨(), j⟩) :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have h := Ideal.add_mem _ (Ideal.mem_sup_left key) (Ideal.mem_sup_right hQ)
  rwa [sub_add_cancel] at h

end

end GroundTheory.Heights₂.Heights
