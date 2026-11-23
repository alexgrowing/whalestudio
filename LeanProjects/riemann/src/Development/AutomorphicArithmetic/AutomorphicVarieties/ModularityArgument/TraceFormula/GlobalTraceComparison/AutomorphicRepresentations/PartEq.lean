import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem row_int (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) (w : Lp ℂ 2 D.ν) (x : H E n 0) :
    Integrable (fun y => kerH φ x y * (w : H E n 0 → ℂ) y) D.ν :=
  MemLp.integrable_mul ((kernel_rows_columns_square_integrable (ctx ratProper_holds D) φ hφ).2 x) (Lp.memLp w)

private theorem ker_trM (D : Dom E n 0) {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ)
    (x y : H E n 0) : kerH (trM Φ M) x y = ∑ i, ∑ j, kerH (Φ i j) x y * M j i := by
  have h := (kerLin (ctx ratProper_holds D) (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1)
    (fun p => hΦ p.1 p.2)).2 x y
  have e : trM Φ M = fun z => ∑ p : ι × ι, Φ p.1 p.2 z * M p.2 p.1 := by
    funext z
    simp only [trM, Fintype.sum_prod_type]
  rw [e]
  refine Eq.trans h ?_
  exact Fintype.sum_prod_type _

private theorem part_eq {D : Dom E n 0} {π : CuspSub E n} {U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D}
    (h : IsPiPart D π U Uπ) (f : Hs (ι := ι) D) : Uπ f = U ((piSp D π ι).starProjection f) := by
  have h1 : Uπ ((piSp D π ι).starProjection f) = U ((piSp D π ι).starProjection f) :=
    h.1 _ (Submodule.starProjection_apply_mem _ _)
  have h2 : Uπ (f - (piSp D π ι).starProjection f) = 0 :=
    h.2 _ (Submodule.sub_starProjection_mem_orthogonal _)
  rw [map_sub, sub_eq_zero] at h2
  rw [h2, h1]

private theorem vec_int {D : Dom E n 0} (w : Lp ℂ 2 D.ν) (c : ι → ℂ) (j : ι) {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    (x : H E n 0) :
    ∫ y, kerH φ x y * ((vecM w c) j : H E n 0 → ℂ) y ∂D.ν = c j * ∫ y, kerH φ x y * (w : H E n 0 → ℂ) y ∂D.ν := by
  have e : ((vecM w c) j : H E n 0 → ℂ) =ᵐ[D.ν] fun y => c j * (w : H E n 0 → ℂ) y := by
    have : (vecM w c) j = c j • w := rfl
    rw [this]
    filter_upwards [Lp.coeFn_smul (c j) w] with y hy
    simpa using hy
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [e] with y hy
  rw [hy]; ring

end SlopeTestRemainingChoices

theorem ker_pf :
    Weak → PointRep → PComm → PDiag → Ker := by
  intro hW hPR hPC hPD E _ _ _ n ι _ s m v x
  set w := P0 s.D s.π v with hw
  let u : ι → Hs (ι := ι) s.D := fun i => ContinuousLinearMap.adjoint m.Uπ (s.k₁ x i)
  have hG : ∀ y, (v : H E n 0 → ℂ) y * m.G x (th y) =
      ∑ i, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) := by
    intro y
    simp only [Mid.G, Gk, Finset.mul_sum, u, ContinuousLinearMap.adjoint_inner_left]
  have hI : ∀ i, Integrable (fun y => (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i)) s.D.ν :=
    fun i => (hW E n ι s v (u i) i).1
  have hterm : ∀ i, ∫ y, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) ∂s.D.ν =
      ∑ j, s.M j i * ∫ y, kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y ∂s.D.ν := by
    intro i
    rw [(hW E n ι s v (u i) i).2]
    have e1 : inner ℂ (u i) (s.T₂ (vecM v fun l => s.M l i)) =
        inner ℂ (s.k₁ x i) (m.U (s.T₂ (vecM w fun l => s.M l i))) := by
      simp only [u, ContinuousLinearMap.adjoint_inner_left]
      rw [part_eq m.pp, hPC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂, hPD E n s.D s.π ι]
    rw [e1, hPR E n ι s m.Φ (s.T₁ * m.U * s.T₂) m.t m.o (m.U (s.T₂ (vecM w fun l => s.M l i)))
      (vecM w fun l => s.M l i) rfl x i]
    exact Finset.sum_congr rfl fun j _ => vec_int w _ j (m.t i j) x
  refine ⟨?_, ?_⟩
  · simp only [hG]
    exact integrable_finset_sum _ fun i _ => hI i
  · simp only [hG]
    rw [integral_finset_sum _ fun i _ => hI i]
    simp only [hterm]
    have e2 : ∀ y, kerH m.φ x y * (w : H E n 0 → ℂ) y =
        ∑ i, ∑ j, s.M j i * (kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) := by
      intro y
      rw [Mid.φ, ker_trM s.D m.t, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2]
    have hr : ∀ i j, Integrable (fun y => kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) s.D.ν :=
      fun i j => row_int s.D (m.t i j) w x
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hr i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (hr i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
