import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionsIndependentOnClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProjZeroPullbackNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ThetaFibre

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem proj_mulVec_mem (hB : BaseFacts S M U₀ EE) (z : M.Z) {v : S.J → Ω} (hv : v ∈ EE.E z) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v ∈ EE.E z := by
  have hT : S.TT M z ≤ S.HH M z := (hB.free z).2 ▸ (hB.free z).1.1
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have := Fintype.ofFinite (S.TT M z)
  have e : ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v =
      algebraMap o (M.O z) (Ring.inverse (Nat.card (S.TT M z) : o)) •
        ∑ t : S.TT M z, ((S.ρ t).map (algebraMap o Ω)).mulVec v := by
    ext i
    simp [ThetaSys.proj, finsum_eq_sum_of_fintype, Matrix.mulVec, dotProduct, Matrix.sum_apply,
      Algebra.smul_def (A := Ω), Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun t _ => hB.stab z _ (hT t.2) v hv)

theorem proj_mulVec_regular (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {v : S.J → Ω} (hv : v ∈ EE.E z) (j : S.J) :
    ((S.proj (S.TT M z) 0).map (algebraMap o Ω)).mulVec v j ∈ M.O z := by
  refine hB.zero z hz _ (proj_mulVec_mem hB z hv) ?_ j
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
    GlobalTheory.ThetaBound.proj_mul_proj S _ _ le_rfl (hB.free z).1.1 (hB.free z).1 0 0 fun _ => rfl]

theorem proj_col_eq_zero (hB : BaseFacts S M U₀ EE) {z : M.Z} (hz : IsClosed ({z} : Set M.Z))
    {K : Type} [Field K] (y : M.O z →+* K) (B : Matrix S.J S.J Ω) (hBm : ∀ k, B k ∈ EE.E z)
    (a : S.J → M.O z) (i : S.J) (ha : ∀ j, ∑ k, (a k : Ω) * B k j = (1 : Matrix S.J S.J Ω) i j)
    (h0 : ∀ k, y (a k) = 0) (j : S.J) :
    y (algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i)) = 0 := by
  have e : algebraMap o (M.O z) (S.proj (S.TT M z) 0 j i) =
      ∑ k, a k * ⟨_, proj_mulVec_regular hB hz (hBm k) j⟩ := by
    apply Subtype.ext
    have h1 : ∑ m, algebraMap o Ω (S.proj (S.TT M z) 0 j m) * (1 : Matrix S.J S.J Ω) i m =
        algebraMap o Ω (S.proj (S.TT M z) 0 j i) := by
      simp [Matrix.one_apply]
    simp only [Subalgebra.coe_algebraMap, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_mul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
    rw [← h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_mul, h0, zero_mul]

theorem exists_mem_nonzeroLocus_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ x ∈ nonzeroLocus (Q.st ρ.i₀), x ∈ Q.G ∧ Q.P.hom x = z := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q hbig hgeo z hz
  by_contra hne
  have hzc : z ∈ ⨆ l, Q.W l := by rw [Q.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hzc
  obtain ⟨K, _, x, hx, hind⟩ := GlobalTheory.T.thetaSections_independent_on_closed_fibre hL o Ω S ρ M U₀ EE hB Q hbig hgeo l z hl hz
  have hc : (fun k => valF x (Q.W l) (Q.c l ρ.i₀ k)) = 0 := by
    refine hind _ fun g j hg hgx => ?_
    by_cases hj : ⊤ ≤ g ⁻¹ᵁ (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι).U j
    · have hw : Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) g
          (fun i => valF g _ ((Q.σ l i).f j)) :=
        ⟨j, 1, hj, fun i => by rw [Units.val_one, _root_.one_mul]; rfl⟩
      have hr := Q.rel l K g _ hw
      rw [hgx] at hr
      by_contra h0
      have hu := (CrdCalc.crd_isUnit_iff ρ.i₀ hr).1 (isUnit_iff_ne_zero.2 h0)
      refine hne ⟨(g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (IsLocalRing.closedPoint K), hu (Set.mem_univ _),
        hg ⟨_, rfl⟩, ?_⟩
      have hm : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rw [hx] at hm
      rw [← hgx] at hm
      exact hm
    · exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_right _ (dif_neg hj)
  obtain ⟨j, hj⟩ := GlobalTheory.proj_zero_pullback_ne_zero hL o Ω S ρ K
    ((RatModel.valHom x z hx).comp (algebraMap o (M.O z))) _ (hB.free z).1
  refine hj (proj_col_eq_zero hB hz (RatModel.valHom x z hx) (Q.B l)
    (fun k => by rw [Q.basis l z hl]; exact Submodule.subset_span ⟨k, rfl⟩)
    (fun k => ⟨_, RatModel.valF_mem_O hl (Q.c l ρ.i₀ k)⟩) ρ.i₀
    (fun j => congrFun (congrFun (Q.c_inv l) ρ.i₀) j) (fun k => ?_) j)
  rw [RatModel.valHom_apply, RatModel.val_valF (by rw [hx]; exact Set.singleton_subset_iff.2 hl)]
  exact congrFun hc k

end GlobalTheory.ZH.ThetaFibre
