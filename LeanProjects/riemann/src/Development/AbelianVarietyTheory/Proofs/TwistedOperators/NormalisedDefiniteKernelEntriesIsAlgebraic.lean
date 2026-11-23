import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockActionDiagonalCoefficientSpaceSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaJetMapWeightedTableScaleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetOperatorBideterminantBasisReprIsAlgebraicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.KernelAlg

open GlobalTheory.ThetaAlgebraic in

theorem coefIn_dict (D : D7) (hI : GlobalTheory.NormSum.Inp D) {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : StandardLatticesGL3.Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0) {N N' : ℕ} (e0 : TaylorLogMetric.VC D N N' → ℂ)
    (he : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t0 (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') e0)
    (Ls : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (κ : ℂ) (hκ : κ ∈ TaylorLogMetric.Qbar) {n : ℕ} (r : Fin n → TaylorLogMetric.Qbar) (s : Fin n → TaylorLogMetric.VC D N N') (k : ℕ) (hk : 0 < k)
    (hs : ∀ i, k • s i ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt) :
    TaylorLogMetric.CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt) e0) z) TaylorLogMetric.Qbar := by
  obtain ⟨b, κ0, hb, hκ0, rfl⟩ := he
  have hG := hI.g1
  have hU := hI.use1
  have hg := ((good_theta hG hU hC hb ht).iop hG hC hb (StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) b) _
    (la_le cc δ hG hb (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).const_mul hκ0.1
  have hg2 := hg.iop hG hC hb (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') _ (la_le cc δ hG hb Ls Lt)
  have hT : ∀ i, Good cc δ b (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt)
        fun z => κ0 * TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) b) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
          (StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) b (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t0)) z)) := fun i =>
    hg2.transl hG hC hb (sat_of_nsmul hk (la_le cc δ hG hb Ls Lt (hs i)))
  exact ((Good.sum Finset.univ _ fun i _ => (hT i).const_mul (r i).2).const_mul hκ).coefIn

theorem applyAt0_monomial_mem (D : D7) {N N' : ℕ} (m : GL3Theta.Idx D N N' →₀ ℕ) {G : TaylorLogMetric.VC D N N' → ℂ}
    (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) G ∈ TaylorLogMetric.Qbar := by
  classical
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ?_ (prod_mem fun _ _ => natCast_mem _ _)) (hG α)
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem opp_isAlgebraic {T : Type} (p : GlobalTheory.ChiGrid.Pair T) {z : ℂ} (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ (opp p z) :=
  IsAlgebraic.algHom (opp p).toRatAlgHom hz

theorem fvar_fst {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (p : GlobalTheory.ChiGrid.Pair T)
    (k : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank) : (fvar G p k).1 = k.1 := by
  cases p <;> rfl

theorem kk_isAlgebraic : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → GlobalTheory.NormSum.Inp D → GlobalTheory.SumSize.DictAt ch → ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → WtOK ch.G p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl ch.G t → ch.S.Z.HasVec d → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (a : VVIdx (wt ch.G p.big)) (b : VVIdx (wt ch.G p.small)), IsAlgebraic ℚ (ch.S.Z.kk d x y a b) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch hch hInp hDict t p hp hW k d hk hcos hz hP hV x y a b
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, -, -, -, hJ⟩ := hDict t p hp k d hk hcos hz hP x y
  set Z := ch.S.Z
  have hF := coefIn_dict D hInp Z.crv Z.pt0 (Z.e0 p) (Z.e0_is p hp).2.2.2.1 Ls Lt κ hκ.1 r s k hk hs
  set FF := (fun z => κ * ∑ i, ((r i : TaylorLogMetric.Qbar) : ℂ) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) _ _)
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) Ls Lt) (Z.e0 p)) z) with hFF
  set J2 : (DVar D.what₂.Tau (ch.G.V p.small).rank (ch.G.V p.big).rank →₀ ℕ) → ℂ := fun m =>
    opp p (GL3Theta.applyAt0 D (MvPolynomial.monomial (m.mapDomain (fvar ch.G p)) 1) FF) with hJ2
  have hA : ∀ m, IsAlgebraic ℚ (J2 m) := fun m =>
    opp_isAlgebraic p (mem_algebraicClosure_iff.1 (applyAt0_monomial_mem D _ hF))
  set c : D.what₂.Tau → ℂ := fun τ => opp p (period Z.δ τ) with hc
  have hJf : jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _) =
      fun m => (Z.c0 p : ℂ) * ((m.prod fun k e => c k.1 ^ e) * J2 m) := by
    funext m
    rw [hJ m, map_mul]
    congr 2
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), map_finsuppProd]
    simp only [map_pow, fvar_fst, hc]
  have hop : ∀ P : Formalism.L2.DIV.VV ℂ (wt ch.G p.small),
      jetOp (wt ch.G p.small) (wt ch.G p.big) (jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _))
        (nuEnd ch.G p) P = ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) • jetOp _ _ J2 (nuEnd ch.G p) P := by
    intro P
    rw [hJf]
    simp only [jetOp, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [GlobalTheory.T.thetaJetMap_weighted_table_scale, GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul _ _ _ (hW.2 J2 P.1 P.2), smul_smul, map_smul]
    rfl
  simp only [Normal.kk, Normal.kkIn, Normal.kkMap, LinearMap.toMatrix_apply, LinearMap.smul_apply, fockComp]
  rw [hop, map_smul, map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  have hR := GlobalTheory.T.jetOperator_bideterminantBasis_repr_isAlgebraic _ _ J2 (nuEnd ch.G p) hA hW.2 a b
  have e : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) =
      ∏ τ, opp p ((1 / period Z.δ τ) * period Z.δ τ) ^ fockDeg ch.G p τ := by
    simp only [Normal.scal, Pi.one_apply, hc, map_mul, mul_pow, Finset.prod_mul_distrib]
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  have hK : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) ∈ TaylorLogMetric.Qbar := by
    rw [e]
    refine prod_mem fun τ _ => pow_mem ?_ _
    rw [mem_algebraicClosure_iff]
    apply opp_isAlgebraic
    by_cases h : period Z.δ τ = 0
    · simp [h, isAlgebraic_zero]
    · simp [h, isAlgebraic_one]
  rw [← mul_assoc, ← mem_algebraicClosure_iff]
  exact mul_mem hK (mem_algebraicClosure_iff.2 hR)

end GlobalTheory.KernelAlg
