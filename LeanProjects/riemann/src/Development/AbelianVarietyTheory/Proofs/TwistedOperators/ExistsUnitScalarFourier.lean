import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumVectorMovedPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticesSelfDualMovedPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntireStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartZeroNeOfIsVacuumOrientedModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomialStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalPair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyAtOriginMinorProductLinear
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedKappa

theorem fock_jets_moved : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt →
    ∀ f, IsVacO ψ θ S T sS sT (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f →
    ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt ∧ Θ ≠ 0 ∧
      ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ))
        (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 =
        (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  intro D ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ Ls Lt hLs hLt f hf
  have hsS := GlobalTheory.FockPos.cart_one frS hS hcS
  have hsT := GlobalTheory.FockPos.cart_one frT hT hcT
  subst hsS hsT
  obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf
  have hTh := GlobalTheory.T.unitVacuumEntireFactor_isTheta_movedLattices ψ θ S T frS frT hS hT δ hC hδ Ls Lt hLs hLt f hf Φ hΦd hreal
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ = fun Y => Φ (δ⁻¹ • Y) := ⟨_, rfl⟩
  rw [← hΘ] at hTh
  have hΦeq : Φ = fun z => Θ (δ • z) := by
    funext z
    simp only [hΘ, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  refine ⟨Θ, hTh, ?_, fun k => ?_⟩
  · intro h0
    obtain ⟨w, hw, hfw⟩ := GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel ψ θ S T _ _ _ _ f hf
    apply hfw
    have h1 : Φ (GlobalTheory.FockPos.zCo θ frS frT w) = 0 := by
      rw [hΦeq]
      exact congrFun h0 _
    rw [hreal w hw, h1, mul_zero]
  · have hdiff : Differentiable ℂ Θ := hTh.1
    have hj := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hf.2.inf hS hT f Φ hΦd hreal k
    change pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f
      (MvPolynomial.monomial k 1) 0 = _
    rw [hj, hΦeq, GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial',
      GlobalTheory.FockPos.taylor_comp_smul' D _ hdiff]
    have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ =
        δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
      intro τ
      rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
    have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
        (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
      simp only [hper, Finsupp.prod, Finsupp.sum]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    rw [hprod, mul_pow]
    ring

theorem applyAt0_const_mul (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) {G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (hG : Differentiable ℂ G) (a : ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (fun z => a * G z) =
      a * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G := by
  rw [GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.FockPos.applyAt0_monomial', GlobalTheory.ProdThetaConj.taylor_const_mul hG]
  ring

theorem intertwining_mem_ne_zero {D : D7} {δ t0 : ℂ} (hC : Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ)
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D D.host.ccK δ) t0) {N N' : ℕ} {e0 : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (he0 : Formalism.MainNotions.StandardLatticesGL3.oddE0 D D.host.ccK δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : Formalism.MainNotions.StandardLatticesGL3.SD D L) (hL' : Formalism.MainNotions.StandardLatticesGL3.SD D L') {Θ : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ}
    (hΘ : Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') (hΘ0 : Θ ≠ 0) :
    ∃ κ : ℂ, Θ = (fun z => κ * Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0 z) ∧
      Differentiable ℂ (Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0) := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : e0 ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') 0 = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK δ t0 hC ht) hn.symm
  have hK1 : Formalism.MainNotions.StandardLatticesGL3.KLat D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D N, GlobalTheory.NormSum.VacInt.sd_std D N', rfl⟩
  have hK2 : Formalism.MainNotions.StandardLatticesGL3.KLat D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') :=
    Or.inr ⟨L, L', hL, hL', rfl⟩
  have hne : ∃ z, Θ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΘ0 (funext h)
  have hS := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.semiChar_of_ne_zero _ hΘ hne
  have hI := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Iop_mem_ThSp _ hS he0.1
  have hI0 : Formalism.MainNotions.TaylorLogMetric.Iop D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ)
      (Formalism.MainNotions.StandardLatticesGL3.La0 D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) L L') e0 ≠ 0 := by
    intro h0
    obtain ⟨-, -, hself, htrip⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK δ hC N N'
    obtain ⟨μ, hμ⟩ := htrip _ _ _ hK1 hK2 hK1 e0 he0.1 he0ne
    have h1 := hμ.2.2.2.2.2.2.2.2.2
    have hμ8 := hμ.2.2.2.2.2.2.2.2.1
    rw [h0, GlobalTheory.NormSum.VacMove.iop_zero, hself _ hK1 e0 he0.1] at h1
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      norm_num at hμ8
    apply he0ne
    funext z
    have := congrFun h1 z
    simp only [Pi.zero_apply] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hμ0
  obtain ⟨c, hc⟩ := (GlobalTheory.ThetaLine.theta_line D hG D.host.ccK δ hC N N' _ hK2).1 Θ hΘ _ hI hI0
  exact ⟨c, hc, hI.1⟩

theorem fock_jets_moved_vacuum : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y
  have hC := ch.S.Z.crv
  have hδ : ch.S.Z.δ ≠ 0 := GlobalTheory.InertSign.delta_ne_zero hC
  have he0 := ch.S.Z.e0_is p hp
  have hsd := GlobalTheory.T.lattices_self_dual_moved_pair hP hI ch hch p hp x y
  have hvac := GlobalTheory.T.vacuum_vector_moved_pair hP hI ch hch p hp x y
  have hc0 : (ch.S.Z.c0 p : ℂ) ≠ 0 := Units.ne_zero _
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hconj := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac
    obtain ⟨Θ, hΘ, hΘ0, hjet⟩ := fock_jets_moved ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.fr (.grid (i + 1) D.R.m)) (ch.S.N.fr (.grid i D.R.m))
      (ch.S.N.fr_on _ ⟨hi, rfl⟩) (ch.S.N.fr_on _ ⟨by omega, rfl⟩)
      (ch.W.cart_is _ ⟨hi, le_rfl⟩) (ch.W.cart_is _ ⟨by omega, le_rfl⟩) ch.S.Z.δ hC hδ _ _ hsd.1 hsd.2 _ hconj
    obtain ⟨κ, hκ, hd⟩ := intertwining_mem_ne_zero hC ch.S.Z.pt0 he0 hsd.1 hsd.2 hΘ hΘ0
    refine ⟨κ / starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ), fun k => ?_⟩
    have h2 := fun f => GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m))
      (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std ch.W.θ_is k 0
    show pureTensorO _ _ _ _ _ _ _ _ _ _ 0 = _
    rw [h2]
    have hj := hjet k
    erw [hj]
    rw [hκ, applyAt0_const_mul D _ hd, applyAt0_const_mul D _ hd]
    show starRingEnd ℂ _ = _ * starRingEnd ℂ _
    simp only [map_mul, map_div₀, Complex.conj_conj]
    have hc0' : starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ) ≠ 0 := (map_ne_zero _).2 hc0
    field_simp
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have hj1 : j + 1 ≤ D.R.m := hp
    obtain ⟨Θ, hΘ, hΘ0, hjet⟩ := fock_jets_moved ch.W.ψ ch.W.θ (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))
      (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) (ch.S.N.fr (.top j)) (ch.S.N.fr (.top (j + 1)))
      (ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)) (ch.S.N.fr_on (.top (j + 1)) hj1)
      (ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)) (ch.W.cart_is (.top (j + 1)) hj1) ch.S.Z.δ hC hδ _ _ hsd.1 hsd.2 _ hvac
    obtain ⟨κ, hκ, hd⟩ := intertwining_mem_ne_zero hC ch.S.Z.pt0 he0 hsd.1 hsd.2 hΘ hΘ0
    refine ⟨κ / (ch.S.Z.c0 (.top t j) : ℂ), fun k => ?_⟩
    show pureTensorO _ _ _ _ _ _ _ _ _ _ 0 = _
    erw [hjet k]
    rw [hκ, applyAt0_const_mul D _ hd, applyAt0_const_mul D _ hd]
    show _ = _ * RingHom.id ℂ _
    rw [RingHom.id_apply]
    field_simp

end GlobalTheory.MovedKappa
