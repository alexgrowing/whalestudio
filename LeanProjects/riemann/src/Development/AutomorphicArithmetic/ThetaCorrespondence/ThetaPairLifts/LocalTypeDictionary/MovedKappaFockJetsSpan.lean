import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourier
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMovedSeriesDecomposition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumIsVacuumIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitScalarFourierStatement

section
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
theorem fock_jets_of_moved_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
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
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hvac := _root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp x y
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
end
end

section
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedKappa_fock_jets_span : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum | exact _root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum | (intros; apply _root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum <;> assumption)
end
