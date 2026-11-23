import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumVectorMovedPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMovedLatticeAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumVectorMovedPairStatement

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
namespace GlobalTheory.MovedDict
theorem moved_vacuum_isVacuumIntegral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  have hn := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  set gh := ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
    ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) with hgh
  have mem : gh.1 ∈ GfC (ch.G.pS p) ∧ gh.2 ∈ GfC (ch.G.pT p) := by
    rw [hgh]
    cases p with
    | chi i j => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | mu t i j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
    | core i => exact ⟨negMem _ (y * ch.S.N.u _).2, (x * ch.S.N.u _).2⟩
    | top t j => exact ⟨(x * ch.S.N.u _).2, (y * ch.S.N.u _).2⟩
  obtain ⟨hstd, hv⟩ := ch.S.Z.vac_is p hp
  have hact := (_root_.GlobalTheory.T.twisted_moved_lattice_action hPr hInp ch hIs p hp x y).2
  have hth' := hom.om_pres gh _ hv.theta
  have hgh' : gh = (gh.1, gh.2) := rfl
  refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩, fock := fun τ z => ?_, norm := ⟨hv.norm.1, fun q hq => ?_⟩ }⟩
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    have h2 : actO _ _ gh.1 gh.2 u + actO _ _ gh.1 gh.2 u = actO _ _ gh.1 gh.2 (u + u) := by
      simp only [actO, Matrix.mul_add, Matrix.add_mul]
    have h3 := hv.lat.1 u hu
    rw [two_nsmul] at h3 ⊢
    rw [h2, hgh', ← hom.om_heis gh.1 gh.2 _ _ hv.theta, h3]
  · obtain ⟨u, hu, rfl⟩ := hact u' hu'
    rw [hgh', ← hom.om_heis gh.1 gh.2 u _ hv.theta, hv.lat.2 e he u hu (GlobalTheory.MovedVac.halfBack D _ _ gh.1 gh.2 e u hhalf)]
  · have hθ := ch.W.θ_is
    have e : ∀ z', Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.W.om p gh (ch.S.Z.vac p)) =
        ch.W.om p gh (Formalism.IndefR.Datum.dRho (heisO ch.W.ψ _ _) ch.W.θ τ z' (ch.S.Z.vac p)) := by
      intro z'
      rw [hgh', GlobalTheory.OrientedHeis.om_dRho hom hθ gh.1 gh.2 τ z' hv.theta, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ mem.2,
        GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC ch.W.θ _ (inv_mem mem.1), Matrix.one_mul, Matrix.mul_one]
    have h0 := hv.fock τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add, h0, map_zero]
  · show nrm2 q.1 q.2 (ch.W.om p gh (ch.S.Z.vac p)) = 1
    have hU := hom.om_unit q.1 q.2 hq.1 hq.2.1 gh _ hv.theta
    haveI : OpensMeasurableSpace (WO (ch.G.pS p) (ch.G.pT p)) := ⟨le_rfl⟩
    have key : ∀ F : WO (ch.G.pS p) (ch.G.pT p) → ℂ, Continuous F → nrm2 q.1 q.2 F = (∫⁻ w in q.2, ‖F w‖ₑ ^ 2 ∂q.1).toReal := by
      intro F hF
      unfold nrm2
      have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
        (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
      congr 1
      refine MeasureTheory.lintegral_congr fun w => ?_
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [key _ hth'.cont, hU, ← key _ hv.theta.cont]
    exact hv.norm.2 q hq
end GlobalTheory.MovedDict
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
theorem _root_.GlobalTheory.T.twisted_moved_vacuum_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | exact _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral | (intros; apply _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral <;> assumption)
end
