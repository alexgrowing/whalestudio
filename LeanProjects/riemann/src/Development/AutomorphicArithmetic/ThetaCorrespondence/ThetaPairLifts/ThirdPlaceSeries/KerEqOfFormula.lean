import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelAtFittedPoints
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ICBaseFactorOfRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaEV0EqICPqStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EV0MemGoodFStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem ker_mulVecLin_eq_U_of_formulaAt {p : PtAt ex Csz} (hp : p.PointConditions') (hD : 0 < (Df p).dQ p.P.A3.fam3.base3.μ0)
    (hPq : Function.Surjective ((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec)
    {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (h : TieAt d a)
    (hI : ∀ u, (∀ i, psiK a.ch i u = 0) → u = 0) (hC : ∀ i j t, a.ch.c i j t ≠ 0)
    (hF : ∃ κ ze, FormulaAt a.ch κ ze) :
    LinearMap.ker (d.V p.P.A3.fam3.base3.μ0).mulVecLin = (Df p).U p.P.A3.fam3.base3.μ0 := by
  obtain ⟨κ, ze, hz, hf⟩ := hF
  have hc : cTot a.ch p.P.A3.fam3.base3.μ0 ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hC i j _
  have hze : D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) ≠ 0 := by
    obtain ⟨n, hn, e⟩ := hz p.P.A3.fam3.base3.μ0
    refine (map_ne_zero _).2 fun z => ?_
    rw [z, zero_pow hn.ne'] at e
    exact zero_ne_one e
  have hinj := (_root_.GlobalTheory.T.iC_iota_mulVec_eq_iC p hp).1
  have key : ∀ y, p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) = 0 ↔
      ((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec y = 0 := by
    intro y
    have e := _root_.GlobalTheory.T.theta_j_ev0_eq_ic_pq p hp p.P.A3.fam3.base3.μ0 y
    change p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) = _ at e
    rw [e]
    constructor
    · intro h0
      have h1 := hinj (h0.trans (map_zero _).symm)
      funext i
      exact p.P.A3.fam3.base3.v0.embedding.injective (by simpa [cpt] using congrFun h1 i)
    · intro h0
      rw [h0]
      have : cpt p.P.A3.fam3.base3.v0.embedding (0 : Fin ((Df p).dQ p.P.A3.fam3.base3.μ0) → D.what₂.LL) = 0 := by
        funext i; simp [cpt]
      rw [this, map_zero]
      rfl
  have hκ : κ ≠ 0 := by
    obtain ⟨y, hy⟩ := hPq (Pi.single ⟨0, hD⟩ 1)
    have hne : p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) ≠ 0 := fun h0 => by
      have h2 := congrFun ((key y).1 h0) ⟨0, hD⟩
      rw [hy] at h2
      simp at h2
    obtain ⟨i, hi⟩ : ∃ i, psiK a.ch i (p.R.Th p.P.A3.fam3.base3.μ0
        (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y))) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (hI _ hall)
    exact FormulaAt.ne_zero ⟨hz, hf⟩ hc (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) hi
  ext y
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, DefSide.U]
  rw [← key y]
  constructor
  · intro h0
    apply hI
    intro i
    have e := hf p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) i
    have hs := h.sums p.P.A3.fam3.base3.μ0 (Or.inl rfl) y i
    have hv : vK a.ch p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) i = 0 :=
      hs.symm.trans (by rw [h0]; exact map_zero _)
    have e2 := e.trans (by rw [hv, mul_zero])
    exact ((mul_eq_zero.1 e2).resolve_left (mul_ne_zero hze hc))
  · intro h0
    funext i
    have e := hf p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) i
    have hs := h.sums p.P.A3.fam3.base3.μ0 (Or.inl rfl) y i
    have hz0 : psiK a.ch i (p.R.Th p.P.A3.fam3.base3.μ0
        (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y))) = 0 := by
      rw [h0]; exact psiK_zero _ _
    rw [hz0, mul_zero, ← hs] at e
    have h3 := (mul_eq_zero.1 e.symm).resolve_left hκ
    exact D.what₂.embLL.injective (by rw [h3]; exact (map_zero _).symm)
theorem leafKernel_of_linK_injK_constK_formula2K : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → LinK → InjK → ConstK → Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafKernel @Comparison₂ := by
  intro hB hS _ hI hC hF
  obtain ⟨CF0, hA⟩ := hS.atPt (hI.and (hC.and hF))
  refine ⟨CF0, fun CF hCF => (hA CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => _root_.GlobalTheory.BigTop.Fun.evPt_mono e fun x hx i p hp b d hd => ?_⟩⟩
  obtain ⟨-, a, ha⟩ := hd
  obtain ⟨q1, q2, q3⟩ := b d.G d.W d.n a ha.ok
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have h0 : 0 < (p.S false).D := hR ▸ R0.D_pos
  have v : d.O.vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  show LinearMap.ker (d.O.vmu _).mulVecLin = _
  rw [v]
  exact _root_.GlobalTheory.BigTop.Fun.ker_mulVecLin_eq_U_of_formulaAt hp h0 (wf.Pq_surj _) d a ha q1 (fun i j t => (q2 i j t).2) (q3 ha.ok.field)
end GlobalTheory.BigTop.Fun
end
end
