import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupRepresentationTwist
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpanMKEqTopStatement

set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.DefRead
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
set_option maxHeartbeats 1000000 in
theorem point_read_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : _root_.GlobalTheory.CovTop.RowsTAlt p) (hg : GramAt p i)
    (hfree : ∀ k : Fin 2, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction (GlobalTheory.BadCount.Inh.halfH D k) X)
      (A : X → Submodule ℂ (VAt p i)),
      (∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
      ∀ (h : GlobalTheory.BadCount.Inh.halfH D k) (y : X), ∀ v ∈ A y, repAt p i (h : G0g D.nd) v ∈ A (h • y)) :
    ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (π : Γ →* G0g D.nd) (s : G0g D.nd →* Γ) (ρ : Representation ℂ Γ V) (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ)
      (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ)
      (H : Fin 2 → Subgroup (G0g D.nd)), IsSplit π s ∧ IsWhit D Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧
      (∀ k, IsHalf D k (H k)) ∧ (∀ k, ∃ (X : Type) (_ : Fintype X) (_ : DecidableEq X) (_ : MulAction ((H k).comap π) X)
        (A : X → Submodule ℂ V), (∀ (h : (H k).comap π) (y : X), h • y = y → h = 1) ∧ DirectSum.IsInternal A ∧
        ∀ (h : (H k).comap π) (y : X), ∀ v ∈ A y, ρ (h : Γ) v ∈ A (h • y)) ∧
      Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧
      Formalism.HN.rkK (latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g D.nd) V) D.ntypes.e0) : Submodule ℂ V) := by
  classical
  obtain ⟨lam, ψ, hW, hlam, -⟩ := _root_.GlobalTheory.ShareOn.isWhit_and_eq_embLL_inv_and_halfUnip D L hT Gi Gl Kc Y0 cX ex Csz p hp.1
  have hfin : Finite (G0g D.nd) := Finite.of_equiv _ (p.R.eG.trans p.cG).toEquiv
  let e := p.R.eG.trans p.cG
  let Pb := p.P.P0.map e.toMonoidHom
  let lamb : Pb.comap (MonoidHom.id (G0g D.nd)) →* ℂˣ :=
    lam.comp (MulEquiv.subgroupCongr (Subgroup.comap_id Pb)).toMonoidHom
  have hEig : eig (repAt p i) (Pb.comap (MonoidHom.id (G0g D.nd))) lamb =
      eig (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi) (p.F.lv2.lvl false).P
        ((Units.map D.what₂.embLL.toMonoidHom).comp (p.F.lv2.lvl false).ψ⁻¹) := by
    ext v
    rw [mem_eig, mem_eig]
    constructor
    · intro h g
      have hm : e g ∈ Pb := ⟨g, g.2, rfl⟩
      have := h ⟨e g, hm⟩
      rw [repAt_apply] at this
      simp only [e, MulEquiv.symm_apply_apply] at this
      rw [this]
      congr 2
      exact Units.ext (hlam g hm)
    · intro h γ
      obtain ⟨g, hg, hge⟩ := γ.2
      have := h ⟨g, hg⟩
      rw [repAt_apply]
      have h1 : (p.R.eG.trans p.cG).symm (γ : G0g D.nd) = g := by
        rw [MulEquiv.symm_apply_eq]; exact hge.symm
      rw [h1, this]
      congr 2
      apply Units.ext
      have h2 := hlam ⟨g, hg⟩ ⟨g, hg, rfl⟩
      have h3 : lamb γ = lam ⟨e g, ⟨g, hg, rfl⟩⟩ := by
        show lam ⟨(γ : G0g D.nd), _⟩ = _
        congr 1
        exact Subtype.ext hge.symm
      rw [h3, h2]
      rfl
  refine ⟨G0g D.nd, inferInstance, hfin, VAt p i, inferInstance, inferInstance, inferInstance, MonoidHom.id _, MonoidHom.id _,
    repAt p i, Pb, lam, ψ, lamb, GlobalTheory.BadCount.Inh.halfH D, ⟨fun g => rfl, fun g γ hγ => ?_⟩, hW, fun γ => rfl,
    fun k => GlobalTheory.BadCount.Inh.isHalf_halfH D k, fun k => ?_, ?_, ?_⟩
  · have : γ = 1 := hγ
    subst this; simp
  · obtain ⟨X, hX, hXd, hact, A, hf, hA, hc⟩ := hfree k
    let f : (GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd)) →* GlobalTheory.BadCount.Inh.halfH D k :=
      { toFun := fun h => ⟨h.1, h.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    letI : MulAction ((GlobalTheory.BadCount.Inh.halfH D k).comap (MonoidHom.id (G0g D.nd))) X := MulAction.compHom X f
    refine ⟨X, hX, hXd, this, A, fun h y hy => ?_, hA, fun h y v hv => hc (f h) y v hv⟩
    have := hf (f h) y hy
    exact Subtype.ext (congrArg Subtype.val this)
  · have hC := _root_.GlobalTheory.T.gram_MK_spans_of_gramAt p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _) = _
    rw [hB.1, typeSubspace_eq_iInf_ker, hA.1, hEig]
  · have hC := _root_.GlobalTheory.T.gram_MK_spans_of_gramAt p i hp hg
    have hB := GlobalTheory.T.arithmetic_forms_span_invariant D.what₂.LL p.T.Q.c.F (p.R.nW i) _ p.P.Gp (p.R.toRealDat.FW i) (p.F.lv2.lvl false).P
      (p.F.lv2.lvl false).ψ⁻¹ (eGood p.R.toRealDat i) hC
    have hA := GlobalTheory.T.finrank_characterEigenspace_twistedComplexification D.what₂.LL (Fin (p.R.nW i) → D.what₂.LL) p.P.Gp D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi
      (p.F.lv2.lvl false).P (p.F.lv2.lvl false).ψ⁻¹ (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    obtain ⟨-, -, -, hc, -, -⟩ := p.grpRecPin
    have hsum : ∀ x : MonoidAlgebra ℂ (G0g D.nd), x = ∑ h, MonoidAlgebra.single h (x.coeff h) := fun x =>
      MonoidAlgebra.ext (by
        rw [MonoidAlgebra.coeff_sum]
        simp only [MonoidAlgebra.coeff_single]
        exact (Finsupp.univ_sum_single _).symm)
    have he0 : D.ntypes.e0 = ∑ g : p.P.Gp,
        MonoidAlgebra.single (e g) (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)) := by
      rw [hsum D.ntypes.e0, ← Equiv.sum_comp e.toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hc g]
      rfl
    have hK : Representation.asAlgebraHom ((repAt p i).comp (MonoidHom.id (G0g D.nd))) D.ntypes.e0 =
        Representation.asAlgebraHom (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi)
          (∑ g, MonoidAlgebra.single g (D.what₂.embLL ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g))) := by
      rw [he0, map_sum, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Representation.asAlgebraHom_single, Representation.asAlgebraHom_single]
      have hee : (p.R.eG.trans p.cG).symm (e g) = g := MulEquiv.symm_apply_apply _ _
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, repAt_apply, hee]
    show Formalism.HN.rkK ((p.R.toRealDat.FW i).Mall _ _ ⊓ (LinearMap.ker (eGood p.R.toRealDat i)).restrictScalars _) = _
    have hEG : eGood p.R.toRealDat i = ∑ g, ((Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g *
        (((p.R.toRealDat.FW i).chi g)⁻¹ : D.what₂.LLˣ)) • (p.R.toRealDat.FW i).ρ g := by
      unfold eGood Formalism.IndefR.Arith.FormsL.eOp; rfl
    rw [hB.2, typeSubspace_eq_iInf_ker, hEG, hA.2]
    rw [hEig, hK]
end GlobalTheory.DefRead
namespace GlobalTheory.DefRead
end GlobalTheory.DefRead
end
