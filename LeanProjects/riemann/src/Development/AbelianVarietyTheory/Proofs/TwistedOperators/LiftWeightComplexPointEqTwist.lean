import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjScalarCoord

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)

theorem wC_cpt (j : Fin D.R.m) (v : InfinitePlace D.what₂.LL) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) •
        (R.FW j).j (sgAt D.what₂.embLL v) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
        R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H) =
      ((∑ k, cj (twAt D.what₂.embLL v) (v.embedding (c k)) •
        (⟨R.toRealDat.bC F.lv2 b j _ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) :
        (R.HW j (sgAt D.what₂.embLL v)).H) := rfl
  rw [e, Submodule.coe_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, emb_eq D.what₂.embLL v, cj_cj, LinearMap.map_smulₛₗ, smul_comm]
  rfl

theorem sqrt_ne : ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F.lv2) b)).ne'

theorem liftWeight_complexPoint_eq_twist (j : Fin D.R.m) (c : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      (R.FW j).j (sg0 D A3.A) (∑ k, c k • R.toRealDat.bL F.lv2 b j k) := by
  have e : (Tw.out (s := twAt D.what₂.embLL A3.A.v0) ((R.toCx3 F).w0C b j (cpt A3.A.v0.embedding c)) : (R.HW j (sg0 D A3.A)).H) =
      ((Real.sqrt (RealDat.nP F.lv2 b) : ℝ) : ℂ) • ((Tw.out (s := twAt D.what₂.embLL A3.A.v0)
        ((R.toCx3 F).wC b j A3.A.v0 (cpt A3.A.v0.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL A3.A.v0)) : (R.HW j (sgAt D.what₂.embLL A3.A.v0)).H) := rfl
  rw [e, wC_cpt, smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ (sqrt_ne F b), one_smul]

theorem inner_wC (j : Fin D.R.m) {v : InfinitePlace D.what₂.LL} (hv : v ≠ A3.A.v0) (c c' : Fin ((R.toCx3 F).dW b j) → D.what₂.LL) :
    ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      (Nat.card (F.lv2.lvl b).P : ℂ)⁻¹ * ⟪(R.FW j).j v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b j k),
        (R.FW j).j v.embedding (∑ k, c' k • R.toRealDat.bL F.lv2 b j k)⟫_ℂ := by
  have hs : sgAt D.what₂.embLL v = v.embedding := if_neg (R.hv0 ▸ hv)
  have ht : twAt D.what₂.embLL v = false := if_pos hs.symm
  have e : ⟪(R.toCx3 F).wC b j v (cpt v.embedding c), (R.toCx3 F).wC b j v (cpt v.embedding c')⟫_ℂ =
      cj (twAt D.what₂.embLL v) ⟪((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c)) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H),
        ((Tw.out (s := twAt D.what₂.embLL v) ((R.toCx3 F).wC b j v (cpt v.embedding c')) :
          R.toRealDat.WS F.lv2 b j (sgAt D.what₂.embLL v)) : (R.HW j (sgAt D.what₂.embLL v)).H)⟫_ℂ := rfl
  rw [e, wC_cpt, wC_cpt, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (RealDat.nP_pos (F := F.lv2) b).le, hs]
  generalize twAt D.what₂.embLL v = s at ht
  subst ht
  simp only [cj, RealDat.nP, Bool.false_eq_true, if_false]
  simp only [cond_false, RingHom.id_apply, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem tC_cpt (cr : Crd A3.fam3.amb3 F.fc) (j : Fin D.R.m) (t : T0)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) b).dZ j t) → D.what₂.LL) :
    (R.toCx3 F).tC cr b j t (cpt A3.fam3.base3.v0.embedding x) =
      (R.toCx3 F).θ' j t ((R.toCx3 F).jL j t (cr.toL (R.toCx3 F).zs b j t x)) := by
  conv_rhs => rw [← (Pi.basisFun D.what₂.LL _).sum_repr x]
  simp only [CxData.tC, lin_apply, map_sum, map_smul, LinearMap.map_smulₛₗ, Pi.basisFun_repr, Pi.basisFun_apply, cpt,
    RingHom.id_apply]

theorem liftMat_isRatLift_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).H5 F.cr false → (R.toCx3 F).RATth F.cr false → ∀ i, (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsRatLift R.toRealDat i (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) (F.cr.toL (R.toCx3 F).zs false i A3.A.μ0 x) (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k)) ∧ ∀ v, v ≠ A3.A.v0 → ∀ x y, ⟪(R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x)), (R.toCx3 F).wC false i v (cpt v.embedding (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y))⟫_ℂ = ((Nat.card F.P0 : ℕ) : ℂ)⁻¹ * ⟪(R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec x) k • R.toRealDat.bL F.lv2 false i k), (R.FW i).j v.embedding (∑ k, (((R.toCx3 F).liftMat F.cr false i A3.A.μ0).mulVec y) k • R.toRealDat.bL F.lv2 false i k)⟫_ℂ := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hR i
  refine ⟨fun x => ?_, fun v hv x y => ?_⟩
  · show (R.FW i).j (sg0 D A3.A) _ = _
    refine (liftWeight_complexPoint_eq_twist R F false i _).symm.trans ?_
    have h1 := ((R.toCx3 F).key_lift F.cr false hT hR i A3.A.μ0 x).trans (tC_cpt R F false F.cr i A3.A.μ0 x)
    exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) h1
  · rw [inner_wC R F false i hv]
    rfl

end GlobalTheory.ConjScalarCoord
