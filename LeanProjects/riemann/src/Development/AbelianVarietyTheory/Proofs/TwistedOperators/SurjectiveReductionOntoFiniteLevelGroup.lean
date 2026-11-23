import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfLevelOnObjects
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Formalism.L2.SG.AdBridge

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem map_thetaV_eq_one (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) (AF I.F ⊗[I.F] I.E))
    (hM : M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)) = 1) : M.map (thetaV I v) = 1 := by
  letI : Algebra I.F ℂ := v.embedding.toAlgebra
  let evI : Ainf I.F →ₐ[I.F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding v).comp
        (Pi.evalRingHom (fun w : InfinitePlace I.F => w.Completion) v)
      commutes' := fun c => evV_algebraMap I v c }
  let φA : I.E →ₐ[I.F] ℂ := { I.φ v with commutes' := I.φ_over v }
  let θ' := Algebra.TensorProduct.lift evI φA (fun _ _ => Commute.all _ _)
  have key : ∀ z : AF I.F ⊗[I.F] I.E, thetaV I v z =
      θ' (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a x =>
      rw [thetaV_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have e : M.map (thetaV I v) = (M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E))).map θ' := by
    ext i j; simp only [Matrix.map_apply]; exact key _
  rw [e, hM]
  exact Matrix.map_one _ (map_zero θ') (map_one θ')

theorem fst_eq_one_of_bridge (I : AutInst) (e : I.GA ≃ₜ* HAd I) (hB : IsBridge I e) (x : I.GA) (z : HAd I)
    (hz : e x = z) (hx : (hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F) (AlgHom.id I.F I.E)) = 1) :
    x.1 = 1 := by
  funext v
  apply Subtype.ext
  apply Units.ext
  have h1 := (hB x).1 v
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  show uMat (x.1 v) = 1
  rw [h1]
  unfold ofHAInf
  rw [hz]
  rw [map_thetaV_eq_one I v _ hx, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem iota_fst_eq_one {D : D7} (y : GA D (D.sp.Y 0)) (hy : y ∈ GfC (D.sp.Y 0)) :
    (Formalism.IndefR.RationalEmbedding.iota D y).1 = 1 := by
  refine fst_eq_one_of_bridge _ _ (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) _ y
    ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply y) ?_
  have h := congrArg (fun g : GL (Fin (D.sp.Y 0).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    g.val) (MonoidHom.mem_ker.1 hy)
  exact h

theorem castGA_fst {I I' : AutInst} (h : I = I') (x : I.GA) (hx : x.1 = 1) : (castGA h x).1 = 1 := by
  subst h; exact hx

theorem real_one {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (y : GA D (D.sp.Y 0)) (hy : y ∈ GfC (D.sp.Y 0)) : (iotaX X h y).1 = 1 :=
  castGA_fst h.symm _ (iota_fst_eq_one y hy)

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_intAf (U : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hU : ∀ i j, U i j ∈ Formalism.L2.Herm.intAf F E) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hw : ∀ i, w i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) : (U *ᵥ w) i ∈ Formalism.L2.Herm.intAf F E := by
  rw [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hU i j) (hw j)

theorem mem_hatL_iff_of_St {β M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hF : Formalism.L2.DIV.IsFrame β Λ) (hM : M ∈ Formalism.L2.DIV.St β) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨u, rfl⟩ := hM
  have hint : ∀ v : GL (Fin n) (Formalism.L2.Herm.intAf F E), ∀ i j,
      (Formalism.L2.DIV.intGL F E n v).val i j ∈ Formalism.L2.Herm.intAf F E :=
    fun v i j => (v.val i j).2
  have e : (β⁻¹).val *ᵥ ((Formalism.L2.DIV.frGL β u).val *ᵥ x) =
      (Formalism.L2.DIV.intGL F E n u).val *ᵥ ((β⁻¹).val *ᵥ x) := by
    have : Formalism.L2.DIV.frGL β u = β * Formalism.L2.DIV.intGL F E n u * β⁻¹ := rfl
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [hF, hF, e]
  constructor
  · intro hw i
    exact mulVec_mem_intAf _ (hint u) _ hw i
  · intro hw i
    have e2 : (β⁻¹).val *ᵥ x = (Formalism.L2.DIV.intGL F E n u⁻¹).val *ᵥ
          ((Formalism.L2.DIV.intGL F E n u).val *ᵥ ((β⁻¹).val *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    rw [e2]
    exact mulVec_mem_intAf _ (hint u⁻¹) _ hw i

end Frame

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix Formalism.L2.SG.AdBridge

theorem ofHAFin_eq (I : AutInst) (z : HAd I) :
    ofHAFin I z = ((hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E))).map
      (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E) := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply]
  induction (hmat I z i j) using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem fmat_eq_of_bridge (I : AutInst) (e : I.GA ≃ₜ* HAd I) (hB : IsBridge I e) (x : I.GA) (z : HAd I)
    (hz : e x = z) : I.fmat x.2 =
      ((hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E))).map
        (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E) := by
  rw [(hB x).2, hz, ofHAFin_eq]

theorem Lv_iff {D : D7} (z : Fin (D.sp.Y 0).rank → D.host.E) :
    z ∈ Formalism.L2.SG.InstExistsPf.Lv D ↔ z ∈ Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 := by
  constructor
  · intro hz
    exact ⟨_, hz, (D.sp.Y 0).frame.equivFun.apply_symm_apply z⟩
  · rintro ⟨w, hw, rfl⟩
    show (D.sp.Y 0).frame.equivFun.symm ((D.sp.Y 0).frame.equivFun w) ∈ (D.sp.Y 0).L0
    simpa using hw

theorem Lf_eq {D : D7} :
    @Eq (Submodule (Formalism.MainNotions.S.IntAf (Formalism.L2.SG.InstExistsPf.instOf D).F (Formalism.L2.SG.InstExistsPf.instOf D).E)
      (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E ⊗[(Formalism.L2.SG.InstExistsPf.instOf D).F]
        Formalism.MainNotions.S.Af (Formalism.L2.SG.InstExistsPf.instOf D).F))
      (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      (Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)) := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext w
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact ⟨z, (Lv_iff z).1 hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, (Lv_iff z).2 hz⟩, rfl⟩

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix Formalism.L2.SG.AdBridge

theorem conj_mem_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β a M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hM : M ∈ Formalism.L2.DIV.St β) :
    a * M * a⁻¹ ∈ Formalism.L2.DIV.St (a * β) := by
  obtain ⟨u, rfl⟩ := hM
  refine ⟨u, ?_⟩
  show a * β * Formalism.L2.DIV.intGL F E n u * (a * β)⁻¹ = a * (β * Formalism.L2.DIV.intGL F E n u * β⁻¹) * a⁻¹
  group

theorem iota_snd_mem_Kset {D : D7} (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (hF : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)) (y : GA D (D.sp.Y 0))
    (hy : finE (D.sp.Y 0) y ∈ Formalism.L2.DIV.St β) :
    (Formalism.IndefR.RationalEmbedding.iota D y).2 ∈ (Formalism.IndefR.RationalEmbedding.inst D).Kset := by
  have hfm := fmat_eq_of_bridge _ _ (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) (Formalism.IndefR.RationalEmbedding.iota D y) y
    ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply y)
  intro x
  show x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
    ((Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D y).2) *ᵥ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
  rw [hfm, Lf_eq]
  exact mem_hatL_iff_of_St hF hy x

theorem castGA_snd_Kset {I I' : AutInst} (h : I = I') (x : I.GA) (hx : x.2 ∈ I.Kset) : (castGA h x).2 ∈ I'.Kset := by
  subst h; exact hx

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

theorem onto : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame γ
  obtain ⟨κ, hκf, hκp, hκr⟩ := GlobalTheory.LevelRowsObj.liftsExist hLev (cG.symm γ)
  set y : GA D (Yc D 0) := t * κ * t⁻¹ with hydef
  have hy : y ∈ GfC (Yc D 0) := (GfC _).mul_mem ((GfC _).mul_mem ht hκf) ((GfC _).inv_mem ht)
  have h1 := real_one X h y hy
  have hy' : (iotaX X h).symm (1, (iotaX X h y).2) = y := by
    rw [← h1]; exact (iotaX X h).symm_apply_apply y
  refine ⟨(iotaX X h y).2, ?_, ?_⟩
  · have hS : finE (Yc D 0) y ∈ Formalism.L2.DIV.St (finE (Yc D 0) t * R.βY 0) := by
      rw [hydef, map_mul, map_mul, map_inv]
      exact conj_mem_St (Formalism.L2.DIV.parLev_St hκp)
    exact castGA_snd_Kset h.symm _ (iota_snd_mem_Kset _ hFrame y hS)
  · have hk : kap X h t (iotaX X h y).2 = κ := by
      unfold kap
      rw [hy']
      show (t⁻¹ * (t * κ * t⁻¹) * t : GA D (Yc D 0)) = κ
      group
    rw [hk, hκr, MulEquiv.apply_symm_apply]

end GlobalTheory.SeeMatchOnto
