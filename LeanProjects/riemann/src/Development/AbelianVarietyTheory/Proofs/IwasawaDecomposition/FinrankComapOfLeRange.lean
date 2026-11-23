import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch

noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.RowIso

theorem finrank_eq_of_semi {σ : ℂ →+* ℂ} (hσ : Function.Bijective σ) {E F : Type} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : E →ₛₗ[σ] F) (hf : Function.Bijective f) :
    Module.finrank ℂ E = Module.finrank ℂ F := by
  unfold Module.finrank
  congr 1
  exact rank_eq_of_equiv_equiv σ (AddEquiv.ofBijective f.toAddMonoidHom hf) hσ (fun r m => f.map_smulₛₗ r m)

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  have hσ : Function.Bijective (cj s) := Function.Involutive.bijective (cj_cj s)
  let f : (Tw.sub s V) →ₛₗ[cj s] V :=
    { toFun := fun x => ⟨Tw.out x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact finrank_eq_of_semi hσ f ⟨fun x y h => Subtype.ext (congrArg Subtype.val h), fun y => ⟨⟨Tw.mk s y.1, y.2⟩, rfl⟩⟩

theorem finrank_comap_of_le_range {E F : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E →ₗ[ℂ] F) (he : Function.Injective e) (V : Submodule ℂ F) (hV : V ≤ LinearMap.range e) :
    Module.finrank ℂ (V.comap e) = Module.finrank ℂ V := by
  have h := (Submodule.equivMapOfInjective e he (V.comap e)).finrank_eq
  rwa [Submodule.map_comap_eq_self hV] at h

theorem finrank_EEC {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) :
    Module.finrank ℂ (EEC St Gd) = Module.finrank ℂ (goodSub St Gd) := by
  let f : EEC St Gd →ₛₗ[starRingEnd ℂ] goodSub St Gd :=
    { toFun := fun x => ⟨star (x : L2X St), (mem_EEC St Gd _).1 x.2⟩
      map_add' := fun x y => Subtype.ext ((conjL (muX St)).map_add _ _)
      map_smul' := fun c x => Subtype.ext ((conjL (muX St)).map_smulₛₗ c _) }
  refine finrank_eq_of_semi (Function.Involutive.bijective (fun z => Complex.conj_conj z)) f ⟨fun x y h => ?_, fun y => ?_⟩
  · exact Subtype.ext (star_injective (congrArg Subtype.val h))
  · refine ⟨⟨star (y : L2X St), ?_⟩, Subtype.ext (star_star _)⟩
    rw [mem_EEC, star_star]
    exact y.2

theorem finrank_of_evalTieT {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {M : DSModel (D.sp.Y 0) S}
    {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))} {E : Submodule ℂ (MMap M)}
    {St : Formalism.L2.SG.HidaSetting.HidaSetting D} {Gd : GoodOp St} {ι : GA D (D.sp.Y 0) ≃* St.B.I.GA} {t : GA D (D.sp.Y 0)} {c : ℝ}
    (hE : EvalTieT M μ 𝓕 E St Gd ι t c) : Module.finrank ℂ (goodSub St Gd) = Module.finrank ℂ E := by
  obtain ⟨_, _, j, _⟩ := hE
  rw [← finrank_EEC, ← j.finrank_eq]

theorem clauses {D : D7} {St : Formalism.L2.SG.HidaSetting.HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : St.LevelSubgroupCharacter) (Gd : GoodOp St) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (Sp : SPer Dc) (hSp : Sp = spOf s Dc hK Gd wdD pw bR)
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) (n : ℝ)
    (sEE : E →ₗ⋆[ℂ] Sp.HH) (sEEc : E →ₗ⋆[ℂ] Tw s (HHX St)) (h : HEq sEE sEEc)
    (h1 : ∀ e ∈ V, n * ‖sEEc e‖ ^ 2 = ‖e‖ ^ 2)
    (h2 : ∀ e ∈ V, ((Tw.out (s := s) (sEEc e) : HHX St) : L2X St) ∈ goodSub St Gd)
    (h3 : Module.finrank ℂ (goodSub St Gd) = Module.finrank ℂ V) :
    (∀ e ∈ V, n * ‖sEE e‖ ^ 2 = ‖e‖ ^ 2) ∧ (∀ e ∈ V, sEE e ∈ Sp.Rw) ∧
      Module.finrank ℂ Sp.Rw = Module.finrank ℂ V := by
  subst hSp
  obtain rfl := eq_of_heq h
  refine ⟨h1, h2, ?_⟩
  rw [← h3]
  refine (finrank_twSub s ((goodSub St Gd).comap (HHX St).subtype)).trans ?_
  refine finrank_comap_of_le_range _ Subtype.val_injective _ ?_
  rw [Submodule.range_subtype]
  exact inf_le_left

theorem seeIso : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.toRealDat.models_HE → (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) ≤ R.toRealDat.EEat R.triv → ∀ (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter) (wdD : (F.Dc (R.toCx3 F).zs).Mem → D.what₂.Word) (pw : ∀ x, PerW St hK (wdD x)) (bR : ∀ x, Fin ((F.Dc (R.toCx3 F).zs).a x) → (D.mem (wdD x)).A.Mram), F.Sp (R.toCx3 F).zs = spOf (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR → ∀ (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ), 0 < c → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd ι t c → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ), HEq sEE sEEc → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) ∧ RealDat.nP F.lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2) → (R.toCx3 F).SEEIso sEE := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hHE hle St Gd hK wdD pw bR hSp ι t c _ hE sEE sEEc κS hh hS
  refine clauses (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD pw bR (F.Sp (R.toCx3 F).zs) hSp
    ((R.toCx3 F).EEl true) ((R.toCx3 F).nP true) sEE sEEc hh (fun e he => (hS e he).2) (fun e he => ?_) ?_
  · refine (congrArg (fun y : Tw (twAt D.what₂.embLL A3.A.v0) (HHX St) =>
      ((Tw.out y : HHX St) : L2X St) ∈ goodSub St Gd) (hS e he).1).mpr ?_
    show ((κS • sEEofTT (R.MY 0) R.ν0 R.fd0 _ St Gd ι t c ⟨R.HE.e (Tw.out e), he⟩ : HHX St) : L2X St) ∈ goodSub St Gd
    rw [Submodule.coe_smul]
    refine Submodule.smul_mem _ _ ?_
    unfold sEEofTT
    rw [dif_pos hE]
    exact (mem_EEC St Gd _).1 (hE.choose_spec.2.choose _).2
  · refine (finrank_of_evalTieT hE).trans ?_
    refine Eq.symm ((finrank_twSub (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0)
      ((R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)).comap R.HE.e)).trans ?_)
    refine finrank_comap_of_le_range _ hHE.1 _ ?_
    rw [hHE.2.1]
    exact hle

end GlobalTheory.Mem.SJ.RowIso

end
