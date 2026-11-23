import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Matrix
namespace GlobalTheory.KapLevel

theorem cast_one_fin {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (k : I'.Gf) (hk : k ∈ I'.Kset) :
    ((Formalism.L2.SG.RowsJoinPinned.castGA e).symm (1, k)).1 = 1 ∧
      ((Formalism.L2.SG.RowsJoinPinned.castGA e).symm (1, k)).2 ∈ I.Kset := by
  subst e
  exact ⟨rfl, hk⟩

theorem lat_eq (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 := by
  rw [Formalism.L2.SG.InstExistsPf.Lv_eq_map]
  rfl

theorem hatL_eq (D : D7) :
    (Formalism.IndefR.RationalEmbedding.inst D).Lf = Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  show Formalism.MainNotions.S.lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) = _
  rw [Formalism.MainNotions.S.Inh.aut_lamAf_eq, lat_eq]
  rfl

theorem kset_stab {D : D7} (x : (Formalism.IndefR.RationalEmbedding.inst D).Gf) (hx : x ∈ (Formalism.IndefR.RationalEmbedding.inst D).Kset)
    (g : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (hg : g = x.1) :
    (∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      g.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) ∧
    ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      (g⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) := by
  subst hg
  have h0 : x.1 ∈ Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf := hx
  have h1 : x.1⁻¹ ∈ Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf := (Formalism.UG.stabGL (Formalism.IndefR.RationalEmbedding.inst D).Lf).inv_mem h0
  have e := SetLike.ext_iff.1 (hatL_eq D)
  refine ⟨fun y hy => (e _).1 ((h0 y).1 ((e y).2 hy)), fun y hy => (e _).1 ((h1 y).1 ((e y).2 hy))⟩

theorem st_of_stab {D : D7} (g ft β : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D))
    (hF : Formalism.L2.DIV.IsFrame (ft * β) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (h0 : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      g.1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (h1 : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0),
      (g⁻¹).1 *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) :
    ft⁻¹ * g * ft ∈ Formalism.L2.DIV.St β := by
  have hS : g ∈ Formalism.L2.DIV.St (ft * β) := (GlobalTheory.LevSplit.mem_St_iff (ft * β) _ hF g).2 ⟨h0, h1⟩
  obtain ⟨z, hz⟩ := hS
  refine ⟨z, ?_⟩
  rw [← hz]
  show β * Formalism.L2.DIV.intGL _ _ _ z * β⁻¹ = ft⁻¹ * ((ft * β) * Formalism.L2.DIV.intGL _ _ _ z * (ft * β)⁻¹) * ft
  group

theorem kap_mem_parLev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, kap X h t k ∈ GfC (Yc D 0) ∧ finE (Yc D 0) (kap X h t k) ∈ Formalism.L2.DIV.parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ cG t _ _ _ ht _ hF k hk
  obtain ⟨hy1, hy2⟩ := cast_one_fin h.symm k hk
  have hkap : kap X h t k = (@id (GA D (D.sp.Y 0)) t)⁻¹ * (Formalism.IndefR.RationalEmbedding.iota D).symm
      ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)) * @id (GA D (D.sp.Y 0)) t := rfl
  refine ⟨?_, ?_⟩
  · rw [hkap]
    exact mul_mem (mul_mem (inv_mem ht) ((Formalism.L2.SG.EvalTIota.brg_mem_GfC_i _).2 hy1)) ht
  · have hU := GlobalTheory.LevSplit.finE_mem_UA (Yc D 0) (kap X h t k)
    have hfin0 : Formalism.IndefR.Lev.finE (D.sp.Y 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (D.sp.Y 0) t)⁻¹ *
        @id (GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (D.sp.Y 0) t := by
      rw [hkap, map_mul, map_mul, map_inv, Formalism.L2.SG.EvalTIota.finE_brg_i]
      rfl
    have hfin : Formalism.IndefR.Lev.finE (Yc D 0) (kap X h t k) = (Formalism.IndefR.Lev.finE (Yc D 0) t)⁻¹ *
        @id (GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) ((Formalism.L2.SG.RowsJoinPinned.castGA h.symm).symm (1, k)).2.1 *
        Formalism.IndefR.Lev.finE (Yc D 0) t := hfin0
    rw [hfin] at hU ⊢
    obtain ⟨s0, s1⟩ := kset_stab _ hy2 _ rfl
    have hr : ∀ a : Fin (Yc D 0).rank, (a : ℕ) < (R.dat0 R.triv).r := fun a =>
      lt_of_lt_of_eq a.2 (Formalism.L2.SG.InstExistsPf.rank_eq D)
    refine Formalism.L2.DIV.mem_parLev.2 ⟨hU, st_of_stab _ _ _ hF s0 s1, fun PP _ => ?_, fun PP hP => ?_⟩
    · rw [Formalism.L2.DIV.mem_blockTri]
      intro i j hij
      exfalso
      unfold Formalism.L2.DIV.blkOf at hij
      rw [if_pos (hr i), if_pos (hr j)] at hij
      exact lt_irrefl 0 hij
    · exact absurd hP (Finset.notMem_empty PP)

end GlobalTheory.KapLevel
