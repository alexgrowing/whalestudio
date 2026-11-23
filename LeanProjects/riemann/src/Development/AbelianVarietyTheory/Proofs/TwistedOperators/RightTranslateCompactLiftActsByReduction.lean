import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowActLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levelCharacter_rowDatum_eq_one_of_reduction_one (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (x : GL (Fin (Yc D 0).rank) (EAf D))
    (hx : rTup (R.βY 0) (R.dat0 P) x = 1) : levFn (R.βY 0) (R.dat0 P) x = 1 := by
  unfold levFn
  rw [hx, blockDiagonalExtendByOnePrimeField_one]
  simp [Formalism.IndefR.Links.LevCh.dat0, datY]

theorem levelCharacter_flag_rowDatum_eq_one (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (x : GL (Fin (Yc D 0).rank) (EAf D)) :
    levFn (R.βY 0) (flagL (R.dat0 P)) x = 1 := by
  have h2 : ext1 (flagL (R.dat0 P)).P.H (flagL (R.dat0 P)).P.chi (rTup (R.βY 0) (flagL (R.dat0 P)) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold levFn
  rw [h2]
  simp [flagL, withP, Formalism.IndefR.Links.LevCh.dat0, datY]

theorem mem_lev_of_flag1 (R : RealDat D A Ks) (P P' : LevelP R.Pg D.R.r ℂ) {κ : GA D (Yc D 0)}
    (hκ : κ ∈ levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 P'))) :
    κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) ∧
      levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 P')) κ := by
  obtain ⟨h1, h2, h3⟩ := hκ
  have h3' : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = 1 := Subgroup.mem_bot.1 h3
  refine ⟨⟨h1, h2, ?_⟩, ?_⟩
  · show rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ (R.dat0 P).P.H
    rw [h3']; exact Subgroup.one_mem _
  · unfold levChi
    rw [levelCharacter_rowDatum_eq_one_of_reduction_one R P _ h3', levFn_flag1, levelCharacter_flag_rowDatum_eq_one]

theorem hasType_flag1_of_mem (R : RealDat D A Ks) (P P' : LevelP R.Pg D.R.r ℂ) {T : MMap (R.MY 0)}
    (hT : T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 P)) (levChi (Yc D 0) (R.βY 0) (R.dat0 P)))
    (v : (R.MY 0).Vec) : HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 P')) (T v) := by
  induction hT using Submodule.span_induction with
  | mem S hS =>
    intro κ hκ g
    obtain ⟨hm, hc⟩ := mem_lev_of_flag1 R P P' hκ
    rw [hS.lev v κ hm g, hc]
  | zero =>
    intro κ _ g
    simp
  | add S S' _ _ hS hS' =>
    intro κ hκ g
    simp only [MultilinearMap.add_apply, Pi.add_apply]
    rw [hS κ hκ g, hS' κ hκ g, mul_add]
  | smul c S _ hS =>
    intro κ hκ g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hS κ hκ g, mul_left_comm]

theorem act_kap : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)), (T : MMap (MP R)) v (g * kap X h t k) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) ((T : MMap (MP R)) v) g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame k hk T' hT v g
  have hl := GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame k hk
  have hlift : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
      (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) (kap X h t k) := ⟨hl.1, hl.2, rfl⟩
  have hType := hasType_flag1_of_mem R (R.levR F true) R.triv hT v
  have hs := level_action_spec hType ⟨_, hlift⟩ _ hlift g
  have hc : levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) (kap X h t k) = 1 := by
    unfold levChi; rw [levelCharacter_flag_rowDatum_eq_one]; rfl
  show _ = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) _ _ g
  rw [hs, hc, inv_one, one_mul]

end GlobalTheory.RowActLift
