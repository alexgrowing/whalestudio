import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacIso

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem piW_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    piW t (cA σ x) = piW (t.comp σ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul a e => rfl

theorem eq_zero_of_at_split {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v)
    {z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E} (hz : At (evFin F v) z) (h1 : piW τ z = 0) (h2 : piW (τ.comp σ) z = 0) : z = 0 := by
  have hc : compFin F E v z = 0 :=
    GlobalTheory.AdelicU.split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  have e := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at e
  rw [e, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  change GlobalTheory.EmbChart.tensAt E v ((1 : Fv F v) ⊗ₜ[F] (1 : E)) * z = 0
  rw [GlobalTheory.EmbChart.tensAt_mul_right, hc, mul_zero, map_zero]

theorem symp_self_eq_zero : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (u : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
    (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∨ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) →
    ∀ ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E,
      symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u = 0 := by
  intro D a a' Bs Γ X om om' hTr u hu hpi ξ
  have hcm : IsCMExt D.host.F D.host.E D.sp.cm.sig := hTr.base.cm
  set z := GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u with hzdef
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) z := by
    intro c hc
    have hij : ∀ i j, c • u i j = 0 := fun i j => by
      have := congrFun (congrFun (hu c hc) i) j
      simpa using this
    simp only [hzdef, GlobalTheory.WeilM.hTens, Finset.smul_sum, ← smul_mul_assoc, hij, zero_mul, Finset.sum_const_zero]
  have first : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁, (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (u i j) = 0) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z = 0 := by
    intro t ht
    simp only [hzdef, GlobalTheory.WeilM.hTens, map_sum, map_mul, ht, zero_mul, Finset.sum_const_zero]
  have last : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F Bs.v₁,
      (∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp D.sp.cm.sig) (u i j) = 0) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z = 0 := by
    intro t ht
    simp only [hzdef, GlobalTheory.WeilM.hTens, map_sum, map_mul, GlobalTheory.VacIso.piW_cA, ht, mul_zero, Finset.sum_const_zero]
  have hz0 : z = 0 := by
    rcases hpi with h0 | h0
    · have h0' : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁ (u i j) = 0 := fun i j => by
        simpa using congrFun (congrFun h0 i) j
      refine GlobalTheory.VacIso.eq_zero_of_at_split hcm Bs.τ₁ hat (first _ h0') (last _ ?_)
      rw [GlobalTheory.AdelicU.comp_conj_conj hcm]; exact h0'
    · have h0' : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig) (u i j) = 0 := fun i j => by
        simpa using congrFun (congrFun h0 i) j
      exact GlobalTheory.VacIso.eq_zero_of_at_split hcm Bs.τ₁ hat (last _ h0') (first _ h0')
  simp only [GlobalTheory.WeilM.symp, ← hzdef, hz0, mul_zero, map_zero]

end GlobalTheory.VacIso
