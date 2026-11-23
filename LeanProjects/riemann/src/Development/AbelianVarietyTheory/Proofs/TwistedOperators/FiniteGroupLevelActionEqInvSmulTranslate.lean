import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingRationalGroups
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateUnitaryLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CommutingRationalGroups GlobalTheory.ThetaProjEquiv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaCommutation

theorem exists_fin_part {D : D7} (V : HSp D) (q : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = q := by
  obtain ⟨h, rfl⟩ := (finHom V).rangeRestrict_surjective q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 h
  refine ⟨k, hk, Subtype.ext ?_⟩
  show finHom V k = finHom V (a * k)
  rw [map_mul, show finHom V a = 1 from ha, one_mul]

theorem finiteGroupLevelAction_eq_inv_smul_translate {H W : Type} [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {Q : Subgroup H} (ch : Q →* ℂˣ)
    (q : Q) (k : H) (hk : k = q) (c : ℂ) (hc : c = ch q) (f : H → W) (h : H) :
    Bridge.g0Act ch q f h = c⁻¹ • f (h * k) := by
  rw [hk, hc, Bridge.g0Act, Units.val_inv_eq_inv_val]

theorem ch_eq {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) := rfl

theorem exists_adelic_lift {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) (g0 : G0 L.Pg L.r) (hq : rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) = g0)
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    ∃ k, IsLevelLift V β L g0 k ∧ ∀ (f : Bridge.Gf V → W) h,
      Bridge.g0Act (levEnv V β L).ch q f h = (levChi V β (flagL L) k)⁻¹ • f (h * (finHom V).rangeRestrict k) := by
  obtain ⟨k, hk, e⟩ := exists_fin_part V q.1
  have e1 : finE V k = Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) :=
    congrArg (fun x : Bridge.Gf V => Formalism.UG.bc (swapAE D) x.1) e
  refine ⟨k, ⟨hk, ?_, ?_⟩, finiteGroupLevelAction_eq_inv_smul_translate _ q _ e _ ?_⟩
  · rw [e1]; exact q.2.1
  · rw [e1]; exact hq
  · exact congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq V β L q).symm)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem algW_apply (i : Fin D.R.m) (c : G → ℂ) (U : MMap (R.MW i (sg0 D A))) :
    algW R i c U = ∑ g, c g • FWT.actW R i (sg0 D A) g U := by
  refine MultilinearMap.ext fun v => ?_
  show (∑ g, c g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (U v) = _
  rw [LinearMap.sum_apply, _root_.sum_apply]
  rfl

theorem map_comb {G H X Y : Type} [Fintype G] [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y]
    [Module ℂ Y] (e : H →ₗ[ℂ] X) (he : Function.Injective e) (Θ : H →ₗ[ℂ] Y) (c : G → ℂ) (a : G → X) (b : G → Y) (y : H)
    (hy : e y = ∑ g, c g • a g) (h1 : ∀ g, ∃ z, e z = a g) (h2 : ∀ g z, e z = a g → Θ z = b g) :
    Θ y = ∑ g, c g • b g := by
  choose z hz using h1
  have h3 : y = ∑ g, c g • z g := he (by simp only [hy, map_sum, map_smul, hz])
  simp only [h3, map_sum, map_smul, h2 _ _ (hz _)]

end GlobalTheory.ThetaCommutation

end
