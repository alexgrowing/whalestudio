import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TriangularInvOfDiagNe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericLuDecompositionUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgIndepOfSameAdjoinStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScalingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombBaseChangeStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

section LieGen
variable {B : Scheme.{0}} {G : CategoryTheory.Over B} [GrpObj G] {R : Type} [CommRing R] {x : Spec (CommRingCat.of R) ⟶ B}
  {L : Type} [AddCommGroup L] [Module R L]

theorem pt_zero (N : LieModel G x L) : N.pt 0 = 1 := by
  have h := N.add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem pt_sum (N : LieModel G x L) {m : ℕ} (f : Fin m → L) :
    (List.ofFn fun i => N.pt (f i)).prod = N.pt (∑ i, f i) := by
  induction m with
  | zero => simp [pt_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, N.add]

end LieGen

section Comb
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem comb_iff {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {L : Type} [AddCommGroup L] [Module S L]
    (N : LieModel Xo.univ.t.G x L) {m : ℕ} (e : Fin m → L) (cf : Fin m → S)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsCombAt x (fun i => (N.pt (e i)).left) cf w ↔ w = (N.pt (∑ i, cf i • e i)).left := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have e1 : u = fun i => N.pt (cf i • e i) := by
      funext i
      exact CategoryTheory.Over.OverMorphism.ext ((hu i).trans (N.smul _ _).symm)
    rw [← hw, e1]
    exact congrArg (fun V => V.left) (pt_sum N _)
  · rintro rfl
    exact ⟨fun i => N.pt (cf i • e i), fun i => N.smul _ _,
      congrArg (fun V => V.left) (pt_sum N _)⟩

end Comb

end GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

namespace GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

section Model
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_univ_model (Y : Model Xo c β) {R : Type} [CommRing R] (p : Sp R ⟶ Xo.XF c) {L : Type} [AddCommGroup L]
    [Module R L] {z : Sp R ⟶ Y.X} (hz : p ≫ Y.j = z) (M₁ : LieModel Y.t.G z L) {x : Sp R ⟶ Xo.X}
    (hx : p ≫ pullback.fst _ _ = x) :
    ∃ N : LieModel Xo.univ.t.G x L,
      (∀ (e : L) (v : Sp (DualNumber R) ⟶ Y.oF.t.G.left), v ≫ Y.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ p →
        ((N.pt e).left = v ≫ Y.m0.toSABMap.φ ↔ v ≫ Y.m.φ = (M₁.pt e).left)) ∧
      ∀ (ρ : 𝓞 E → L → L), (∀ a e, (M₁.pt (ρ a e)).left = (M₁.pt e).left ≫ (Y.t.act.act a).left) →
        ∀ a e, (N.pt (ρ a e)).left = (N.pt e).left ≫ (Xo.univ.t.act.act a).left := by
  subst hz hx
  obtain ⟨M₂, e₂⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Y.m.cart R p L).1 M₁
  obtain ⟨M₃, e₃⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Y.m0.toSABMap.cart R p L).2 M₂
  have hw : ∀ e, (M₂.pt e).left ≫ Y.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ p := fun e =>
    CategoryTheory.Over.w (M₂.pt e)
  refine ⟨M₃, fun e v hv => ⟨fun h => ?_, fun h => ?_⟩, fun ρ hρ a e => ?_⟩
  · have : v = (M₂.pt e).left :=
      Y.m0.toSABMap.cart.1.hom_ext (h.symm.trans (e₃ e).symm) (hv.trans (hw e).symm)
    rw [this]
    exact e₂ e
  · have : v = (M₂.pt e).left := Y.m.cart.1.hom_ext (h.trans (e₂ e).symm) (hv.trans (hw e).symm)
    rw [this]
    exact (e₃ e).symm
  · have h2 : (M₂.pt (ρ a e)).left = (M₂.pt e).left ≫ (Y.oF.t.act.act a).left := by
      refine Y.m.cart.1.hom_ext ?_ ?_
      · rw [e₂, hρ, Category.assoc, Y.m.act, ← Category.assoc, e₂]
      · rw [hw, Category.assoc, CategoryTheory.Over.w (Y.oF.t.act.act a), hw]
    rw [← e₃, h2, Category.assoc, Y.m0.toSABMap.act, ← Category.assoc, e₃]

theorem pt_eq_u_iff (Y : Model Xo c β) {R : Type} [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) {p : Sp R ⟶ Xo.XF c}
    (hp : Small.ptF y = p) {L : Type} [AddCommGroup L] [Module R L] {z : Sp R ⟶ Y.X} {M₁ : LieModel Y.t.G z L}
    {x : Sp R ⟶ Xo.X} {N : LieModel Xo.univ.t.G x L}
    (hN : ∀ (e : L) (v : Sp (DualNumber R) ⟶ Y.oF.t.G.left), v ≫ Y.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ p →
        ((N.pt e).left = v ≫ Y.m0.toSABMap.φ ↔ v ≫ Y.m.φ = (M₁.pt e).left)) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (e : L) :
    (N.pt e).left = y.u τ i ↔ Small.tanY Y y τ i = (M₁.pt e).left := by
  subst hp
  have := hN e (Small.tanF Y y τ i) (Small.tanF_hom Y y τ i)
  rw [Small.tanF_φ] at this
  exact this

end Model

end GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

namespace GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

section Pure

theorem exists_change {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} {c e : Fin r → V}
    {W : Submodule K V} (hc : LinearIndependent K c) (hcW : Submodule.span K (Set.range c) = W)
    (he : LinearIndependent K e) (heW : ∀ k, e k ∈ W) :
    ∃ P : Matrix (Fin r) (Fin r) K, P.det ≠ 0 ∧ ∀ k, c k = ∑ j, P k j • e j := by
  have hs : Submodule.span K (Set.range e) = W := GlobalTheory.CompanionTheory.Ar.FlagRead.span_eq_of_indep he heW hc hcW
  have h1 : ∀ k, ∃ a : Fin r → K, ∑ j, a j • e j = c k := fun k => by
    have h : c k ∈ Submodule.span K (Set.range e) := by
      rw [hs, ← hcW]
      exact Submodule.subset_span ⟨k, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun K).1 h
  have h2 : ∀ j, ∃ a : Fin r → K, ∑ k, a k • c k = e j := fun j => by
    have h : e j ∈ Submodule.span K (Set.range c) := by
      rw [hcW]
      exact heW j
    exact (Submodule.mem_span_range_iff_exists_fun K).1 h
  choose P hP using h1
  choose Q hQ using h2
  have hPQ : Matrix.of P * Matrix.of Q = 1 := by
    ext k m
    have e1 : ∑ m, (∑ j, P k j * Q j m) • c m = c k := by
      rw [← hP k]
      simp only [← hQ, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    have e2 : ∑ m, ((∑ j, P k j * Q j m) - (1 : Matrix (Fin r) (Fin r) K) k m) • c m = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, e1, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    have e3 := Fintype.linearIndependent_iff.1 hc _ e2 m
    simpa [Matrix.mul_apply, sub_eq_zero] using e3
  refine ⟨Matrix.of P, ?_, fun k => (hP k).symm⟩
  intro h0
  have := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem adjoin_all_eq_strict {K L S : Type} [Field K] [Field L] [Algebra K L] {r : S → ℕ}
    (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L) (h1 : ∀ s k, u s k k = 1) (h0 : ∀ s l k, l < k → u s l k = 0) :
    IntermediateField.adjoin K (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin K (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} =>
        u q.1 q.2.1.1 q.2.1.2) := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨s, l, k⟩, rfl⟩
    rcases lt_trichotomy l k with h | h | h
    · show u s l k ∈ _
      rw [h0 s l k h]
      exact zero_mem _
    · subst h
      show u s l l ∈ _
      rw [h1]
      exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨s, ⟨⟨l, k⟩, h⟩⟩, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (l, k)⟩, rfl⟩

theorem adjoin_all_le {K L S : Type} [Field K] [Field L] [Algebra K L] {r : S → ℕ}
    (u v : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L)
    (h : ∀ s, IntermediateField.adjoin K (Set.range fun p : Fin (r s) × Fin (r s) => u s p.1 p.2) =
      IntermediateField.adjoin K (Set.range fun p : Fin (r s) × Fin (r s) => v s p.1 p.2)) :
    IntermediateField.adjoin K (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) ≤
      IntermediateField.adjoin K (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => v q.1 q.2.1 q.2.2) := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro _ ⟨⟨s, l, k⟩, rfl⟩
  have hm : u s l k ∈ IntermediateField.adjoin K (Set.range fun p : Fin (r s) × Fin (r s) => v s p.1 p.2) := by
    rw [← h s]
    exact IntermediateField.subset_adjoin _ _ ⟨(l, k), rfl⟩
  refine (IntermediateField.adjoin_le_iff.2 ?_ : _ ≤ _) hm
  rintro _ ⟨⟨l', k'⟩, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (l', k')⟩, rfl⟩

theorem lin_core {Ω₀ Ω Li₀ Li : Type} [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] [AddCommGroup Li₀] [Module Ω₀ Li₀]
    [AddCommGroup Li] [Module Ω Li] (j : Li₀ →+ Li) {S : Type} [Finite S] {r : S → ℕ}
    (V₀ : S → Submodule Ω₀ Li₀) (b : ∀ s, Fin (r s) → Li) (d : ℕ) (hg : IsGenericFlag (Ω' := Ω) j V₀ b d)
    (ec : ∀ s, Fin (r s) → Li₀) (hec : ∀ s, LinearIndependent Ω₀ (ec s)) (hmem : ∀ s k, ec s k ∈ V₀ s)
    (hf : ∀ s, LinearIndependent Ω fun k => j (ec s k)) :
    ∃ v Tm : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω, (∀ s k, v s k k = 1) ∧ (∀ s l k, l < k → v s l k = 0) ∧
      AlgebraicIndependent Ω₀ (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧
      Module.finrank (IntermediateField.adjoin Ω₀
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => v q.1 q.2.1 q.2.2)) Ω = d ∧
      (∀ s i, b s i = ∑ m, Tm s i m • ∑ l, v s l m • j (ec s l)) ∧ (∀ s i m, i < m → Tm s i m = 0) ∧
      ∀ s i, Tm s i i ≠ 0 := by
  obtain ⟨cc, u, hcV, hjs, hjc, hb, hu1, hu0, hfl, hind, hd, hdeg⟩ := hg
  have hP := fun s => exists_change (hcV s).1 (hcV s).2 (hec s) (hmem s)
  choose P hPdet hP using hP
  have hAdet : ∀ s, ((P s)ᵀ).det ≠ 0 := fun s => by rw [Matrix.det_transpose]; exact hPdet s
  have hinds : ∀ s, AlgebraicIndependent Ω₀
      (fun q : {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => u s q.1.1 q.1.2) := fun s =>
    hind.comp (fun q => (⟨s, q⟩ : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}))
      (fun a b h => by simpa using h)
  have hLU := fun s => GlobalTheory.T.exists_lu_decomposition_mul_generic_unipotent Ω₀ Ω (r s) ((P s)ᵀ) (u s) (hAdet s) (hu1 s) (hu0 s) (hinds s)
  choose v w hvw hv1 hv0 hw0 hw using hLU
  have hfld := fun s => GlobalTheory.T.lu_factors_generate_same_field Ω₀ Ω (r s) ((P s)ᵀ) (u s) (v s) (w s) (hAdet s) (hu1 s) (hu0 s) (hv1 s) (hv0 s)
    (hw0 s) (hw s) (hvw s)
  have hall : IntermediateField.adjoin Ω₀ (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin Ω₀ (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => v q.1 q.2.1 q.2.2) :=
    le_antisymm (adjoin_all_le u v hfld) (adjoin_all_le v u fun s => (hfld s).symm)
  have hindv : AlgebraicIndependent Ω₀ (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} =>
      v q.1 q.2.1.1 q.2.1.2) := by
    refine GlobalTheory.T.alg_indep_of_same_adjoin Ω₀ Ω _ _ _ hind ?_
    rw [← adjoin_all_eq_strict u hu1 hu0, ← adjoin_all_eq_strict v hv1 hv0, hall]
  have hTm := fun s => GlobalTheory.T.generic_flag_triangular_change Ω Li (r s) (fun k => j (ec s k)) (b s)
    (fun k => ∑ l, u s l k • j (cc s l)) (v s) (w s) (hf s) (hb s) (hv1 s) (hv0 s) (hw0 s) (hw s) (fun k => by
      rw [← hvw s]
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e1 : j (cc s l) = ∑ m, algebraMap Ω₀ Ω (P s l m) • j (ec s m) := by
        rw [hP s l, map_sum]
        exact Finset.sum_congr rfl fun m _ => hjs _ _
      rw [e1, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_smul, mul_comm]) (hfl s)
  choose Tm hT hT0 hTd using hTm
  exact ⟨v, Tm, hv1, hv0, hindv, by rw [← hall]; exact hdeg, hT, hT0, hTd⟩

end Pure

end GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

namespace GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pt {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {L : Type} [AddCommGroup L] [Module S L]
    (N : LieModel Xo.univ.t.G x L) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : Formalism.L2.Pj.IsTanAt x v) :
    ∃ e, (N.pt e).left = v := by
  obtain ⟨e, he⟩ := N.onto (CategoryTheory.Over.homMk v hv.1) hv.2
  exact ⟨e, congrArg (fun V => V.left) he⟩

theorem indep_of_basis {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {x : Sp S ⟶ Xo.X} (hx : y.x = x) {L : Type}
    [AddCommGroup L] [Module S L] (N : LieModel Xo.univ.t.G x L) (τ : E →+* ℂ) (f : Fin (Dw.mult τ) → L)
    (hf : ∀ k, (N.pt (f k)).left = y.u τ k) : LinearIndependent S f := by
  subst hx
  classical
  have hu : (fun i => (N.pt (f i)).left) = y.u τ := funext hf
  refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
  have h1 : IsCombAt y.x (y.u τ) (fun i => if i = k then 1 else 0) (y.u τ k) := by
    rw [← hu, comb_iff N]
    simp
  have h2 : IsCombAt y.x (y.u τ) (fun i => g i + if i = k then 1 else 0) (y.u τ k) := by
    rw [← hu, comb_iff N]
    simp [add_smul, Finset.sum_add_distrib, hg]
  have h3 := (y.basis τ _ (y.tan τ k) (y.eig τ k)).unique h2 h1
  have h4 := congrFun h3 k
  simpa using h4

theorem frBor_of_comb {S : Type} [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S) (hx : z.x = y.x)
    (h : ∀ τ i, ∃ cf : Fin (Dw.mult τ) → S, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt y.x (y.u τ) cf (z.u τ i)) :
    ∃ t : Ix Dw → Sˣ, FrBor t y z := by
  choose cf hcu hc0 hcc using h
  obtain ⟨zx, zxo, zu, ztan, zeig, zbasis, zs, zgen⟩ := z
  dsimp only at hx hcc
  subst hx
  obtain ⟨a, ha, -⟩ := y.gen zs
  obtain ⟨a', ha', -⟩ := zgen y.s
  have haa : a' * a = 1 := by
    refine (y.gen y.s).unique (fun i => ?_) (fun i => ?_)
    · rw [GlobalTheory.Reg.scal_mul_tie, _root_.mul_assoc, ← ha i, ← ha' i]
    · rw [GlobalTheory.Reg.scal_one_tie, _root_.one_mul]
  have hau : IsUnit a := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact haa)
  refine ⟨fun k => match k with
    | none => hau.unit
    | some ⟨τ, i⟩ => (hcu τ i).unit, rfl, fun τ i => ⟨cf τ i, rfl, hc0 τ i, hcc τ i⟩, 𝟙 _, Category.id_comp _,
      Category.id_comp _, fun i h => ?_⟩
  have e : (Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h) = 𝟙 _ := by
    show 𝟙 _ ≫ (Gx y.x).presheaf.map (𝟙 _) = _
    rw [Category.id_comp, CategoryTheory.Functor.map_id]
  show (Scheme.Hom.appLE (𝟙 (Gx y.x)) ((PPx y.x).U i) ((PPx y.x).U i) h).hom (scal y.x a i * y.s.f i) = zs.f i
  rw [e, ha i]
  rfl

end Frames

end GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

namespace GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

theorem dualMap_comp₂ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    Formalism.L2.Pj.dualMap (g.comp f) = (Formalism.L2.Pj.dualMap g).comp (Formalism.L2.Pj.dualMap f) := by
  ext a <;> simp [Formalism.L2.Pj.dualMap]

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

section Core
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {SS : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem flags_setup (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (ψ : kap Z ≃+* Or.𝔐.Ω₀)
    (hψ : spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀)
    (hc : ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a)
    (y₀ : FrPt Xo c (kap Z)) (hy₀ : y₀.x = xGen Z) :
    letI := Small.cstAlg Or
    ∃ (N : LieModel Xo.univ.t.G Fr.y₀.x Or.𝔐.Li) (ec : ∀ τ, Fin (Dw.mult τ) → Or.Fl.Li₀),
      (spMap (Or.𝔐.fn.comp ψ.toRingHom) ≫ y₀.x = Fr.y₀.x) ∧
      (∀ s (k : Fin (Dw.mult (Small.labelC s))),
        (N.pt (Or.Fl.b s (Fin.cast (Small.mult_labelC Dw s) k))).left = Fr.y₀.u (Small.labelC s) k) ∧
      (∀ τ k, (N.pt (Or.Fl.j (ec τ k))).left =
        spMap (Formalism.L2.Pj.dualMap (Or.𝔐.fn.comp ψ.toRingHom)) ≫ y₀.u τ k) ∧
      (∀ τ, LinearIndependent Or.𝔐.Ω₀ (ec τ)) ∧
      (∀ τ, LinearIndependent RM.Ω fun k => Or.Fl.j (ec τ k)) ∧
      (∀ s k, ec (Small.labelC s) k ∈ Or.Fl.V₀ s) := by
  letI algΩ := Small.cstAlg Or
  letI alg₀ : Algebra c.F Or.𝔐.Ω₀ := ((ψ.toRingHom).comp (algebraMap c.F (kap Z))).toAlgebra
  let ψA : kap Z →ₐ[c.F] Or.𝔐.Ω₀ := { ψ.toRingHom with commutes' := fun _ => rfl }
  let fnA : Or.𝔐.Ω₀ →ₐ[c.F] RM.Ω := { Or.𝔐.fn with commutes' := fun a => hc a }
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨y₁, h₁⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ ψA y₀
  obtain ⟨y₂, h₂⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ fnA y₁
  have hp0 : Small.ptF y₀ = genSp Z := by
    apply pullback.hom_ext
    · rw [Small.ptF_fst, hy₀]; rfl
    · rw [Small.ptF_snd]; exact Spec.map_preimage _
  have hp1 : Small.ptF y₁ = spMap ψ.toRingHom ≫ genSp Z := by
    rw [Small.ptF_map h₁, hp0]
  have hz₀ : Small.ptF y₁ ≫ Y.j = Or.𝔐.ξ₀ := by
    rw [hp1, Category.assoc]; exact hψ
  have hptY : Small.ptY Y y₂ = Small.ptY Y Fr.y₀ := by
    refine Eq.trans ?_ Fr.pt_eq.symm
    show Small.ptF y₂ ≫ Y.j = _
    rw [Small.ptF_map h₂, Category.assoc, hz₀]
    exact Or.𝔐.fn_over.symm
  have hpF : Small.ptF y₂ = Small.ptF Fr.y₀ := Small.ptF_eq_of_ptY_eq Y hptY
  have hx₂ : y₂.x = Fr.y₀.x := by
    rw [← Small.ptF_fst y₂, hpF, Small.ptF_fst]
  obtain ⟨M₁, e₁⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Or.𝔐.m.cart RM.Ω Or.𝔐.ξ Or.𝔐.Li).2 Or.𝔐.M
  obtain ⟨N, hN, hNa⟩ := exists_univ_model Y (Small.ptF Fr.y₀) Fr.pt_eq M₁ (Small.ptF_fst Fr.y₀)
  obtain ⟨N₀, hN₀, -⟩ := exists_univ_model Y (Small.ptF y₁) hz₀ Or.Fl.M₀ (Small.ptF_fst y₁)
  have hex : ∀ τ k, ∃ e, (N₀.pt e).left = y₁.u τ k := fun τ k => exists_pt N₀ (y₁.tan τ k)
  choose ec hec using hex
  have hM₀ : ∀ τ k, Small.tanY Y y₁ τ k = (Or.Fl.M₀.pt (ec τ k)).left := fun τ k =>
    (pt_eq_u_iff Y y₁ rfl hN₀ τ k _).1 (hec τ k)
  have hy₂ : ∀ τ k, (N.pt (Or.Fl.j (ec τ k))).left = y₂.u τ k := fun τ k =>
    (pt_eq_u_iff Y y₂ hpF hN τ k _).2 (by
      rw [Small.tanY_map Y h₂, hM₀, ← e₁, Or.Fl.j_pt])
  have hu₂ : ∀ τ k, y₂.u τ k = spMap (Formalism.L2.Pj.dualMap (Or.𝔐.fn.comp ψ.toRingHom)) ≫ y₀.u τ k := fun τ k => by
    rw [h₂.2.1, h₁.2.1, ← Category.assoc, dualMap_comp₂, spc]
  refine ⟨N, ec, ?_, fun s k => ?_, fun τ k => (hy₂ τ k).trans (hu₂ τ k), fun τ => indep_of_basis y₁ rfl N₀ τ _ (hec τ),
    fun τ => indep_of_basis y₂ hx₂ N τ _ (hy₂ τ), fun s k => ?_⟩
  · rw [← hx₂, h₂.1, h₁.1, ← Category.assoc, spc]
  · refine (pt_eq_u_iff Y Fr.y₀ rfl hN _ k _).2 ?_
    exact (Fr.tan_eq s (Fin.cast (Small.mult_labelC Dw s) k)).trans (e₁ _)
  · refine (Or.Fl.V₀_mem s _).2 ?_
    have hρ : ∀ (a : 𝓞 E) (e : Or.𝔐.Li), (M₁.pt (Or.𝔐.ρ a e)).left = (M₁.pt e).left ≫ (Y.t.act.act a).left := fun a e => by
      rw [← e₁, ← e₁, Or.𝔐.act a e, CategoryTheory.Over.comp_left, Category.assoc, Or.𝔐.m.act, Category.assoc]
    have hact := hNa (fun a e => Or.𝔐.ρ a e) hρ
    show _ ∈ eigSp Or.𝔐.ρ (Or.𝔐.emb s)
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    intro a
    apply N.inj
    apply CategoryTheory.Over.OverMorphism.ext
    have h3 := y₂.eig (Small.labelC s) k a
    rw [hact a, hy₂, h3, LinearMap.smul_apply, LinearMap.id_apply, N.smul, hy₂, Small.embK_labelC]
    rfl

end Core

end GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

namespace GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

section Lift

theorem generic_cast {Ω₀ Ω Li₀ Li S : Type} [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] [AddCommGroup Li₀] [Module Ω₀ Li₀]
    [AddCommGroup Li] [Module Ω Li] (j : Li₀ →+ Li) (r r' : S → ℕ) (hr : ∀ s, r' s = r s)
    (V : S → Submodule Ω₀ Li₀) (b : ∀ s, Fin (r s) → Li) (d : ℕ) (h : IsGenericFlag (Ω' := Ω) j V b d) :
    IsGenericFlag (Ω' := Ω) (r := r') j V (fun s k => b s (Fin.cast (hr s) k)) d := by
  obtain rfl : r' = r := funext hr
  exact h

theorem exists_lift {K₀ Ω₀ Ω V : Type} [Field K₀] [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (ψ : K₀ ≃+* Ω₀) (T : V → Ω)
    (hT : AlgebraicIndependent Ω₀ T) :
    ∃ φ : FractionRing (MvPolynomial V K₀) →+* Ω,
      (∀ x, φ (algebraMap (MvPolynomial V K₀) _ (MvPolynomial.C x)) = algebraMap Ω₀ Ω (ψ x)) ∧
      (∀ i, φ (algebraMap (MvPolynomial V K₀) _ (MvPolynomial.X i)) = T i) ∧
      (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial V K₀)) Ω) =
        Module.finrank (IntermediateField.adjoin Ω₀ (Set.range T)) Ω := by
  let φ₀ : MvPolynomial V K₀ →+* Ω :=
    (MvPolynomial.aeval T : MvPolynomial V Ω₀ →ₐ[Ω₀] Ω).toRingHom.comp (MvPolynomial.map ψ.toRingHom)
  have hinj : Function.Injective φ₀ :=
    (algebraicIndependent_iff_injective_aeval.1 hT).comp (MvPolynomial.map_injective _ ψ.injective)
  let φ : FractionRing (MvPolynomial V K₀) →+* Ω := IsFractionRing.lift hinj
  have hφ : ∀ p, φ (algebraMap (MvPolynomial V K₀) _ p) = φ₀ p := fun p => IsFractionRing.lift_algebraMap hinj p
  refine ⟨φ, fun x => ?_, fun i => ?_, ?_⟩
  · rw [hφ]
    simp [φ₀]
  · rw [hφ]
    simp [φ₀]
  set F := IntermediateField.adjoin Ω₀ (Set.range T) with hF
  have hmem₀ : ∀ p, φ₀ p ∈ F := fun p => by
    have h1 : φ₀ p ∈ Algebra.adjoin Ω₀ (Set.range T) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨_, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin Ω₀ _ h1
  have hmem : ∀ x, φ x ∈ F := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial V K₀) x
    rw [map_div₀, hφ, hφ]
    exact div_mem (hmem₀ a) (hmem₀ b)
  let F' : IntermediateField Ω₀ Ω := φ.fieldRange.toIntermediateField fun a =>
    ⟨algebraMap (MvPolynomial V K₀) _ (MvPolynomial.C (ψ.symm a)), by
      rw [hφ]
      simp [φ₀]⟩
  have hle : F ≤ F' := IntermediateField.adjoin_le_iff.2 (by
    rintro _ ⟨i, rfl⟩
    exact ⟨algebraMap (MvPolynomial V K₀) _ (MvPolynomial.X i), by
      rw [hφ]
      simp [φ₀]⟩)
  let g : FractionRing (MvPolynomial V K₀) →+* F := φ.codRestrict F hmem
  have hgb : Function.Bijective g := by
    refine ⟨g.injective, fun y => ?_⟩
    obtain ⟨x, hx⟩ := hle y.2
    exact ⟨x, Subtype.ext hx⟩
  letI := φ.toAlgebra
  let e := RingEquiv.ofBijective g hgb
  refine Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl Ω) ?_
  ext x
  rfl

end Lift

end GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

namespace GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

section Read
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ev_map (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {S T : Type} [CommRing S]
    [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (h : FrMap φ y z) :
    evR Xo c f z = φ (evR Xo c f y) := by
  have hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := by
    obtain ⟨p, χ, y', h'⟩ := hy
    exact ⟨p, φ.comp χ, y', ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ φ h' h⟩
  unfold evR evalAt
  rw [dif_pos hy, dif_pos hz]
  exact hWD f hf T _ _ _ (φ.comp hy.choose_spec.choose) _ _ z hz.choose_spec.choose_spec.choose_spec
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hy.choose_spec.choose_spec.choose_spec h)

theorem exists_strictHenselian_absolutely_closed_local_ring {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (v : ∀ s : CMType H ⊕ CMType H, Matrix (Fin (Dw.mult (Small.labelC s))) (Fin (Dw.mult (Small.labelC s))) Ω)
    (hvi : AlgebraicIndependent K (fun q : Σ s : CMType H ⊕ CMType H,
      {lk : Fin (Dw.mult (Small.labelC s)) × Fin (Dw.mult (Small.labelC s)) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) :
    ∃ T : FlagVar Dw → Ω, AlgebraicIndependent K T ∧
      Set.range T = (Set.range fun q : Σ s : CMType H ⊕ CMType H,
        {lk : Fin (Dw.mult (Small.labelC s)) × Fin (Dw.mult (Small.labelC s)) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧
      ∀ s k l (h : k < l), T ⟨Small.labelC s, ⟨(k, l), h⟩⟩ = v s l k := by
  let e : (Σ s : CMType H ⊕ CMType H,
      {lk : Fin (Dw.mult (Small.labelC s)) × Fin (Dw.mult (Small.labelC s)) // lk.2 < lk.1}) ≃ FlagVar Dw :=
    Equiv.sigmaCongr (Small.labelEquiv H) fun s =>
      { toFun := fun q => ⟨(q.1.2, q.1.1), q.2⟩
        invFun := fun q => ⟨(q.1.2, q.1.1), q.2⟩
        left_inv := fun q => rfl
        right_inv := fun q => rfl }
  refine ⟨_ ∘ e.symm, hvi.comp e.symm e.symm.injective, e.symm.surjective.range_comp _, fun s k l h => ?_⟩
  have : (⟨Small.labelC s, ⟨(k, l), h⟩⟩ : FlagVar Dw) = e ⟨s, ⟨(l, k), h⟩⟩ := rfl
  rw [this]
  exact congrArg (fun q : (Σ s : CMType H ⊕ CMType H,
      {lk : Fin (Dw.mult (Small.labelC s)) × Fin (Dw.mult (Small.labelC s)) // lk.2 < lk.1}) => v q.1 q.2.1.1 q.2.1.2)
    (e.symm_apply_apply ⟨s, ⟨(l, k), h⟩⟩)

variable {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {SS : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem read_core (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c)
    (hgT : GenFromTest Xo c h)
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hZ : GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z)) : Nonempty (Reading Fr h Z) := by
  letI algΩ := Small.cstAlg Or
  obtain ⟨ψ, hψ, hc⟩ := GlobalTheory.T.root_origin_component_generic_point E H Dw l Xo c Y SS RM Sys Fx Or Z hZ
  obtain ⟨hgx, y₀, hy₀, hy₀c⟩ := isGenFr_genFr h Z
  obtain ⟨N, ec, hx, hb, hj, hli₀, hli, hmem⟩ := flags_setup Or Fr Z ψ hψ hc y₀ hy₀
  letI algfn : Algebra Or.𝔐.Ω₀ RM.Ω := Or.𝔐.fn.toAlgebra
  have hg' := generic_cast Or.Fl.j (labelRk Dw) (fun s => Dw.mult (Small.labelC s)) (Small.mult_labelC Dw) Or.Fl.V₀
    Or.Fl.b Or.Fl.deg Or.Fl.generic
  obtain ⟨v, Tm, hv1, hv0, hvi, hvd, hbT, hT0, hTd⟩ := lin_core Or.Fl.j Or.Fl.V₀ _ Or.Fl.deg hg'
    (fun s => ec (Small.labelC s)) (fun s => hli₀ _) hmem (fun s => hli _)
  obtain ⟨T, hTi, hTr, hTv⟩ := exists_strictHenselian_absolutely_closed_local_ring v hvi
  obtain ⟨φ, hφC, hφX, hφd⟩ := exists_lift ψ T hTi
  have hφk : ∀ x, φ (algebraMap (kap Z) (Om Z) x) = Or.𝔐.fn (ψ x) := fun x => by
    rw [IsScalarTower.algebraMap_apply (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) x]
    exact hφC x
  have hφc : ∀ a : c.F, φ (algebraMap c.F (Om Z) a) = Or.𝔐.cst a := fun a => by
    rw [gfp_tower Z a, hφk, hc]
  let φA : Om Z →ₐ[c.F] RM.Ω := { φ with commutes' := hφc }
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨y₃, h₃⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ φA (genFr h Z)
  have hk : φ.comp (algebraMap (kap Z) (Om Z)) = Or.𝔐.fn.comp ψ.toRingHom := RingHom.ext hφk
  have hbase : spMap φ ≫ (genFr h Z).x = Fr.y₀.x := by
    rw [hgx, ← Category.assoc, spc, hk, ← hy₀]
    exact hx
  have hx₃ : y₃.x = Fr.y₀.x := h₃.1.trans hbase
  have hcoef : ∀ s (i j : Fin (Dw.mult (Small.labelC s))), φ (genCoef Z (Small.labelC s) i j) = v s j i := by
    intro s i j
    unfold genCoef
    split_ifs with h1 h2
    · rw [hφX]
      exact hTv s i j h1
    · subst h2
      rw [map_one, hv1]
    · rw [map_zero, hv0 s j i (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))]
  have hy3 : ∀ s, y₃.u (Small.labelC s) = fun m =>
      (N.pt (∑ l, v s l m • Or.Fl.j (ec (Small.labelC s) l))).left := by
    intro s
    funext i
    have h1 := GlobalTheory.T.is_comb_base_change E H Dw l Xo _ _ φ (genFr h Z).x _ _ _ _ (hy₀c (Small.labelC s) i)
    have hv : (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap (kap Z) (Om Z))) ≫
        y₀.u (Small.labelC s) j) = fun j => (N.pt (Or.Fl.j (ec (Small.labelC s) j))).left := by
      funext j
      rw [hj, ← Category.assoc, spc, ← dualMap_comp₂, hk]
    rw [hbase, hv, comb_iff N] at h1
    rw [h₃.2.1]
    refine h1.trans ?_
    simp only [hcoef]
  obtain ⟨t, ht⟩ : ∃ t, FrBor t y₃ Fr.y₀ := frBor_of_comb y₃ Fr.y₀ hx₃.symm (fun τ i => by
    obtain ⟨s, rfl⟩ := (Small.labelC_bijective H).2 τ
    refine ⟨Tm s i, isUnit_iff_ne_zero.2 (hTd s i), fun j hij => hT0 s i j hij, ?_⟩
    rw [hx₃, hy3 s, comb_iff N]
    exact (hb s i).symm.trans (congrArg (fun e => (N.pt e).left) (hbT s i)))
  refine ⟨{ φ := φ, φ_cst := hφc, t := t, rd_eq := fun a f hf => ?_, deg := ?_ }⟩
  · have h1 := GlobalTheory.T.frame_point_borel_section_scaling E H Dw l Xo c a f RM.Ω t y₃ Fr.y₀ hf ht
    have h2 := ev_map hWD hf.1 φA (genFr h Z) y₃ (hgT Z) h₃
    show evR Xo c f Fr.y₀ = _ * φ (evC h Z f)
    rw [h1, h2]
    rfl
  · refine hφd.trans ?_
    rw [hTr, ← adjoin_all_eq_strict v hv1 hv0]
    exact hvd

end Read

end GlobalTheory.CompanionTheory.Ar.Rec.ReadEx

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem read_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp), CompOf o κ → ∀ (B : ℕ) (Z : Comp Xo c), ∃ Fr : Small.GenFrame (o.Or B (κ Z)), Nonempty (Reading Fr h Z) := by
  intro E _ _ _ H Dw l Xo c r U h e hL Y T o κ hκ B Z
  obtain ⟨Fr⟩ := GlobalTheory.T.root_origin_generic_frame E H Dw l Xo c Y (o.S B) (T.M B (κ Z)) (o.Sys (κ Z)) (o.Fx (κ Z)) (o.Or B (κ Z))
  exact ⟨Fr, ReadEx.read_core (o.Or B (κ Z)) Fr h Z hL.genT hL.evalWD (hκ Z)⟩

end GlobalTheory.CompanionTheory.Ar.Rec
