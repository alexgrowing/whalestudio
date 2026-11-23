import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ParahoricIdxZ
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DatumConjInv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DatumBlockEigen
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.UMultOne
import Formalism.SharpRestriction.AdmissibleParameterJoins.FamilyAuxiliaryPrimeSize
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.CanonicalTranslateJets
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.GoodPartEigenspaceKernelSplitting
import Formalism.DoubleCosetMeasures.StatementV
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions MeasureTheory Matrix ComplexConjugate

theorem arithmetic_real_place_admissible_of (A : TH.ProvA)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond A) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine A)
    (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth A) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth A) : Formalism.MainNotions.ZetaProductPairs.adm8 A :=
  ⟨h1, h2, h3, h4, h5⟩

theorem archimedean_hypothesis_of_items (D : D7) (Y : Formalism.MainNotions.SchurIrreducible.Prov D)
    (h : Formalism.MainNotions.SchurIrreducible.Conclusion1 D Y ∧ Formalism.MainNotions.SchurIrreducible.Conclusion2 D Y ∧ Formalism.MainNotions.SchurIrreducible.PointsLemma D Y ∧ Formalism.MainNotions.SchurIrreducible.Conclusion4 D Y ∧
      Formalism.MainNotions.SchurIrreducible.Conclusion5 D Y) : Formalism.MainNotions.ZetaProductPairs.adm8 Y.toProvA := h

theorem second_lemma_hypothesis_same (D : D7) (Z : DivX D) (h : Formalism.MainNotions.ZetaProductPairs.L2 Z) : Formalism.MainNotions.InnerProductFormulaField.adm6 D Z := h

def LemmaUInst (qn : ℝ) (a t idx : ℕ) (Zv : ℂ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : TopologicalSpace F) (_ : IsTopologicalRing F) (_ : T2Space F)
    (_ : SecondCountableTopology F) (_ : MeasurableSpace F) (_ : BorelSpace F) (O : Subring F)
    (_ : IsOpen (O : Set F)) (ϖ : F) (hϖ : ϖ ∈ O) (_ : ϖ ≠ 0) (_ : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ)
    (_ : Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) (J' : Subgroup (GL (Fin a) F))
    (_ : Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J') (_ : J' ≤ Formalism.DoubleCosetMeasures.GLint O a)
    (_ : IsCompact (J' : Set (GL (Fin a) F)))
    (ρ : J' →* ℂˣ) (_ : ∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1)
    (χ : Fˣ →* ℂˣ) (nrm : AbsoluteValue F ℝ) (lam : J' →* ℂˣ)
    (_ : ∀ k : J', ((χ (Matrix.GeneralLinearGroup.det (k : GL (Fin a) F)) : ℂˣ) : ℂ) *
        (((nrm ((Matrix.GeneralLinearGroup.det (k : GL (Fin a) F) : Fˣ) : F)) ^
          (((a + t : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((ρ k : ℂˣ) : ℂ) * conj ((lam k : ℂˣ) : ℂ) = 1)
    (c : GL (Fin a) F → ℂ) (_ : ∀ g : GL (Fin a) F, ∀ k : J', c (g * k) = ((lam k : ℂˣ) : ℂ) * c g)
    (_ : c 1 = 1)
    (μ : Measure (GL (Fin a) F)) (_ : μ.IsMulLeftInvariant) (_ : μ (J' : Set (GL (Fin a) F)) = 1)
    (ν₁ : Measure (Matrix (Fin a) (Fin a) F)) (_ : ν₁.IsAddLeftInvariant) (_ : SFinite ν₁)
    (_ : ν₁ (Formalism.DoubleCosetMeasures.intMat O a a) = 1)
    (ν₂ : Measure (Matrix (Fin t) (Fin a) F)) (_ : ν₂.IsAddLeftInvariant) (_ : SFinite ν₂)
    (_ : ν₂ (Formalism.DoubleCosetMeasures.intMat O t a) = 1)
    (J : Subgroup (GL (Fin (a + t)) F)) (_ : ∀ A, A ∈ J ↔ Formalism.MainNotions.ZetaProductPairs.blockCond O ϖ J' A),
    qn = (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) : ℝ) ∧
    idx = (J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index ∧
    Zv = Formalism.DoubleCosetMeasures.localZ μ ((ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2)) χ nrm
          (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) (Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ) c

theorem L1index_inst (h : Formalism.MainNotions.ZetaProductPairs.L1index) {qn : ℝ} {a t idx : ℕ} {Zv : ℂ}
    (H : LemmaUInst qn a t idx Zv) :
    (idx : ℂ) * ((Formalism.MainNotions.ZetaProductPairs.zetaProd qn (a + t) : ℝ) : ℂ) * Zv =
      ((Formalism.MainNotions.ZetaProductPairs.zetaProd qn t : ℝ) : ℂ) := by
  obtain ⟨F, _, _, _, _, _, _, _, O, hO, ϖ, hϖ, h0, hl, hf, J', hJ1, hJ2, hJc, ρ, hρ, χ, nrm, lam, hc, c, hcl,
    hc1, μ, _, hμ, ν₁, _, _, hν₁, ν₂, _, _, hν₂, J, hJ, rfl, rfl, rfl⟩ := H
  exact h F O hO ϖ hϖ h0 hl hf a t J' hJ1 hJ2 hJc ρ hρ χ nrm lam hc c hcl hc1 μ hμ ν₁ hν₁ ν₂ hν₂ J hJ

structure TieG (D : D7) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) : Prop where
  ch : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ, ∀ v ∈ X.Sg,
    LemmaUInst (Formalism.MainNotions.InnerProductFormulaField.normPl v) (D.R.r + (j - 1) * D.R.t) D.R.t (X.idxgCh μ j v) (X.ZgCh μ j σ v)
  sb : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ σ, ∀ v ∈ X.Sg,
    LemmaUInst (Formalism.MainNotions.InnerProductFormulaField.normPl v) D.R.r D.R.t (X.idxgSb μ j v) (X.ZgSb μ j σ v)

theorem parahoric_index_hypothesis (D : D7) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (T : TieG D X) (h : Formalism.MainNotions.ZetaProductPairs.L1index) :
    Formalism.MainNotions.InnerProductFormulaField.adm5 D X := by
  intro μ j hj hj' σ v hv
  refine ⟨?_, L1index_inst h (T.sb μ j hj hj' σ v hv)⟩
  have := L1index_inst h (T.ch μ j hj hj' σ v hv)
  have e : D.R.r + (j - 1) * D.R.t + D.R.t = D.R.r + j * D.R.t := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [e] at this
  exact this

theorem parahoric_index_hypothesis_proved (D : D7) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (T : TieG D X) : Formalism.MainNotions.InnerProductFormulaField.adm5 D X :=
  parahoric_index_hypothesis D X T parahoric_index_int

theorem real_type_of_uniform_type {D : D7} (T : ThetaX D) (h : Formalism.MainNotions.InnerProductFormulaField.TieRowTyp T) : Formalism.MainNotions.ZetaProductPairs.TieRowTyp T :=
  fun μ x => h μ D.R.m le_rfl x

theorem multiplicity_bundle_first_part {D : D7} {T : ThetaX D} (X : Formalism.MainNotions.ZetaProductPairs.Loc D T) (h : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneConditional X) :
    Formalism.MainNotions.ZetaProductPairs.UnfoldingScalarUnitary X :=
  fun u => let ⟨hF, hU, s, hs, h0, _⟩ := h u; ⟨hF, hU, s, hs, h0⟩

theorem real_constant_hypothesis_of_lift {D : D7} {T : ThetaX D} (X : Formalism.MainNotions.ZetaProductPairs.Loc D T) (h : Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing D T X) :
    Formalism.MainNotions.ZetaProductPairs.RealConstantNonvanishing X := h

theorem multiplicity_closed_of_constant {D : D7} {T : ThetaX D} (X : Formalism.MainNotions.ZetaProductPairs.Loc D T) (h : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneConditional X)
    (h6 : Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing D T X) : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneExplicit X := by
  intro u
  obtain ⟨hF, hU, s, hs, -, hMI⟩ := h u
  obtain ⟨c, hc, hA, hne⟩ := h6 u
  exact ⟨hF, hU, s, c, hs, hc, hA, hMI c hc hA hne⟩

theorem HypG_of_WtHyp {D : D7} (T : ThetaX D) (hW : Formalism.MainNotions.ZetaProductPairs.WtHyp T) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (τ : D.what₂.Tau) (al be ga de : List ℚ) (c c' : ℚ)
    (h1 : ∀ a, (TH.lamA al be ga de a + c, a.isLeft) ∈ (Formalism.MainNotions.ZetaProductPairs.parD T).Dpar j τ)
    (h2 : ∀ a, (TH.lamA' D.R.t al be ga de a + c', a.isLeft) ∈ (Formalism.MainNotions.ZetaProductPairs.parD T).Dpar (j + 1) τ)
    (hp : al.length + be.length = (sigYD D.R j).1) (hq : ga.length + de.length = (sigYD D.R j).2)
    (hn : al.length + be.length + ga.length + de.length = D.R.rankY j) :
    TH.HypG D.R.t al be ga de := by
  have sb : ∀ {p q : ℕ} (a b : TH.Ix p q), ¬ TH.sameBlock a b → a.isLeft ≠ b.isLeft := by
    intro p q a b
    cases a <;> cases b <;> simp [TH.sameBlock]
  have hM : (((al.length + be.length + ga.length + de.length + D.R.t : ℕ) : ℝ)) ^ 3 ≤
      ((D.R.rankY D.R.m : ℝ)) ^ 3 := by
    have : al.length + be.length + ga.length + de.length + D.R.t ≤ D.R.rankY D.R.m := by
      rw [hn]
      unfold Ranks.rankY
      have := Nat.mul_le_mul_right D.R.t hj
      nlinarith
    gcongr
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · have k := (hW.2.2 j (by omega) τ _ (h1 a) _ (h1 b) (sb a b hab)).1
    have e : TH.lamA al be ga de a + c - (TH.lamA al be ga de b + c) =
        TH.lamA al be ga de a - TH.lamA al be ga de b := by ring
    simp only [e] at k
    exact lt_of_le_of_lt hM k
  · have k := (hW.2.2 (j + 1) hj τ _ (h2 a) _ (h2 b) (sb a b hab)).1
    have e : TH.lamA' D.R.t al be ga de a + c' - (TH.lamA' D.R.t al be ga de b + c') =
        TH.lamA' D.R.t al be ga de a - TH.lamA' D.R.t al be ga de b := by ring
    simp only [e] at k
    exact lt_of_le_of_lt hM k
  · have k := (hW.2.2 j (by omega) τ _ (h1 a) _ (h1 b) (sb a b hab)).2
    have e : TH.lamA al be ga de a + c - (TH.lamA al be ga de b + c) =
        TH.lamA al be ga de a - TH.lamA al be ga de b := by ring
    simp only [e] at k
    have e1 : ((al.length + be.length + ga.length + de.length : ℕ) : ℝ) = (D.R.rankY j : ℝ) := by
      rw [hn]
    have e2 : ((min (al.length + be.length) (ga.length + de.length) : ℕ) : ℝ) =
        ((min (sigYD D.R j).1 (sigYD D.R j).2 : ℕ) : ℝ) := by rw [hp, hq]
    rw [e1, e2]
    exact k

theorem HypA_mod_of_WtHyp {D : D7} (T : ThetaX D) (hW : Formalism.MainNotions.ZetaProductPairs.WtHyp T) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) {p q : ℕ} (lam : TH.Ix p q → ℚ)
    (h1 : ∀ a, (lam a + (-(Formalism.MainNotions.ZetaProductPairs.parD T).e τ ⟨j, hj⟩ +
      (if Odd j then (Formalism.MainNotions.ZetaProductPairs.parD T).eta τ else 0)), a.isLeft) ∈ (Formalism.MainNotions.ZetaProductPairs.parD T).Dpar j τ) :
    ∀ a, ((D.R.t : ℚ) + 3) / 2 ≤ |lam a| := by
  intro a
  obtain ⟨hv, hb, hbl⟩ := (hW.2.1 τ ⟨j, hj⟩).2
  have h := h1 a
  unfold TH.TPar.Dpar at h
  rw [Finset.mem_image] at h
  obtain ⟨x, hx, e⟩ := h
  have e1 : lam a = x.1 + (Formalism.MainNotions.ZetaProductPairs.parD T).e τ ⟨j, hj⟩ := by
    have := congrArg Prod.fst e
    simp only at this
    linarith
  rw [e1]
  rw [Finset.mem_union, Finset.mem_union] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hv i
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    have := hb i
    rwa [show (Formalism.MainNotions.ZetaProductPairs.parD T).e τ ⟨j, hj⟩ - (Formalism.MainNotions.ZetaProductPairs.parD T).b τ i =
      -(Formalism.MainNotions.ZetaProductPairs.parD T).b τ i + (Formalism.MainNotions.ZetaProductPairs.parD T).e τ ⟨j, hj⟩ by ring] at this
  · obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hij : i ≠ ⟨j, hj⟩ := by
      intro h
      have := (Finset.mem_filter.mp hi).2
      rw [h] at this
      exact lt_irrefl _ this
    exact hbl i hij y hy

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem archimedean_statement_iff_local (D : D7) (X : Formalism.MainNotions.SchurIrreducible.Prov D) :
    Formalism.MainNotions.SchurIrreducible.Stmt D X ↔ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisLocal D X := Iff.rfl

theorem arakelov_clauses_admissible_of (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (h0 : Formalism.MainNotions.SchurIrreducible.DiscreteSeriesBlattner X.ar)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X.ar) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X.ar) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X.ar)
    (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X.ar) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X.ar) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm13 D X :=
  ⟨h0, h1, h2, h3, h4, h5⟩

theorem decomposition_hypothesis_of_items (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (Y : Formalism.MainNotions.SchurIrreducible.Prov D)
    (hY : Y.toProvA = X.ar) (h0 : Formalism.MainNotions.SchurIrreducible.adm3 D Y)
    (h : Formalism.MainNotions.SchurIrreducible.Conclusion1 D Y ∧ Formalism.MainNotions.SchurIrreducible.Conclusion2 D Y ∧ Formalism.MainNotions.SchurIrreducible.PointsLemma D Y ∧ Formalism.MainNotions.SchurIrreducible.Conclusion4 D Y ∧
      Formalism.MainNotions.SchurIrreducible.Conclusion5 D Y) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm13 D X := by
  unfold Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm13
  rw [← hY]
  exact ⟨h0, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem decomposition_iff_archimedean (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (Y : Formalism.MainNotions.SchurIrreducible.Prov D)
    (hY : Y.toProvA = X.ar) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm8 D X ↔ Formalism.MainNotions.SchurIrreducible.ArchimedeanSignatureMatching D Y := by
  unfold Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm8 Formalism.MainNotions.SchurIrreducible.ArchimedeanSignatureMatching
  rw [hY]

def ArchimedeanChainApplication (D : D7) (T : ThetaX D) (A : ProvA) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.WtHyp T →
    (∀ j, 1 ≤ j → j ≤ D.R.m →
      ∃ z : D.what₂.Tau → ℂ, (∀ τ, Formalism.MainNotions.InnerProductFormulaField.IsARZ A (z τ)) ∧ ((X.ZChR j : ℝ) : ℂ) = ∏ τ, z τ) ∧
    (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < X.ZSbR j ∧ 0 < X.nT j) ∧
    (∀ (μ : D.what₂.Tup) (i l : ℕ), i < D.R.m → 1 ≤ l → l ≤ (sigYD D.R (i + 1)).2 →
      ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)) (G : T.cusp (D.sp.Y i)), Formalism.MainNotions.InnerProductFormulaField.IsTypeD T i G →
        Formalism.MainNotions.InnerProductFormulaField.thS T μ i _ Φ G = 0)

theorem archimedean_hypothesis_of_parts (D : D7) (T : ThetaX D) (A : ProvA) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (h : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A)
    (hc : ArchimedeanChainApplication D T A X) : Formalism.MainNotions.InnerProductFormulaField.adm3 D T A X := ⟨h, hc⟩

theorem IsARZ_pos (A : ProvA) (h : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A) {z : ℂ} (H : Formalism.MainNotions.InnerProductFormulaField.IsARZ A z) :
    ∃ x : ℝ, 0 < x ∧ z = (x : ℂ) := by
  rcases H with ⟨t, al, be, ga, de, hd, Φ, v, hΦ, hv, rfl⟩ | ⟨t, al, be, ga, de, hd, Φ, v, hΦ, hv, rfl⟩
  · obtain ⟨-, h2, h3, -⟩ := (h.1 t al be ga de hd).2 Φ v hΦ hv
    exact ⟨_, div_pos (pow_pos h3 2) (A.ds _ _ _).fdeg_pos, h2⟩
  · obtain ⟨-, h2, h3, -⟩ := (h.2 t al be ga de hd).2 Φ v hΦ hv
    exact ⟨_, div_pos (pow_pos h3 2) (A.ds _ _ _).fdeg_pos, h2⟩

theorem real_integral_positive_of_chain (D : D7) (T : ThetaX D) (A : ProvA) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (h : Formalism.MainNotions.InnerProductFormulaField.adm3 D T A X)
    (hW : Formalism.MainNotions.ZetaProductPairs.WtHyp T) : ∀ j, 1 ≤ j → j ≤ D.R.m → 0 < X.ZChR j := by
  intro j h1 h2
  obtain ⟨z, hz, e⟩ := (h.2 hW).1 j h1 h2
  choose x hx hxe using fun τ => IsARZ_pos A h.1 (hz τ)
  have : ((X.ZChR j : ℝ) : ℂ) = ((∏ τ, x τ : ℝ) : ℂ) := by
    rw [e, Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun τ _ => hxe τ
  rw [Complex.ofReal_inj.mp this]
  exact Finset.prod_pos fun τ _ => hx τ

theorem up_lift_lands_in_kernel (D : D7) (h : Formalism.MainNotions.PrimeDegreeVariant.ThetaUpInV0 D) : Formalism.MainNotions.InnerProductFormulaField.adm10 D := h

theorem transfer_hypothesis_of_isotypic (D : D7) (hI : Rows.IsotInternal D.what₂) (hR : Rows.IsotRank D.what₂)
    (h3 : Formalism.MainNotions.PrimeDegreeVariant.ExactRowOccurrence D) : Formalism.MainNotions.InnerProductFormulaField.adm11 D := ⟨hI, hR, h3⟩

theorem isot_ne_bot (D : D7) (h3 : Formalism.MainNotions.PrimeDegreeVariant.ExactRowOccurrence D) (hr : Rows.IsotRank D.what₂) :
    Formalism.MainNotions.InnerProductFormulaField.IsotypicPartsNonzero D := by
  intro j h1 h2 π hb
  have := hr j h1 h2 π
  rw [hb, finrank_bot] at this
  exact (h3 π).ne this

theorem fock_hypothesis_of_lift_theorem (D : D7) (Z : DivX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (h : Formalism.MainNotions.InnerProductFormulaField.ConjugationNormInvariance D Z X) :
    Formalism.MainNotions.CanonicalTranslateJets.ArchimedeanSignatureMatching D :=
  fun μ j hj σ => ⟨(h μ j hj.1 hj.2 σ).1, fun hne => ((h μ j hj.1 hj.2 σ).2 hne).1⟩

theorem LamPDef_of (D : D7) (Z : DivX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (h : Formalism.MainNotions.InnerProductFormulaField.ConjugationNormInvariance D Z X) :
    Rows.LamPDef D.what₂ := fun μ j h1 h2 σ => (h μ j h1 h2 σ).1

theorem LamEig_of_LamPDef (D : D7) (h : Rows.LamPDef D.what₂) : Formalism.MainNotions.InnerProductFormulaField.LamEig D := by
  intro μ j h1 h2 π c hne hc
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact smul_left_injective ℂ hx0 ((h μ j h1 h2 π x hx).symm.trans (hc x hx))

theorem lambda_positivity_admissible_of_def (D : D7) (h : Rows.LamPDef D.what₂)
    (hp : ∀ μ j, Formalism.MainNotions.CanonicalTranslateJets.InR D j → ∀ σ, D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ) :
    Formalism.MainNotions.CanonicalTranslateJets.ArchimedeanSignatureMatching D :=
  fun μ j hj σ => ⟨fun x hx => h μ j hj.1 hj.2 σ x hx, hp μ j hj σ⟩

theorem eigenvalues_positive_of_surjective (D : D7) (h : Rows.LamPDef D.what₂)
    (hs : ∀ μ j, Formalism.MainNotions.CanonicalTranslateJets.InR D j → Function.Surjective (D.what₂.thetaP μ j)) :
    Formalism.MainNotions.CanonicalTranslateJets.ArchimedeanSignatureMatching D := by
  refine lambda_positivity_admissible_of_def D h fun μ j hj σ hne => ?_
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have e := h μ j hj.1 hj.2 σ x hx
  have hT : D.what₂.thetaT μ j x ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := hs μ j hj x
    have : inner ℂ x x = (0 : ℂ) := by
      conv_lhs => rw [← hz]
      have := LinearMap.adjoint_inner_left (D.what₂.thetaP μ j) z x
      unfold Rows.Data.thetaT at h0
      rw [h0, inner_zero_left] at this
      rw [hz] at this ⊢
      exact this.symm
    exact hx0 (inner_self_eq_zero.mp this)
  have k : ((D.what₂.lamP μ j σ : ℝ) : ℂ) * inner ℂ x x =
      inner ℂ (D.what₂.thetaT μ j x) (D.what₂.thetaT μ j x) := by
    rw [← inner_smul_right, ← e]
    unfold Rows.Data.thetaT
    rw [LinearMap.adjoint_inner_left]
  have k' : D.what₂.lamP μ j σ * ‖x‖ ^ 2 = ‖D.what₂.thetaT μ j x‖ ^ 2 := by
    have h1 := congrArg Complex.re k
    rw [Complex.re_ofReal_mul] at h1
    have a1 : (inner ℂ x x).re = ‖x‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) x
    have a2 : (inner ℂ (D.what₂.thetaT μ j x) (D.what₂.thetaT μ j x)).re = ‖D.what₂.thetaT μ j x‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (D.what₂.thetaT μ j x)
    rw [a1, a2] at h1
    exact h1
  have p1 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
  have p2 : 0 < ‖D.what₂.thetaT μ j x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hT) 2
  exact (mul_pos_iff_of_pos_right p1).mp (k' ▸ p2)

def Qof (D : D7) (μ : D.what₂.Tup) (ι : D.what₂.Amb μ →ₗ[ℂ] D.what₂.EE) : Submodule ℂ (D.what₂.Amb μ) :=
  D.what₂.V0 μ ⊓ (D.what₂.V0 μ ⊓ LinearMap.ker ι)ᗮ

def BijOn (D : D7) (μ : D.what₂.Tup) (ι : D.what₂.Amb μ →ₗ[ℂ] D.what₂.EE) : Prop :=
  Function.Bijective (ι.domRestrict (Qof D μ ι))

def AdjOn (D : D7) (μ : D.what₂.Tup) (ι : D.what₂.Amb μ →ₗ[ℂ] D.what₂.EE) (y z : D.what₂.EE) : Prop :=
  (ι.domRestrict (Qof D μ ι) ∘ₗ LinearMap.adjoint (ι.domRestrict (Qof D μ ι))) y = z

theorem sharp_bij_iff (D : D7) (μ : D.what₂.Tup) :
    Function.Bijective ((RowSide.sharp D).iotaQ μ) ↔ Function.Bijective (Formalism.MainNotions.InnerProductFormulaField.iotaQ D μ) := by
  have h : BijOn D μ ((RowSide.sharp D).iota μ) ↔ BijOn D μ (D.what₂.iota μ) := by
    rw [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota]
  exact h

theorem sharp_adj_iff (D : D7) (μ : D.what₂.Tup) (y z : D.what₂.EE) :
    ((RowSide.sharp D).iotaQ μ ∘ₗ LinearMap.adjoint ((RowSide.sharp D).iotaQ μ)) y = z ↔
      (Formalism.MainNotions.InnerProductFormulaField.iotaQ D μ ∘ₗ LinearMap.adjoint (Formalism.MainNotions.InnerProductFormulaField.iotaQ D μ)) y = z := by
  have h : AdjOn D μ ((RowSide.sharp D).iota μ) y z ↔ AdjOn D μ (D.what₂.iota μ) y z := by
    rw [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota]
  exact h

theorem tuple_data_of_lift_rows (D : D7) (Z : DivX D) (h : Formalism.MainNotions.InnerProductFormulaField.PointsLemma D Z) (μ : D.what₂.Tup) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataTup D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D) μ (Z.kapR D.what₂.embLL) :=
  ⟨(sharp_bij_iff D μ).2 (h μ).1, fun σ => (sharp_adj_iff D μ _ _).2 ((h μ).2 σ)⟩

theorem prod_Icc_one_eq_factorial (N : ℕ) : ∏ x ∈ Finset.Icc 1 N, x = N.factorial := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]

theorem hook_row (n i : ℕ) (z : ℕ → ℕ) (hmono : ∀ i l, i < l → l < n → z l ≤ z i) :
    ∏ l ∈ Finset.Ioo i n, (z i - z l + l - i) ≤ (z i + n - 1 - i).factorial := by
  rw [← prod_Icc_one_eq_factorial]
  have hinj : ∀ l ∈ Finset.Ioo i n, ∀ l' ∈ Finset.Ioo i n,
      z i - z l + l - i = z i - z l' + l' - i → l = l' := by
    intro l hl l' hl' h
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
    obtain ⟨h1', h2'⟩ := Finset.mem_Ioo.mp hl'
    have a1 := hmono i l h1 h2
    have a2 := hmono i l' h1' h2'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hmono l l' hlt h2'
      omega
    · have := hmono l' l hlt h2
      omega
  calc ∏ l ∈ Finset.Ioo i n, (z i - z l + l - i)
      = ∏ x ∈ (Finset.Ioo i n).image (fun l => z i - z l + l - i), x :=
        (Finset.prod_image (f := fun x => x) hinj).symm
    _ ≤ ∏ x ∈ Finset.Icc 1 (z i + n - 1 - i), x := by
        refine Finset.prod_le_prod_of_subset_of_one_le' ?_ (fun x hx _ => (Finset.mem_Icc.mp hx).1)
        intro x hx
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
        have a1 := hmono i l h1 h2
        rw [Finset.mem_Icc]
        omega

theorem logHk_nonneg (n : ℕ) (a : ℕ → ℝ) (z : ℕ → ℕ) (ha : ∀ i < n, a i = z i)
    (hmono : ∀ i l, i < l → l < n → z l ≤ z i) : 0 ≤ Formalism.MainNotions.InnerProductFormulaField.logHk n a := by
  unfold Formalism.MainNotions.InnerProductFormulaField.logHk
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hG : Real.Gamma (a i + n - i) = ((z i + n - 1 - i).factorial : ℝ) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = i + k + 1 := ⟨n - i - 1, by omega⟩
    have e : z i + (i + k + 1) - 1 - i = z i + k := by omega
    rw [e, ← Real.Gamma_nat_eq_factorial, ha i hi']
    congr 1
    push_cast
    ring
  have hS : ∑ l ∈ Finset.Ioo i n, Real.log (a i - a l + l - i) =
      Real.log ((∏ l ∈ Finset.Ioo i n, (z i - z l + l - i) : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun l hl => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
      have a1 := hmono i l h1 h2
      have e : z i - z l + l - i = (z i - z l) + (l - i) := by omega
      rw [e, ha i hi', ha l h2, Nat.cast_add, Nat.cast_sub a1, Nat.cast_sub h1.le]
      congr 1
      ring
    · intro l hl
      obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
      have : 0 < z i - z l + l - i := by omega
      exact_mod_cast this.ne'
  rw [hG, hS, sub_nonneg]
  refine Real.log_le_log ?_ (by exact_mod_cast hook_row n i z hmono)
  have : 0 < ∏ l ∈ Finset.Ioo i n, (z i - z l + l - i) := by
    refine Finset.prod_pos fun l hl => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hl
    omega
  exact_mod_cast this

def APlusPart (D : D7) (j : ℕ) : Prop :=
  ∀ τ, ∃ z : ℕ → ℕ, (∀ i < (D.R.sigW j).1, DV.aPlus D j τ i = z i) ∧
    ∀ i l, i < l → l < (D.R.sigW j).1 → z l ≤ z i

theorem sumHkP_nonneg (D : D7) (j : ℕ) (h : APlusPart D j) : 0 ≤ Formalism.MainNotions.InnerProductFormulaField.sumHkP D j :=
  Finset.sum_nonneg fun τ _ => let ⟨z, h1, h2⟩ := h τ; logHk_nonneg _ _ z h1 h2

theorem APlusPart_of (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hdec : ∀ τ i i', i ≤ i' → i' < (D.R.sigW j).1 → DV.aPlus D j τ i' ≤ DV.aPlus D j τ i) : APlusPart D j := by
  intro τ
  choose zz hz using fun i => DV.aPlusQ_int D j τ i
  have hR : ∀ i, DV.aPlus D j τ i = ((zz i : ℤ) : ℝ) := fun i => by
    unfold DV.aPlus
    rw [hz i]
    norm_cast
  have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have hlast : (1 : ℝ) ≤ DV.aPlus D j τ (D.R.k + j - 1 - 1) := by
    have := DV.aPlusQ_last D j h1 h2 τ
    unfold DV.aPlus
    exact_mod_cast this
  have hpos : ∀ i < (D.R.sigW j).1, 0 ≤ zz i := by
    intro i hi
    have h := hdec τ i (D.R.k + j - 1 - 1) (by rw [hp] at hi; omega) (by rw [hp]; omega)
    have h' : (1 : ℝ) ≤ ((zz i : ℤ) : ℝ) := by rw [← hR]; linarith
    have h'' : (1 : ℤ) ≤ zz i := by exact_mod_cast h'
    omega
  refine ⟨fun i => (zz i).toNat, fun i hi => ?_, fun i l hil hl => ?_⟩
  · rw [hR]
    have := Int.toNat_of_nonneg (hpos i hi)
    exact_mod_cast this.symm
  · have h := hdec τ i l hil.le hl
    rw [hR, hR] at h
    have h' : zz l ≤ zz i := by exact_mod_cast h
    exact Int.toNat_le_toNat h'

theorem sumHkP_nonneg_of (D : D7)
    (hdec : ∀ j ∈ SizeData₂.lifts D, ∀ τ i i', i ≤ i' → i' < (D.R.sigW j).1 → DV.aPlus D j τ i' ≤ DV.aPlus D j τ i) :
    ∀ j ∈ SizeData₂.lifts D, 0 ≤ Formalism.MainNotions.InnerProductFormulaField.sumHkP D j := fun j hj =>
  sumHkP_nonneg D j (APlusPart_of D j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 (hdec j hj))

theorem hkSigPar_lt (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) < DV.sigPar D τ i := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dif_pos h1, dif_pos h0]
    have a := (D.hc τ).u_gt_v ⟨i + 1, h1⟩
    have b := (D.hc τ).v_gt_u ⟨i, h0⟩
    exact a.trans b
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb, dif_pos h0]
      have a := (D.hc τ).u_last_gt (by omega) (by omega)
      have b := (D.hc τ).v_gt_u ⟨i, h0⟩
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      have e2 : (⟨i + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have b' : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        rw [← e2]
        exact b
      exact a.trans b'
    · have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb2 : i - (D.R.k - 1) + 1 < D.R.m := by omega
      rw [dif_neg h1, dif_pos hb1, dif_neg h0, dif_pos hb0]
      have a := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have b := (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ hb2
      have e1 : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, hb2⟩ := by
        rw [Fin.mk.injEq]
        omega
      rw [e1]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  obtain ⟨a, ha⟩ := DV.sigPar_int D τ i
  obtain ⟨b, hb⟩ := DV.sigPar_int D τ (i + 1)
  have h := hkSigPar_lt D τ i hi
  rw [ha, hb] at h
  have h' : b < a := by exact_mod_cast h
  have h'' : (b : ℚ) + 1 ≤ a := by exact_mod_cast h'
  rw [DV.aPlusQ_eq, DV.aPlusQ_eq, ha, hb]
  push_cast
  linarith

theorem aPlus_dec (D : D7) (j : ℕ) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (i i' : ℕ) (h : i ≤ i')
    (hi' : i' < (D.R.sigW j).1) : DV.aPlus D j τ i' ≤ DV.aPlus D j τ i := by
  have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have hk := D.R.m_add_three_le_k
  rw [hp] at hi'
  have hQ : DV.aPlusQ D j τ i' ≤ DV.aPlusQ D j τ i := by
    induction i', h using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (aPlusQ_step D j τ n (by omega)).trans (ih (by omega))
  unfold DV.aPlus
  exact_mod_cast hQ

theorem sumHkP_nonneg_rec (D : D7) : ∀ j ∈ SizeData₂.lifts D, 0 ≤ Formalism.MainNotions.InnerProductFormulaField.sumHkP D j :=
  sumHkP_nonneg_of D fun j hj τ i i' h hi' => aPlus_dec D j (Finset.mem_Icc.mp hj).2 τ i i' h hi'

theorem logHk_nonneg_of_int (n : ℕ) (a : ℕ → ℝ) (zz : ℕ → ℤ) (ha : ∀ i, a i = zz i)
    (hdec : ∀ i l, i < l → l < n → zz l ≤ zz i) (hpos : ∀ i < n, 0 ≤ zz i) : 0 ≤ Formalism.MainNotions.InnerProductFormulaField.logHk n a :=
  logHk_nonneg n a (fun i => (zz i).toNat)
    (fun i hi => by rw [ha]; exact_mod_cast (Int.toNat_of_nonneg (hpos i hi)).symm)
    (fun i l h1 h2 => Int.toNat_le_toNat (hdec i l h1 h2))

theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c + 1 < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  have h1 : j + (c + 1) < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dif_pos h0, dif_pos h1]
  have a := (D.hc τ).gap_be ⟨j + c, h0⟩
  have b := (D.hc τ).gap_eb ⟨j + c, h0⟩ hc
  have e1 : (⟨j + (c + 1), h1⟩ : Fin D.R.m) = ⟨j + c + 1, hc⟩ := by
    rw [Fin.mk.injEq]
    omega
  rw [e1]
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c c' : ℕ) (h : c ≤ c') (hc' : j + c' < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ c' := by
  induction c', h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (ih (by omega)).trans (aMinusQ_step D j τ n (by omega))

theorem aMinusQ_first (D : D7) (j : ℕ) (h1 : 1 ≤ j) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    1 ≤ DV.aMinusQ D j τ 0 := by
  have h0 : j + 0 < D.R.m := by omega
  have h2 : j - 1 + 1 < D.R.m := by omega
  unfold DV.aMinusQ DV.eQ
  rw [dif_pos h0, dif_pos ⟨h1, hj.le⟩]
  have b := (D.hc τ).gap_eb ⟨j - 1, by omega⟩ h2
  have e1 : (⟨j + 0, h0⟩ : Fin D.R.m) = ⟨j - 1 + 1, h2⟩ := by
    rw [Fin.mk.injEq]
    omega
  rw [e1]
  push_cast
  linarith

theorem sumHkM_nonneg_rec (D : D7) (j : ℕ) (h1 : 1 ≤ j) : 0 ≤ Formalism.MainNotions.InnerProductFormulaField.sumHkM D j := by
  unfold Formalism.MainNotions.InnerProductFormulaField.sumHkM
  refine Finset.sum_nonneg fun τ _ => ?_
  have hq : (D.R.sigW j).2 = D.R.m - j := rfl
  rw [hq]
  choose zz hz using fun c => DV.aMinusQ_int D j τ c
  refine logHk_nonneg_of_int _ _ (fun i => zz (D.R.m - j - 1 - i)) (fun i => ?_) (fun i l hil hl => ?_)
    (fun i hi => ?_)
  · unfold DV.aMinus
    rw [hz]
    norm_cast
  · have h := aMinusQ_mono D j τ (D.R.m - j - 1 - l) (D.R.m - j - 1 - i) (by omega) (by omega)
    rw [hz, hz] at h
    exact_mod_cast h
  · have a := aMinusQ_first D j h1 (by omega) τ
    have b := aMinusQ_mono D j τ 0 (D.R.m - j - 1 - i) (by omega) (by omega)
    have c := a.trans b
    rw [hz] at c
    have c' : (1 : ℤ) ≤ zz (D.R.m - j - 1 - i) := by exact_mod_cast c
    show 0 ≤ zz (D.R.m - j - 1 - i)
    omega

theorem real_size_hypotheses_of_bounds (D : D7) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (L : SizeData₂ D) (C : ℝ)
    (h1 : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π,
      |Real.log (X.LsS μ j π).re - Real.log (X.dFin D.R.r).re| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * Formalism.MainNotions.InnerProductFormulaField.Lp D L)
    (h2 : ∀ j, 1 ≤ j → j ≤ D.R.m →
      |Real.log (X.ZSbR j) - Formalism.MainNotions.InnerProductFormulaField.sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * Formalism.MainNotions.InnerProductFormulaField.Lp D L)
    (h3 : ∀ j, 1 ≤ j → j ≤ D.R.m →
      |Real.log (X.cSb j * X.massSb j)| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 * Formalism.MainNotions.InnerProductFormulaField.Lp D L) :
    Formalism.MainNotions.InnerProductFormulaField.admS D X L C :=
  ⟨h1, h2, h3, fun j hj _ => sumHkM_nonneg_rec D j hj⟩

theorem lambda_lower_bound_of_lift (D : D7) (Z : DivX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (L : SizeData₂ D) (C b : ℝ)
    (hA : Formalism.MainNotions.InnerProductFormulaField.ConjugationNormInvariance D Z X) (hN : Formalism.MainNotions.InnerProductFormulaField.IsotypicPartsNonzero D) (h6 : Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound D L C)
    (hH : ∀ j ∈ SizeData₂.lifts D, 0 ≤ Formalism.MainNotions.InnerProductFormulaField.sumHkP D j)
    (hsz : C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ b) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow D b := by
  intro j hj σ
  have hj' := Finset.mem_Icc.mp hj
  have hne := hN j hj'.1 hj'.2 σ
  have hpos := ((hA D.what₂.mu0 j hj'.1 hj'.2 σ).2 hne).1
  have h := h6 j hj σ hne
  have h0 := hH j hj
  rw [← Real.le_log_iff_exp_le hpos]
  linarith

theorem data_at_sharp_level_of_lattice (D : D7) (Z : DivX D) (h : Formalism.MainNotions.InnerProductFormulaField.PointsLemma D Z) (b : ℝ) (hb : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow D b) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D) b (Z.kapR D.what₂.embLL) :=
  ⟨⟨fun _ => 1, rfl, fun _ => one_pos, fun μ _ => by rw [mul_one]; exact tuple_data_of_lift_rows D Z h μ⟩, hb⟩

theorem embedding_data_of_lift (D : D7) (Z : DivX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (L : SizeData₂ D) (C : ℝ)
    (h3 : Formalism.MainNotions.InnerProductFormulaField.PointsLemma D Z) (hA : Formalism.MainNotions.InnerProductFormulaField.ConjugationNormInvariance D Z X) (hN : Formalism.MainNotions.InnerProductFormulaField.IsotypicPartsNonzero D)
    (h6 : Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound D L C) (hH : ∀ j ∈ SizeData₂.lifts D, 0 ≤ Formalism.MainNotions.InnerProductFormulaField.sumHkP D j)
    (hsz : C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ L.sc.b) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D) L.sc.b (Z.kapR D.what₂.embLL) :=
  data_at_sharp_level_of_lattice D Z h3 _ (lambda_lower_bound_of_lift D Z X L C _ hA hN h6 hH hsz)

theorem sharp_kap_eq (D : D7) (Z : DivX D) (hk : DV.KapRBase Z) :
    (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D).kap = Z.kapR D.what₂.embLL := hk.symm

theorem row_level_data_of_lift (D : D7) (Z : DivX D) (hk : DV.KapRBase Z) (h : Formalism.MainNotions.InnerProductFormulaField.PointsLemma D Z) (b : ℝ)
    (hb : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow D b) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D) b (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D).kap := by
  rw [sharp_kap_eq D Z hk]
  exact data_at_sharp_level_of_lattice D Z h b hb

def LambdaLowerBoundAllEmbeddings (D : D7) (Z : DivX D) (b : ℝ) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ), ∀ j ∈ SizeData₂.lifts D, ∀ σ, -b ≤ Z.logLam j σ s

theorem lambda_lower_bound_fixed_embedding (D : D7) (Z : DivX D) (b : ℝ) (hb : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow D b) :
    ∀ j ∈ SizeData₂.lifts D, ∀ σ, -b ≤ Z.logLam j σ D.what₂.embLL := by
  intro j hj σ
  have h := hb j hj σ
  rw [Z.logLam_base, Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h)]
  exact h

theorem lambda_lower_bound_other_embeddings (D : D7) (Z : DivX D) (b : ℝ) (hb : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow D b)
    (hc : ∀ s : D.what₂.LL →+* ℂ, s ≠ D.what₂.embLL → ∀ j ∈ SizeData₂.lifts D, ∀ σ, -b ≤ Z.logLam j σ s) :
    LambdaLowerBoundAllEmbeddings D Z b := by
  intro s j hj σ
  by_cases hs : s = D.what₂.embLL
  · rw [hs]
    exact lambda_lower_bound_fixed_embedding D Z b hb j hj σ
  · exact hc s hs j hj σ

theorem sumHk_nonneg_rec (D : D7) : ∀ j ∈ SizeData₂.lifts D, 0 ≤ Formalism.MainNotions.InnerProductFormulaField.sumHk D j := by
  intro j hj
  have e : Formalism.MainNotions.InnerProductFormulaField.sumHk D j = Formalism.MainNotions.InnerProductFormulaField.sumHkP D j + Formalism.MainNotions.InnerProductFormulaField.sumHkM D j := by
    unfold Formalism.MainNotions.InnerProductFormulaField.sumHk Formalism.MainNotions.InnerProductFormulaField.sumHkP Formalism.MainNotions.InnerProductFormulaField.sumHkM
    rw [Finset.sum_add_distrib]
  rw [e]
  exact add_nonneg (sumHkP_nonneg_rec D j hj) (sumHkM_nonneg_rec D j (Finset.mem_Icc.mp hj).1)

theorem lambda_lower_bound_of_positivity (D : D7) (L : SizeData₂ D) (Z : DivX D) (C : ℝ) (h : Formalism.MainNotions.placeRankTwoOne.adm5 D L Z C)
    (hl : Rows.LamPDef D.what₂) (hG : Formalism.MainNotions.placeRankTwoOne.GapsA D L) (hN : Formalism.MainNotions.InnerProductFormulaField.IsotypicPartsNonzero D)
    (hsz : C * D.R.f * (D.R.nV : ℝ) ^ 2 *
      Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV) ≤ L.sc.b) :
    LambdaLowerBoundAllEmbeddings D Z L.sc.b := by
  intro s j hj σ
  have hj' := Finset.mem_Icc.mp hj
  have h1 := ((h hl hG j hj'.1 hj'.2 σ (hN j hj'.1 hj'.2 σ)).2 s)
  have h2 := sumHk_nonneg_rec D j hj
  have e : Formalism.MainNotions.placeRankTwoOne.sumHk D j = Formalism.MainNotions.InnerProductFormulaField.sumHk D j := rfl
  rw [e] at h1
  have h3 := (abs_le.mp h1).1
  linarith

theorem iota_adjoint_scaling_of_sides (D : D7) (Z : DivX D) (h : Formalism.MainNotions.InnerProductFormulaField.PointsLemma D Z) :
    (∀ μ, Function.Bijective (Formalism.MainNotions.LocalQuadraticParts.iotaQ D μ)) ∧
    (0 < Z.kapR D.what₂.embLL ∧ ∃ ρ : D.what₂.Tup → ℝ, ρ D.what₂.mu0 = 1 ∧ (∀ μ, 0 < ρ μ) ∧
    ∀ μ (σ : Fin D.what₂.Drows),
      (Formalism.MainNotions.LocalQuadraticParts.iotaQ D μ ∘ₗ LinearMap.adjoint (Formalism.MainNotions.LocalQuadraticParts.iotaQ D μ)) (D.what₂.onb σ) =
        ((Z.kapR D.what₂.embLL * ρ μ * ∏ j ∈ SizeData₂.lifts D, D.what₂.lamP μ j (D.what₂.ft σ) : ℝ) : ℂ) •
          D.what₂.onb σ) :=
  ⟨fun μ => (h μ).1, Z.kapR_pos _, fun _ => 1, rfl, fun _ => one_pos, fun μ σ => by
    rw [mul_one]; exact (h μ).2 σ⟩

theorem log_lambda_near_heat_sum (D : D7) (Z : DivX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (L : SizeData₂ D) (C : ℝ)
    (hA : Formalism.MainNotions.InnerProductFormulaField.ConjugationNormInvariance D Z X) (hS : Formalism.MainNotions.InnerProductFormulaField.RallisSizeBound D L C) :
    ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ →
    0 < D.what₂.lamP D.what₂.mu0 j σ ∧
    |Z.logLam j σ D.what₂.embLL - Formalism.MainNotions.placeRankTwoOne.sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 *
      Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV) :=
  fun j h1 h2 σ hne => ⟨((hA D.what₂.mu0 j h1 h2 σ).2 hne).1, by
    rw [Z.logLam_base]; exact hS D.what₂.mu0 j h1 h2 σ hne⟩

theorem log_lambda_bound_admissible (D : D7) (Z : DivX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (L : SizeData₂ D) (C : ℝ)
    (hA : Formalism.MainNotions.InnerProductFormulaField.ConjugationNormInvariance D Z X) (hS : Formalism.MainNotions.InnerProductFormulaField.RallisSizeBound D L C)
    (hc : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∀ s, s ≠ D.what₂.embLL →
      |Z.logLam j σ s - Formalism.MainNotions.placeRankTwoOne.sumHk D j| ≤ C * D.R.f * (D.R.nV : ℝ) ^ 2 *
        Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)) :
    Formalism.MainNotions.placeRankTwoOne.adm5 D L Z C := by
  intro _ _ j h1 h2 σ hne
  refine ⟨(log_lambda_near_heat_sum D Z X L C hA hS j h1 h2 σ hne).1, fun s => ?_⟩
  by_cases hs : s = D.what₂.embLL
  · rw [hs]; exact (log_lambda_near_heat_sum D Z X L C hA hS j h1 h2 σ hne).2
  · exact hc j h1 h2 σ hne s hs

theorem positivity_hypothesis_of_galois (D : D7) (Z : DivX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) (L : SizeData₂ D) (Y : Formalism.MainNotions.PGAL.Loc D Z) (C : ℝ)
    (hA : Formalism.MainNotions.InnerProductFormulaField.ConjugationNormInvariance D Z X) (hd : Formalism.MainNotions.PGAL.LogLamDef D Z Y) (h : Formalism.MainNotions.PGAL.LogEigenvalueDeviation D L Z Y C) :
    Formalism.MainNotions.placeRankTwoOne.adm5 D L Z C := by
  intro _ _ j h1 h2 σ hne
  exact ⟨((hA D.what₂.mu0 j h1 h2 σ).2 hne).1, fun s => h hd j h1 h2 σ hne s⟩

theorem lambda_lower_bound_of_galois (D : D7) (L : SizeData₂ D) (Z : DivX D) (Y : Formalism.MainNotions.PGAL.Loc D Z) (C : ℝ)
    (hd : Formalism.MainNotions.PGAL.LogLamDef D Z Y) (h : Formalism.MainNotions.PGAL.LogEigenvalueLowerBound D L Z Y C) (hN : Formalism.MainNotions.InnerProductFormulaField.IsotypicPartsNonzero D)
    (hsz : C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ L.sc.b) : LambdaLowerBoundAllEmbeddings D Z L.sc.b := by
  intro s j hj σ
  have hj' := Finset.mem_Icc.mp hj
  have h1 := h hd j hj σ (hN j hj'.1 hj'.2 σ) s
  have h2 := sumHkP_nonneg_rec D j hj
  linarith

theorem kapR_mk_of_KapConj (D : D7) (Z : DivX D) (h : Formalism.MainNotions.PGAL.KapConj D Z) (s : D.what₂.LL →+* ℂ) :
    Z.kapR (NumberField.InfinitePlace.mk s).embedding = Z.kapR s := by
  rcases NumberField.InfinitePlace.embedding_mk_eq s with e | e
  · rw [e]
  · rw [e]
    exact h s

theorem embedding_data_first_of_sides (D : D7) (Z : DivX D) (P : BaseLevelRowSide D) (h : Formalism.MainNotions.LocalQuadraticParts.adm1 D Z P) :
    ∃ ρ : D.what₂.Tup → ℝ, ρ D.what₂.mu0 = 1 ∧ (∀ μ, 0 < ρ μ) ∧
      ∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ →
        Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataTup D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D) μ (Z.kapR D.what₂.embLL * ρ μ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hb, ⟨-, ρ, h0, hp, -, hρ⟩, -⟩ := h
  exact ⟨ρ, h0, hp, fun μ _ => ⟨(sharp_bij_iff D μ).2 (hb μ), fun σ => (sharp_adj_iff D μ _ _).2 (hρ μ σ)⟩⟩

theorem lambda_positivity_of_lattice_clause (D : D7) (Z : DivX D) (P : BaseLevelRowSide D) (h : Formalism.MainNotions.LocalQuadraticParts.adm1 D Z P) :
    Formalism.MainNotions.CanonicalTranslateJets.ArchimedeanSignatureMatching D := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hθ, hL, -⟩ := h
  refine eigenvalues_positive_of_surjective D hL fun μ j hj y => ?_
  obtain ⟨z, hz⟩ := (hθ μ j (Finset.mem_Icc.mpr hj)).2 y
  exact ⟨z, hz⟩

theorem group_order_hypothesis_both_levels (D : D7) (P : BaseLevelRowSide D) (C : ℝ) (h : Formalism.MainNotions.LocalQuadraticParts.adm9 D P C) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm17 D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D) ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm17 D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.p0 P) := ⟨h.1, h.2.1⟩

theorem embedding_data_of_eigen_clause (D : D7) (V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D) (κ b : ℝ) (h : V.S.RowLatticeBoundForBasis V.onb V.ft κ)
    (hb : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow D b) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt D V b κ := by
  obtain ⟨hbij, -, ρ, h0, hp, -, h⟩ := h
  exact ⟨⟨ρ, h0, hp, fun μ _ => ⟨hbij μ, fun σ => h μ σ⟩⟩, hb⟩

theorem level_data_of_lift_division (D : D7) (V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D) (b : ℝ) (h : Formalism.MainNotions.InnerProductFormulaField.LevelIotaBijective V.S V.onb V.ft)
    (hb : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow D b) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt D V b V.kap :=
  embedding_data_of_eigen_clause D V _ b (Formalism.MainNotions.InnerProductFormulaField.lattice_clause_of_level_bijection V.S V.onb V.ft h) hb

theorem L1c0Def_of (D : D7) (P : BaseLevelRowSide D) (h : Formalism.MainNotions.InnerProductFormulaField.LevelIotaBijective P.s D.what₂.onb0 D.what₂.ft0) : P.BaseLevelSideLevelOneCondition :=
  Formalism.MainNotions.InnerProductFormulaField.lattice_clause_of_level_bijection P.s D.what₂.onb0 D.what₂.ft0 h

theorem uplift_in_V0_at_small_level (D : D7) (P : BaseLevelRowSide D) (h : Formalism.MainNotions.PrimeDegreeVariant.ThetaUpInV0Small P) : Formalism.MainNotions.InnerProductFormulaField.UpliftInV0AtLevel P.s := h

theorem data_at_small_level_of_lattice (D : D7) (P : BaseLevelRowSide D) (b : ℝ) (h : P.BaseLevelSideLevelOneCondition) (hb : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow D b) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.p0 P) b (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.p0 P).kap :=
  embedding_data_of_eigen_clause D (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.p0 P) _ b h hb

theorem eig_real (D : D7) (μ : D.what₂.Tup) (j : ℕ) (x : D.what₂.Mj j) (hx0 : x ≠ 0) (c : ℂ)
    (hc : D.what₂.thetaP μ j (D.what₂.thetaT μ j x) = c • x) :
    c = ((‖D.what₂.thetaT μ j x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) := by
  have e1 : inner ℂ x (D.what₂.thetaP μ j (D.what₂.thetaT μ j x)) =
      inner ℂ (D.what₂.thetaT μ j x) (D.what₂.thetaT μ j x) := by
    unfold Rows.Data.thetaT
    rw [LinearMap.adjoint_inner_left]
  rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e1
  have hn : ((‖x‖ : ℂ)) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    exact_mod_cast this.ne'
  push_cast
  rw [eq_div_iff hn]
  exact e1

theorem LamEig_of_LamDef (D : D7) (h : DV.LamDef D) : Formalism.MainNotions.InnerProductFormulaField.LamEig D := by
  intro μ j h1 h2 π c hne hc
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hr := eig_real D μ j x hx0 c (hc x hx)
  have hc' : ∀ y ∈ D.what₂.isot j π, D.what₂.thetaP μ j (D.what₂.thetaT μ j y) =
      ((‖D.what₂.thetaT μ j x‖ ^ 2 / ‖x‖ ^ 2 : ℝ) : ℂ) • y := by
    intro y hy
    rw [← hr]; exact hc y hy
  rw [h μ j h1 h2 π hne, DV.lamTr_of_scalar D μ j π _ hne hc', ← hr]

def ArchimedeanTheoremFiveParts (A : ProvA) : Prop :=
  Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth A ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth A

def ExtraLowerBoundAtEmbeddings (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} (L : SizeData₂ D) (XD : DivX D) {Am : AmbForm D V.S}
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (C : ℝ) : Prop :=
  (∀ (s : D.what₂.LL →+* ℂ), ∀ j ∈ SizeData₂.lifts D, ∀ σ : Fin V.n, -L.sc.b ≤ XD.logLam j (V.ft σ) s) ∧
  (∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ → ∀ Φ, X.T0 μ Φ ∈ X.Good μ Formalism.MainNotions.AbsolutelyIrreducibleSpan.hBot ∧
    ∀ F ∈ V.S.V0 μ, X.ev μ Formalism.MainNotions.AbsolutelyIrreducibleSpan.hBot (X.T0 μ Φ) F = X.rowUp Φ D.R.m (X.real (V.S.iota μ F))) ∧
  (∀ w Φ, X.T0 (D.what₂.muAt w) Φ ∈ X.IntAt (D.what₂.muAt w) Formalism.MainNotions.AbsolutelyIrreducibleSpan.hBot w 0) ∧
  (∀ v Φ, X.T0 D.what₂.mu0 Φ ∈
    X.SzAt D.what₂.mu0 Formalism.MainNotions.AbsolutelyIrreducibleSpan.hBot v (C * (D.R.m : ℝ) * (X.Nst : ℝ) ^ 2 * X.weightedLogLevelSum))

def SquareLeaves (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} (L : SizeData₂ D) (XD : DivX D) {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am)
    (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) : Prop :=
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.HypSz D L X K ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm1 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm3 D L XD X K.Cint ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.ArchimedeanSignatureMatching D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm8 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm10 K.Ctr ∧
  Formalism.MainNotions.SchurIrreducible.DiscreteSeriesBlattner X.ar ∧
  ExtraLowerBoundAtEmbeddings D L XD X K.Cgr ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm9 D L ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm14 D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm15 D L XD X K.Cgr ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm16 D L X K.Cval ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm17 D V ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm18 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm19 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm20 D L X K.Cfp K.Cfp' ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm21 D L X K.Cip ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm22 D L X K.Cmm ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm23 D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.FrobeniusExpansionCongruence D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrExtensionClause D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm26 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrCocycleExtensionClass D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.FontaineFormalProperties D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.AmbientMetricLowerBound D XD X

theorem square_hypotheses_of_leaves (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} (L : SizeData₂ D) (XD : DivX D) {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am)
    (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) (hAR : ArchimedeanTheoremFiveParts X.ar)
    (hD : Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt D V L.sc.b V.kap) (hL : SquareLeaves D L XD X K) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.HypSz D L X K ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.admitted D L XD X K := by
  obtain ⟨hs, a1, a3, a4, a8, a10, ds1, a2r, a9, rest⟩ := hL
  exact ⟨hs, ⟨a1, a3, a4, a8, a10, (⟨ds1, hAR⟩ : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm13 D X)⟩,
    (⟨hD, a2r⟩ : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm2 D L XD X K.Cgr), a9, Formalism.HN.slopeIneqMean, rest⟩

theorem admissible_of_clauses {D : D7} (T : ThetaX D) (A : ProvA) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond A) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine A)
    (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth A) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth A)
    (a1 : Formalism.MainNotions.ZetaProductPairs.adm1) (a2 : Formalism.MainNotions.ZetaProductPairs.adm2 T) (a3 : Formalism.MainNotions.ZetaProductPairs.adm3) (a5 : Formalism.MainNotions.ZetaProductPairs.adm5 D)
    (a6 : Formalism.MainNotions.ZetaProductPairs.adm6 G) (a7 : Formalism.MainNotions.ZetaProductPairs.adm7) (a8g : Formalism.MainNotions.ZetaProductPairs.ThetaCuspidalChain T) : Formalism.MainNotions.ZetaProductPairs.admitted T A G :=
  ⟨a1, a2, a3, a5, a6, a7, ⟨h1, h2, h3, h4, h5⟩, a8g⟩

theorem lift_hypotheses_of_parts (D : D7) (Z : DivX D) (T : ThetaX D) (A : ProvA) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A) (hL1 : Formalism.MainNotions.ZetaProductPairs.L1) (hL2 : Formalism.MainNotions.ZetaProductPairs.L2 Z) (hV : Formalism.MainNotions.PrimeDegreeVariant.ThetaUpInV0 D)
    (h3 : Formalism.MainNotions.PrimeDegreeVariant.ExactRowOccurrence D)
    (a1 : Formalism.MainNotions.InnerProductFormulaField.adm1 D Z T X) (a2 : Formalism.MainNotions.InnerProductFormulaField.adm2 D Z X) (a3 : ArchimedeanChainApplication D T A X)
    (a4 : Formalism.MainNotions.InnerProductFormulaField.ArchimedeanSignatureMatching D T X) (tg : TieG D X) (a7 : Formalism.MainNotions.InnerProductFormulaField.adm7 D X) (a8 : Formalism.MainNotions.InnerProductFormulaField.adm8 D)
    (a9 : Formalism.MainNotions.InnerProductFormulaField.adm9 D T X) (hI : Rows.IsotInternal D.what₂) (hR : Rows.IsotRank D.what₂) :
    Formalism.MainNotions.InnerProductFormulaField.admitted D Z T A X :=
  ⟨a1, a2, archimedean_hypothesis_of_parts D T A X h1 a3, a4, parahoric_index_hypothesis D X tg hL1.2.1, second_lemma_hypothesis_same D Z hL2, a7, a8, a9, hV,
    transfer_hypothesis_of_isotypic D hI hR h3⟩

theorem lift_hypotheses_of_definitions (D : D7) (Z : DivX D) (T : ThetaX D) (hW : Formalism.MainNotions.ZetaProductPairs.WtHyp T) (hR : Formalism.MainNotions.InnerProductFormulaField.TieRowTyp T)
    (hl : DV.LamDef D) (hk : DV.KapRBase Z) (hg : Formalism.MainNotions.InnerProductFormulaField.GapHyp T) : Formalism.MainNotions.InnerProductFormulaField.Hyp D Z T :=
  ⟨hW, hR, LamEig_of_LamDef D hl, hk, hg⟩

theorem square_hypotheses_of_parts (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} (L : SizeData₂ D) (XD : DivX D) {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am)
    (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X.ar) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X.ar) (h3 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X.ar)
    (h4 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X.ar) (h5 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X.ar)
    (hD : Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt D V L.sc.b V.kap)
    (a1 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm1 D X) (a2r : ExtraLowerBoundAtEmbeddings D L XD X K.Cgr) (a3 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm3 D L XD X K.Cint)
    (a4 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.ArchimedeanSignatureMatching D X)
    (a8 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm8 D X) (a9 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm9 D L) (a10 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm10 K.Ctr)
    (ds1 : Formalism.MainNotions.SchurIrreducible.DiscreteSeriesBlattner X.ar)
    (a14 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm14 D X) (a15 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm15 D L XD X K.Cgr) (a16 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm16 D L X K.Cval)
    (a17 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm17 D V) (a18 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm18 D X) (a19 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm19 D X)
    (a20 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm20 D L X K.Cfp K.Cfp') (a21 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm21 D L X K.Cip)
    (a22 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm22 D L X K.Cmm) (a23 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm23 D X) (a24 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.FrobeniusExpansionCongruence D X)
    (a25 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrExtensionClause D X) (a26 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm26 D X) (a27 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrCocycleExtensionClass D X)
    (a28 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.FontaineFormalProperties D X) (a29 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.AmbientMetricLowerBound D XD X) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.admitted D L XD X K :=
  ⟨⟨a1, a3, a4, a8, a10, (⟨ds1, h1, h2, h3, h4, h5⟩ : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm13 D X)⟩,
    (⟨hD, a2r⟩ : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm2 D L XD X K.Cgr), a9, Formalism.HN.slopeIneqMean, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25,
    a26, a27, a28, a29⟩

def MultiplicityLeaves {D : D7} (T : ThetaX D) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.adm1 ∧ Formalism.MainNotions.ZetaProductPairs.adm2 T ∧ Formalism.MainNotions.ZetaProductPairs.adm3 ∧ Formalism.MainNotions.ZetaProductPairs.adm5 D ∧ Formalism.MainNotions.ZetaProductPairs.adm6 G ∧
    Formalism.MainNotions.ZetaProductPairs.adm7 ∧ Formalism.MainNotions.ZetaProductPairs.ThetaCuspidalChain T

def LiftLeaves (D : D7) (Z : DivX D) (T : ThetaX D) (A : ProvA) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D) : Prop :=
  Formalism.MainNotions.InnerProductFormulaField.adm1 D Z T X ∧ Formalism.MainNotions.InnerProductFormulaField.adm2 D Z X ∧ ArchimedeanChainApplication D T A X ∧ Formalism.MainNotions.InnerProductFormulaField.ArchimedeanSignatureMatching D T X ∧ TieG D X ∧
    Formalism.MainNotions.InnerProductFormulaField.adm7 D X ∧ Formalism.MainNotions.InnerProductFormulaField.adm8 D ∧ Formalism.MainNotions.InnerProductFormulaField.adm9 D T X ∧ Rows.IsotInternal D.what₂ ∧
    Rows.IsotRank D.what₂

def ConstantFreeMultiplicityItems {D : D7} {T : ThetaX D} (Z : DivX D) (X : Formalism.MainNotions.ZetaProductPairs.Loc D T) : Prop :=
  Formalism.MainNotions.ZetaProductPairs.HeckeOperatorScalarUnitary D ∧ Formalism.MainNotions.ZetaProductPairs.L1 ∧ Formalism.MainNotions.ZetaProductPairs.L2 Z ∧ Formalism.MainNotions.ZetaProductPairs.ThetaLiftChainTyped T ∧ Formalism.MainNotions.ZetaProductPairs.UnfoldingScalarUnitary X ∧
    Formalism.MainNotions.ZetaProductPairs.ExchangeOfPositions X ∧ Formalism.MainNotions.ZetaProductPairs.PeriodIntegrality Z

theorem constant_free_items_of_parts {D : D7} {T : ThetaX D} (Z : DivX D) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D) (X : Formalism.MainNotions.ZetaProductPairs.Loc D T)
    (SFF : Formalism.MainNotions.ZetaProductPairs.HeckeScalarStatement D) (SL1 : Formalism.MainNotions.ZetaProductPairs.LocalComputationOne) (SL2 : Formalism.MainNotions.ZetaProductPairs.DoublingComputation Z) (SL4 : Formalism.MainNotions.ZetaProductPairs.ThetaChainStatement T)
    (S0 : Formalism.MainNotions.ZetaProductPairs.UnfoldingStatement X) (SRE : Formalism.MainNotions.ZetaProductPairs.ExchangeStatement X) (SINT : Formalism.MainNotions.ZetaProductPairs.IntegralityStatement Z G)
    (hT : Formalism.MainNotions.ZetaProductPairs.Tied X) (link_brest_alt₂ : MultiplicityLeaves T G) (hk : Formalism.MainNotions.ZetaProductPairs.HeckeKernelCommutation D) : ConstantFreeMultiplicityItems Z X := by
  obtain ⟨b1, b2, b3, b5, b6, b7, b8g⟩ := link_brest_alt₂
  exact ⟨SFF b5, SL1, SL2, SL4 b2 b8g, S0 hT b1 b2 b3 b5 hk b8g, SRE hT b5, SINT b6 b7⟩

def RowsMultiplicityClosed {D : D7} {T : ThetaX D} (X : Formalism.MainNotions.ZetaProductPairs.Loc D T) : Prop :=
  Rows.BuDefQ D.what₂ → Formalism.MainNotions.ZetaProductPairs.ZeDef X → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ →
  ∀ u : D.what₂.Word, ∃ h : Formalism.MainNotions.ZetaProductPairs.FFStable D u, Formalism.MainNotions.ZetaProductPairs.FFScalarUnitary u h ∧
    (∀ μ : D.what₂.Tup, ∃ n : ℕ, 0 < n ∧ D.what₂.zeC u μ ^ n = 1) ∧
    ∃ s c : ℂ, Formalism.MainNotions.ZetaProductPairs.SuShape D u s ∧ c ≠ 0 ∧ (∀ da, X.Au u da = c * X.ellT u da) ∧
      (∀ (φ : D.what₂.Mu u) (F : D.what₂.EE),
        D.what₂.Bu u φ F = (c * s⁻¹)⁻¹ * X.B0 u (Formalism.MainNotions.ZetaProductPairs.FFm u h φ) F) ∧
      ∀ (μ : D.what₂.Tup) (φ : D.what₂.Mu u), ∀ F ∈ D.what₂.V0 μ,
        D.what₂.perCol u μ φ F = D.what₂.zeC u μ * D.what₂.Bu u φ (D.what₂.iota μ F)

theorem rows_form_without_side_condition {D : D7} {T : ThetaX D} (X : Formalism.MainNotions.ZetaProductPairs.Loc D T) (h : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneWithZeta X)
    (h6 : Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing D T X) : RowsMultiplicityClosed X := by
  intro hB hZ hS u
  obtain ⟨hF, hU, hz, s, hs, hc⟩ := h hB hZ hS u
  obtain ⟨c, c0, hA, hne⟩ := h6 u
  exact ⟨hF, hU, hz, s, c, hs, c0, hA, hc c c0 hA hne⟩

theorem chainD_MI_rec {D : D7} {T : ThetaX D} (X : Formalism.MainNotions.ZetaProductPairs.Loc D T)
    (W : Formalism.MainNotions.InnerProductFormulaField.LocC X)
    (p0 : Formalism.MainNotions.ZetaProductPairs.UnfoldingScalarUnitary X) (S6 : Formalism.MainNotions.InnerProductFormulaField.RealConstantStatement W) (a6 : Formalism.MainNotions.InnerProductFormulaField.RealConstantHypotheses W) (SMI : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneStatement X)
    (Sc : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneConditionalStatement X) (Sr : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneBlocks X) :
    Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing D T X ∧ Formalism.MainNotions.ZetaProductPairs.MultiplicityOneExplicit X ∧ RowsMultiplicityClosed X := by
  have p6 : Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing D T X := S6 a6
  exact ⟨p6, SMI p0 (real_constant_hypothesis_of_lift X p6), rows_form_without_side_condition X (Sr (Sc p0)) p6⟩

theorem division_chain_lift_recursive (D : D7) (L : SizeData₂ D) (Z : DivX D) (T : ThetaX D) (A : ProvA) (X20 : Formalism.MainNotions.InnerProductFormulaField.Loc D)
    (Csz Ksz : ℝ) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A) (hL1 : Formalism.MainNotions.ZetaProductPairs.L1) (hL2 : Formalism.MainNotions.ZetaProductPairs.L2 Z)
    (twenty_words_le_b : Formalism.MainNotions.InnerProductFormulaField.Stmt D Z T A X20) (S20z : Formalism.MainNotions.InnerProductFormulaField.SizesStatement D Z T A X20 L Csz Ksz)
    (hV : Formalism.MainNotions.PrimeDegreeVariant.ThetaUpInV0 D) (h3 : Formalism.MainNotions.PrimeDegreeVariant.ExactRowOccurrence D)
    (hW : Formalism.MainNotions.ZetaProductPairs.WtHyp T) (hR : Formalism.MainNotions.InnerProductFormulaField.TieRowTyp T) (hl : DV.LamDef D) (hk : DV.KapRBase Z)
    (hg : Formalism.MainNotions.InnerProductFormulaField.GapHyp T) (lintegral_lt_top_of_thetaIP_ne : LiftLeaves D Z T A X20) (hC : 0 ≤ Csz) (hS : Formalism.MainNotions.InnerProductFormulaField.admS D X20 L Csz)
    (hLp0 : 0 ≤ Formalism.MainNotions.InnerProductFormulaField.Lp D L) (hLp : Formalism.MainNotions.InnerProductFormulaField.Lp D L ≤ Ksz * L.La) :
    Formalism.MainNotions.InnerProductFormulaField.aux₃ D Z T X20 ∧ Formalism.MainNotions.InnerProductFormulaField.RallisSizeBound D L (3 * Csz) ∧ Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound D L (3 * Csz * Ksz) := by
  obtain ⟨c1, c2, c3, c4, tg, c7, c8, c9, hI, hRk⟩ := lintegral_lt_top_of_thetaIP_ne
  have LocalHeightDeterminant := lift_hypotheses_of_definitions D Z T hW hR hl hk hg
  have A20 := lift_hypotheses_of_parts D Z T A X20 h1 hL1 hL2 hV h3 c1 c2 c3 c4 tg c7 c8 c9 hI hRk
  obtain ⟨pz, -, p6⟩ := S20z LocalHeightDeterminant A20 hC hS
  exact ⟨twenty_words_le_b LocalHeightDeterminant A20, pz, p6 hLp0 hLp⟩

theorem chain_divisor_recursion_levels (D : D7) (L : SizeData₂ D) (Z : DivX D) (X20 : Formalism.MainNotions.InnerProductFormulaField.Loc D) {Am : AmbForm D (RowSide.sharp D)}
    (X36 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Loc D Am)
    (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) (Cl C Ch Ch' : ℝ) (S36 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Stmt D L Z X36 K C Ch Ch')
    (hAR : ArchimedeanTheoremFiveParts X36.ar) (pA : Formalism.MainNotions.InnerProductFormulaField.ConjugationNormInvariance D Z X20) (pN : Formalism.MainNotions.InnerProductFormulaField.IsotypicPartsNonzero D) (p3 : Formalism.MainNotions.InnerProductFormulaField.PointsLemma D Z)
    (p6 : Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound D L Cl) (hk : DV.KapRBase Z)
    (hsz : Cl * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ L.sc.b)
    (hG : Formalism.MainNotions.AbsolutelyIrreducibleSpan.HypGap D X36) (locJunk_chart : SquareLeaves D L Z X36 K) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.aux₃ D L X36 C Ch Ch' := by
  have hD := row_level_data_of_lift D Z hk p3 _ (lambda_lower_bound_of_lift D Z X20 L _ _ pA pN p6 (sumHkP_nonneg_rec D) hsz)
  have A36 := square_hypotheses_of_leaves D L Z X36 K hAR hD locJunk_chart
  exact S36 ⟨hG, A36.1⟩ A36.2

theorem chainD_rec (D : D7) (L : SizeData₂ D) (Z : DivX D) (T : ThetaX D) (A : ProvA) (G : Formalism.MainNotions.product_first_zeroth_parts.Th22 D)
    (X19 : Formalism.MainNotions.ZetaProductPairs.Loc D T) (X20 : Formalism.MainNotions.InnerProductFormulaField.Loc D) {Am : AmbForm D (RowSide.sharp D)}
    (X36 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Loc D Am) (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts)
    (Csz Ksz C Ch Ch' : ℝ)
    (S46 : Formalism.MainNotions.SchurIrreducible.IntegralityGoodReduction A) (S19 : Formalism.MainNotions.ZetaProductPairs.ConstantFreeStatements Z G X19) (S19m : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneStatement X19)
    (twenty_words_le_b : Formalism.MainNotions.InnerProductFormulaField.Stmt D Z T A X20)
    (S20z : Formalism.MainNotions.InnerProductFormulaField.SizesStatement D Z T A X20 L Csz Ksz) (W19 : Formalism.MainNotions.InnerProductFormulaField.LocC X19) (S20s : Formalism.MainNotions.InnerProductFormulaField.RealConstantStatement W19)
    (a6 : Formalism.MainNotions.InnerProductFormulaField.RealConstantHypotheses W19)
    (S36 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Stmt D L Z X36 K C Ch Ch')
    (hV : Formalism.MainNotions.PrimeDegreeVariant.ThetaUpInV0 D) (h3 : Formalism.MainNotions.PrimeDegreeVariant.ExactRowOccurrence D)
    (locP_compan_le : Formalism.MainNotions.SchurIrreducible.AdmA A) (hT : Formalism.MainNotions.ZetaProductPairs.Tied X19) (link_brest_alt₂ : MultiplicityLeaves T G) (h5k : Formalism.MainNotions.ZetaProductPairs.HeckeKernelCommutation D)
    (hW : Formalism.MainNotions.ZetaProductPairs.WtHyp T) (hR : Formalism.MainNotions.InnerProductFormulaField.TieRowTyp T) (hl : DV.LamDef D) (hk : DV.KapRBase Z)
    (hg : Formalism.MainNotions.InnerProductFormulaField.GapHyp T) (lintegral_lt_top_of_thetaIP_ne : LiftLeaves D Z T A X20) (hC : 0 ≤ Csz) (hS : Formalism.MainNotions.InnerProductFormulaField.admS D X20 L Csz)
    (hLp0 : 0 ≤ Formalism.MainNotions.InnerProductFormulaField.Lp D L) (hLp : Formalism.MainNotions.InnerProductFormulaField.Lp D L ≤ Ksz * L.La)
    (hsz : 3 * Csz * Ksz * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La ≤ L.sc.b)
    (hA36 : X36.ar = A) (hG : Formalism.MainNotions.AbsolutelyIrreducibleSpan.HypGap D X36) (locJunk_chart : SquareLeaves D L Z X36 K) :
    ConstantFreeMultiplicityItems Z X19 ∧ Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing D T X19 ∧ Formalism.MainNotions.ZetaProductPairs.MultiplicityOneExplicit X19 ∧ RowsMultiplicityClosed X19 ∧
      Formalism.MainNotions.InnerProductFormulaField.aux₃ D Z T X20 ∧ Formalism.MainNotions.InnerProductFormulaField.RallisSizeBound D L (3 * Csz) ∧
      Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound D L (3 * Csz * Ksz) ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.aux₃ D L X36 C Ch Ch' := by
  have hAR : ArchimedeanTheoremFiveParts A := S46 locP_compan_le
  obtain ⟨sFF, sL1, IsSettingL2, sL4, s0, sRE, sINT, sc, sr⟩ := S19
  have pF := constant_free_items_of_parts Z G X19 sFF sL1 IsSettingL2 sL4 s0 sRE sINT hT link_brest_alt₂ h5k
  obtain ⟨pS6, pMI, pRows⟩ := chainD_MI_rec X19 W19 pF.2.2.2.2.1 S20s a6 S19m sc sr
  obtain ⟨p20, pz, p6⟩ := division_chain_lift_recursive D L Z T A X20 Csz Ksz hAR.1 pF.2.1 pF.2.2.1 twenty_words_le_b S20z hV h3 hW hR hl hk hg lintegral_lt_top_of_thetaIP_ne
    hC hS hLp0 hLp
  exact ⟨pF, pS6, pMI, pRows, p20, pz, p6,
    chain_divisor_recursion_levels D L Z X20 X36 K _ C Ch Ch' S36 (by rw [hA36]; exact hAR) p20.2.1 p20.2.2.1 p20.2.2.2.2.2.2 p6 hk
      hsz hG locJunk_chart⟩

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def MultiplicityLeavesFamily (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i)) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.ZetaProductPairs.adm1 ∧ Formalism.MainNotions.ZetaProductPairs.adm2 (Fm.ex x hx i).th ∧ Formalism.MainNotions.ZetaProductPairs.adm3 ∧ Formalism.MainNotions.ZetaProductPairs.adm5 (Fm.D x i) ∧
    Formalism.MainNotions.ZetaProductPairs.adm6 (GF x i) ∧ Formalism.MainNotions.ZetaProductPairs.adm7 ∧ Formalism.MainNotions.ZetaProductPairs.ThetaCuspidalChain (Fm.ex x hx i).th

theorem multiplicity_hypotheses_family (A : ProvA) (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i)) (hAR : ArchimedeanTheoremFiveParts A)
    (hL : MultiplicityLeavesFamily Fm GF) : Formalism.MainNotions.ZetaProductPairs.AdmF Fm A GF := by
  intro x hx i
  obtain ⟨a1, a2, a3, a5, a6, a7, a8g⟩ := hL x hx i
  exact ⟨a1, a2, a3, a5, a6, a7, hAR, a8g⟩

theorem lift_hypotheses_family_of_parts (hW : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.WtHyp (Fm.ex x hx i).th)
    (hR : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.TieRowTyp (Fm.ex x hx i).th) : Formalism.MainNotions.InnerProductFormulaField.HypF Fm :=
  fun x hx i => ⟨hW x hx i, hR x hx i, LamEig_of_LamDef _ (Fm.ex x hx i).lam_def, (Fm.ex x hx i).kapR_def,
    Formalism.MainNotions.InnerProductFormulaField.GapHypF Fm x hx i⟩

def LeafHypothesesFamily (A : ProvA) (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.InnerProductFormulaField.adm1 (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th (XF x hx i) ∧
    Formalism.MainNotions.InnerProductFormulaField.adm2 (Fm.D x i) (Fm.X x i) (XF x hx i) ∧
    ArchimedeanChainApplication (Fm.D x i) (Fm.ex x hx i).th A (XF x hx i) ∧
    Formalism.MainNotions.InnerProductFormulaField.ArchimedeanSignatureMatching (Fm.D x i) (Fm.ex x hx i).th (XF x hx i) ∧
    TieG (Fm.D x i) (XF x hx i) ∧
    Formalism.MainNotions.InnerProductFormulaField.adm7 (Fm.D x i) (XF x hx i) ∧ Formalism.MainNotions.InnerProductFormulaField.adm8 (Fm.D x i) ∧
    Formalism.MainNotions.InnerProductFormulaField.adm9 (Fm.D x i) (Fm.ex x hx i).th (XF x hx i) ∧
    Rows.IsotInternal (Fm.D x i).what₂ ∧ Rows.IsotRank (Fm.D x i).what₂

theorem lift_hypotheses_family_leaves (A : ProvA)
    (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A)
    (h19 : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.ZetaProductPairs.L1 ∧ Formalism.MainNotions.ZetaProductPairs.L2 (Fm.X x i))
    (hV : Formalism.MainNotions.PrimeDegreeVariant.familyThetaUpInV0 Fm) (h3 : Formalism.MainNotions.PrimeDegreeVariant.familyExactRowOccurrence Fm)
    (hL : LeafHypothesesFamily Fm A XF) : Formalism.MainNotions.InnerProductFormulaField.AdmF Fm A XF := by
  intro x hx i
  obtain ⟨a1, a2, a3, a4, tg, a7, a8, a9, hI, hR⟩ := hL x hx i
  exact ⟨a1, a2, archimedean_hypothesis_of_parts _ _ _ _ h1 a3, a4, parahoric_index_hypothesis _ _ tg (h19 x hx i).1.2.1,
    second_lemma_hypothesis_same _ _ (h19 x hx i).2, a7, a8, a9, hV x hx i, transfer_hypothesis_of_isotypic _ hI hR (h3 x hx i)⟩

theorem lattice_length_bound_family_of (A : ProvA) (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) (C K CH : ℝ)
    (S : Formalism.MainNotions.InnerProductFormulaField.SizesFamily C K Fm A XF) (hH : Formalism.MainNotions.InnerProductFormulaField.HypF Fm) (hA : Formalism.MainNotions.InnerProductFormulaField.AdmF Fm A XF) (hC : 0 ≤ C)
    (hS : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.admS (Fm.D x i) (XF x hx i) (Fm.L x i) C)
    (hLp : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, 0 ≤ Formalism.MainNotions.InnerProductFormulaField.Lp (Fm.D x i) (Fm.L x i) ∧
      Formalism.MainNotions.InnerProductFormulaField.Lp (Fm.D x i) (Fm.L x i) ≤ K * (Fm.L x i).La) :
    ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound (Fm.D x i) (Fm.L x i) (3 * C * K) :=
  fun x hx i => ((S x hx i) (hH x hx i) (hA x hx i) hC (hS x hx i)).2.2 (hLp x hx i).1 (hLp x hx i).2

theorem lambda_lower_bound_family (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) (C : ℝ)
    (h20 : Formalism.MainNotions.InnerProductFormulaField.OrbitValuationBound Fm XF)
    (h6 : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound (Fm.D x i) (Fm.L x i) C)
    (hH : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), 0 ≤ Formalism.MainNotions.InnerProductFormulaField.sumHkP (Fm.D x i) j)
    (hsz : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
      C * ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ^ 2 * (Fm.L x i).La ≤ (Fm.L x i).sc.b) :
    ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow (Fm.D x i) (Fm.L x i).sc.b :=
  fun x hx i => lambda_lower_bound_of_lift _ (Fm.X x i) (XF x hx i) _ C _ (h20 x hx i).2.1 (h20 x hx i).2.2.1 (h6 x hx i)
    (hH x hx i) (hsz x hx i)

theorem row_level_data_family (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) (h20 : Formalism.MainNotions.InnerProductFormulaField.OrbitValuationBound Fm XF)
    (hb : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow (Fm.D x i) (Fm.L x i).sc.b) :
    ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt (Fm.D x i) (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp (Fm.D x i))
      (Fm.L x i).sc.b (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp (Fm.D x i)).kap :=
  fun x hx i => row_level_data_of_lift _ (Fm.X x i) (Fm.ex x hx i).kapR_def (h20 x hx i).2.2.2.2.2.2 _ (hb x hx i)

theorem p0_level_data_family (P0F : ∀ x (i : Fm.Ix x), BaseLevelRowSide (Fm.D x i))
    (hL0 : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, (P0F x i).BaseLevelSideLevelOneCondition)
    (hb : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.AbsolutelyIrreducibleSpan.LamLow (Fm.D x i) (Fm.L x i).sc.b) :
    ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt (Fm.D x i) (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.p0 (P0F x i))
      (Fm.L x i).sc.b (Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.p0 (P0F x i)).kap :=
  fun x hx i => data_at_small_level_of_lattice _ _ _ (hL0 x hx i) (hb x hx i)

theorem admissible_family_of_local_data {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV (Fm.D x i) (VF x hx i) (AF x hx i)) (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) (A : ProvA)
    (hA : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), (XF x hx i).ar = A) (hAR : ArchimedeanTheoremFiveParts A)
    (hD : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt (Fm.D x i) (VF x hx i) (Fm.L x i).sc.b (VF x hx i).kap)
    (hL : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SquareLeaves (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i) K) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.AdmF Fm XF K :=
  ⟨Fm.x1, fun x hx _ i => square_hypotheses_of_leaves _ _ _ _ K (by rw [hA x hx i]; exact hAR) (hD x hx i) (hL x hx i)⟩

theorem admissible_family_of_small_level {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV (Fm.D x i) (VF x hx i) (AF x hx i)) (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) (A : ProvA)
    (hA : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), (XF x hx i).ar = A) (hAR : ArchimedeanTheoremFiveParts A)
    (hD : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.MainNotions.AbsolutelyIrreducibleSpan.DataAt (Fm.D x i) (VF x hx i) (Fm.L x i).sc.b (VF x hx i).kap)
    (hL : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm9 (Fm.D x i) (Fm.L x i) →
      SquareLeaves (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i) K) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.AdmF Fm XF K := by
  obtain ⟨xa, ha⟩ := Formalism.MainNotions.J.family_auxiliary_prime_size Fm
  obtain ⟨xb, hb⟩ := hL
  exact ⟨max xa xb, fun x hx h0 i => square_hypotheses_of_leaves _ _ _ _ K (by rw [hA x hx i]; exact hAR) (hD x hx i)
    (hb x hx (le_trans (le_max_right _ _) h0) i (ha x (le_trans (le_max_left _ _) h0) hx i))⟩

theorem free_family_of_leaves_and_admissible (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i))
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.Loc (Fm.D x i) (Fm.ex x hx i).th)
    (S : Formalism.MainNotions.ZetaProductPairs.ConstantFreeFamily Fm GF XF)
    (hT : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.Tied (XF x hx i)) (link_brest_alt₂ : MultiplicityLeavesFamily Fm GF)
    (h5k : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.ZetaProductPairs.HeckeKernelCommutation (Fm.D x i)) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConstantFreeMultiplicityItems (Fm.X x i) (XF x hx i) := by
  intro x hx i
  obtain ⟨sFF, sL1, IsSettingL2, sL4, s0, sRE, sINT, -, -⟩ := S x hx i
  exact constant_free_items_of_parts _ (GF x i) _ sFF sL1 IsSettingL2 sL4 s0 sRE sINT (hT x hx i) (link_brest_alt₂ x hx i) (h5k x hx i)

theorem chainD_MI (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.Loc (Fm.D x i) (Fm.ex x hx i).th) (CH : ℝ)
    (p0 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.UnfoldingScalarUnitary (XF x hx i))
    (WF : Formalism.MainNotions.InnerProductFormulaField.LocCF Fm XF) (S6 : Formalism.MainNotions.InnerProductFormulaField.RealConstantFamily Fm XF WF)
    (a6 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.RealConstantHypotheses (WF x hx i)) (SMI : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneFamily Fm XF)
    (Sc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.MultiplicityOneConditionalStatement (XF x hx i))
    (Sr : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.MultiplicityOneBlocks (XF x hx i)) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing (Fm.D x i) (Fm.ex x hx i).th (XF x hx i) ∧
      Formalism.MainNotions.ZetaProductPairs.MultiplicityOneExplicit (XF x hx i) ∧ RowsMultiplicityClosed (XF x hx i) :=
  fun x hx i => chainD_MI_rec _ (WF x hx i) (p0 x hx i) (S6 x hx i) (a6 x hx i) (SMI x hx i) (Sc x hx i) (Sr x hx i)

theorem division_chain_lift_statement (A : ProvA) (XF20 : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) (Csz Ksz CH : ℝ)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A)
    (h19 : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.ZetaProductPairs.L1 ∧ Formalism.MainNotions.ZetaProductPairs.L2 (Fm.X x i))
    (twenty_words_le_b : Formalism.MainNotions.InnerProductFormulaField.KudlaFamilyStatement Fm A XF20) (S20z : Formalism.MainNotions.InnerProductFormulaField.SizesFamily Csz Ksz Fm A XF20)
    (hV : Formalism.MainNotions.PrimeDegreeVariant.familyThetaUpInV0 Fm) (h3 : Formalism.MainNotions.PrimeDegreeVariant.familyExactRowOccurrence Fm)
    (hW : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.WtHyp (Fm.ex x hx i).th)
    (hR : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.TieRowTyp (Fm.ex x hx i).th)
    (lintegral_lt_top_of_thetaIP_ne : LeafHypothesesFamily Fm A XF20) (hC : 0 ≤ Csz)
    (hS : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.admS (Fm.D x i) (XF20 x hx i) (Fm.L x i) Csz)
    (hLp : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, 0 ≤ Formalism.MainNotions.InnerProductFormulaField.Lp (Fm.D x i) (Fm.L x i) ∧
      Formalism.MainNotions.InnerProductFormulaField.Lp (Fm.D x i) (Fm.L x i) ≤ Ksz * (Fm.L x i).La) :
    Formalism.MainNotions.InnerProductFormulaField.OrbitValuationBound Fm XF20 ∧
      ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound (Fm.D x i) (Fm.L x i) (3 * Csz * Ksz) := by
  have LocalHeightDeterminant := lift_hypotheses_family_of_parts Fm hW hR
  have A20 := lift_hypotheses_family_leaves Fm A XF20 h1 h19 hV h3 lintegral_lt_top_of_thetaIP_ne
  exact ⟨twenty_words_le_b LocalHeightDeterminant A20, lattice_length_bound_family_of Fm A XF20 Csz Ksz CH S20z LocalHeightDeterminant A20 hC hS hLp⟩

theorem division_chain_square_statement (A : ProvA) (XF20 : Formalism.MainNotions.InnerProductFormulaField.LocF Fm)
    {AF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (RowSide.sharp (Fm.D x i))}
    (XF36 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.AbsolutelyIrreducibleSpan.Loc (Fm.D x i) (AF x hx i))
    (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) (Cl C Ch Ch' : ℝ) (S36 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.ErrorExponentStatement K C Ch Ch' Fm XF36)
    (hAR : ArchimedeanTheoremFiveParts A) (p20 : Formalism.MainNotions.InnerProductFormulaField.OrbitValuationBound Fm XF20)
    (p6 : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound (Fm.D x i) (Fm.L x i) Cl)
    (hsz : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
      Cl * ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ^ 2 * (Fm.L x i).La ≤ (Fm.L x i).sc.b)
    (hA36 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), (XF36 x hx i).ar = A)
    (locJunk_chart : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SquareLeaves (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF36 x hx i) K) :
    Formalism.MainNotions.AbsolutelyIrreducibleSpan.Conclusion1Family Fm XF36 ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.Conclusion2Family Fm XF36 C ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.Conclusion3Family Fm XF36 Ch Ch' := by
  have hb := lambda_lower_bound_family Fm XF20 Cl p20 p6 (fun x _ i => sumHkP_nonneg_rec (Fm.D x i)) hsz
  exact S36 (admissible_family_of_local_data Fm XF36 K A hA36 hAR (row_level_data_family Fm XF20 p20 hb) locJunk_chart)

theorem chainD (A : ProvA) (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i))
    (XF19 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.Loc (Fm.D x i) (Fm.ex x hx i).th)
    (XF20 : Formalism.MainNotions.InnerProductFormulaField.LocF Fm)
    {AF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (RowSide.sharp (Fm.D x i))}
    (XF36 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.AbsolutelyIrreducibleSpan.Loc (Fm.D x i) (AF x hx i))
    (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) (Csz Ksz C Ch Ch' CH : ℝ)
    (S46 : Formalism.MainNotions.SchurIrreducible.IntegralityGoodReduction A) (S19 : Formalism.MainNotions.ZetaProductPairs.ConstantFreeFamily Fm GF XF19) (S19m : Formalism.MainNotions.ZetaProductPairs.MultiplicityOneFamily Fm XF19)
    (twenty_words_le_b : Formalism.MainNotions.InnerProductFormulaField.KudlaFamilyStatement Fm A XF20)
    (S20z : Formalism.MainNotions.InnerProductFormulaField.SizesFamily Csz Ksz Fm A XF20) (WF19 : Formalism.MainNotions.InnerProductFormulaField.LocCF Fm XF19)
    (S20s : Formalism.MainNotions.InnerProductFormulaField.RealConstantFamily Fm XF19 WF19) (a6 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.RealConstantHypotheses (WF19 x hx i))
    (S36 : Formalism.MainNotions.AbsolutelyIrreducibleSpan.ErrorExponentStatement K C Ch Ch' Fm XF36)
    (S01 : Formalism.MainNotions.PrimeDegreeVariant.KudlaFamilyStatement Fm CH) (YF : Formalism.MainNotions.PrimeDegreeVariant.ProvF Fm) (L01 : Formalism.MainNotions.PrimeDegreeVariant.AdmF Fm YF)
    (locP_compan_le : Formalism.MainNotions.SchurIrreducible.AdmA A)
    (hT : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.Tied (XF19 x hx i)) (link_brest_alt₂ : MultiplicityLeavesFamily Fm GF)
    (h5k : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.ZetaProductPairs.HeckeKernelCommutation (Fm.D x i))
    (hW : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.ZetaProductPairs.WtHyp (Fm.ex x hx i).th)
    (hR : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.TieRowTyp (Fm.ex x hx i).th)
    (lintegral_lt_top_of_thetaIP_ne : LeafHypothesesFamily Fm A XF20) (hC : 0 ≤ Csz)
    (hS : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.admS (Fm.D x i) (XF20 x hx i) (Fm.L x i) Csz)
    (hLp : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, 0 ≤ Formalism.MainNotions.InnerProductFormulaField.Lp (Fm.D x i) (Fm.L x i) ∧
      Formalism.MainNotions.InnerProductFormulaField.Lp (Fm.D x i) (Fm.L x i) ≤ Ksz * (Fm.L x i).La)
    (hsz : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
      3 * Csz * Ksz * ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ^ 2 * (Fm.L x i).La ≤
        (Fm.L x i).sc.b)
    (hA36 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), (XF36 x hx i).ar = A)
    (locJunk_chart : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SquareLeaves (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF36 x hx i) K) :
    (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConstantFreeMultiplicityItems (Fm.X x i) (XF19 x hx i)) ∧
      (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.InnerProductFormulaField.ArchimedeanFactorNonvanishing (Fm.D x i) (Fm.ex x hx i).th (XF19 x hx i) ∧
        Formalism.MainNotions.ZetaProductPairs.MultiplicityOneExplicit (XF19 x hx i) ∧ RowsMultiplicityClosed (XF19 x hx i)) ∧
      Formalism.MainNotions.InnerProductFormulaField.OrbitValuationBound Fm XF20 ∧
      (∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.InnerProductFormulaField.LogEigenvalueLowerBound (Fm.D x i) (Fm.L x i) (3 * Csz * Ksz)) ∧
      Formalism.MainNotions.AbsolutelyIrreducibleSpan.Conclusion1Family Fm XF36 ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.Conclusion2Family Fm XF36 C ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.Conclusion3Family Fm XF36 Ch Ch' := by
  have hAR : ArchimedeanTheoremFiveParts A := S46 locP_compan_le
  obtain ⟨-, -, -, hV, -, h3, -⟩ := S01 YF L01
  have pF := free_family_of_leaves_and_admissible Fm GF XF19 S19 hT link_brest_alt₂ h5k
  have pMI := chainD_MI Fm XF19 CH (fun x hx i => (pF x hx i).2.2.2.2.1) WF19 S20s a6 S19m
    (fun x hx i => (S19 x hx i).2.2.2.2.2.2.2.1) (fun x hx i => (S19 x hx i).2.2.2.2.2.2.2.2)
  obtain ⟨p20, p6⟩ := division_chain_lift_statement Fm A XF20 Csz Ksz CH hAR.1 (fun x hx i => ⟨(pF x hx i).2.1, (pF x hx i).2.2.1⟩) twenty_words_le_b S20z
    hV h3 hW hR lintegral_lt_top_of_thetaIP_ne hC hS hLp
  exact ⟨pF, pMI, p20, p6, division_chain_square_statement Fm A XF20 XF36 K _ C Ch Ch' S36 hAR p20 p6 hsz hA36 locJunk_chart⟩

end Family

structure SqSett {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (μ : D.what₂.Tup) (i j : ℕ) where
  S : Formalism.MainNotions.KudlaSiegelWeil.Sett D T Lc
  rk_a : S.a = D.R.r + j * D.R.t + i * X.s + D.R.t + X.s
  rk_a' : S.a' = D.R.r + j * D.R.t + i * X.s
  p_eq : S.p = (D.R.m - j - 1) / 2
  q_eq : S.q = (D.R.m - j) / 2
  inf : ∀ τ (hj : j < D.R.m), |T.infTy (S.α / S.β) τ| = (D.hc τ).e ⟨j, hj⟩ + X.cInf (D.R.m - i) τ
  csq_def : ∀ c, S.Prop2 0 0 c → X.csq μ i j = c

theorem SqSett.kap_iff {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} {T : ThetaX D} {Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T}
    {X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am} {μ : D.what₂.Tup} {i j : ℕ} (Q : SqSett T Lc X μ i j) (τ : D.what₂.Tau)
    (hj : j < D.R.m) :
    ((2 * (D.R.r + j * D.R.t + i * X.s) + D.R.t + X.s : ℕ) : ℚ) < 2 * ((D.hc τ).e ⟨j, hj⟩ + X.cInf (D.R.m - i) τ) ↔
      (Q.S.d : ℚ) < |2 * T.infTy (Q.S.α / Q.S.β) τ| := by
  have hd : Q.S.d = 2 * (D.R.r + j * D.R.t + i * X.s) + D.R.t + X.s := by
    have h1 := Q.S.sum
    have h2 := Q.rk_a
    have h3 := Q.rk_a'
    omega
  rw [hd, abs_mul, Q.inf τ hj, abs_two]

theorem sq_ranges (m t s n j e : ℕ) (h1 : 4 * m + 2 < t + s) (h2 : 2 * m + 1 < n) (he : t + s = 2 * e) :
    2 * ((m - j - 1) / 2 + (m - j) / 2) + 1 < e ∧ 2 * ((m - j - 1) / 2 + (m - j) / 2) + 1 < n := by
  omega

theorem commutation_rank_inequalities {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) :
    4 * D.R.m + 2 < D.R.t + X.s ∧ ∀ i j : ℕ, 2 * D.R.m + 1 < D.R.r + j * D.R.t + i * X.s := by
  have h1 := X.s_eq
  have h2 := D.R.three_m_lt_t
  have h3 := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  exact ⟨by omega, fun i j => by omega⟩

theorem commutation_third_inequality {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (i j : ℕ)
    (hi : i < D.R.m) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    ((2 * (D.R.r + j * D.R.t + i * X.s) + D.R.t + X.s : ℕ) : ℚ) <
      2 * ((D.hc τ).e ⟨j, hj⟩ + X.cInf (D.R.m - i) τ) := by
  have h := X.chi_above (D.R.m - i) (by omega) (by omega) ⟨j, hj⟩ τ
  refine lt_of_le_of_lt ?_ h
  have a : j * D.R.t + D.R.t ≤ D.R.m * D.R.t := by
    calc j * D.R.t + D.R.t = (j + 1) * D.R.t := by ring
      _ ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have b : i * X.s + X.s ≤ D.R.m * X.s := by
    calc i * X.s + X.s = (i + 1) * X.s := by ring
      _ ≤ D.R.m * X.s := Nat.mul_le_mul_right _ hi
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have e : D.R.m * (D.R.t + X.s + 1) = D.R.m * D.R.t + D.R.m * X.s + D.R.m := by ring
  have h2 : D.R.k + D.R.m * (D.R.t + X.s + 1) ≤ (D.R.k + D.R.m * (D.R.t + X.s + 1)) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  have h3 : 2 * (D.R.r + j * D.R.t + i * X.s) + D.R.t + X.s ≤ 2 * (D.R.k + D.R.m * (D.R.t + X.s + 1)) ^ 3 := by
    refine le_trans ?_ (Nat.mul_le_mul_left 2 h2)
    rw [e]
    omega
  exact_mod_cast h3

def TieCsq {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) : Prop :=
  ∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ → ∀ i j, i < D.R.m → j < D.R.m → Nonempty (SqSett T Lc X μ i j)

theorem SqSett.prop2 {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} {T : ThetaX D} {Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T}
    {X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am} {μ : D.what₂.Tup} {i j : ℕ} (Q : SqSett T Lc X μ i j)
    (hK : Formalism.MainNotions.KudlaSiegelWeil.aux₃ D T Lc) : Q.S.Prop2 0 0 (X.csq μ i j) := by
  obtain ⟨_, _, _, _, _, _, hS⟩ := hK
  obtain ⟨-, c, hc, -⟩ := hS Q.S
  have h0 := hc 0 (Nat.zero_le _) 0 (Nat.zero_le _)
  rw [Q.csq_def _ h0]
  exact h0

theorem square_constant_nonzero {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (tie : TieCsq T Lc X) (hK : Formalism.MainNotions.KudlaSiegelWeil.aux₃ D T Lc)
    (h : Formalism.MainNotions.KudlaSiegelWeil.KudlaConstantNonzero D T Lc) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm18 D X := by
  intro μ hμ i j hi hj
  obtain ⟨Q⟩ := tie μ hμ i j hi hj
  exact h Q.S 0 (Nat.zero_le _) 0 (Nat.zero_le _) _ (Q.prop2 hK)

def SqSett.SeeSaw {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} {T : ThetaX D} {Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T}
    {X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am} {μ : D.what₂.Tup} {i : ℕ} (h : ℕ → ℕ) (Q : SqSett T Lc X μ i (h i)) : Prop :=
  ∀ (P : X.PD μ h) (P' : X.PD μ (Formalism.MainNotions.AbsolutelyIrreducibleSpan.flipP h i)), X.pA μ h i P' = X.pB μ h i P → ∀ F ∈ V.S.V0 μ,
    ∃ (ι : Type) (_ : Fintype ι) (ΦA : ι → T.Sch (Q.S.Vt 0) (Q.S.Wt (0 + 0)))
      (ΦB : ι → T.Sch (Q.S.V't 0) (Q.S.Wt (0 + 0)))
      (Λ : ι → (Lc.w.G (Q.S.Wt (0 + 0)) → ℂ) →ₗ[ℂ] X.th.AF (X.vx D.R.m 0)),
      (∀ k, ΦA k ∈ T.kfin (Q.S.Vt 0) (Q.S.Wt (0 + 0))) ∧ (∀ k, ΦB k ∈ Q.S.Sz 0 0) ∧
      (∀ k, Lc.p.pG (Q.S.Vt 0) (Q.S.V't 0) (Q.S.Wt (0 + 0)) Q.S.α Q.S.β (ΦA k) =
        Lc.p.pG' (Q.S.Vt 0) (Q.S.V't 0) (Q.S.Wt (0 + 0)) Q.S.α Q.S.β (ΦB k)) ∧
      X.ev μ (Formalism.MainNotions.AbsolutelyIrreducibleSpan.flipP h i) P' F = ∑ k, Λ k (Q.S.IA 0 0 (ΦA k)) ∧
      X.ev μ h P F = ∑ k, Λ k (Q.S.IB 0 0 (ΦB k))

def CommutationSquares {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) : Prop :=
  ∀ μ, Formalism.MainNotions.AbsolutelyIrreducibleSpan.Used D μ → ∀ h i, Formalism.MainNotions.AbsolutelyIrreducibleSpan.IsPath D.R.m h → Formalism.MainNotions.AbsolutelyIrreducibleSpan.Flippable D.R.m h i →
    4 * D.R.m + 2 < D.R.t + X.s → 2 * D.R.m + 1 < D.R.r + h i * D.R.t + i * X.s →
    (∀ τ (hj : h i < D.R.m), ((2 * (D.R.r + h i * D.R.t + i * X.s) + D.R.t + X.s : ℕ) : ℚ) <
      2 * ((D.hc τ).e ⟨h i, hj⟩ + X.cInf (D.R.m - i) τ)) →
    ∃ Q : SqSett T Lc X μ i (h i), Q.SeeSaw h

theorem kernel_square_step_hypothesis {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (sq : CommutationSquares T Lc X) (hK : Formalism.MainNotions.KudlaSiegelWeil.aux₃ D T Lc) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm14 D X := by
  intro μ hμ h i hp hf h1 h2 h3 P P' hm F hF
  obtain ⟨Q, hQ⟩ := sq μ hμ h i hp hf h1 h2 h3
  obtain ⟨ι, _, ΦA, ΦB, Λ, hA, hB, hpp, eA, eB⟩ := hQ P P' hm F hF
  have hc := Q.prop2 hK
  rw [eA, eB, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc (ΦA k) (hA k) (ΦB k) (hB k) (hpp k), map_smul]

def SquareLeavesWithoutCommutation (D : D7) {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (L : SizeData₂ D) (XD : DivX D)
    (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) : Prop :=
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.HypSz D L X K ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm1 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm3 D L XD X K.Cint ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.ArchimedeanSignatureMatching D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm8 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm10 K.Ctr ∧
  Formalism.MainNotions.SchurIrreducible.DiscreteSeriesBlattner X.ar ∧
  ExtraLowerBoundAtEmbeddings D L XD X K.Cgr ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm9 D L ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm15 D L XD X K.Cgr ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm16 D L X K.Cval ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm17 D V ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm19 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm20 D L X K.Cfp K.Cfp' ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm21 D L X K.Cip ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm22 D L X K.Cmm ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm23 D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.FrobeniusExpansionCongruence D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrExtensionClause D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.adm26 D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.HerrCocycleExtensionClass D X ∧
  Formalism.MainNotions.AbsolutelyIrreducibleSpan.FontaineFormalProperties D X ∧ Formalism.MainNotions.AbsolutelyIrreducibleSpan.AmbientMetricLowerBound D XD X

theorem square_leaves_of_kernel_theorem {D : D7} {V : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev D} {Am : AmbForm D V.S} (L : SizeData₂ D) (XD : DivX D)
    (T : ThetaX D) (Lc : Formalism.MainNotions.KudlaSiegelWeil.Loc D T) (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV D V Am) (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts)
    (S35 : Formalism.MainNotions.KudlaSiegelWeil.Stmt D T Lc) (P35p : Formalism.MainNotions.KudlaSiegelWeil.Pin D T Lc) (locJunk_be_pd : Formalism.MainNotions.KudlaSiegelWeil.admitted D T Lc) (tie : TieCsq T Lc X)
    (sq : CommutationSquares T Lc X)
    (L0 : SquareLeavesWithoutCommutation D L XD X K) : SquareLeaves D L XD X K := by
  obtain ⟨hK, hNZ, _⟩ := S35 P35p locJunk_be_pd
  obtain ⟨hs, a1, a3, a4, a8, a10, ds1, a2r, a9, a15, a16, a17, rest⟩ := L0
  exact ⟨hs, a1, a3, a4, a8, a10, ds1, a2r, a9, kernel_square_step_hypothesis T Lc X sq hK, a15, a16, a17,
    square_constant_nonzero T Lc X tie hK hNZ, rest⟩

theorem square_leaves_family_of_kernel {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.AbsolutelyIrreducibleSpan.LocV (Fm.D x i) (VF x hx i) (AF x hx i))
    (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.KudlaSiegelWeil.Loc (Fm.D x i) (Fm.ex x hx i).th)
    (K : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Consts) (S35 : Formalism.MainNotions.KudlaSiegelWeil.KudlaFamilyStatement Fm LF) (P35p : Formalism.MainNotions.KudlaSiegelWeil.PinF Fm LF) (locJunk_be_pd : Formalism.MainNotions.KudlaSiegelWeil.AdmF Fm LF)
    (tie : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TieCsq (Fm.ex x hx i).th (LF x hx i) (XF x hx i))
    (sq : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), CommutationSquares (Fm.ex x hx i).th (LF x hx i) (XF x hx i))
    (L0 : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SquareLeavesWithoutCommutation (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i) K) :
    ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SquareLeaves (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i) K :=
  fun x hx i => square_leaves_of_kernel_theorem _ _ _ (LF x hx i) _ K (fun _ _ => S35 P35p locJunk_be_pd x hx i) (P35p x hx i) (locJunk_be_pd x hx i) (tie x hx i)
    (sq x hx i)
    (L0 x hx i)

theorem kappa_hypothesis_of_sides (D : D7) (Z : DivX D) {Am : AmbForm D (RowSide.sharp D)} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Loc D Am)
    (hk : ∀ s : D.what₂.LL →+* ℂ, X.kapV (NumberField.InfinitePlace.mk s) = Z.kapR s)
    (h : Formalism.MainNotions.LocalQuadraticParts.PeterssonBoundAllEmbeddings D Z Am) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.AmbientMetricLowerBound D Z X := by
  intro s x q hq hx
  rw [hk s]
  have hq' : Am.jAmb D.what₂.mu0 q ∈ D.what₂.V0 D.what₂.mu0 := hq
  have hx' : D.jEE x = D.what₂.iota D.what₂.mu0 (Am.jAmb D.what₂.mu0 q) := by
    rw [← Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota]
    exact hx
  have e : Formalism.MainNotions.AbsolutelyIrreducibleSpan.qnAt D (V := Formalism.MainNotions.AbsolutelyIrreducibleSpan.Lev.sharp D) Am (NumberField.InfinitePlace.mk s) q =
      Formalism.MainNotions.LocalQuadraticParts.qn Am (NumberField.InfinitePlace.mk s) q := by
    rfl
  rw [e]
  exact h s x q hq' hx'

theorem kappa_hypothesis_of_levels (D : D7) (Z : DivX D) {Am : AmbForm D (RowSide.sharp D)} (X : Formalism.MainNotions.AbsolutelyIrreducibleSpan.Loc D Am)
    (hL : Formalism.MainNotions.AbsolutelyIrreducibleSpan.KapLevels Z X) (hc : Formalism.MainNotions.PGAL.KapConj D Z)
    (h : Formalism.MainNotions.LocalQuadraticParts.PeterssonBoundAllEmbeddings D Z Am) : Formalism.MainNotions.AbsolutelyIrreducibleSpan.AmbientMetricLowerBound D Z X :=
  kappa_hypothesis_of_sides D Z X (fun s => (hL _).trans (kapR_mk_of_KapConj D Z hc s)) h

theorem chain_bound_admissible_of_data (D : D7) (P : BaseLevelRowSide D) (C : ℝ) (hC : 0 < C)
    (hd : C * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)) ≤ 1 / 3)
    (h5 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion5 D P C) (hk : Formalism.MainNotions.PrimeDegreeVariant.ChainConstantPassage D P C) : Formalism.MainNotions.LocalQuadraticParts.adm10 D P C :=
  ⟨hC, hd, h5, hk⟩

def TieDatG (D : D7) (Z : DivX D) (G : Formalism.MainNotions.CanonicalTranslateJets.Loc D Z) : Prop :=
  ∀ μ j (h : G.Cls μ j) i x, ∃ (F : Type) (_ : Field F) (O : Subring F) (ϖ : F) (a t : ℕ)
    (J' : Subgroup (GL (Fin a) F)) (ρ : J' →* ℂˣ) (_ : ∀ k, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (y : Matrix (Fin a ⊕ Fin t) (Fin a) F),
    D.what₂.embLL (G.datG μ j h i x) = Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ y

theorem unitary_datum_hypothesis (D : D7) (Z : DivX D) (G : Formalism.MainNotions.CanonicalTranslateJets.Loc D Z) (T : TieDatG D Z G) :
    Formalism.MainNotions.CanonicalTranslateJets.adm1 D Z G := by
  intro μ j _ h i x
  obtain ⟨F, _, O, ϖ, a, t, J', ρ, hρ, y, e⟩ := T μ j h i x
  unfold Formalism.DoubleCosetMeasures.phiU at e
  split_ifs at e with hc
  · right
    obtain ⟨n, hn, hk⟩ := hρ (Classical.choose hc.1)
    refine ⟨n, hn, D.what₂.embLL.injective ?_⟩
    rw [map_pow, e, map_one, ← Units.val_pow_eq_pow_val, hk, Units.val_one]
  · left
    exact D.what₂.embLL.injective (by rw [e, map_zero])

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.BasicNotions.DV

theorem lift_sum_bound_admissible_of_data (D : D7) (L : SizeData₂ D) (X : Formalism.MainNotions.LocalQuadraticParts.Loc D) (C' BJ C Cabs : ℝ)
    (h : Formalism.MainNotions.PDVN.ONTwJ D L C') (hJ0 : ∀ j w, 0 ≤ X.Jx j w)
    (hJ : ∀ j ∈ SizeData₂.lifts D, ∀ T : Finset D.what₂.places.Pl,
      ∑ w ∈ T, SizeData₂.lwP w * ur D w (X.Jx j w) ≤ BJ)
    (hsz : Formalism.MainNotions.PDVN.onBoundJ D L C' + BJ ≤ C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc)) :
    Formalism.MainNotions.LocalQuadraticParts.ArchimedeanSignatureMatching D L X C Cabs := by
  obtain ⟨fl, r, h1, h2, h3, h4, -⟩ := h
  have hl : ∀ w : D.what₂.places.Pl, 0 ≤ SizeData₂.lwP w := by
    intro w
    unfold SizeData₂.lwP lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have herr : ∀ j w, 0 ≤ Formalism.MainNotions.PDVN.onRj D fl r j w := by
    intro j w
    unfold Formalism.MainNotions.PDVN.onRj
    exact add_nonneg (h1 _ _) (div_nonneg (add_nonneg (h2 _ _) (h2 _ _)) (Nat.cast_nonneg _))
  refine ⟨fun j w => Formalism.MainNotions.PDVN.onRj D fl r j w, fl, r, h1, h2, hJ0, fun j w => rfl, fun w hw => ?_,
    fun j hj => ?_⟩
  · have he : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by exact_mod_cast D.what₂.places.ramIdx_pos w
    have k := mul_le_mul_of_nonneg_left (h3 w hw) he.le
    have e : (D.what₂.places.ramIdx w : ℝ) * Formalism.MainNotions.PDVN.onL D L (D.what₂.muAt w) w =
        ∑ j ∈ SizeData₂.lifts D,
          (((D.what₂.Ij (D.what₂.muAt w) j w : ℝ) +
            (D.what₂.Ij (D.what₂.muAt w) j (D.what₂.places.conj w) : ℝ)) /
            (D.what₂.D0 : ℝ) - 2 * ur D w (L.F j w)) := by
      unfold Formalism.MainNotions.PDVN.onL Formalism.MainNotions.PDVN.inL ur
      rw [Finset.mul_sum, Formalism.MainNotions.PDVN.ramIdx_conj]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [e] at k
    exact k
  · have hnn : ∀ w, 0 ≤ SizeData₂.lwP w * ur D w (Formalism.MainNotions.PDVN.onRj D fl r j w + X.Jx j w) := fun w =>
      mul_nonneg (hl w) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (herr j w) (hJ0 j w)))
    have hb : ∀ T : Finset D.what₂.places.Pl,
        ∑ w ∈ T, SizeData₂.lwP w * ur D w (Formalism.MainNotions.PDVN.onRj D fl r j w + X.Jx j w) ≤
          C * L.sc.x ^ (Cabs * L.sc.eps) * (L.B0 + L.Nc) := by
      intro T
      have : ∑ w ∈ T, SizeData₂.lwP w * ur D w (Formalism.MainNotions.PDVN.onRj D fl r j w + X.Jx j w) =
          ∑ w ∈ T, SizeData₂.lwP w * ur D w (Formalism.MainNotions.PDVN.onRj D fl r j w) +
            ∑ w ∈ T, SizeData₂.lwP w * ur D w (X.Jx j w) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        unfold ur
        ring
      rw [this]
      exact le_trans (add_le_add (h4 j hj T) (hJ j hj T)) hsz
    have hs := summable_of_sum_le hnn hb
    exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

section Proved

open Formalism.BasicNotions.TH

theorem first_lemma_all_clauses : Formalism.MainNotions.ZetaProductPairs.L1 :=
  ⟨Formalism.DoubleCosetMeasures.P.lemmaUSplit, parahoric_index_int, datum_block_eigenvalues, datum_conjugation_invariant⟩

theorem first_lemma_statement_proved : Formalism.MainNotions.ZetaProductPairs.LocalComputationOne := first_lemma_all_clauses

theorem unitary_multiplicity_one : Formalism.MainNotions.ZetaProductPairs.adm3 := uMultOne_closed

theorem lift_hypotheses_with_second_lemma (D : D7) (Z : DivX D) (T : ThetaX D) (A : ProvA) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A) (hL2 : Formalism.MainNotions.ZetaProductPairs.L2 Z) (hV : Formalism.MainNotions.PrimeDegreeVariant.ThetaUpInV0 D)
    (h3 : Formalism.MainNotions.PrimeDegreeVariant.ExactRowOccurrence D)
    (a1 : Formalism.MainNotions.InnerProductFormulaField.adm1 D Z T X) (a2 : Formalism.MainNotions.InnerProductFormulaField.adm2 D Z X) (a3 : ArchimedeanChainApplication D T A X)
    (a4 : Formalism.MainNotions.InnerProductFormulaField.ArchimedeanSignatureMatching D T X) (tg : TieG D X) (a7 : Formalism.MainNotions.InnerProductFormulaField.adm7 D X) (a8 : Formalism.MainNotions.InnerProductFormulaField.adm8 D)
    (a9 : Formalism.MainNotions.InnerProductFormulaField.adm9 D T X) (hI : Rows.IsotInternal D.what₂) (hR : Rows.IsotRank D.what₂) :
    Formalism.MainNotions.InnerProductFormulaField.admitted D Z T A X :=
  lift_hypotheses_of_parts D Z T A X h1 first_lemma_all_clauses hL2 hV h3 a1 a2 a3 a4 tg a7 a8 a9 hI hR

theorem admissible_family_of_L2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (A : ProvA)
    (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst A)
    (h19 : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.ZetaProductPairs.L2 (Fm.X x i))
    (hV : Formalism.MainNotions.PrimeDegreeVariant.familyThetaUpInV0 Fm) (h3 : Formalism.MainNotions.PrimeDegreeVariant.familyExactRowOccurrence Fm)
    (hL : LeafHypothesesFamily Fm A XF) : Formalism.MainNotions.InnerProductFormulaField.AdmF Fm A XF :=
  lift_hypotheses_family_leaves Fm A XF h1 (fun x hx i => ⟨first_lemma_all_clauses, h19 x hx i⟩) hV h3 hL

end Proved

section Split20

set_option linter.unusedVariables false

open Formalism.BasicNotions Formalism.BasicNotions.TH

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def LiftLeavesFamilyByKind (A : ProvA) (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.InnerProductFormulaField.AdmLit (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).th (XF x hx i) ∧
    ArchimedeanChainApplication (Fm.D x i) (Fm.ex x hx i).th A (XF x hx i) ∧
    TieG (Fm.D x i) (XF x hx i) ∧
    Formalism.MainNotions.InnerProductFormulaField.AdmOwn (Fm.D x i) (Fm.ex x hx i).th (XF x hx i) ∧
    Rows.IsotInternal (Fm.D x i).what₂ ∧ Rows.IsotRank (Fm.D x i).what₂

theorem leaf_family_iff_grouped (A : ProvA) (XF : Formalism.MainNotions.InnerProductFormulaField.LocF Fm) : LeafHypothesesFamily Fm A XF ↔ LiftLeavesFamilyByKind Fm A XF :=
  ⟨fun h x hx i => let ⟨a1, a2, a3, a4, tg, a7, a8, a9, hI, hR⟩ := h x hx i
    ⟨⟨a1, a2, a4, a7⟩, a3, tg, ⟨a8, a9⟩, hI, hR⟩,
   fun h x hx i => let ⟨⟨a1, a2, a4, a7⟩, a3, tg, ⟨a8, a9⟩, hI, hR⟩ := h x hx i
    ⟨a1, a2, a3, a4, tg, a7, a8, a9, hI, hR⟩⟩

end Split20

end Formalism.MainNotions.DIV

end
