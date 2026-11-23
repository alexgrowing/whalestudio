import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyCriticalLevelLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DegreeRatioFormulaStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SplitsCompletelyIff
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LocalFormOfHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DecayHypothesisOfLargeConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.PairTermsOfFlagRigidity
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.WeightedProjectionSumSelfAdjoint
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalL1StatementOfProjectors
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions Formalism.MainNotions MeasureTheory

namespace AutInst

variable (I : AutInst)

open Classical in

def IsLevelCharIdem (μf : Measure I.Gf) (g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  ∃ (K'' : Subgroup I.Gf) (χ : I.Gf → ℂ), IsOpen (K'' : Set I.Gf) ∧ IsCompact (K'' : Set I.Gf) ∧
    (K'' : Set I.Gf) ⊆ I.Kset ∧ (∀ k ∈ K'', I.UnipMod g₀ k) ∧
    (∀ k ∈ K'', ∀ k' ∈ K'', χ (k * k') = χ k * χ k') ∧ (∀ k ∈ K'', ‖χ k‖ = 1) ∧
    ∀ x, e x = if x ∈ K'' then (χ x)⁻¹ / ((μf (K'' : Set I.Gf)).toReal : ℂ) else 0

end AutInst

namespace CountE

open Formalism.MainNotions.PlaceDegreeData NumberField

variable (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop)

def CountIdempotentsClass (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → P I μf g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h →
    Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) →
    Real.log (Real.log b) ≤ cb * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) →
    |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (fdegAll I σ w) μf fund e| ≤
      Real.exp (-c * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (fdegAll I σ w) μf fund e

def RowsTieP (D : Formalism.BasicNotions.D7) (X : RowsAut) : Prop := RowsTie D X ∧ P X.I X.μf X.g₀ X.e

def CountRowsClass (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (X : RowsAut) (b h : ℝ), RowsTieP P D X → HidaSetting X.I n₀ A b X.lam X.μf X.g X.g₀ X.e →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (X.I.ε v) (X.lam v) h) →
    C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (b * D.host.rdE) ≤ h →
    Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) →
    Real.log (Real.log b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ) →
    |(D.what₂.Dall : ℝ) - D.what₂.Dstar| ≤
      Real.exp (-(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ))) * D.what₂.Dstar

def CountAllPointsClass {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  0 < c ∧ 0 < cb ∧ ∀ x (i : Fm.Ix x), CountIdempotentsClass P (Fm.D x i) n₀ A C c cb

def CountRowsClassFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  0 < c ∧ 0 < cb ∧ ∀ x (i : Fm.Ix x), CountRowsClass P (Fm.D x i) n₀ A C c cb

def CountFamilyClassStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ) : Prop :=
  admF4 Fm ∧ admF5 Fm ∧ admF6 Fm ∧ admF7 Fm Cres ∧ admF8 Fm → FamilyDiscreteSeriesDecay Fm → ConclusionF2 Fm n₀ A Cb →
    CountAllPointsClass P Fm n₀ A C c cb

def ShareFamilyAtConstant {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ) : Prop :=
  AdmF Fm Cres →
    FamilyLowestKTypeFormula Fm ∧ FamilyDiscreteSeriesDecay Fm ∧ FamilyMatrixCoefficientL1 Fm ∧ FamilyAbstractProjectorEveryMember Fm ∧ FamilyLocalProjectorEveryMember Fm ∧ ConclusionF2 Fm n₀ A Cb ∧ CountAllPointsClass P Fm n₀ A C c cb

theorem count_class_of_count {D : Formalism.BasicNotions.D7} {n₀ : ℕ} {A C c cb : ℝ} (h : PointsLemma D n₀ A C c cb) : CountIdempotentsClass P D n₀ A C c cb := by
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h' hS _ hc hg h1 h2 h3
  exact h I b lam g g₀ e H σ w Hs σs tens μf fund R Re h' hS hc hg h1 h2 h3

theorem count_family_class_of_count {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {Cres : ℝ} {n₀ : ℕ} {A Cb C c cb : ℝ}
    (h : FlatLineDegreeFamilyStatement Fm Cres n₀ A Cb C c cb) : CountFamilyClassStatement P Fm Cres n₀ A Cb C c cb := fun hA h1 h2 =>
  let h3 := h hA h1 h2
  ⟨h3.1, h3.2.1, fun x i => count_class_of_count P (h3.2.2 x i)⟩

theorem family_statement_class_of_general {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {Cres : ℝ} {n₀ : ℕ} {A Cb C c cb : ℝ}
    (h : KudlaFamilyStatement Fm Cres n₀ A Cb C c cb) : ShareFamilyAtConstant P Fm Cres n₀ A Cb C c cb := fun hA =>
  let h' := h hA
  ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1,
    h'.2.2.2.2.2.2.1, h'.2.2.2.2.2.2.2.1, fun x i => count_class_of_count P (h'.2.2.2.2.2.2.2.2 x i)⟩

theorem family_link_count_class {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {Cres : ℝ} {n₀ : ℕ} {A Cb C c cb : ℝ} (i0 : FamilyFormulaStatement Fm)
    (i5 : DeterminantValueFamily Fm n₀ A Cb) (i6 : CountFamilyClassStatement P Fm Cres n₀ A Cb C c cb) : ShareFamilyAtConstant P Fm Cres n₀ A Cb C c cb := by
  intro hA
  have a1 : admF1 Fm := fun x i => (hA x i).1
  have a2 : admF2 Fm := fun x i => (hA x i).2.1
  have a3 : admF3 Fm := fun x i => (hA x i).2.2.1
  have a4 : admF4 Fm := fun x i => (hA x i).2.2.2.1
  have a5 : admF5 Fm := fun x i => (hA x i).2.2.2.2.1
  have a6 : admF6 Fm := fun x i => (hA x i).2.2.2.2.2.1
  have a7 : admF7 Fm Cres := fun x i => (hA x i).2.2.2.2.2.2.1
  have a8 : admF8 Fm := fun x i => (hA x i).2.2.2.2.2.2.2
  have p0 := i0 ⟨a2, a3⟩
  have p1 := BridgeLemma.family_decay_of_formula Fm p0
  have p2 := BridgeLemma.family_spherical_L1_statement Fm a2 p1
  have p3 := BridgeLemma.family_abstract_projector_statement Fm
  have p4 := BridgeLemma.family_projector_section_local Fm a1 p2 p3
  have p5 := i5 ⟨a1, a6, a8⟩ p1 p4
  exact ⟨p0, p1, p2, p3, p4, p5, i6 ⟨a4, a5, a6, a7, a8⟩ p1 p5⟩

section Count

open Finset

variable {D : D7}

theorem admissibility_ten_of_rows_class (large₂ : SizeData₂ D) (X : RowsAut) (hX : RowsTieP P D X) (n0 : ℕ) (A C cb c : ℝ)
    (h : CountRowsClass P D n0 A C c cb) : AdmissibleBoundsFromSource.adm10 D large₂ n0 A C cb c := by
  intro hp
  obtain ⟨-, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := hp
  have hX' := hX.1
  obtain ⟨⟨pl, T⟩, t5, tsp⟩ := hX'
  have hn := T.n_eq
  have trd := T.rd_eq
  have tg0 := T.g0_eq
  have tg := T.g_eq
  have hq : ∀ v, X.I.pAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = true).card ∧
      X.I.qAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = false).card := by
    intro v
    have he := T.eps_eq v
    constructor
    · simp only [AutInst.pAt, he]
      exact card_cast hn (fun a => epsS D.R a = true)
    · simp only [AutInst.qAt, he]
      exact card_cast hn (fun a => epsS D.R a = false)
  have hS : PlaceDegreeData.HidaSetting X.I n0 A large₂.sc.b X.lam X.μf X.g X.g₀ X.e := by
    refine ⟨by rw [hn]; exact p2, ⟨_, _, hq, ?_⟩, p11, ?_, t5, ?_, X.e_adm, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hn]
      exact le_trans (Nat.pow_le_pow_left card_epsS_false 2) p3
    · rw [trd, hn]; exact p4
    · intro v a
      rw [T.lam_eq v a]; exact p5 _ _
    · rw [tg]
      exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    · rw [tg]
      have : gg D = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by unfold gg; push_cast; ring
      rw [← this]; exact p6
    · rw [tg0]; exact D.host.g_prime 0
    · rw [tg0, hn]; exact p7
    · exact tsp p8
  refine h X large₂.sc.b _ hX hS (fun v a c hac => ?_) le_rfl p10 p12
  rw [T.lam_eq v a, T.lam_eq v c]
  exact p9 _ _ _ (by rw [← T.eps_eq v a, ← T.eps_eq v c]; exact hac)

theorem count_rows_class_of_count_class (n₀ : ℕ) (A C c cb : ℝ) (hp : CountIdempotentsClass P D n₀ A C c cb) : CountRowsClass P D n₀ A C c cb := by
  intro X b h hT hS hg h1 h2 h3
  have hPX := hT.2
  obtain ⟨⟨pl, hA⟩, -, -⟩ := hT.1
  have hD := hA.D_eq
  have hDs : X.I.Dstar (PlaceDegreeData.fdegAll X.I X.σ X.w) X.μf X.fund X.e = D.what₂.Dstar := hA.Dstar_eq.symm
  have hf := hA.f_eq
  have hrd := hA.rd_eq
  have hn := hA.n_eq
  have hc : PlaceDegreeData.CountData X.I X.lam X.σ X.w X.σs X.tens X.μf X.fund X.R X.e X.Re :=
    ⟨hA.ds, hA.low, X.tens_spec, X.haar, X.fund_spec, X.R_spec, X.Re_spec⟩
  rw [← hn, ← hf, ← hrd] at h1
  rw [← hn, ← hf] at h2 h3
  have := hp X.I b X.lam X.g X.g₀ X.e X.H X.σ X.w X.Hs X.σs X.tens X.μf X.fund X.R X.Re h hS hPX hc hg h1 h2 h3
  have e1 : (X.I.Dcount X.σs X.μf X.fund X.R X.Re : ℝ) = (D.what₂.Dall : ℝ) := by exact_mod_cast hD
  rw [e1, hDs] at this
  rw [← hn, ← hf]
  convert this using 3
  ring

end Count

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem countOwn_of_rowsP (Cg cb Cu cT CT C0 : ℝ) (n0 : ℕ) (A C c cb7 : ℝ) (hC : 0 ≤ C) (hA : 2 * Cg ≤ A)
    (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm)
    (hR : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, RowsTieP P (Fm.D x i) X)
    (h30 : CountRowsClassFamily P Fm n0 A C c cb7) : CountOwn Fm Cg cb Cu cT CT C0 c := by
  obtain ⟨-, hcb, h30⟩ := h30
  have hG := cGam_pos Fm
  obtain ⟨Y1, hY1, HY1⟩ := linear_le_pow_eight_eventually (8 * Fm.CGam) n0 (by positivity)
  obtain ⟨Y2, -, HY2⟩ := linear_le_pow_eight_eventually (cb7 * (8 * Fm.CGam)) 8 (by positivity)
  obtain ⟨x4, hx4⟩ := ev_y Fm (max Y1 Y2)
  refine ⟨max (Fm.x1 + 1) x4, fun x hx i hH => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hx
    linarith
  have hy := hx4 x (le_trans (le_max_right _ _) hx)
  set y : ℝ := x ^ (eps / 8) with hydef
  have hy1 : 1 ≤ y := le_trans hY1 (le_trans (le_max_left _ _) hy)
  have a1 := HY1 y (le_trans (le_max_left _ _) hy)
  have a2 := HY2 y (le_trans (le_max_right _ _) hy)
  have hL := scL_eq Fm x hx1 i
  have hh : AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 (sC' Fm) (sCl Fm) Cg cb Cu cT CT := ⟨hH.2.1, hH.1, hH.2.2⟩
  have hk8 := k_ge_of_hyp (Fm.L x i) hh
  rw [hL, Fm.CGam_eq x i] at hk8
  obtain ⟨X, hX⟩ := hR x hx1 i
  refine admissibility_ten_of_rows_class P (Fm.L x i) X hX n0 A C cb7 c (h30 x i)
    (count_parameters_of_hyp (Fm.L x i) C0 _ _ Cg cb Cu cT CT n0 A C cb7 hC hcb hA ?_ hCl2 hCl3 ?_ hh)
  · have : (n0 : ℝ) ≤ n0 * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    linarith
  · rw [hL, Real.log_pow]
    have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
    have h2 : cb7 * (8 * Fm.CGam * y ^ 8) ≤ cb7 * ((Fm.D x i).R.k : ℝ) := mul_le_mul_of_nonneg_left hk8 hcb.le
    push_cast
    nlinarith

theorem linkS_of_thmSP (Cg cb Cu cT CT C0 Cres : ℝ) (n0 : ℕ) (A Cb C c7 cb7 : ℝ) (h1 : 1 ≤ C0) (hC : 0 ≤ C)
    (hA : 2 * Cg ≤ A) (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm)
    (hS0 : StandingHypothesesWithConstants Fm Cg cb Cu cT CT C0)
    (hR : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, RowsTieP P (Fm.D x i) X)
    (hT : ThmSOwn Fm Cg cb Cu cT CT C0)
    (S30 : ShareFamilyAtConstant P Fm Cres n0 A Cb C c7 cb7) (A30 : PlaceDegreeData.AdmF Fm Cres) : Formalism.MainNotions.LinkS Fm C0 := by
  have h30 : CountAllPointsClass P Fm n0 A C c7 cb7 := (S30 A30).2.2.2.2.2.2
  have h30R : CountRowsClassFamily P Fm n0 A C c7 cb7 :=
    ⟨h30.1, h30.2.1, fun x i => count_rows_class_of_count_class P n0 A C c7 cb7 (h30.2.2 x i)⟩
  exact linkS_of_standing_hypotheses Fm Cg cb Cu cT CT C0 c7 h1 h30.1 hS0 hT
    (countOwn_of_rowsP P Fm Cg cb Cu cT CT C0 n0 A C c7 cb7 hC hA hCl2 hCl3 hR h30R)

theorem countOwn_of_rowsP' (Cg cb Cu cT CT C0 : ℝ) (n0 : ℕ) (A C c cb7 : ℝ) (hC : 0 ≤ C) (hA : 2 * Cg ≤ A)
    (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm)
    (hR : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, RowsTieP P (Fm.D x i) X)
    (h30 : CountRowsClassFamily P Fm n0 A C c cb7) : CountOwn Fm Cg cb Cu cT CT C0 c := by
  obtain ⟨x0, hR0⟩ := hR
  obtain ⟨-, hcb, h30⟩ := h30
  have hG := cGam_pos Fm
  obtain ⟨Y1, hY1, HY1⟩ := linear_le_pow_eight_eventually (8 * Fm.CGam) n0 (by positivity)
  obtain ⟨Y2, -, HY2⟩ := linear_le_pow_eight_eventually (cb7 * (8 * Fm.CGam)) 8 (by positivity)
  obtain ⟨x4, hx4⟩ := ev_y Fm (max Y1 Y2)
  refine ⟨max (max (Fm.x1 + 1) x4) x0, fun x hx i hH => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
    linarith
  have hy := hx4 x (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx))
  set y : ℝ := x ^ (eps / 8) with hydef
  have hy1 : 1 ≤ y := le_trans hY1 (le_trans (le_max_left _ _) hy)
  have a1 := HY1 y (le_trans (le_max_left _ _) hy)
  have a2 := HY2 y (le_trans (le_max_right _ _) hy)
  have hL := scL_eq Fm x hx1 i
  have hh : AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 (sC' Fm) (sCl Fm) Cg cb Cu cT CT := ⟨hH.2.1, hH.1, hH.2.2⟩
  have hk8 := k_ge_of_hyp (Fm.L x i) hh
  rw [hL, Fm.CGam_eq x i] at hk8
  obtain ⟨X, hX⟩ := hR0 x (le_trans (le_max_right _ _) hx) hx1 i
  refine admissibility_ten_of_rows_class P (Fm.L x i) X hX n0 A C cb7 c (h30 x i)
    (count_parameters_of_hyp (Fm.L x i) C0 _ _ Cg cb Cu cT CT n0 A C cb7 hC hcb hA ?_ hCl2 hCl3 ?_ hh)
  · have : (n0 : ℝ) ≤ n0 * y := le_mul_of_one_le_right (Nat.cast_nonneg _) hy1
    linarith
  · rw [hL, Real.log_pow]
    have h1 : Real.log y ≤ y := Real.log_le_self (by linarith)
    have h2 : cb7 * (8 * Fm.CGam * y ^ 8) ≤ cb7 * ((Fm.D x i).R.k : ℝ) := mul_le_mul_of_nonneg_left hk8 hcb.le
    push_cast
    nlinarith

theorem linkS_of_thmSP' (Cg cb Cu cT CT C0 Cres : ℝ) (n0 : ℕ) (A Cb C c7 cb7 : ℝ) (h1 : 1 ≤ C0) (hC : 0 ≤ C)
    (hA : 2 * Cg ≤ A) (hCl2 : 2 ≤ sCl Fm) (hCl3 : 2 * C ≤ sCl Fm)
    (hS0 : StandingHypothesesWithConstants Fm Cg cb Cu cT CT C0)
    (hR : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, ∃ X : RowsAut, RowsTieP P (Fm.D x i) X)
    (hT : ThmSOwn Fm Cg cb Cu cT CT C0)
    (S30 : ShareFamilyAtConstant P Fm Cres n0 A Cb C c7 cb7) (A30 : PlaceDegreeData.AdmF Fm Cres) : Formalism.MainNotions.LinkS Fm C0 := by
  have h30 : CountAllPointsClass P Fm n0 A C c7 cb7 := (S30 A30).2.2.2.2.2.2
  have h30R : CountRowsClassFamily P Fm n0 A C c7 cb7 :=
    ⟨h30.1, h30.2.1, fun x i => count_rows_class_of_count_class P n0 A C c7 cb7 (h30.2.2 x i)⟩
  exact linkS_of_standing_hypotheses Fm Cg cb Cu cT CT C0 c7 h1 h30.1 hS0 hT
    (countOwn_of_rowsP' P Fm Cg cb Cu cT CT C0 n0 A C c7 cb7 hC hA hCl2 hCl3 hR h30R)

end Family

abbrev PLev : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop := fun I μf g₀ e => I.IsLevelCharIdem μf g₀ e

end CountE

open Classical in

def IsCharIdemFin {G : Type} [Group G] (f : MonoidAlgebra ℂ G) : Prop :=
  ∃ (U : Subgroup G) (χ : G → ℂ), (∀ a ∈ U, ∀ b ∈ U, χ (a * b) = χ a * χ b) ∧ (∀ a ∈ U, ‖χ a‖ = 1) ∧
    ∀ a, f.coeff a = if a ∈ U then (χ a)⁻¹ / (Nat.card U : ℂ) else 0

namespace AutInst

variable (I : AutInst)

structure RedDatum (g₁ g₂ : ℕ) : Type 1 where
  G₁ : Type
  G₂ : Type
  [grp₁ : Group G₁]
  [grp₂ : Group G₂]
  [fin₁ : Fintype G₁]
  [fin₂ : Fintype G₂]
  red : I.Gf → G₁ × G₂
  red_mul : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, red (x * y) = red x * red y
  red_surj : ∀ a : G₁ × G₂, ∃ x ∈ I.Kset, red x = a
  red_fib₁ : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, ((red x).1 = (red y).1 ↔ x⁻¹ * y ∈ I.Kg g₁)
  red_fib₂ : ∀ x ∈ I.Kset, ∀ y ∈ I.Kset, ((red x).2 = (red y).2 ↔ x⁻¹ * y ∈ I.Kg g₂)

attribute [instance] RedDatum.grp₁ RedDatum.grp₂ RedDatum.fin₁ RedDatum.fin₂

open Classical in

def IsCountIdem (μf : Measure I.Gf) (g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  ∃ (a b p : ℕ) (R : I.RedDatum (g₀ ^ a) (p ^ b)) (f₀ : MonoidAlgebra ℂ R.G₁) (z ε₂ : MonoidAlgebra ℂ R.G₂),
    p.Prime ∧ p ≠ g₀ ∧ IsCharIdemFin f₀ ∧ (∀ x ∈ I.Kset, f₀.coeff (R.red x).1 ≠ 0 → I.UnipMod g₀ x) ∧
    IsCharIdemFin ε₂ ∧ z * z = z ∧ (∀ y : MonoidAlgebra ℂ R.G₂, z * y = y * z) ∧
    ∀ x, e x = if x ∈ I.Kset then
      f₀.coeff (R.red x).1 * (z * ε₂).coeff (R.red x).2 / ((μf (I.Kg (g₀ ^ a) ∩ I.Kg (p ^ b))).toReal : ℂ) else 0

end AutInst

namespace CountE

abbrev PCount : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop :=
  fun I μf g₀ e => I.IsLevelCharIdem μf g₀ e ∨ I.IsCountIdem μf g₀ e

end CountE

end Formalism.MainNotions.S
