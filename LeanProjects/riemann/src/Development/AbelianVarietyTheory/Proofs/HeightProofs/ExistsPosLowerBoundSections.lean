import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FullTranscendenceDegree
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitAndGenValInj
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoCommonZeroOfReadings
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfDefinite

noncomputable section

namespace GlobalTheory.BignessCompare

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree (CuspAt XP Generates ptNorm l2Norm FullTrdeg SmallForm ExistsNonzeroCuspFormOfWeightPair CurveModelAt CurveModelExists
  ptNorm_nonneg)

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} [Fintype κ]

theorem bdd_of_mem_holSub (X : κ → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, ∀ p : FPt X, (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ M := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    refine ⟨∑ c, |C c|, fun p => (hC p.1 p.2 p.2.2).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  | zero => exact ⟨0, fun p => (pnorm_zero _ _ _).le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    exact ⟨a + b, fun p => (pnorm_add_le _ _ _ _ _).trans (add_le_add (ha p) (hb p))⟩
  | smul a P _ hP =>
    obtain ⟨b, hb⟩ := hP
    exact ⟨‖a‖ * b, fun p => (pnorm_smul _ _ a _ _).le.trans (mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _))⟩

end Model

section Weights

variable {D : D7} {j : ℕ}

theorem wt_ext {u v : WeightFamilies.Wt D j} (e1 : ∀ τ i, u.aP τ i = v.aP τ i) (e2 : ∀ τ i, u.aM τ i = v.aM τ i)
    (e3 : u.n = v.n) : u = v := by
  have e1' : u.aP = v.aP := funext fun τ => funext (e1 τ)
  have e2' : u.aM = v.aM := funext fun τ => funext (e2 τ)
  obtain ⟨⟩ := u
  obtain ⟨⟩ := v
  simp only at e1' e2' e3
  subst e1' e2' e3
  rfl

theorem wsmul_add_one (e : ℕ) (w : WeightFamilies.Wt D j) : wadd (wsmul e w) w = wsmul (e + 1) w :=
  wt_ext (fun _ _ => (add_one_mul _ _).symm) (fun _ _ => (add_one_mul _ _).symm) (add_one_mul _ _).symm

theorem wadd_assoc (u v w : WeightFamilies.Wt D j) : wadd u (wadd v w) = wadd (wadd u v) w :=
  wt_ext (fun _ _ => (add_assoc _ _ _).symm) (fun _ _ => (add_assoc _ _ _).symm) (add_assoc _ _ _).symm

end Weights

section Record

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

theorem exists_nonZeroComp_mul {u v : WeightFamilies.Wt D j} {F : B.Cusp j u} {G : B.Cusp j v} (hF : X.NonZeroComp u F)
    (hG : X.NonZeroComp v G) : ∃ H : B.Cusp j (wadd u v), X.NonZeroComp (wadd u v) H := by
  obtain ⟨H, hH⟩ := X.inc_mul u v F G
  refine ⟨H, fun w' K hK => ?_⟩
  obtain ⟨H', hH'⟩ := X.inc_mul v w' G K
  have h0 : H' = 0 := hF _ H' (by rw [← hH', ← mul_assoc, hH, hK])
  exact hG w' K (by rw [hH', h0, map_zero])

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
  (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)

include hinj in

theorem nonZeroComp_iff_ev {wL : WeightFamilies.Wt D j}
    (hs : ∀ Z, ∃ g : B.Cusp j wL, gF Z (X.inc wL g) ≠ 0 ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0)
    {u : WeightFamilies.Wt D j} (F : B.Cusp j u) : X.NonZeroComp u F ↔ ∀ Z, gF Z (X.inc u F) ≠ 0 := by
  refine ⟨fun hF Z h0 => ?_, fun hF w' G hG => hinj w' G fun Z => ?_⟩
  · obtain ⟨g, h1, h2⟩ := hs Z
    obtain ⟨H, hH⟩ := X.inc_mul u wL F g
    have hz : H = 0 := by
      refine hinj _ H fun Z' => ?_
      rw [← hH, map_mul]
      by_cases e : Z' = Z
      · subst e
        rw [h0, zero_mul]
      · rw [h2 Z' e, mul_zero]
    have hg0 : g = 0 := hF wL g (by rw [hH, hz, map_zero])
    exact h1 (by rw [hg0, map_zero, map_zero])
  · have := congrArg (gF Z) hG
    rw [map_mul, map_zero] at this
    exact (mul_eq_zero.1 this).resolve_left (hF Z)

theorem exists_ev_ne_zero [Finite ι] {wL : WeightFamilies.Wt D j}
    (hs : ∀ Z, ∃ g : B.Cusp j wL, gF Z (X.inc wL g) ≠ 0 ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0) :
    ∃ g : B.Cusp j wL, ∀ Z, gF Z (X.inc wL g) ≠ 0 := by
  have := Fintype.ofFinite ι
  choose g h1 h2 using hs
  refine ⟨∑ Z, g Z, fun Z => ?_⟩
  rw [map_sum, map_sum, Finset.sum_eq_single Z (fun Z' _ e => h2 Z' Z e.symm) (fun h => absurd (Finset.mem_univ _) h)]
  exact h1 Z

end Record

section Inst

variable {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {ka wL wF : WeightFamilies.Wt D j}

def GenNeZero {u : WeightFamilies.Wt D j} (F : CuspAt h j u) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z (F.1 : T.R j) ≠ 0

def HasForms (wL : WeightFamilies.Wt D j) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ g : CuspAt h j wL, evC hG Z (g.1 : T.R j) ≠ 0

include h hj in

theorem genFromTest : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)

theorem formsEv_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) :
    formsEvR j hG (genFromTest h j hj hG) Z ((XP h j hj).inc u F) = evC hG Z (F.1 : T.R j) :=
  formsEvR_single j hG _ Z _ _

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem separating (H : HasForms h j hG wL) (Z : Comp (T.Q.Xo j) T.Q.c) :
    ∃ g : CuspAt h j wL, formsEvR j hG (genFromTest h j hj hG) Z ((XP h j hj).inc wL g) ≠ 0 ∧
      ∀ Z', Z' ≠ Z → formsEvR j hG (genFromTest h j hj hG) Z' ((XP h j hj).inc wL g) = 0 := by
  obtain ⟨g, hg⟩ := H Z
  obtain ⟨g', e1, e2⟩ := (GlobalTheory.Reg.compSplit_and_genValInj D T h j hj hG).1 Z wL g
  exact ⟨g', fun h0 => hg (e1.symm.trans ((formsEv_inc h j hj hG Z wL g').symm.trans h0)),
    fun Z' hZ => (formsEv_inc h j hj hG Z' wL g').trans (e2 Z' hZ)⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nonZeroComp_iff_genNeZero (H : HasForms h j hG wL) {u : WeightFamilies.Wt D j} (F : CuspAt h j u) :
    (XP h j hj).NonZeroComp u F ↔ GenNeZero h j hG F := by
  have hV := (GlobalTheory.Reg.compSplit_and_genValInj D T h j hj hG).2
  refine (nonZeroComp_iff_ev (XP h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG (genFromTest h j hj hG) Z)
    (fun u F hF => hV u F fun Z => (formsEv_inc h j hj hG Z u F).symm.trans (hF Z))
    (separating h j hj hG H) F).trans (forall_congr' fun Z => ?_)
  exact ⟨fun a b => a ((formsEv_inc h j hj hG Z u F).trans b), fun a b => a ((formsEv_inc h j hj hG Z u F).symm.trans b)⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_nonZeroComp (H : HasForms h j hG wL) : ∃ g : CuspAt h j wL, (XP h j hj).NonZeroComp wL g := by
  have := CompFin.finite_comp (T.Q.Xo j) T.Q.c
  obtain ⟨g, hg⟩ := exists_ev_ne_zero (XP h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG (genFromTest h j hj hG) Z) (separating h j hj hG H)
  exact ⟨g, (nonZeroComp_iff_genNeZero h j hj hG H g).2 fun Z b => hg Z ((formsEv_inc h j hj hG Z wL g).trans b)⟩

def Bounds (σ : T.Q.c.F →+* ℂ) {N : ℕ} (w : Fin N → CuspAt h j wL) (k m₀ : ℕ) (β : CuspAt h j (wsmul k wL))
    (C : ℝ) : Prop :=
  ∀ p : FPt (T.U j σ).X, ptNorm h j σ (wsmul k wL) β p ≤ C * l2Norm h j σ w p ^ k ∧
    ptNorm h j σ (wsmul k wL) β p ^ m₀ ≤ C * l2Norm h j σ w p ^ (k * m₀ + 1)

def SmallOne {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∃ (σ : T.Q.c.F →+* ℂ) (k m₀ : ℕ) (β : CuspAt h j (wsmul k wL)) (C : ℝ),
    GoodEmb T.Q.c σ ∧ 1 ≤ m₀ ∧ GenNeZero h j hG β ∧ Bounds h j σ w k m₀ β C

def SmallAll {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∃ (k m₀ : ℕ) (β : CuspAt h j (wsmul k wL)) (C : ℝ),
    1 ≤ m₀ ∧ GenNeZero h j hG β ∧ ∀ σ, GoodEmb T.Q.c σ → Bounds h j σ w k m₀ β C

def IsHyperbolicFrameAt (e : ℕ) (wL wF : WeightFamilies.Wt D j) : Prop :=
  ∃ (w' : WeightFamilies.Wt D j) (θ : CuspAt h j w'), wadd wF w' = wsmul e wL ∧ GenNeZero h j hG θ

include hj in
theorem IsHyperbolicFrameAt.mono (H : HasForms h j hG wL) {e e' : ℕ} (he : e ≤ e') (hA : IsHyperbolicFrameAt h j hG e wL wF) :
    IsHyperbolicFrameAt h j hG e' wL wF := by
  induction he with
  | refl => exact hA
  | step _ ih =>
    obtain ⟨w', θ, h1, h2⟩ := ih
    obtain ⟨g, hg⟩ := exists_nonZeroComp h j hj hG H
    obtain ⟨θ', h3⟩ := exists_nonZeroComp_mul (XP h j hj) ((nonZeroComp_iff_genNeZero h j hj hG H θ).2 h2) hg
    exact ⟨wadd w' wL, θ', by rw [wadd_assoc, h1, wsmul_add_one], (nonZeroComp_iff_genNeZero h j hj hG H θ').1 h3⟩

def Extra (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  (j < D.R.m → SmallAll h j hG G.w) ∧ ∃ e ≤ WeightFamilies.dimY D j + 4, IsHyperbolicFrameAt h j hG e wL wF

def CurveOn (b : Bool) : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (S : Scal (recB h.toLawsCore))
    (g₀ : (recB h.toLawsCore).Cusp j wF), (Extra h j hj hG G ↔ b = true) →
    SpanW (recPlus h j hj) G.w S → Formalism.L2.Pj.BigAt h j hj hG G → ThAt h j hj hG G g₀ →
    (recPlus h j hj).NonZeroComp wF g₀ → Nonempty (CurveModel G la g₀)

def SecondAt : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (XP h j hj) ka wL wF)
    (S : Scal (recB h.toLawsCore)), CurveModelAt h j hj hG G S

end Inst

end GlobalTheory.BignessCompare
