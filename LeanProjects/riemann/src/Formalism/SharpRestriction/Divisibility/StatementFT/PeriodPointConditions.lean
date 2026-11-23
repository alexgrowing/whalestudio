import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.HermitianForms.BothSym

noncomputable section

namespace Formalism.MainNotions.RT.PeriodPointConditions

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions

attribute [local instance] MemberForms.clsPFin

def resC {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (z : (D.mem u).P.Wrow) :
    (D.mem u).P.Wrow :=
  open Classical in T.valP.eW.symm (fun c' => if c' = c then T.valP.eW z c' else 0)

def pcL {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (c : (D.fm u).clsP) (z : (D.mem u).P.Wrow)
    (F : (D.mem u).P.Mt) : ℂ :=
  ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℂ) * (D.fm u).ipP (resC T c (T.jM F)) (resC T c z)

def PerDec0At {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
    ∀ x ∈ (D.fm u).ptLat.L, ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, ∀ c,
      ∃ y : D.what₂.LL, D.what₂.embLL y = pcL T c ((D.fm u).ptEmb x) ((D.eMt u).symm F) ∧
        ∀ w : D.what₂.places.Pl, y = 0 ∨ 0 ≤ vAdd (D.plEq w) y

def PerDec0 (D : D7) (u : D.what₂.Word) : Prop :=
  ∃ (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf), PerDec0At T

theorem perDec0_of_cols {D : D7} (C : Formalism.L2.Forms.ColsTiedSym D) (h : ∀ u, PerDec0At (C.forms u)) (u : D.what₂.Word) :
    PerDec0 D u := ⟨_, _, C.forms u, h u⟩

def PerDecTw (D : D7) (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ pc : (T.fm u μ).clsP → (D.PTw u μ).Wrow → (D.PTw u μ).Mt → ℂ,
    (∀ z F, (D.PTw u μ).period z F = ∑ c, ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : ℂ)⁻¹ * pc c z F) ∧
    ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, ∀ c,
      ∃ y : D.what₂.LL, D.what₂.embLL y = pc c ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
        ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ → y = 0 ∨ 0 ≤ vAdd (D.plEq w) y

def PeriodTwistCompatibility (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  (∀ u, PerDec0 D u) ∧ ∀ u μ, μ ≠ D.what₂.mu0 → PerDecTw D Dx T u μ

theorem perTw_rat {D : D7} {Dx : DivX D} {T : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (h : PerDecTw D Dx T u μ) :
    ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier,
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) := by
  intro x hx F hF
  obtain ⟨pc, hper, hint⟩ := h
  choose y hy _ using hint x hx F hF
  refine ⟨∑ c, ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c, ?_⟩
  rw [hper]
  simp only [map_sum, map_mul, map_inv₀, map_natCast, hy]

def aPairAt (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  WeightDegreeSizes.MemberChainIntegral D ∧ WeightDegreeSizes.TwistedChainIntegral D T ∧ WeightDegreeSizes.PeriodClassSumWeyl D ∧ WeightDegreeSizes.TwistedPeriodIntegral D Dx T

def PointPeriodConditional (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  WeightDegreeSizes.MemberChainIntegral D ∧ WeightDegreeSizes.TwistedChainIntegral D T ∧ (PeriodTwistCompatibility D Dx T → WeightDegreeSizes.PeriodClassSumWeyl D ∧ WeightDegreeSizes.TwistedPeriodIntegral D Dx T)

theorem point_period_of_conditional {D : D7} {Dx : DivX D} {T : TwForms D} (h : PointPeriodConditional D Dx T) (t : PeriodTwistCompatibility D Dx T) :
    aPairAt D Dx T := ⟨h.1, h.2.1, (h.2.2 t).1, (h.2.2 t).2⟩

theorem conditional_of_point_period {D : D7} {Dx : DivX D} {T : TwForms D} (h : aPairAt D Dx T) : PointPeriodConditional D Dx T :=
  ⟨h.1, h.2.1, fun _ => h.2.2⟩

section Fam

variable {eps : ℝ} (Fm : FamP eps)

def TieF : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, PeriodTwistCompatibility (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

def PointPeriodConditionalFamily : Prop :=
  DIV.Ev Fm fun x hx i => PointPeriodConditional (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

theorem point_period_eventually_of_conditional (h : PointPeriodConditionalFamily Fm) (t : TieF Fm) :
    DIV.Ev Fm fun x hx i => WeightDegreeSizes.MemberChainIntegral (Fm.D x i) ∧ WeightDegreeSizes.TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw ∧
      WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i) ∧ WeightDegreeSizes.TwistedPeriodIntegral (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw := by
  obtain ⟨x0, hx0⟩ := h
  obtain ⟨x1, hx1⟩ := t
  refine ⟨max x0 x1, fun x hle hx i => ?_⟩
  exact point_period_of_conditional (hx0 x (le_trans (le_max_left _ _) hle) hx i) (hx1 x hx (le_trans (le_max_right _ _) hle) i)

def PeriodPointCompatibilityFamily : Prop :=
  TieF Fm ∧ DIV.Ev Fm fun x hx i => WeightDegreeSizes.MemberChainIntegral (Fm.D x i) ∧ WeightDegreeSizes.TwistedChainIntegral (Fm.D x i) (Fm.ex x hx i).tw

def LiftErrorFamilyInClassOfChainIntegrality (𝒪 : LiftErrorLocal.ObjClass) (H : WeightAlgebra.KHyp) (C2h A2 CR CRd C1 C2 C3 CA CD : ℝ) (_CH : ℝ) : Prop :=
  ∀ XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch,
    (∀ x hx i, 𝒪 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)) → PeriodPointCompatibilityFamily Fm →
    LiftErrorLocal.AdmF Fm XF H C2h A2 CR CRd → LiftErrorLocal.OrbitValuationBound Fm XF CRd C1 C2 C3 CA CD

theorem statement_family_of_conditional_form {𝒪 : LiftErrorLocal.ObjClass} {H : WeightAlgebra.KHyp} {C2h A2 CR CRd C1 C2 C3 CA CD CH : ℝ}
    (h : LiftErrorFamilyInClassOfChainIntegrality Fm 𝒪 H C2h A2 CR CRd C1 C2 C3 CA CD CH) (t : PeriodPointCompatibilityFamily Fm) :
    LiftErrorLocal.KudlaFamilyStatement 𝒪 H C2h A2 CR CRd C1 C2 C3 CA CD Fm CH :=
  fun XF hO hA => h XF hO t hA

theorem stmtFT1_of_stmtF {𝒪 : LiftErrorLocal.ObjClass} {H : WeightAlgebra.KHyp} {C2h A2 CR CRd C1 C2 C3 CA CD CH : ℝ}
    (h : LiftErrorLocal.KudlaFamilyStatement 𝒪 H C2h A2 CR CRd C1 C2 C3 CA CD Fm CH) : LiftErrorFamilyInClassOfChainIntegrality Fm 𝒪 H C2h A2 CR CRd C1 C2 C3 CA CD CH :=
  fun XF hO _ hA => h XF hO hA

end Fam

end Formalism.MainNotions.RT.PeriodPointConditions
