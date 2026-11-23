import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ThGe ell errE)

noncomputable section

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

theorem locPot_add_φ (P Q : LocPot X) (x y : X) : (P + Q).φ x y = P.φ x y + Q.φ x y := rfl

theorem locPot_add_U (P Q : LocPot X) (x : X) : (P + Q).U x = P.U x ∩ Q.U x := rfl

def FormNonneg (A : FinHolAtlas D X) (V : Set X) (P : LocPot X) : Prop :=
  ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (V ∩ P.U x), ∀ w : Fin D → ℂ,
    0 ≤ levi (P.φ x ∘ (A.chart k).symm) y w

def LeviLe (A : FinHolAtlas D X) (V : Set X) (a : ℝ) (P : LocPot X) (b : ℝ) (Q : LocPot X) :
    Prop :=
  ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (V ∩ P.U x ∩ Q.U x), ∀ w : Fin D → ℂ,
    a * levi (P.φ x ∘ (A.chart k).symm) y w ≤ b * levi (Q.φ x ∘ (A.chart k).symm) y w

structure KaehlerForm (A : FinHolAtlas D X) where

  pot : LocPot X
  isPot : IsPotential A pot
  pos : IsPosPot A pot

def KaehlerForm.vol {A : FinHolAtlas D X} (Om : KaehlerForm A) : ℝ :=
  mInt A (fun _ => Om.pot) fun _ => 1

def potForm (th : LocPot X) (u : X → ℝ) : LocPot X := th + LocPot.ofFun u

structure IsBoundedPotForm (A : FinHolAtlas D X) (Yo : Set X) (r : X → ℝ) (Om : KaehlerForm A)
    (C₁ : ℝ) (th : LocPot X) (u : X → ℝ) : Prop where
  th_pot : IsPotential A th
  th_le : LeviLe A Set.univ 1 th 1 Om.pot
  neg_le_th : LeviLe A Set.univ (-1) Om.pot 1 th
  u_smooth : A.SmoothOn Yo u
  u_nonpos : ∀ x ∈ Yo, u x ≤ 0
  le_u : ∀ x ∈ Yo, -(C₁ * Real.log (r x)) ≤ u x
  nonneg : FormNonneg A Yo (potForm th u)
  smooth_or_pole : A.Smooth u ∨ ∀ y, y ∉ Yo → Tendsto u (𝓝[Yo] y) atBot

def IsSmoothPotForm (A : FinHolAtlas D X) (Yo : Set X) (r : X → ℝ) (Om : KaehlerForm A) (C₁ : ℝ)
    (th : LocPot X) (u : X → ℝ) : Prop :=
  IsBoundedPotForm A Yo r Om C₁ th u ∧ A.Smooth u

def IsBoundedNonnegForm (A : FinHolAtlas D X) (a om : LocPot X) (C : ℝ) : Prop :=
  IsPotential A a ∧ FormNonneg A Set.univ a ∧ LeviLe A Set.univ 1 a C om

def tail (Yo : Set X) (r : X → ℝ) (R₀ : ℝ) : Set X := {x | x ∈ Yo ∧ R₀ ≤ r x}

def MassBound (A : FinHolAtlas D X) (Yo : Set X) (T Θ : Fin D → LocPot X) (V : ℝ) : Prop :=
  MIntegrable A T (Yo.indicator 1) ∧ mInt A T (Yo.indicator 1) = mInt A Θ (fun _ => 1) ∧
    mInt A Θ (fun _ => 1) ≤ V

def TailMassBound (A : FinHolAtlas D X) (Yo : Set X) (r : X → ℝ) (T : Fin D → LocPot X)
    (CE : ℝ) : Prop :=
  ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ → MIntegrable A T ((tail Yo r R₀).indicator 1) ∧
    mInt A T ((tail Yo r R₀).indicator 1) ≤ CE * Real.log R₀ ^ D / R₀

def TailLogBound (A : FinHolAtlas D X) (Yo : Set X) (r : X → ℝ) (T : Fin D → LocPot X)
    (CE : ℝ) : Prop :=
  ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
    MIntegrable A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) ∧
    mInt A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) ≤
      CE * Real.log R₀ ^ (D + 1) / R₀

structure System {A : FinHolAtlas D X} (R : RegChartData A) where

  ph : ℝ → X → ℝ

  C : ℝ

  ell₀ : ℝ
  smooth : ∀ t, 0 < t → ell₀ ≤ ell t → A.Smooth (ph t)
  le_ph : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ R.Yo, R.φ x ≤ ph t x
  ph_le : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x, ph t x ≤ C
  le_log : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x, -(C * Real.log (ell t)) ≤ ph t x
  thGe : ∀ t, 0 < t → ell₀ ≤ ell t → ThGe A R.θ (ph t) R.om (-errE C t)
  near : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ R.Yo, R.r x ≤ ell t →
    ph t x ≤ R.φ x + t ^ (1 / 3 : ℝ) + errE C t
  far : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ R.Yo,
    ph t x ≤ R.φ x + t ^ (1 / 3 : ℝ) + errE C t * R.r x
  mono : ∀ t t₀, 0 < t → t ≤ t₀ → ell₀ ≤ ell t₀ → ∀ x, ph t x ≤ ph t₀ x + C * errE C t₀
  c2 : ∀ (k : Fin A.n) (K : Set (Fin D → ℂ)), IsCompact K →
    K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' R.Yo →
    TendstoUniformlyOn (fun t y => ph t ((A.chart k).symm y)) (fun y => R.φ ((A.chart k).symm y))
        (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => ph t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fun y' => R.φ ((A.chart k).symm y')) y) (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ fun y' => ph t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => R.φ ((A.chart k).symm y')) y) (𝓝[>] 0) K

def thetaOmega {A : FinHolAtlas D X} (R : RegChartData A) : LocPot X := R.θ + R.om

namespace System

variable {A : FinHolAtlas D X} {R : RegChartData A} (S : System R)

def uT (t : ℝ) : X → ℝ := fun x => S.ph t x - S.C

def curr (t : ℝ) : LocPot X := potForm (thetaOmega R) (S.uT t)

end System

def lincomb : (m : ℕ) → (Fin m → ℝ) → (Fin m → LocPot X) → LocPot X
  | 0, _, _ => LocPot.ofFun fun _ => 0
  | m + 1, c, P => LocPot.rsmul (c 0) (P 0) + lincomb m (fun i => c i.succ) fun i => P i.succ

theorem lincomb_φ (m : ℕ) (c : Fin m → ℝ) (P : Fin m → LocPot X) (x y : X) :
    (lincomb m c P).φ x y = ∑ i, c i * (P i).φ x y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Fin.sum_univ_succ, ← ih]
    rfl

structure Family (A : FinHolAtlas D X) where

  m : ℕ

  R : Fin m → RegChartData A

  sys : ∀ i, System (R i)
  Yo : Set X
  r : X → ℝ
  om : LocPot X
  Yo_eq : ∀ i, (R i).Yo = Yo
  r_eq : ∀ i, ∀ x ∈ Yo, (R i).r x = r x
  om_eq : ∀ i, (R i).om = om

def Family.chernForm {A : FinHolAtlas D X} (F : Family A) (c : Fin F.m → ℝ) (t : ℝ) : LocPot X :=
  lincomb F.m c fun i => (F.R i).θ + LocPot.ofFun ((F.sys i).ph t)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData projLine_fubiniStudy_isPosPot)

theorem tendstoUniformlyOn_self {α β ι : Type*} [UniformSpace β] (f : α → β) (p : Filter ι)
    (s : Set α) : TendstoUniformlyOn (fun _ => f) f p s :=
  fun _ hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu

theorem errE_zero (t : ℝ) : errE 0 t = 0 := by simp [errE]

theorem levi_const {ι : Type*} [Fintype ι] (c : ℝ) (z w : ι → ℂ) :
    levi (fun _ : ι → ℂ => c) z w = 0 := by
  simp [levi]

def projectiveLineKaehler : KaehlerForm p1 := ⟨fsPot, projLine_isSmoothPotential, projLine_fubiniStudy_isPosPot⟩

def projectiveLineConstantSystem : System projLineChartData where
  ph _ _ := 0
  C := 0
  ell₀ := 1
  smooth _ _ _ _ := contDiffOn_const
  le_ph _ _ _ _ _ := le_rfl
  ph_le _ _ _ _ := le_rfl
  le_log _ _ _ _ := by simp
  thGe t _ _ := by
    intro x k y _ w
    have h : ((fun z => projLineChartData.θ.φ x z + (fun _ : OnePoint ℂ => (0 : ℝ)) z) ∘ (p1.chart k).symm) =
        fun _ => (0 : ℝ) := by
      funext z
      show (0 : ℝ) + 0 = 0
      simp
    rw [h, levi_const, errE_zero]
    simp
  near t ht _ _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  far t ht _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t * _
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  mono _ _ _ _ _ _ := by simp
  c2 _ _ _ _ := ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _,
    tendstoUniformlyOn_self _ _ _⟩

theorem projectiveLine_constantSystem_uT (t : ℝ) : projectiveLineConstantSystem.uT t = fun _ => 0 :=
  funext fun _ => sub_self (0 : ℝ)

theorem thetaOmega_p1Data_φ (x : OnePoint ℂ) : (thetaOmega projLineChartData).φ x = fsPot.φ x :=
  funext fun z => by
    show (0 : ℝ) + fsPot.φ x z = fsPot.φ x z
    simp

theorem thetaOmega_p1Data_pot : IsPotential p1 (thetaOmega projLineChartData) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd p1 _ _
    (ReciprocityTheory.AnForm.M.isPotential_ofFun p1 0 fun _ => contDiffOn_const) projLine_isSmoothPotential

theorem projectiveLine_current_smoothPotForm (t : ℝ) :
    IsSmoothPotForm p1 projLineChartData.Yo projLineChartData.r projectiveLineKaehler 0 (thetaOmega projLineChartData) (projectiveLineConstantSystem.uT t) := by
  rw [projectiveLine_constantSystem_uT]
  refine ⟨⟨thetaOmega_p1Data_pot, ?_, ?_, fun _ => contDiffOn_const, fun _ _ => le_rfl,
    fun _ _ => by simp, ?_, Or.inl fun _ => contDiffOn_const⟩, fun _ => contDiffOn_const⟩
  · intro x k y _ w
    rw [thetaOmega_p1Data_φ]
    exact le_rfl
  · intro x k y hy w
    rw [thetaOmega_p1Data_φ]
    have := projLine_isPlurisubharmonic x k y ⟨hy.1, hy.2.1.2⟩ w
    show -1 * levi (fsPot.φ x ∘ (p1.chart k).symm) y w ≤
      1 * levi (fsPot.φ x ∘ (p1.chart k).symm) y w
    linarith
  · intro x k y hy w
    have h : (potForm (thetaOmega projLineChartData) fun _ => (0 : ℝ)).φ x = fsPot.φ x := by
      funext z
      show (thetaOmega projLineChartData).φ x z + 0 = fsPot.φ x z
      rw [thetaOmega_p1Data_φ, add_zero]
    rw [h]
    exact projLine_isPlurisubharmonic x k y ⟨hy.1, hy.2.2.1.2⟩ w

theorem projectiveLine_boundedNonnegForm : IsBoundedNonnegForm p1 fsPot fsPot 1 :=
  ⟨projLine_isSmoothPotential, fun x k y hy w => projLine_isPlurisubharmonic x k y ⟨hy.1, hy.2.2⟩ w,
    fun _ _ _ _ _ => le_rfl⟩

def projectiveLineFamily : Family p1 where
  m := 1
  R _ := projLineChartData
  sys _ := projectiveLineConstantSystem
  Yo := projLineChartData.Yo
  r := projLineChartData.r
  om := fsPot
  Yo_eq _ := rfl
  r_eq _ _ _ := rfl
  om_eq _ := rfl

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
