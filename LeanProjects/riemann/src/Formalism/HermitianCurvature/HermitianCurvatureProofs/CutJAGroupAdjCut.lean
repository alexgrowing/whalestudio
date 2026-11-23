import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.GA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def gaChi (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem isCut0_gaChi : C6.IsCut0 gaChi := by
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · show Real.smoothTransition (2 * x - 1) = 0
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · show Real.smoothTransition (2 * x - 1) = 1
    exact Real.smoothTransition.one_of_one_le (by linarith)

def GACutGraded : Prop :=
  ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (χ₀ : ℝ → ℝ), C6.IsCut0 χ₀ → ∀ (ε A Bg : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), 0 < ε → Cg * ((r : ℝ) + 1) ≤ Bg →
      B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC (A - Bg * m) m F) →
      B.CkOn ⊤ (B.GV k r) (D.cutF Bs χ₀ F ε) ∧ ∀ m : ℕ, B.InCC (A - Bg * m) m (D.cutF Bs χ₀ F ε)

def GAJComm : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cc ∧ 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg →
      IsAAOp S T v Θ → CutCoef S T v Θ d Bg →
      ∀ (η : ℝ) (F : GFn S v), 0 < η → B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        CCg S v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg F →
        (∀ g ∈ B.GV S.G.k S.G.r, F g ≠ 0 → η ≤ GfP S T v g) →
      ∀ (U : Set ℝ) (J : GFn S v), IsOpen U → J ∈ smoothFormsPositiveCone S T v →
        (∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, GfP S T v (B.gq (T v).base x) ∈ U →
          J (B.gq (T v).base x) = B.JF (T v).base F (B.gq (T v).base x)) →
        ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, GfP S T v (B.gq (T v).base x) ∈ U →
          B.opApply Θ J (B.gq (T v).base x) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base x) ∧
          B.opAdj Θ J (B.gq (T v).base x) = B.JF (T v).base (B.opAdj Θ F) (B.gq (T v).base x)

def GAPair : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ X Y F F' : GFn S v, X ∈ smoothFormsPositiveCone S T v → Y ∈ smoothFormsPositiveCone S T v →
      B.InCC (B.AB S.G.k S.G.r) 5 F → B.InCC (B.AB S.G.k S.G.r) 5 F' →
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (MA.E (D.parOf S v).r)),
        x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT →
          X (B.gq (T v).base x) = B.JF (T v).base F (B.gq (T v).base x) ∧
          (X (B.gq (T v).base x) ≠ 0 → Y (B.gq (T v).base x) = B.JF (T v).base F' (B.gq (T v).base x))) →
      MA.ipA (D.parOf S v) (trJ S T v e X) (trJ S T v e Y) = B.beta (T v).base F F'

section zero

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rw_zero_fn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ v : List (B.Mat k r), B.Rw v (0 : B.Mat k r → E) = 0
  | [] => rfl
  | X :: v => by
    show Formalism.REAL.RdV X (B.Rw v 0) = 0
    rw [rw_zero_fn v]
    funext g
    simp [Formalism.REAL.RdV]

theorem dLR_zero_fn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (B.Mat k r)) :
    ∀ u : List (B.Mat k r), B.dLR u v (0 : B.Mat k r → E) = 0
  | [] => rw_zero_fn v
  | X :: u => by
    show B.LdV X (B.dLR u v 0) = 0
    rw [dLR_zero_fn v u]
    funext g
    simp [B.LdV]

theorem opApply_zero_fn (Θ : B.DiffOp k r Wp Wq) : B.opApply Θ 0 = 0 := by
  funext g
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hx
  rw [rw_zero_fn]
  simp

theorem JF_zero_fn (Bs : B.RealPlaceData k r Wp Wq) : B.JF Bs 0 = 0 := by
  funext g
  unfold B.JF Formalism.QuantumDeterminants.besselJ
  simp

theorem ckOn_zero_fn {m : ℕ∞} {UU : Set (B.Mat k r)} : B.CkOn m UU (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
  fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

theorem inCC_zero_fn (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → (Wq →L[ℂ] Wp)) :=
  ⟨0, ckOn_zero_fn, fun u v _ _ _ g _ => by rw [dLR_zero_fn]; simp⟩

end zero

theorem jAGroupAdj_of_leaves (hCut : GACutGraded) (hComm : GAJComm) (hPair : GAPair) : JAGroupAdj := by
  obtain ⟨Cg₁, hCg₁, hC1⟩ := hCut
  obtain ⟨Cc, Cg₂, hCc, hCg₂, hC2⟩ := hComm
  refine ⟨Cc, max Cg₁ Cg₂, le_max_of_le_left hCg₁, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr Θ d Bg hd hBg hΘ hCoef ε hε J₁ J₂ hJ₁ hJ₂ hvan
    hΘJ₁ hΘJ₂
  have hr1 : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by positivity
  have hBg1 : Cg₁ * ((S.G.r : ℝ) + 1) ≤ Bg :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr1) hBg
  have hBg2 : Cg₂ * ((S.G.r : ℝ) + 1) ≤ Bg :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hr1) hBg
  have hBg0 : 0 ≤ Bg := le_trans (mul_nonneg (le_max_of_le_left hCg₁) hr1) hBg
  have hχ0 : ∀ x, x < 1 / 2 → gaChi x = 0 := fun x hx => by
    show Real.smoothTransition (2 * x - 1) = 0
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  have hχ1 : ∀ x, 1 ≤ x → gaChi x = 1 := fun x hx => by
    show Real.smoothTransition (2 * x - 1) = 1
    exact Real.smoothTransition.one_of_one_le (by linarith)

  have hrep : ∀ (J : GFn S v) (t : ℝ), 0 < t →
      LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J →
      ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧
        CCg S v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg F ∧
        (∀ g ∈ B.GV S.G.k S.G.r, F g ≠ 0 → t / 2 ≤ GfP S T v g) ∧
        (∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, t ≤ GfP S T v (B.gq (T v).base x) →
          B.JF (T v).base F (B.gq (T v).base x) = J (B.gq (T v).base x)) ∧
        (∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, J (B.gq (T v).base x) = 0 →
          B.JF (T v).base F (B.gq (T v).base x) = 0) := by
    intro J t ht hJ
    obtain ⟨F₀, hF₀s, hF₀g, hF₀e⟩ := hJ.2 (t / 2) (by positivity)
    obtain ⟨hcs, hcg⟩ := hC1 S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base gaChi isCut0_gaChi t
      (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg F₀ ht hBg1 hF₀s hF₀g
    refine ⟨D.cutF (T v).base gaChi F₀ t, hcs, hcg, ?_, ?_, ?_⟩
    · intro g _ hg
      by_contra hlt
      push Not at hlt
      unfold GfP at hlt
      have h0 : gaChi (Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g / t) = 0 :=
        hχ0 _ (by rw [div_lt_iff₀ ht]; linarith)
      apply hg
      simp [Formalism.FourierDecayAlt.D.cutF, h0]
    · intro x hx hle
      have hle' := hle
      unfold GfP at hle'
      have h1 : gaChi (Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) / t) = 1 :=
        hχ1 _ (by rw [le_div_iff₀ ht]; linarith)
      rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, h1, ← hF₀e x hx (by linarith)]
      simp
    · intro x hx h0
      rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF]
      by_cases hlt : GfP S T v (B.gq (T v).base x) < t / 2
      · unfold GfP at hlt
        have h0' : gaChi (Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base x) / t) = 0 :=
          hχ0 _ (by rw [div_lt_iff₀ ht]; linarith)
        rw [h0']
        simp
      · push Not at hlt
        rw [← hF₀e x hx hlt, h0, smul_zero]

  obtain ⟨-, -, -, -, -, -, hB3P⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))
    (T v).base (B.AB S.G.k S.G.r) le_rfl
  have hAB0 : (0 : ℝ) ≤ B.AB S.G.k S.G.r := by unfold B.AB; positivity
  obtain ⟨-, hSC⟩ := Formalism.FourierDecayAlt.P.clause_of_regularized_limit S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base
    (B.AB S.G.k S.G.r) hAB0
    (Formalism.FourierDecayAlt.P.matrix_coefficient_integrable_all S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ le_rfl)
  obtain ⟨F₁, hF₁s, hF₁g, hF₁supp, hF₁e, hF₁z⟩ := hrep J₁ ε hε hJ₁
  obtain ⟨F₂, hF₂s, hF₂g, hF₂supp, hF₂e, -⟩ := hrep J₂ (ε / 2) (by positivity) hJ₂
  have hε' : (0 : ℝ) < ε / 2 / 2 := by positivity
  have hs₁ : ∀ g ∈ B.GV S.G.k S.G.r, F₁ g ≠ 0 →
      ε / 2 / 2 ≤ Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := fun g hg h =>
    le_trans (by linarith) (hF₁supp g hg h)
  have hs₂ : ∀ g ∈ B.GV S.G.k S.G.r, F₂ g ≠ 0 →
      ε / 2 / 2 ≤ Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := fun g hg h => hF₂supp g hg h
  have hd'0 : (0 : ℝ) ≤ d + Bg * ((B.opOrder Θ : ℝ) + 5) := by positivity
  have hPoly : B.PolyCoef (T v).base (ε / 2 / 2) (d + Bg * ((B.opOrder Θ : ℝ) + 5)) (B.opOrder Θ + 5) Θ := by
    intro Tm hTm
    obtain ⟨Cb, hCb⟩ := hCoef Tm hTm (ε / 2 / 2) hε' (B.opOrder Θ + 5)
    refine ⟨Cb, fun u w hu hw hl g hg hG => ?_⟩
    have h := hCb u w hu hw hl g hg hG
    have e : d + Bg * ((B.opOrder Θ + 5 : ℕ) : ℝ) = d + Bg * ((B.opOrder Θ : ℝ) + 5) := by push_cast; ring
    rw [e] at h
    exact h
  have hcc : ∀ F : GFn S v, CCg S v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg F →
      B.InCC (B.AB S.G.k S.G.r + (d + Bg * ((B.opOrder Θ : ℝ) + 5))) (B.opOrder Θ + 5) F := by
    intro F hF
    obtain ⟨c, hc⟩ := hF (B.opOrder Θ + 5)
    refine ⟨c, Formalism.FourierDecayAlt.P.compactly_supported_monotone S.G.k S.G.r _ _ _ c _ F ?_ hc⟩
    have h0 : 0 ≤ Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 := mul_nonneg (mul_nonneg hCc hr1) (sq_nonneg _)
    have h1 : (0 : ℝ) ≤ 6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) := by positivity
    push_cast
    linarith
  have hβ := hB3P Θ (ε / 2 / 2) (d + Bg * ((B.opOrder Θ : ℝ) + 5)) hε' hd'0 hΘ.1 hΘ.2 hPoly F₁ F₂
    (hcc F₁ hF₁g) (hcc F₂ hF₂g) hs₁ hs₂
  obtain ⟨-, -, hF₁5, hF₂5, hΘF₁5, hΘF₂5, -⟩ := hSC Θ (ε / 2 / 2) (d + Bg * ((B.opOrder Θ : ℝ) + 5)) hε' hd'0
    hΘ.1 hPoly F₁ F₂ (hcc F₁ hF₁g) (hcc F₂ hF₂g) hs₁ hs₂

  have hJF₁ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      J₁ (B.gq (T v).base x) = B.JF (T v).base F₁ (B.gq (T v).base x) := by
    intro x hx
    by_cases hG : GfP S T v (B.gq (T v).base x) < ε
    · rw [hvan x hx hG, hF₁z x hx (hvan x hx hG)]
    · push Not at hG
      exact (hF₁e x hx hG).symm

  have hAJ := hC2 E Wp Wq S T f χ ν' m₀ top A₀ hB v Θ d Bg hd hBg2 hΘ hCoef
  have hi := hAJ (ε / 2) F₁ (by positivity) hF₁s hF₁g hF₁supp Set.univ J₁ isOpen_univ hJ₁.1
    (fun x hx _ => hJF₁ x hx)
  have hii := hAJ 1 0 one_pos ckOn_zero_fn (fun m => inCC_zero_fn _ m) (fun g _ h => absurd rfl h)
    (Set.Iio ε) J₁ isOpen_Iio hJ₁.1 (fun x hx hG => by rw [JF_zero_fn]; exact hvan x hx hG)
  have hiii := hAJ (ε / 2 / 2) F₂ hε' hF₂s hF₂g hF₂supp (Set.Ioi (ε / 2)) J₂ isOpen_Ioi hJ₂.1
    (fun x hx hG => (hF₂e x hx (le_of_lt hG)).symm)

  have hL := hPair Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr (B.opApply Θ J₁) J₂ (B.opApply Θ F₁) F₂
    hΘJ₁ hJ₂.1 hΘF₁5 hF₂5 (by
      refine Filter.Eventually.of_forall fun x hx => ⟨(hi x hx (Set.mem_univ _)).1, fun hne => ?_⟩
      by_cases hG : GfP S T v (B.gq (T v).base x) < ε
      · exact absurd (by simpa [opApply_zero_fn, JF_zero_fn] using (hii x hx hG).1) hne
      · push Not at hG
        exact (hF₂e x hx (by linarith)).symm)
  have hR := hPair Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr J₁ (B.opAdj Θ J₂) F₁ (B.opAdj Θ F₂)
    hJ₁.1 hΘJ₂ hF₁5 hΘF₂5 (by
      refine Filter.Eventually.of_forall fun x hx => ⟨hJF₁ x hx, fun hne => ?_⟩
      by_cases hG : GfP S T v (B.gq (T v).base x) < ε
      · exact absurd (hvan x hx hG) hne
      · push Not at hG
        exact (hiii x hx (show GfP S T v (B.gq (T v).base x) ∈ Set.Ioi (ε / 2) by
          simp only [Set.mem_Ioi]; linarith)).2)
  rw [hL, hR]
  exact hβ

end

end Formalism.FourierDecayAlt.P.CutMP.JA.GA
