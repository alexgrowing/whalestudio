import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWaveMain

noncomputable section

namespace GlobalTheory.FormsFromXi

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

variable (hXi : B.XiExists)
include hXi

section beta

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.JCx4
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem beta_sesq (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {F F' G : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : InCC A 5 F) (hF' : InCC A 5 F') (hG : InCC A 5 G) (c : ℂ) :
    beta D (F + c • F') G = beta D F G + c * beta D F' G ∧
      beta D G (F + c • F') = beta D G F + conj c * beta D G F' := by
  obtain ⟨c0, -, -, -, hβ, -⟩ := BXiAsm.any_of hXi k r Wp Wq D A hA
  obtain ⟨Ξ, hCB, hXi⟩ := hXi k r Wp Wq D A hA
  have hS := (Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear k r Wp Wq D Ξ A hA hCB hXi).2.2 (1, 1)
    ⟨by norm_num, by norm_num⟩
  have h4 : ∀ {H : Mat k r → (Wq →L[ℂ] Wp)}, InCC A 5 H → InCC A 4 H :=
    fun h => sq_inCC_mono le_rfl (by norm_num) h
  have hcF' : InCC A 5 (c • F') := sq_inCC_smul c hF'
  have hsum : InCC A 5 (F + c • F') := sq_inCC_add hF hcF'
  rw [hβ _ _ hsum hG, hβ _ _ hF hG, hβ _ _ hF' hG, hβ _ _ hG hsum, hβ _ _ hG hF, hβ _ _ hG hF']
  unfold betaInf
  rw [hS.1 _ _ _ (h4 hF) (h4 hcF') (h4 hG), hS.2.2.1 c _ _ (h4 hF') (h4 hG),
    hS.2.1 _ _ _ (h4 hG) (h4 hF) (h4 hcF'), hS.2.2.2 c _ _ (h4 hG) (h4 hF')]
  constructor <;> ring

theorem integrable_weight_normSq (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    Integrable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) := by
  obtain ⟨-, -, -, ⟨C, hB1⟩, -⟩ := BXiAsm.any_of hXi k r Wp Wq D (B.AB k r) le_rfl
  obtain ⟨c4, hc4⟩ := hF (B.AB k r) 4
  have hfin := (hB1 F F c4 c4 (hF _ 5) (hF _ 5) hc4 hc4).1
  have hmeas : AEStronglyMeasurable
      (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) volume :=
    rb_aesm D _ ((rb_contOn_bcW D).mul ((rb_contOn_J D F hF).norm.pow 2)) fun q h => by simp [h]
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q =>
    mul_nonneg (rb_bcWeight_nonneg _ _ q) (sq_nonneg _))]
  exact lt_of_le_of_ne le_top hfin

theorem integrable_weight_pair (D : B.RealPlaceData k r Wp Wq) (F F' : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) (hF' : ∀ (A : ℝ) (m : ℕ), B.InCC A m F') :
    Integrable (fun q => (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))) := by
  have hmeas : AEStronglyMeasurable (fun q => (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))) volume := by
    refine rb_aesm D _ ?_ fun q h => by simp [h]
    exact (Complex.continuous_ofReal.comp_continuousOn (rb_contOn_bcW D)).mul
      ((rb_contOn_J D F' hF').inner (rb_contOn_J D F hF))
  refine Integrable.mono' (((integrable_weight_normSq hXi D F hF).add (integrable_weight_normSq hXi D F' hF')).div_const 2) hmeas ?_
  refine Filter.Eventually.of_forall fun q => ?_
  set b := bcWeight k r (Tz k r D.z) (Tz k r D.z') q
  set u := ‖B.hsVec (B.JF D F (B.gq D q))‖
  set v := ‖B.hsVec (B.JF D F' (B.gq D q))‖
  have hb : 0 ≤ b := rb_bcWeight_nonneg _ _ q
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb]
  have h1 : ‖inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))‖ ≤ v * u :=
    norm_inner_le_norm _ _
  have h2 : v * u ≤ (u ^ 2 + v ^ 2) / 2 := by nlinarith [sq_nonneg (u - v)]
  calc b * ‖inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))‖ ≤ b * ((u ^ 2 + v ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hb
    _ = (b * u ^ 2 + b * v ^ 2) / 2 := by ring

theorem form_eq_sum_beta (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r)) (C1 : ℝ)
    (hpair : ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Q.RadSp k r D.z D.z' D.π D.π'),
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F) y.1 y.2) →
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F') y.1 y.2) →
      ∀ c ∈ OmX r, P5.pairAt μ Φ Φ' c = (C1 : ℂ) * ∫ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) *
        (((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ)))))
    {n : ℕ} (x x' : Wd.Ix (Fin n) → B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Wd.Ix (Fin n) → Q.RadSp k r D.z D.z' D.π D.π')
    (hx : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x a)) (hx' : ∀ a, ∀ (A : ℝ) (m : ℕ), B.InCC A m (x' a))
    (hΦ : ∀ a, ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ a : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D (x a)) y.1 y.2)
    (hΦ' : ∀ a, ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ' a : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D (x' a)) y.1 y.2) :
    P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta D (x a) (x' a) := by
  rw [rb_form_eq]
  let f : Wd.Ix (Fin n) → (Fin r → ℂ) × ℂ → ℂ := fun a q =>
    (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D (x' a) (B.gq D q))) (B.hsVec (B.JF D (x a) (B.gq D q)))
  have hint : ∀ a, Integrable (f a) := fun a => integrable_weight_pair hXi D (x a) (x' a) (hx a) (hx' a)
  have hae : (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, P5.pairAt μ (Φ b) (Φ' b) c)
      =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
    filter_upwards [rb_ae_OmX] with c hc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    dsimp only
    rw [rb_weight hc]
    rfl
  rw [integral_congr_ae hae, integral_finsetSum _ (fun b _ => ((hint b).integral_prod_left).const_mul _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, ← integral_prod _ (hint b)]
  rfl

end

theorem formLev_sesq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) (hmm : P5.mmUser P0 w.length ≤ mm)
    (x x' y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : ∀ a, InCC A mm (x a)) (hx' : ∀ a, InCC A mm (x' a)) (hy : ∀ a, InCC A mm (y a)) :
    D.formLev T s j w (x + c • x') y = D.formLev T s j w x y + c * D.formLev T s j w x' y ∧
      D.formLev T s j w y (x + c • x') = D.formLev T s j w y x + starRingEnd ℂ c * D.formLev T s j w y x' := by
  have hS := ma_hS P0 T s j w

  have hAB : AB P0.k (P0.r - ↑j) ≤ A - 2 * (w.length : ℝ) := by
    have h1 := pd_thr_AB P0 j w.length A hA
    linarith
  have hm5 : 5 + (2 * (P0.r - ↑j) + P0.k + 1) * w.length ≤ mm := pd_thr_mm P0 j w.length mm hmm
  have hN0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _

  have hin : ∀ {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}, InCC A mm F →
      InCC (A - 2 * (w.length : ℝ) + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - ↑j) + P0.k + 1) * w.length) F :=
    fun h => sq_inCC_mono (by push_cast; linarith) hm5 h

  have hvec : ∀ v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, InCC A mm (v a)) → ∀ a,
        InCC (A - 2 * (w.length : ℝ)) 5 (D.actOp (D.RRlev T s j w) v a) := by
    intro v hv a
    rw [ma_actOp_eq]
    exact sq_inCC_sum Finset.univ (fun b => (D.RRlev T s j w a b) (v b)) (fun b _ => ma_inCC (hS a b) (hin (hv b)))
  have hlow : ∀ {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}, InCC A mm F →
      InCC (A - 2 * (w.length : ℝ)) 5 F := fun h =>
    sq_inCC_mono (by linarith) (by omega) h
  refine ⟨?_, ?_⟩
  · show ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) (x + c • x') a) (y a) =
      ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) x a) (y a) +
        c * ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) x' a) (y a)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hGV : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T s j w) (x + c • x') a g =
        (D.actOp (D.RRlev T s j w) x a + c • D.actOp (D.RRlev T s j w) x' a) g := by
      intro g hg
      show (∑ b, D.ap (D.RRlev T s j w a b) ((x + c • x') b)) g =
        (∑ b, D.ap (D.RRlev T s j w a b) (x b) + c • ∑ b, D.ap (D.RRlev T s j w a b) (x' b)) g
      rw [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply, Finset.smul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact (hS a b).2.1 _ _ (x b) (x' b) c (hin (hx b)) (hin (hx' b)) g hg
    rw [sq_beta_congr (T.bs j) hGV]
    exact (beta_sesq hXi (T.bs j) hAB (hvec x hx a) (hvec x' hx' a) (hlow (hy a)) c).1
  · show ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) ((x + c • x') a) =
      ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) (x a) +
        conj c * ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) (x' a)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (beta_sesq hXi (T.bs j) hAB (hlow (hx a)) (hlow (hx' a)) (hvec y hy a) c).2

end beta

section one

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.PBF
open scoped ENNReal NNReal Matrix

theorem form_const_one : Formalism.FourierDecayAlt.P.PBO.FormOne := by
  intro Wp Wq _ _ _ _ _ _ P0 T j X μ L st l0 hD hZ w F F' Φ Φ' ε hε hF hF' hΦ hΦ'
  have hN := Formalism.FourierDecayAlt.P.module_regularity Wp Wq P0 T (M.sgn P0 l0) j w F ε hε hF
  have hPic : ∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (P5.act (P5.RRi L st 0 (D.positionted w)) Φ a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _)
          (B.JF (T.bs j) (D.actOp (D.RRlev T (M.sgn P0 l0) j w) F a)) y.1 y.2 := by
    intro a y hy
    rw [Formalism.FourierDecayAlt.P.radial_module_action Wp Wq P0 T j X μ L st l0 hD w (fun b => B.JF (T.bs j) (F b)) Φ
      (fun b => Formalism.FourierDecayAlt.P.bessel_function_finite_class _ _ Wp Wq (T.bs j) (F b) ε hε (hF b)) hΦ a y hy]
    exact (Formalism.FourierDecayAlt.P.bessel_module Wp Wq P0 T (M.sgn P0 l0) j w F ε hε hF a y hy).symm
  have h := form_eq_sum_beta hXi (T.bs j) μ 1
    (fun G G' Ψ Ψ' hΨ hΨ' c hc => pairAt_one (T.bs j) μ hZ G G' Ψ Ψ' hΨ hΨ' c hc)
    (D.actOp (D.RRlev T (M.sgn P0 l0) j w) F) F' (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ'
    (fun a => (hN a).2.1) (fun a => (hF' a).2.1) hPic hΦ'
  refine Eq.trans ?_ h.symm
  simp only [Complex.ofReal_one, one_mul]
  rfl

end one

theorem radHead : KB.RadHead :=
  pb_radHead_of (form_const_one hXi) exists_zeta_normalized_haar
    (PBP.headPic_of (head_jacquet_of_letter_and_head head_letter_identity head_germ_smooth_extension))

section wave

open Matrix Finset Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBG
open scoped ComplexConjugate

section pairing

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)

theorem formLev_add_smul_left (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : DecV x₁) (h₂ : DecV x₂) (hy : DecV y) :
    D.formLev T s j w (x₁ + c • x₂) y = D.formLev T s j w x₁ y + c * D.formLev T s j w x₂ y :=
  (formLev_sesq hXi P0 T s j w _ _ le_rfl le_rfl x₁ x₂ y c (fun a => h₁ a _ _)
    (fun a => h₂ a _ _) (fun a => hy a _ _)).1

theorem formLev_add_smul_right (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : DecV x) (h₁ : DecV y₁) (h₂ : DecV y₂) :
    D.formLev T s j w x (y₁ + c • y₂) = D.formLev T s j w x y₁ + conj c * D.formLev T s j w x y₂ :=
  (formLev_sesq hXi P0 T s j w _ _ le_rfl le_rfl y₁ y₂ x c (fun a => h₁ a _ _)
    (fun a => h₂ a _ _) (fun a => hx a _ _)).2

theorem pairing_add_smul_left : ∀ (ys : List ℝ) (x₁ x₂ : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ),
    DecV x₁ → DecV x₂ → DecV y →
    KB.pairJ (D.formLev T s j w) ys (x₁ + c • x₂) y =
      KB.pairJ (D.formLev T s j w) ys x₁ y + c * KB.pairJ (D.formLev T s j w) ys x₂ y
  | [], x₁, x₂, y, c, h₁, h₂, hy => formLev_add_smul_left hXi P0 T s j w x₁ x₂ y c h₁ h₂ hy
  | _ :: ys, x₁, x₂, y, c, h₁, h₂, hy => by
    simp only [KB.pairJ]
    have e1 := pairing_add_smul_left ys (fun e => x₁ (Fin.cons 1 e)) (fun e => x₂ (Fin.cons 1 e)) (fun e => y (Fin.cons 0 e))
      c (decV_restrict h₁ 1) (decV_restrict h₂ 1) (decV_restrict hy 0)
    have e0 := pairing_add_smul_left ys (fun e => x₁ (Fin.cons 0 e)) (fun e => x₂ (Fin.cons 0 e)) (fun e => y (Fin.cons 1 e))
      c (decV_restrict h₁ 0) (decV_restrict h₂ 0) (decV_restrict hy 1)
    have r1 : (fun e => (x₁ + c • x₂) (Fin.cons 1 e)) = (fun e => x₁ (Fin.cons 1 e)) + c • (fun e => x₂ (Fin.cons 1 e)) := rfl
    have r0 : (fun e => (x₁ + c • x₂) (Fin.cons 0 e)) = (fun e => x₁ (Fin.cons 0 e)) + c • (fun e => x₂ (Fin.cons 0 e)) := rfl
    rw [r1, r0, e1, e0]
    ring

theorem pairing_add_smul_right : ∀ (ys : List ℝ) (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (y₁ y₂ : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ),
    DecV x → DecV y₁ → DecV y₂ →
    KB.pairJ (D.formLev T s j w) ys x (y₁ + c • y₂) =
      KB.pairJ (D.formLev T s j w) ys x y₁ + conj c * KB.pairJ (D.formLev T s j w) ys x y₂
  | [], x, y₁, y₂, c, hx, h₁, h₂ => formLev_add_smul_right hXi P0 T s j w x y₁ y₂ c hx h₁ h₂
  | _ :: ys, x, y₁, y₂, c, hx, h₁, h₂ => by
    simp only [KB.pairJ]
    have e1 := pairing_add_smul_right ys (fun e => x (Fin.cons 1 e)) (fun e => y₁ (Fin.cons 0 e)) (fun e => y₂ (Fin.cons 0 e))
      c (decV_restrict hx 1) (decV_restrict h₁ 0) (decV_restrict h₂ 0)
    have e0 := pairing_add_smul_right ys (fun e => x (Fin.cons 0 e)) (fun e => y₁ (Fin.cons 1 e)) (fun e => y₂ (Fin.cons 1 e))
      c (decV_restrict hx 0) (decV_restrict h₁ 1) (decV_restrict h₂ 1)
    have r0 : (fun e => (y₁ + c • y₂) (Fin.cons 0 e)) = (fun e => y₁ (Fin.cons 0 e)) + c • (fun e => y₂ (Fin.cons 0 e)) := rfl
    have r1 : (fun e => (y₁ + c • y₂) (Fin.cons 1 e)) = (fun e => y₁ (Fin.cons 1 e)) + c • (fun e => y₂ (Fin.cons 1 e)) := rfl
    rw [r1, r0, e1, e0]
    ring

theorem pairing_sum_sum (ys : List ℝ) {ι ι' : Type} (S : Finset ι) (S' : Finset ι') (a : ι → ℂ) (b : ι' → ℂ)
    (v : ι → Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (u : ι' → Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (hv : ∀ i, DecV (v i)) (hu : ∀ i, DecV (u i)) :
    KB.pairJ (D.formLev T s j w) ys (∑ i ∈ S, a i • v i) (∑ i ∈ S', b i • u i) =
      ∑ i ∈ S, ∑ i' ∈ S', a i * conj (b i') * KB.pairJ (D.formLev T s j w) ys (v i) (u i') := by
  have hU : DecV (∑ i ∈ S', b i • u i) := by
    classical
    induction S' using Finset.induction_on with
    | empty => simpa using (decV_zero (k := P0.k) (ρ := P0.r - j) (Wp := Wp) (Wq := Wq))
    | insert c t hc ih => rw [Finset.sum_insert hc]; exact decV_add (decV_smul _ (hu c)) ih
  rw [sesq_sum_left DecV DecV (fun x y => KB.pairJ (D.formLev T s j w) ys x y) decV_zero
    (fun _ _ => decV_add) (fun c _ => decV_smul c)
    (fun x₁ x₂ y c h₁ h₂ hy => pairing_add_smul_left hXi P0 T s j w ys x₁ x₂ y c h₁ h₂ hy) S a v hv _ hU]
  apply Finset.sum_congr rfl
  intro i _
  rw [sesq_sum_right DecV DecV (fun x y => KB.pairJ (D.formLev T s j w) ys x y) decV_zero
    (fun _ _ => decV_add) (fun c _ => decV_smul c)
    (fun x y₁ y₂ c hx h₁ h₂ => pairing_add_smul_right hXi P0 T s j w ys x y₁ y₂ c hx h₁ h₂) _ (hv i) S' b u hu,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i' _
  ring

end pairing

section deg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
  (w : List C.Letter) (h h' : C.LPt) (hh : D.ptSize h = j) (hh' : D.ptSize h' = j) (s : ℂ)
  (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))

end deg

end wave

end GlobalTheory.FormsFromXi

end
