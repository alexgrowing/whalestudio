import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinearStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormEqBigCellIntegralTopDensityCompactStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficients
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolarisationOnSubspace
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVecPol

theorem integrable_inner_of_memLp {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun c => inner ℂ (u c) (v c)) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hv.toLp v)).congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with c h1 h2
  rw [h1, h2]

theorem integral_inner_expand {α E : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : α → E} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (a : ℂ) :
    ∫ c, inner ℂ (u c + a • v c) (u c + a • v c) ∂μ =
      ∫ c, inner ℂ (u c) (u c) ∂μ + a * ∫ c, inner ℂ (u c) (v c) ∂μ +
        (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (u c) ∂μ +
        a * (starRingEnd ℂ) a * ∫ c, inner ℂ (v c) (v c) ∂μ := by
  have h1 := integrable_inner_of_memLp hu hu
  have h2 := (integrable_inner_of_memLp hu hv).const_mul a
  have h3 := (integrable_inner_of_memLp hv hu).const_mul ((starRingEnd ℂ) a)
  have h4 := (integrable_inner_of_memLp hv hv).const_mul (a * (starRingEnd ℂ) a)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add h1 h2]
  have h12 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c)) μ := h1.add h2
  have h123 : Integrable (fun c => inner ℂ (u c) (u c) + a * inner ℂ (u c) (v c) +
      (starRingEnd ℂ) a * inner ℂ (v c) (u c)) μ := h12.add h3
  rw [← integral_add h12 h3, ← integral_add h123 h4]
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  ring

theorem beta_eq_integral_inner_tv : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H H' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CptCoef p.T.base H' → KB.CutWord P p.l0 w → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (H) w) H' = ∫ c, inner ℂ (tv p H' w c) (tv p H w c) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H H' w hD hH hH' hw
  have hS : ∀ (a : ℂ) (x y : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base x → KB.CptCoef p.T.base y →
      KB.CptCoef p.T.base (x + a • y) := fun a x y hx hy => Formalism.FourierDecayAlt.P.PBL.cpt_add hx (Formalism.FourierDecayAlt.P.PBL.cpt_smul a hy)
  have hcc : ∀ x : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base x → ∀ (A : ℝ) (m : ℕ), B.InCC A m x := by
    intro x hx
    obtain ⟨ε, -, h⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hx
    exact h.2.1
  refine GlobalTheory.polarisation_on_subspace (B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (KB.CptCoef p.T.base)
    (fun x y => B.beta p.T.base
      (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) x w) y)
    (fun x y => ∫ c, inner ℂ (tv p y w c) (tv p x w c)) hS ?_ ?_ ?_ H H' hH hH'
  · intro a x y hx hy
    have hs := GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w (B.AB P.k P.r) le_rfl a
    have hz := hS a x y hx hy
    have e1 := (hs x y (x + a • y) x hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc _ hz _ _) (hcc x hx _ _)).1
    have e2 := (hs x y x y hx.1 hy.1 (hcc x hx _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    have e3 := (hs y y x y hy.1 hy.1 (hcc y hy _ _) (hcc y hy _ _) (hcc x hx _ _) (hcc y hy _ _)).2
    beta_reduce
    rw [e1, e2, e3]
    ring
  · intro a x y hx hy
    have hx2 := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb x w hD hx hw).1
    have hy2 := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb y w hD hy hw).1
    have e : ∀ c, tv p (x + a • y) w c = tv p x w c + a • tv p y w c := fun c =>
      GlobalTheory.TopVec.tv_add_smul Wp Wq P p Cb a x y w c hD hw hx hy
    beta_reduce
    simp only [e]
    exact integral_inner_expand hx2 hy2 a
  · intro x hx
    beta_reduce
    rw [(GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb x w hD hx hw).2, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    beta_reduce
    rw [inner_self_eq_norm_sq_to_K]
    simp

end GlobalTheory.TopVecPol
