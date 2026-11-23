import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyEqOfAgreeGLs

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.EigAct

variable {n : ℕ}

section Ops
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_smul (b : ℂ) (X : Mat n) (f : Mat n → V) : Rd X (b • f) = b • Rd X f := by
  funext g
  have : fderiv ℝ (b • f) = b • fderiv ℝ f := fderiv_const_smul_field b
  simp only [Rd, this, Pi.smul_apply]
  rfl

theorem Eu_smul (b : ℂ) (s : Bool) (a c : Fin n) (f : Mat n → V) : Eu s a c (b • f) = b • Eu s a c f := by
  simp only [Eu, Rd_smul]
  module

theorem Epow_smul (b : ℂ) (s : Bool) (m : ℕ) (a c : Fin n) (f : Mat n → V) :
    Epow s m a c (b • f) = b • Epow s m a c f := by
  induction m generalizing a c with
  | zero =>
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    simp only [Epow, ih, Eu_smul, Finset.smul_sum]

theorem gel_smul (b : ℂ) (s : Bool) (m : ℕ) (f : Mat n → V) : gel s m (b • f) = b • gel s m f := by
  simp only [gel, Epow_smul, Finset.smul_sum]

theorem Om_smul (b : ℂ) (f : Mat n → V) : Om (b • f) = b • Om f := by
  simp only [Om, gel_smul]
  module

theorem zOp_smul (b : ℂ) (w : List (Bool × ℕ)) (f : Mat n → V) : zOp w (b • f) = b • zOp w f := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [zOp, ih, gel_smul]

theorem zOp_eig {χ : Inf n} {f : Mat n → V} (hf : IsEig χ f) (w : List (Bool × ℕ)) :
    ∀ x ∈ GLs n, zOp w f x = zVal w χ • f x := by
  induction w with
  | nil => intro x _; simp [zOp, zVal]
  | cons p w ih =>
    intro x hx
    have h := GlobalTheory.CompanionTheory.WaveMult.zOp_agree_GLs n [p] (zOp w f) (zVal w χ • f) (fun g hg => by simpa using ih g hg) x hx
    have h1 : zOp (p :: w) f x = gel p.1 p.2 (zVal w χ • f) x := by simpa [zOp] using h
    rw [h1, gel_smul, Pi.smul_apply, hf p.1 p.2 x hx, smul_smul]
    simp [zVal, mul_comm]

theorem Om_eig {χ : Inf n} {f : Mat n → V} (hf : IsEig χ f) : ∀ x ∈ GLs n, Om f x = cas χ • f x := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, hf _ _ x hx, cas]
  module

end Ops

theorem hasDerivAt_cosh_mul (a : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.cosh (r * a)) (Complex.sinh (s * a) * a) s := by
  have e : HasDerivAt (fun r : ℝ => (r : ℂ) * a) a s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const a
  exact (Complex.hasDerivAt_cosh ((s : ℂ) * a)).comp s e

theorem hasDerivAt_sinh_mul (a : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.sinh (r * a)) (Complex.cosh (s * a) * a) s := by
  have e : HasDerivAt (fun r : ℝ => (r : ℂ) * a) a s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const a
  exact (Complex.hasDerivAt_sinh ((s : ℂ) * a)).comp s e

theorem isWave_cosh (E : KMod n) {χ : Inf n} {f : Mat n → E.V} (hf : f ∈ CE E) (he : IsEig χ f) {a : ℂ}
    (ha : a ^ 2 = cas χ) : IsWave E (fun t x => Complex.cosh (t * a) • f x) := by
  have d1 : ∀ (v : E.V) (s : ℝ), HasDerivAt (fun r : ℝ => Complex.cosh (r * a) • v)
      ((Complex.sinh (s * a) * a) • v) s := fun v s => (hasDerivAt_cosh_mul a s).smul_const v
  have d2 : ∀ (v : E.V) (s : ℝ), HasDerivAt (fun r : ℝ => (Complex.sinh (r * a) * a) • v)
      ((Complex.cosh (s * a) * a * a) • v) s := fun v s =>
    ((hasDerivAt_sinh_mul a s).mul_const a).smul_const v
  refine ⟨?_, fun t => ⟨?_, fun g hg k => ?_⟩, fun t g hg => ?_, fun g _ => ?_⟩
  · have hc : ContDiff ℝ ∞ (fun t : ℝ => Complex.cosh (t * a)) :=
      (Complex.contDiff_cosh.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => Complex.cosh (p.1 * a)) (Set.univ ×ˢ GLs n) :=
      (hc.comp contDiff_fst).contDiffOn
    have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => f p.2) (Set.univ ×ˢ GLs n) :=
      hf.1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    exact h1.smul h2
  · exact contDiffOn_const.smul hf.1
  · simp only [hf.2 g hg k, map_smul]
  · have hOm : Om (fun x => Complex.cosh (t * a) • f x) g = Complex.cosh (t * a) • Om f g :=
      congrFun (Om_smul (Complex.cosh (t * a)) f) g
    have D1 : deriv (fun r : ℝ => Complex.cosh (r * a) • f g) = fun r : ℝ => (Complex.sinh (r * a) * a) • f g :=
      funext fun s => (d1 (f g) s).deriv
    rw [hOm, Om_eig he g hg, iteratedDeriv_succ, iteratedDeriv_one, D1, (d2 (f g) t).deriv, ← ha, smul_smul]
    congr 1
    ring
  · rw [(d1 (f g) 0).deriv]
    simp

section Ker
variable [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)

theorem act_of_isKer {w : List (Bool × ℕ)} {g : ℝ → ℝ} {ks : Mat n → (E.V →L[ℂ] E.V)}
    (hK : IsKer μ E w g ks) {χ : Inf n} {f : Mat n → E.V} (hf : f ∈ CE E) (he : IsEig χ f) {x : Mat n}
    (hx : x ∈ GLs n) : act μ E ks f x = (zVal w χ * coshT g (cas χ)) • f x := by
  have := FiniteDimensional.complete ℂ E.V
  have ha : ((cas χ) ^ (1 / 2 : ℂ)) ^ 2 = cas χ := by
    have := Complex.cpow_nat_inv_pow (cas χ) (n := 2) two_ne_zero
    simpa [one_div] using this
  have hw := hK.2.2.2 _ (isWave_cosh E hf he ha) x hx
  have h0 : (fun x' => Complex.cosh (((0 : ℝ) : ℂ) * (cas χ) ^ (1 / 2 : ℂ)) • f x') = f := by
    funext x'
    simp
  have h1 : (fun x' => ∫ t : ℝ, (g t : ℂ) • (fun t' x'' => Complex.cosh ((t' : ℂ) * (cas χ) ^ (1 / 2 : ℂ)) • f x'') t x') =
      coshT g (cas χ) • f := by
    funext x'
    simp only [smul_smul, Pi.smul_apply, coshT]
    exact integral_smul_const _ _
  rw [h0, h1, zOp_smul, Pi.smul_apply, zOp_eig he w x hx, smul_smul, mul_comm] at hw
  exact hw

end Ker

end GlobalTheory.CompanionTheory.WaveMult.EigAct

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_eq_val_of_isMult : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T → ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x := by
  rintro hL n _ _ μ _ E k val T ⟨m, c, w, g, ks, h1, h2, h3⟩ χ f hf he x hx
  have h := GlobalTheory.CompanionTheory.WaveMult.act_eq_sum_of_kernel hL n μ E c ks k f (fun i => ⟨(h1 i).2.1.continuousOn, (h1 i).2.2.1⟩) h2
    hf.1.continuousOn x hx
  rw [h, h3 χ, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EigAct.act_of_isKer μ E (h1 i).2 hf he hx, smul_smul, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
