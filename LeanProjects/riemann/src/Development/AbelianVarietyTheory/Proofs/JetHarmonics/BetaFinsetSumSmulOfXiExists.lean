import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.BetaSum

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2 MeasureTheory Filter
open scoped ComplexConjugate

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

variable [FiniteDimensional ℂ Wp]

open Finset MeasureTheory Filter in
open scoped ComplexConjugate in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in

theorem _root_.GlobalTheory.BetaSum.beta_sesq (hXi : _root_.Formalism.FourierDecayAlt.B.XiExists) (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ}
    (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {F F' G : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)} (hF : _root_.Formalism.FourierDecayAlt.B.InCC A 5 F) (hF' : _root_.Formalism.FourierDecayAlt.B.InCC A 5 F')
    (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) (c : ℂ) :
    _root_.Formalism.FourierDecayAlt.B.beta D (F + c • F') G = _root_.Formalism.FourierDecayAlt.B.beta D F G + c * _root_.Formalism.FourierDecayAlt.B.beta D F' G ∧
      _root_.Formalism.FourierDecayAlt.B.beta D G (F + c • F') = _root_.Formalism.FourierDecayAlt.B.beta D G F + conj c * _root_.Formalism.FourierDecayAlt.B.beta D G F' :=
  _root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA hF hF' hG c

end GlobalTheory.BetaSum

namespace GlobalTheory

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
private lemma beta_eq_star_beta_swap (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (F G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) :
    _root_.Formalism.FourierDecayAlt.B.beta D F G = star (_root_.Formalism.FourierDecayAlt.B.beta D G F) := by
  unfold _root_.Formalism.FourierDecayAlt.B.beta _root_.Formalism.QuantumDeterminants.betaBig
  rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl, ← integral_conj]
  congr 1
  ext p
  simp [inner_conj_symm]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
private lemma beta_congr_right_on_GV (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {F G G₂ : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp}
    (h : ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, G g = G₂ g) : _root_.Formalism.FourierDecayAlt.B.beta D F G = _root_.Formalism.FourierDecayAlt.B.beta D F G₂ := by
  rw [beta_eq_star_beta_swap D F G, beta_eq_star_beta_swap D F G₂, _root_.Formalism.FourierDecayAlt.P.Dx1.LZ.beta_congr_left D h]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
private lemma beta_sum_smul_left (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp)
    (hFi : ∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) :
    _root_.Formalism.FourierDecayAlt.B.beta D (fun g ↦ ∑ i ∈ s, c i • Fi i g) G = ∑ i ∈ s, c i * _root_.Formalism.FourierDecayAlt.B.beta D (Fi i) G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : _root_.Formalism.FourierDecayAlt.B.InCC A 5 (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) := _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_zero
    have h := (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA h0 h0 hG 1).1
    have e : ((fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) +
        (1 : ℂ) • (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp))) =
        (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) := by
      funext g; simp
    rw [e, one_mul] at h
    simp only [Finset.sum_empty]
    have : _root_.Formalism.FourierDecayAlt.B.beta D (fun _ : _root_.Formalism.FourierDecayAlt.B.Mat k r ↦ (0 : Wq →L[ℂ] Wp)) G = 0 := by
      linear_combination -h
    exact this
  | insert x s hx ih =>
    have hs : _root_.Formalism.FourierDecayAlt.B.InCC A 5 (fun g ↦ ∑ i ∈ s, c i • Fi i g) :=
      _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum s (fun i g ↦ c i • Fi i g) (fun i _ ↦ _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_smul (c i) (hFi i))
    have e : (fun g ↦ ∑ i ∈ insert x s, c i • Fi i g) =
        (fun g ↦ ∑ i ∈ s, c i • Fi i g) + c x • Fi x := by
      funext g; simp [Finset.sum_insert hx, add_comm]
    rw [e, (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq D hA hs (hFi x) hG (c x)).1, ih, Finset.sum_insert hx, add_comm]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in
private lemma beta_sum_smul_right (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp)
    (hFi : ∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) :
    _root_.Formalism.FourierDecayAlt.B.beta D G (fun g ↦ ∑ i ∈ s, c i • Fi i g) = ∑ i ∈ s, star (c i) * _root_.Formalism.FourierDecayAlt.B.beta D G (Fi i) := by
  rw [beta_eq_star_beta_swap, beta_sum_smul_left D hA s c Fi hFi hG, star_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [star_mul', beta_eq_star_beta_swap D G (Fi i)]

open Finset MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] in
variable [FiniteDimensional ℂ Wp] in

theorem _root_.GlobalTheory.beta_finset_sum_smul_of_bessel : _root_.GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (A : ℝ) (ι : Type) (S T : Finset ι) (a b : ι → ℂ) (Fi : ι → _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (F F' : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → (∀ i, _root_.Formalism.FourierDecayAlt.B.InCC A 5 (Fi i)) → (∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, F g = ∑ i ∈ S, a i • Fi i g) → (∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, F' g = ∑ i ∈ T, b i • Fi i g) → _root_.Formalism.FourierDecayAlt.B.beta D F F' = ∑ i ∈ S, ∑ j ∈ T, a i * star (b j) * _root_.Formalism.FourierDecayAlt.B.beta D (Fi i) (Fi j) := by
  intro _ k r Wp Wq _ _ _ _ _ _ D A ι S T a b Fi F F' hA hFi hF hF'
  rw [_root_.Formalism.FourierDecayAlt.P.Dx1.LZ.beta_congr_left D hF, beta_congr_right_on_GV D hF',
    beta_sum_smul_left D hA S a Fi hFi
      (_root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum T (fun i g ↦ b i • Fi i g) (fun i _ ↦ _root_.Formalism.FourierDecayAlt.P.JCx2.sq_inCC_smul (b i) (hFi i)))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [beta_sum_smul_right D hA T b Fi hFi (hFi i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end GlobalTheory
