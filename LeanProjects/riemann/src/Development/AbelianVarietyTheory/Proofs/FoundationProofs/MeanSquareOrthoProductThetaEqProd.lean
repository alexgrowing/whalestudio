import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetAverageProdFundamentalDomainPlaneLatticePow
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PullNorm

noncomputable def coordLin (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b j
  map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
  map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc]

theorem coordLin_apply (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) (z : VC D N N') : coordLin D T b j z = coordB D T b j z := rfl

theorem coordB_sum (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (h1 : ∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) (u : Fin r → ℂ) (k : Fin r) :
    coordB D T b k (∑ j, u j • embV D T (b j)) = u k := by
  rw [← coordLin_apply, map_sum]
  simp [coordLin_apply, h1]

theorem parseval (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (z : VC D N N') (h2 : z = ∑ j, coordB D T b j z • embV D T (b j)) :
    (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (z τ i j)) = ((∑ k, ‖coordB D T b k z‖ ^ 2 : ℝ) : ℂ) := by
  have key : ∀ c : Fin r → ℂ,
      (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) ((∑ k, c k • embV D T (b k)) τ i j))
        = ∑ k, coordB D T b k z * (starRingEnd ℂ) (c k) := by
    intro c
    simp only [coordB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum,
      Finset.sum_mul, embV]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have h := key fun k => coordB D T b k z
  rw [← h2] at h
  rw [h]
  push_cast
  exact Finset.sum_congr rfl fun k _ => Complex.mul_conj' _

theorem gaussianWeight_thetaTranslate_normSq (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) (ω z : ℂ) :
    ‖U1 Λ ω g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)
      = ‖g (ω + z)‖ ^ 2 * Real.exp (-Real.pi * ‖ω + z‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, add_comm z ω]
  congr 2
  have h2 : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
  push_cast
  ring

theorem normSq_pullB : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ T.abelian₂ = AddSubgroup.closure {w₁, w₂}) → (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → (∀ z : VC D N N', z = ∑ j, coordB D T b j z • embV D T (b j)) → ∀ g : ℂ → ℂ, Continuous g → (∀ ω ∈ T.abelian₂, ∀ z, ‖U1 T.abelian₂ ω g z‖ = ‖g z‖) → normSq D T (LaB D T b) (pullB D T b g) = nrm1Sq T.abelian₂ g ^ r := by
  intro D T N N' r b hΛ h1 h2 g _ hg
  let eC : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ) :=
    { LinearMap.pi (fun j => coordLin D T b j) with
      invFun := fun u => ∑ j, u j • embV D T (b j)
      left_inv := fun z => (h2 z).symm
      right_inv := fun u => funext fun k => coordB_sum D T b h1 u k }
  let e : VC D N N' ≃ₗ[ℝ] (Fin r → ℂ) := eC.restrictScalars ℝ
  have he : ∀ z k, e z k = coordB D T b k z := fun _ _ => rfl
  have hA : ∀ x, x ∈ LaB D T b ↔ ∀ k, e x k ∈ T.abelian₂ := by
    intro x
    constructor
    · intro hx k
      unfold LaB at hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, j, rfl⟩ := hy
        rw [he, ← coordLin_apply, map_smul, coordLin_apply, h1]
        split_ifs
        · simpa using hw
        · simp
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | neg y _ hy => rw [map_neg]; exact neg_mem hy
    · intro hx
      rw [h2 x]
      exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨_, hx j, j, rfl⟩
  haveI i1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have main := GlobalTheory.LatticeMean.mean_prod_eq_pow T.abelian₂ hΛ
    (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area T.abelian₂))
    (fun ω hω z => by rw [← gaussianWeight_thetaTranslate_normSq, hg ω hω]) (VC D N N') MeasureTheory.volume r e (LaB D T b) hA
  unfold normSq nrm1Sq
  simp only []
  rw [← main]
  congr 1
  funext z
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Hf, parseval D T b z (h2 z), Complex.div_ofReal_re,
    Complex.ofReal_re, pullB, norm_prod, ← Finset.prod_pow]
  simp only [he]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]

end GlobalTheory.PullNorm
