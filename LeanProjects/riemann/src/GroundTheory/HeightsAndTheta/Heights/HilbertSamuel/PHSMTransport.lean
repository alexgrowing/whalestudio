import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHSMTransport
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKrullDimMatAct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

namespace HSMTransport

section Subst

variable {J : Type} [Fintype J]

def intAct {S : Type*} [CommRing S] (M : J → J → ℤ) (v : J → S) : J → S :=
  fun i => ∑ j, (M i j : S) * v j

def subZ (M : J → J → ℤ) : MvPolynomial J ℤ →ₐ[ℤ] MvPolynomial J ℤ :=
  bind₁ fun i => ∑ j, C (M i j) * X j

def subC (M : J → J → ℤ) : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial J ℂ :=
  bind₁ fun i => ∑ j, C (M i j : ℂ) * X j

theorem aeval_subZ {S : Type*} [CommRing S] (M : J → J → ℤ) (v : J → S) (g : MvPolynomial J ℤ) :
    aeval v (subZ M g) = aeval (intAct M v) g := by
  have h : (fun i => aeval v (∑ j, C (M i j) * X j : MvPolynomial J ℤ)) = intAct M v := by
    funext i
    simp [intAct]
  rw [subZ, aeval_bind₁, h]

theorem eval_subC (M : J → J → ℤ) (z : J → ℂ) (h : MvPolynomial J ℂ) :
    eval z (subC M h) = eval (intAct M z) h := by
  have e : (fun i => aeval z (∑ j, C (M i j : ℂ) * X j : MvPolynomial J ℂ)) = intAct M z := by
    funext i
    simp [intAct]
  show aeval z (subC M h) = aeval (intAct M z) h
  rw [subC, aeval_bind₁, e]

theorem coneMap_subZ {Ω : Type} [Field Ω] (M : J → J → ℤ) (v : J → Ω) (g : MvPolynomial J ℤ) :
    coneMap ℤ v (subZ M g) = coneMap ℤ (intAct M v) g := by
  have h : (coneMap ℤ v).comp (subZ M) = coneMap ℤ (intAct M v) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [subZ, coneMap, intAct, Finset.sum_mul, mul_assoc]
  rw [← AlgHom.comp_apply, h]

theorem isHomogeneous_subZ (M : J → J → ℤ) {g : MvPolynomial J ℤ} {n : ℕ} (hg : g.IsHomogeneous n) :
    (subZ M g).IsHomogeneous n := by
  have := hg.aeval (fun i => ∑ j, C (M i j) * X j) (n := 1) fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X ℤ j).C_mul _
  simpa [subZ, aeval_eq_bind₁, one_mul] using this

theorem map_subZ (M : J → J → ℤ) (g : MvPolynomial J ℤ) :
    map (Int.castRingHom ℂ) (subZ M g) = subC M (map (Int.castRingHom ℂ) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [subZ, subC]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [subZ, subC]

def dirD (z w : J → ℂ) (h : MvPolynomial J ℂ) : ℂ :=
  ∑ i, eval z (pderiv i h) * w i

theorem dirD_add (z w : J → ℂ) (p q : MvPolynomial J ℂ) : dirD z w (p + q) = dirD z w p + dirD z w q := by
  simp only [dirD, map_add, add_mul, Finset.sum_add_distrib]

theorem dirD_mul (z w : J → ℂ) (p q : MvPolynomial J ℂ) :
    dirD z w (p * q) = eval z p * dirD z w q + eval z q * dirD z w p := by
  simp only [dirD, pderiv_mul, map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dirD_C (z w : J → ℂ) (a : ℂ) : dirD z w (C a) = 0 := by
  simp [dirD]

theorem dirD_X (z w : J → ℂ) (n : J) : dirD z w (X n) = w n := by
  classical
  rw [dirD, Finset.sum_eq_single n (fun i _ hi => by rw [pderiv_X_of_ne (Ne.symm hi), map_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ n) h), pderiv_X_self, map_one, one_mul]

theorem dirD_sum (z w : J → ℂ) {α : Type} (s : Finset α) (f : α → MvPolynomial J ℂ) :
    dirD z w (∑ a ∈ s, f a) = ∑ a ∈ s, dirD z w (f a) := by
  simp only [dirD, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem dirD_subC (M : J → J → ℤ) (z w : J → ℂ) (h : MvPolynomial J ℂ) :
    dirD z w (subC M h) = dirD (intAct M z) (intAct M w) h := by
  induction h using MvPolynomial.induction_on with
  | C a => simp only [subC, bind₁_C_right, dirD_C]
  | add p q hp hq => rw [map_add, dirD_add, dirD_add, hp, hq]
  | mul_X p n hp =>
    have hX : subC M (X n) = ∑ j, C (M n j : ℂ) * X j := by simp [subC]
    have h1 : dirD z w (∑ j, C (M n j : ℂ) * X j) = intAct M w n := by
      rw [dirD_sum]
      simp only [dirD_mul, dirD_C, dirD_X, eval_C, eval_X]
      simp [intAct]
    have h2 : eval z (∑ j, C (M n j : ℂ) * X j) = intAct M z n := by simp [intAct]
    rw [map_mul, dirD_mul, dirD_mul, hp, eval_subC, hX, h1, h2, dirD_X, eval_X]

theorem exists_clear_den (A : Matrix J J ℚ) : ∃ c : ℕ, c ≠ 0 ∧ ∀ i j, ∃ k : ℤ, (c : ℚ) * A i j = k := by
  classical
  refine ⟨∏ i, ∏ j, (A i j).den,
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => (A i j).den_nz, fun i j => ?_⟩
  obtain ⟨t, ht⟩ : (A i j).den ∣ ∏ i, ∏ j, (A i j).den :=
    (Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (A i j).den) (Finset.mem_univ i))
  refine ⟨t * (A i j).num, ?_⟩
  rw [ht]
  push_cast
  rw [mul_comm ((A i j).den : ℚ) t, mul_assoc, Rat.den_mul_eq_num]

theorem intAct_eq {Ω : Type*} [Field Ω] [CharZero Ω] {B' : Matrix J J ℚ} {c : ℕ} {M : J → J → ℤ}
    (hM : ∀ i j, (c : ℚ) * B' i j = M i j) (v : J → Ω) : intAct M v = (c : Ω) • matAct B' v := by
  funext i
  simp only [intAct, matAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Rat.cast_intCast, ← hM]
  push_cast
  ring

theorem intAct_eqC {B' : Matrix J J ℚ} {c : ℕ} {M : J → J → ℤ}
    (hM : ∀ i j, (c : ℚ) * B' i j = M i j) (z : J → ℂ) : intAct M z = (c : ℂ) • matActC B' z :=
  intAct_eq hM z

theorem coordIdeal_const_mul {Ω : Type} [Field Ω] {c : Ω} (hc : c ≠ 0) (x : J → Ω) :
    coordIdeal ℤ (fun i => c * x i) = coordIdeal ℤ x := by
  have key : ((Polynomial.aeval (Polynomial.C c * Polynomial.X : Polynomial Ω)).restrictScalars ℤ).comp
      (coneMap ℤ x) = coneMap ℤ (fun i => c * x i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [coneMap, Polynomial.C_mul]
    ring
  have back : ∀ p : Polynomial Ω,
      (Polynomial.aeval (Polynomial.C c * Polynomial.X) p).comp (Polynomial.C c⁻¹ * Polynomial.X) = p := by
    intro p
    rw [← Polynomial.comp_eq_aeval, Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul,
      Polynomial.comp_X]
  ext f
  show f ∈ RingHom.ker (coneMap ℤ _) ↔ f ∈ RingHom.ker (coneMap ℤ x)
  rw [RingHom.mem_ker, RingHom.mem_ker, ← key, AlgHom.comp_apply, AlgHom.restrictScalars_apply]
  constructor
  · intro h0
    rw [← back (coneMap ℤ x f), h0, Polynomial.zero_comp]
  · intro h0
    rw [h0, map_zero]

theorem subZ_mem_coordIdeal_iff {Ω : Type} [Field Ω] [CharZero Ω] [DecidableEq J] {B B' : Matrix J J ℚ}
    (hB'B : B' * B = 1) {c : ℕ} (hc : c ≠ 0) {M : J → J → ℤ} (hM : ∀ i j, (c : ℚ) * B' i j = M i j)
    (v : J → Ω) (g : MvPolynomial J ℤ) : subZ M g ∈ coordIdeal ℤ (matAct B v) ↔ g ∈ coordIdeal ℤ v := by
  have e : intAct M (matAct B v) = fun i => (c : Ω) * v i := by
    rw [intAct_eq hM, matAct_matAct hB'B]
    rfl
  show subZ M g ∈ RingHom.ker (coneMap ℤ _) ↔ _
  rw [RingHom.mem_ker, coneMap_subZ, e, ← RingHom.mem_ker]
  change g ∈ coordIdeal ℤ (fun i => (c : Ω) * v i) ↔ _
  rw [coordIdeal_const_mul (Nat.cast_ne_zero.2 hc)]

theorem matActC_conjPt (A : Matrix J J ℚ) (z : J → ℂ) : matActC A (conjPt z) = conjPt (matActC A z) := by
  funext i
  simp [matActC, conjPt, map_sum, map_mul]

theorem contDiff_matActC {k : WithTop ℕ∞} (A : Matrix J J ℚ) : ContDiff ℝ k (matActC A) := by
  refine contDiff_pi.2 fun i => ?_
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)

theorem eval_matSubst [DecidableEq J] (B : Matrix J J ℚ) (z : J → ℂ) (g : MvPolynomial J ℚ) :
    eval z (map (algebraMap ℚ ℂ) (matSubst B g)) = eval (matActC B z) (map (algebraMap ℚ ℂ) g) := by
  rw [eval_map, eval_map, ← aeval_def, ← aeval_def]
  have : matSubst B g = linSub B g := by rw [matSubst, linSub, aeval_eq_bind₁]
  rw [this, aeval_linSub]
  rfl

theorem linearIndependent_matAct {Ω : Type} [Field Ω] [CharZero Ω] [DecidableEq J] {A A' : Matrix J J ℚ} (h : A * A' = 1)
    {x : J → Ω} (hx : LinearIndependent ℤ x) : LinearIndependent ℤ (matAct A x) := by
  rw [LinearIndependent.iff_fractionRing ℤ ℚ] at hx ⊢
  rw [Fintype.linearIndependent_iff] at hx ⊢
  intro g hg
  have hsum : ∑ j, (Matrix.vecMul g A j) • x j = 0 := by
    rw [← hg]
    simp only [matAct, Matrix.vecMul, dotProduct, Finset.smul_sum, Finset.sum_smul, Rat.smul_def,
      Rat.cast_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have h0 : Matrix.vecMul g A = 0 := funext (hx _ hsum)
  have hg' : g = Matrix.vecMul (Matrix.vecMul g A) A' := by rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]
  intro i
  rw [hg', h0, Matrix.zero_vecMul]
  rfl

end Subst

section Levi

variable {J : Type} [Fintype J]

def clmAct (M : J → J → ℤ) : (J → ℂ) →L[ℂ] (J → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Matrix.of fun i j => (M i j : ℂ)))

theorem clmAct_apply (M : J → J → ℤ) (z : J → ℂ) : clmAct M z = intAct M z := by
  funext i
  simp [clmAct, intAct, Matrix.mulVec, dotProduct]

theorem fderiv2_comp (φ : (J → ℂ) → ℝ) (L : (J → ℂ) →L[ℂ] (J → ℂ)) {U : Set (J → ℂ)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) {z : J → ℂ} (hz : L z ∈ U) (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ fun y => φ (L y)) z v v = fderiv ℝ (fderiv ℝ φ) (L z) (L v) (L v) := by
  set Lr : (J → ℂ) →L[ℝ] (J → ℂ) := L.restrictScalars ℝ with hLr
  have hnb : ∀ᶠ y in 𝓝 z, L y ∈ U := L.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hz)
  have h1 : (fderiv ℝ fun y => φ (L y)) =ᶠ[𝓝 z] fun y => (fderiv ℝ φ (L y)).comp Lr := by
    filter_upwards [hnb] with y hy
    have hd : DifferentiableAt ℝ φ (Lr y) :=
      (hφ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
    have := fderiv_fun_comp (𝕜 := ℝ) (g := φ) (f := ⇑Lr) y hd Lr.differentiableAt
    rw [Lr.fderiv] at this
    exact this
  rw [h1.fderiv_eq]
  have hd2 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (Lr z)) (Lr z) := by
    have := (hφ.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)
    exact (this.differentiableAt one_ne_zero).hasFDerivAt
  let P : ((J → ℂ) →L[ℝ] ℝ) →L[ℝ] ((J → ℂ) →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ (J → ℂ) (J → ℂ) ℝ).flip Lr
  have h2 : HasFDerivAt (fun y => (fderiv ℝ φ (L y)).comp Lr) (P.comp ((fderiv ℝ (fderiv ℝ φ) (Lr z)).comp Lr)) z :=
    P.hasFDerivAt.comp z (hd2.comp z Lr.hasFDerivAt)
  rw [h2.fderiv]
  rfl

theorem leviForm_comp (φ : (J → ℂ) → ℝ) (L : (J → ℂ) →L[ℂ] (J → ℂ)) {U : Set (J → ℂ)} (hU : IsOpen U)
    (hφ : ContDiffOn ℝ 2 φ U) {z : J → ℂ} (hz : L z ∈ U) (w : J → ℂ) :
    leviForm (fun y => φ (L y)) z w = leviForm φ (L z) (L w) := by
  unfold leviForm
  rw [fderiv2_comp φ L hU hφ hz w, fderiv2_comp φ L hU hφ hz (Complex.I • w), map_smul]

theorem leviForm_congr {f g : (J → ℂ) → ℝ} {z : J → ℂ} (h : f =ᶠ[𝓝 z] g) (w : J → ℂ) :
    leviForm f z w = leviForm g z w := by
  unfold leviForm
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

theorem leviForm_sub_const (f : (J → ℂ) → ℝ) (a : ℝ) (z w : J → ℂ) :
    leviForm (fun y => f y - a) z w = leviForm f z w := by
  have : (fderiv ℝ fun y => f y - a) = fderiv ℝ f := funext fun y => fderiv_sub_const a
  unfold leviForm
  rw [this]

end Levi

section GlobalTheory

variable {κ : Type} [Fintype κ]

theorem blk_ne_zero_iff {S : Type*} [Zero S] (z : Ix κ → S) :
    (∀ k : Unit, ∃ i : GlobalTheory κ k, z ⟨k, i⟩ ≠ 0) ↔ z ≠ 0 := by
  constructor
  · rintro h rfl
    obtain ⟨i, hi⟩ := h ()
    exact hi rfl
  · intro h k
    obtain ⟨⟨k', i⟩, hi⟩ := Function.ne_iff.mp h
    cases k
    cases k'
    exact ⟨i, hi⟩

theorem mem_mcPts_iff_pts (P : Ideal (MRing (GlobalTheory κ))) (z : Ix κ → ℂ) :
    z ∈ mcPts (ι := GlobalTheory κ) P ↔ z ∈ pts P := by
  simp only [mcPts, pts, conePts, Set.mem_ofPred_eq, blk_ne_zero_iff]

theorem blk_isMultiHomog_iff (g : MRing (GlobalTheory κ)) (a : Unit → ℕ) :
    IsMultiHomog (ι := GlobalTheory κ) g a ↔ g.IsHomogeneous (a ()) := by
  have hdeg : ∀ s : Ix κ →₀ ℕ, ∑ i : κ, s ⟨(), i⟩ = s.degree := by
    intro s
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp
  constructor
  · intro h s hs
    have h1 : Finsupp.degree s = a () := by
      rw [← hdeg]
      exact h s (mem_support_iff.mpr hs) ()
    rw [Finsupp.degree_eq_weight_one] at h1
    exact h1
  · intro h s hs k
    have h1 : Finsupp.degree s = a () := by
      rw [Finsupp.degree_eq_weight_one]
      exact h (mem_support_iff.mp hs)
    rw [← hdeg] at h1
    cases k
    exact h1

theorem isMultiHomog_subZ (M : Ix κ → Ix κ → ℤ) {f : MRing (GlobalTheory κ)} {a : Unit → ℕ}
    (h : IsMultiHomog (ι := GlobalTheory κ) f a) : IsMultiHomog (ι := GlobalTheory κ) (subZ M f) a :=
  (blk_isMultiHomog_iff _ _).2 (isHomogeneous_subZ M ((blk_isMultiHomog_iff _ _).1 h))

theorem sameOrbit_matActC (A : Matrix (Ix κ) (Ix κ) ℚ) {z z' : Ix κ → ℂ} (h : SameOrbit (ι := GlobalTheory κ) z z') :
    SameOrbit (ι := GlobalTheory κ) (matActC A z) (matActC A z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c, hc, ?_⟩
  funext p
  simp only [matActC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [show c j.1 = c p.1 from rfl]
    ring

theorem vanish_map_iff (M : Ix κ → Ix κ → ℤ) (I : Ideal (MRing (GlobalTheory κ))) (w : Ix κ → ℂ) :
    (∀ f ∈ I.map (subZ M), eval w (map (Int.castRingHom ℂ) f) = 0) ↔
      ∀ g ∈ I, eval (intAct M w) (map (Int.castRingHom ℂ) g) = 0 := by
  simp only [aeval_int_eq]
  constructor
  · intro h g hg
    rw [← aeval_subZ]
    exact h _ (Ideal.mem_map_of_mem _ hg)
  · intro h f hf
    have hle : I.map (subZ M) ≤
        RingHom.ker ((aeval w : MvPolynomial (Ix κ) ℤ →ₐ[ℤ] ℂ) : MvPolynomial (Ix κ) ℤ →+* ℂ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change aeval w (subZ M g) = 0
      rw [aeval_subZ]
      exact h g hg
    exact hle hf

theorem mem_mcPts_map_iff [DecidableEq (Ix κ)] {I : Ideal (MRing (GlobalTheory κ))} (hI : IsMultiHomogIdeal (ι := GlobalTheory κ) I)
    {B B' : Matrix (Ix κ) (Ix κ) ℚ} (hBB' : B * B' = 1) {c : ℕ} (hc : c ≠ 0) {M : Ix κ → Ix κ → ℤ}
    (hM : ∀ i j, (c : ℚ) * B' i j = M i j) (w : Ix κ → ℂ) :
    w ∈ mcPts (ι := GlobalTheory κ) (I.map (subZ M)) ↔ matActC B' w ∈ mcPts (ι := GlobalTheory κ) I := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  have hsm : (c : ℂ) • matActC B' w ∈ mcPts (ι := GlobalTheory κ) I ↔ matActC B' w ∈ mcPts (ι := GlobalTheory κ) I := by
    constructor
    · intro h
      have := mcPts_smul hI (fun _ => ((c : ℂ))⁻¹) (fun _ => inv_ne_zero hc') h
      convert this using 1
      funext p
      simp [hc']
    · intro h
      have := mcPts_smul hI (fun _ => (c : ℂ)) (fun _ => hc') h
      convert this using 1
      funext p
      rfl
  rw [← hsm, mem_mcPts_iff_pts, mem_mcPts_iff_pts]
  simp only [pts, conePts, Set.mem_ofPred_eq]
  rw [vanish_map_iff, intAct_eqC hM]
  refine and_congr_left' ?_
  rw [Ne, Ne, smul_eq_zero, not_or]
  simp only [hc', not_false_eq_true, true_and]
  exact not_congr (matAct_eq_zero_iff hBB' w).symm

section ResFields

variable {P I P' I' : Ideal (MRing (GlobalTheory κ))} {e : ℕ} (R : AnRes (ι := GlobalTheory κ) P I e) (A : Matrix (Ix κ) (Ix κ) ℚ)

theorem holo_tr : ∀ x p, R.A.HoloOn (R.U x) (fun y => matActC A (R.lift x y) p) := by
  intro x p j
  show AnalyticOnNhd ℂ (fun u => ∑ q, (A p q : ℂ) * R.lift x ((R.A.chart j).symm u) q) _
  have := Finset.analyticOnNhd_sum (f := fun q u => (A p q : ℂ) * R.lift x ((R.A.chart j).symm u) q)
    Finset.univ fun q _ => analyticOnNhd_const.mul (R.holo x q j)
  rw [Finset.sum_fn] at this
  exact this

theorem mem_tr (hP : ∀ z, matActC A z ∈ mcPts (ι := GlobalTheory κ) P' ↔ z ∈ mcPts (ι := GlobalTheory κ) P) :
    ∀ x, ∀ y ∈ R.U x, matActC A (R.lift x y) ∈ mcPts (ι := GlobalTheory κ) P' :=
  fun x y hy => (hP _).2 (R.mem x y hy)

theorem compat_tr : ∀ x x', ∀ y ∈ R.U x ∩ R.U x',
    SameOrbit (ι := GlobalTheory κ) (matActC A (R.lift x y)) (matActC A (R.lift x' y)) :=
  fun x x' y hy => sameOrbit_matActC A (R.compat x x' y hy)

theorem surj_tr (A' : Matrix (Ix κ) (Ix κ) ℚ) (hAA' : ∀ z, matActC A (matActC A' z) = z)
    (hP : ∀ z, matActC A z ∈ mcPts (ι := GlobalTheory κ) P' ↔ z ∈ mcPts (ι := GlobalTheory κ) P)
    (hI : ∀ z, matActC A z ∈ mcPts (ι := GlobalTheory κ) I' ↔ z ∈ mcPts (ι := GlobalTheory κ) I) :
    ∀ z ∈ mcPts (ι := GlobalTheory κ) P', z ∉ mcPts (ι := GlobalTheory κ) I' →
      ∃ x, SameOrbit (ι := GlobalTheory κ) (matActC A (R.lift x x)) z := by
  intro z hz hzI
  obtain ⟨x, hx⟩ := R.surj (matActC A' z) ((hP _).1 (by rw [hAA']; exact hz))
    (fun h => hzI (by rw [← hAA' z]; exact (hI _).2 h))
  refine ⟨x, ?_⟩
  have := sameOrbit_matActC A hx
  rwa [hAA'] at this

theorem inj_tr (A' : Matrix (Ix κ) (Ix κ) ℚ) (hA'A : ∀ z, matActC A' (matActC A z) = z)
    (hI : ∀ z, matActC A z ∈ mcPts (ι := GlobalTheory κ) I' ↔ z ∈ mcPts (ι := GlobalTheory κ) I) :
    ∀ x x', matActC A (R.lift x x) ∉ mcPts (ι := GlobalTheory κ) I' →
      SameOrbit (ι := GlobalTheory κ) (matActC A (R.lift x x)) (matActC A (R.lift x' x')) → x = x' := by
  intro x x' hx hs
  refine R.inj x x' (fun h => hx ((hI _).2 h)) ?_
  have := sameOrbit_matActC A' hs
  rwa [hA'A, hA'A] at this

theorem null_tr (hI : ∀ z, matActC A z ∈ mcPts (ι := GlobalTheory κ) I' ↔ z ∈ mcPts (ι := GlobalTheory κ) I) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | matActC A (R.lift x x) ∈ mcPts (ι := GlobalTheory κ) I'}) = 0 := by
  have e : {x : R.X | matActC A (R.lift x x) ∈ mcPts (ι := GlobalTheory κ) I'} = {x | R.lift x x ∈ mcPts I} :=
    Set.ext fun x => hI _
  rw [e]
  exact R.null j

end ResFields

def metricTr (m : ConeMetric ℂ (Ix κ)) (A : Matrix (Ix κ) (Ix κ) ℚ)
    (hA : ∀ v : Ix κ → ℂ, matActC A v = 0 → v = 0) : ConeMetric ℂ (Ix κ) where
  ρ w := m.ρ (matActC A w)
  pos w hw := m.pos _ fun h => hw (hA w h)
  smul c w := by
    classical
    rw [show matActC A (c • w) = c • matActC A w from matAct_smul A c w, m.smul]

end GlobalTheory

section Datum

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] [DecidableEq (Ix κ)]

theorem arith_tr (hK : KrullDimMatAct.Statement) (d : HSMDatum D Ω κ) {B B' : Matrix (Ix κ) (Ix κ) ℚ}
    (hB : IsInvMat B) (hB'B : B' * B = 1) : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ (matAct B d.x)) (D + 1) := by
  obtain ⟨hne, ⟨_, _, hrel⟩, _, hdim⟩ := d.arith
  refine ⟨hne, ⟨coordIdeal_isPrime ℤ _, isMultiHomogIdeal_coordIdeal _, ?_⟩, isHorizontal_coordIdeal _, ?_⟩
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    have hx : d.x ≠ 0 := fun h => hi ((X_mem_coordIdeal_iff d.x _).mpr (by rw [h]; rfl))
    have hAx : matAct B d.x ≠ 0 := fun h => hx ((matAct_eq_zero_iff hB'B d.x).mp h)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hAx
    obtain ⟨⟨⟩, j⟩ := j
    refine ⟨j, ?_⟩
    rw [X_mem_coordIdeal_iff]
    cases k
    exact hj
  · rw [← hdim]
    exact hK Ω (Ix κ) d.x B hB

theorem smooth_tr (m : ConeMetric ℂ (Ix κ)) (hm : IsSmoothMetric m) {B B' : Matrix (Ix κ) (Ix κ) ℚ}
    (hBB' : B * B' = 1) (hA : ∀ v : Ix κ → ℂ, matActC B' v = 0 → v = 0) : IsSmoothMetric (metricTr m B' hA) :=
  hm.comp (contDiff_matActC B').contDiffOn fun w hw h => hw ((matAct_eq_zero_iff hBB' w).1 h)

theorem conjInv_tr (m : ConeMetric ℂ (Ix κ)) (hm : IsConjInvariant m) (B' : Matrix (Ix κ) (Ix κ) ℚ)
    (hA : ∀ v : Ix κ → ℂ, matActC B' v = 0 → v = 0) : IsConjInvariant (metricTr m B' hA) := fun z => by
  show m.ρ (matActC B' (conjPt z)) = m.ρ (matActC B' z)
  rw [matActC_conjPt]
  exact hm _

theorem log_contDiffOn (m : ConeMetric ℂ (Ix κ)) (hm : IsSmoothMetric m) :
    ContDiffOn ℝ 2 (fun u => Real.log (m.ρ u)) {u : Ix κ → ℂ | u ≠ 0} :=
  (hm.log fun u hu => (m.pos u hu).ne').of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem semipos_tr (d : HSMDatum D Ω κ) {B B' : Matrix (Ix κ) (Ix κ) ℚ} (hBB' : B * B' = 1)
    (hB'B : B' * B = 1) (hB : IsInvMat B) {c : ℕ} (hc : c ≠ 0) {M : Ix κ → Ix κ → ℤ}
    (hM : ∀ i j, (c : ℚ) * B' i j = M i j) (hA : ∀ v : Ix κ → ℂ, matActC B' v = 0 → v = 0) :
    IsSemipositiveRel (coordIdeal ℤ (matAct B d.x)) (coordIdeal ℤ (matAct B d.x))
      (HermLine.ofCone (metricTr d.m B' hA)) := by
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  refine ⟨(smooth_tr d.m d.smooth hBB' hA).mono fun z hz => (blk_ne_zero_iff z).1 hz, fun z hz w hw => ?_⟩
  have hz0 : z ≠ 0 := (blk_ne_zero_iff z).1 hz.1
  have hz' : matActC B' z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
    rw [mem_mcPts_iff_pts, ← pts_matAct_gen d.x B hB, ← mem_mcPts_iff_pts]
    rw [show matActC B (matActC B' z) = z from matAct_matAct hBB' z]
    exact hz
  have hLz : clmAct M z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
    rw [clmAct_apply, intAct_eqC hM]
    exact mcPts_smul (isMultiHomogIdeal_coordIdeal d.x) (fun _ => (c : ℂ)) (fun _ => hc') hz'
  have htan : IsConeTangent (Int.castRingHom ℂ) d.P0 (clmAct M z) (clmAct M w) := by
    intro g hg
    have hmem : subZ M g ∈ coordIdeal ℤ (matAct B d.x) :=
      (subZ_mem_coordIdeal_iff hB'B hc hM d.x g).2 (d.normalForm_baseLattice_le_dualSpan_sup_line hg)
    have := hw _ hmem
    change dirD z w (map (Int.castRingHom ℂ) (subZ M g)) = 0 at this
    rw [map_subZ, dirD_subC] at this
    show dirD (clmAct M z) (clmAct M w) (map (Int.castRingHom ℂ) g) = 0
    rw [clmAct_apply, clmAct_apply]
    exact this
  have hsem := d.semipos.2 _ hLz _ htan
  have heq : (fun y => Real.log ((HermLine.ofCone (metricTr d.m B' hA)).h y)) =ᶠ[𝓝 z]
      fun y => Real.log (d.m.ρ (clmAct M y)) - Real.log c := by
    filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
    have hy' : matActC B' y ≠ 0 := fun h => hy ((matAct_eq_zero_iff hBB' y).1 h)
    show Real.log (d.m.ρ (matActC B' y)) = Real.log (d.m.ρ (clmAct M y)) - Real.log c
    rw [clmAct_apply, intAct_eqC hM, d.m.smul, Complex.norm_natCast,
      Real.log_mul (Nat.cast_ne_zero.2 hc) (d.m.pos _ hy').ne']
    ring
  have hcomp := leviForm_comp (fun u => Real.log (d.m.ρ u)) (clmAct M) isOpen_ne (log_contDiffOn d.m d.smooth)
    ((blk_ne_zero_iff _).1 hLz.1) w
  beta_reduce at hcomp
  rw [leviForm_congr heq, leviForm_sub_const, hcomp]
  exact hsem

theorem homog_tr (d : HSMDatum D Ω κ) (M : Ix κ → Ix κ → ℤ) :
    IsMultiHomogIdeal (ι := GlobalTheory κ) (d.J.map (subZ M)) := by
  obtain ⟨S, hS, hJS⟩ := d.R.homog
  refine ⟨subZ M '' S, ?_, ?_⟩
  · rintro f ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    exact ⟨a, isMultiHomog_subZ M ha⟩
  · rw [hJS, Ideal.map_span]

theorem nondeg_tr (d : HSMDatum D Ω κ) {B B' : Matrix (Ix κ) (Ix κ) ℚ} (hB'B : B' * B = 1) {c : ℕ} (hc : c ≠ 0)
    {M : Ix κ → Ix κ → ℤ} (hM : ∀ i j, (c : ℚ) * B' i j = M i j) :
    ¬ d.J.map (subZ M) ≤ coordIdeal ℤ (matAct B d.x) := by
  intro hle
  apply d.R.nondeg
  intro g hg
  exact (subZ_mem_coordIdeal_iff hB'B hc hM d.x g).1 (hle (Ideal.mem_map_of_mem _ hg))

theorem matActC_mem_mcPts_iff (d : HSMDatum D Ω κ) {B : Matrix (Ix κ) (Ix κ) ℚ} (hB : IsInvMat B) (z : Ix κ → ℂ) :
    matActC B z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ (matAct B d.x)) ↔ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
  rw [mem_mcPts_iff_pts, mem_mcPts_iff_pts]
  exact pts_matAct_gen d.x B hB z

theorem hJ_tr (d : HSMDatum D Ω κ) {B B' : Matrix (Ix κ) (Ix κ) ℚ} (hBB' : B * B' = 1) (hB'B : B' * B = 1)
    {c : ℕ} (hc : c ≠ 0) {M : Ix κ → Ix κ → ℤ} (hM : ∀ i j, (c : ℚ) * B' i j = M i j) (z : Ix κ → ℂ) :
    matActC B z ∈ mcPts (ι := GlobalTheory κ) (d.J.map (subZ M)) ↔ z ∈ mcPts (ι := GlobalTheory κ) d.J := by
  rw [mem_mcPts_map_iff d.R.homog hBB' hc hM, show matActC B' (matActC B z) = z from matAct_matAct hB'B z]

theorem resGram_mk (x0 : Ix κ → Ω) (m : ConeMetric ℂ (Ix κ)) (P0 J : Ideal (MRing (GlobalTheory κ)))
    (homog : IsMultiHomogIdeal (ι := GlobalTheory κ) J) (nondeg : ¬ J ≤ coordIdeal ℤ x0) (Xt : Type) [TopologicalSpace Xt]
    [CompactSpace Xt] [T2Space Xt] (A : FinHolAtlas D Xt) (U : Xt → Set Xt) (isOpen_U : ∀ x, IsOpen (U x))
    (mem_U : ∀ x, x ∈ U x) (lift : Xt → Xt → Ix κ → ℂ) (holo : ∀ x p, A.HoloOn (U x) (fun y => lift x y p))
    (mem : ∀ x, ∀ y ∈ U x, lift x y ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ x0))
    (compat : ∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (ι := GlobalTheory κ) (lift x y) (lift x' y))
    (surj : ∀ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ x0), z ∉ mcPts (ι := GlobalTheory κ) J →
      ∃ x, SameOrbit (ι := GlobalTheory κ) (lift x x) z)
    (inj : ∀ x x', lift x x ∉ mcPts (ι := GlobalTheory κ) J → SameOrbit (ι := GlobalTheory κ) (lift x x) (lift x' x') → x = x')
    (null : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' {x | lift x x ∈ mcPts (ι := GlobalTheory κ) J}) = 0)
    [MeasurableSpace Xt] [BorelSpace Xt] (dV : Measure Xt) (one_le : 1 ≤ D)
    (arith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x0) (D + 1)) (indep : LinearIndependent ℤ x0)
    (smooth : IsSmoothMetric m) (conjInv : IsConjInvariant m) (normalForm_baseLattice_le_dualSpan_sup_line : P0 ≤ coordIdeal ℤ x0)
    (semipos : IsSemipositiveRel P0 (coordIdeal ℤ x0) (HermLine.ofCone m)) (vol : IsSmoothVolume A dV)
    (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    resGram (HSMDatum.mk x0 m P0 J (AnRes.mk homog nondeg Xt A U isOpen_U mem_U lift holo mem compat surj inj null)
      dV one_le arith indep smooth conjInv normalForm_baseLattice_le_dualSpan_sup_line semipos vol) n b =
      fun k l => (1 / 2) * ((∫ y, pairVal m n (b k) (b l) (lift y y) ∂dV).re +
        (∫ y, pairVal m n (b k) (b l) (conjPt (lift y y)) ∂dV).re) := rfl

def datumTr (d : HSMDatum D Ω κ) (B B' : Matrix (Ix κ) (Ix κ) ℚ) (hBB' : B * B' = 1)
    (hB'B : B' * B = 1) (hB : IsInvMat B) (c : ℕ) (hc : c ≠ 0) (M : Ix κ → Ix κ → ℤ)
    (hM : ∀ i j, (c : ℚ) * B' i j = M i j) (x' : Ix κ → Ω) (hx' : matAct B d.x = x')
    (J' : Ideal (MRing (GlobalTheory κ))) (hhom : IsMultiHomogIdeal (ι := GlobalTheory κ) J') (hnd : ¬ J' ≤ coordIdeal ℤ x')
    (hPx : ∀ z, matActC B z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ x') ↔ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x))
    (hJ' : ∀ z, matActC B z ∈ mcPts (ι := GlobalTheory κ) J' ↔ z ∈ mcPts (ι := GlobalTheory κ) d.J)
    (harith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x') (D + 1)) : HSMDatum D Ω κ where
  x := x'
  m := metricTr d.m B' fun v h => (matAct_eq_zero_iff hBB' v).1 h
  P0 := coordIdeal ℤ x'
  J := J'
  R :=
    { homog := hhom
      nondeg := hnd
      X := d.R.X
      A := d.R.A
      U := d.R.U
      isOpen_U := d.R.isOpen_U
      mem_U := d.R.mem_U
      lift := fun x y => matActC B (d.R.lift x y)
      holo := holo_tr d.R B
      mem := mem_tr d.R B hPx
      compat := compat_tr d.R B
      surj := surj_tr d.R B B' (fun z => matAct_matAct hBB' z) hPx hJ'
      inj := inj_tr d.R B B' (fun z => matAct_matAct hB'B z) hJ'
      null := null_tr d.R B hJ' }
  meas := d.meas
  borel := d.borel
  dV := d.dV
  one_le := d.one_le
  arith := harith
  indep := by
    subst hx'
    exact linearIndependent_matAct hBB' d.indep
  smooth := smooth_tr d.m d.smooth hBB' _
  conjInv := conjInv_tr d.m d.conjInv B' _
  normalForm_baseLattice_le_dualSpan_sup_line := le_rfl
  semipos := by
    subst hx'
    exact semipos_tr d hBB' hB'B hB hc hM _
  vol := d.vol

theorem resGram_datumTr (d : HSMDatum D Ω κ) (B B' : Matrix (Ix κ) (Ix κ) ℚ) (hBB' : B * B' = 1)
    (hB'B : B' * B = 1) (hB : IsInvMat B) (c : ℕ) (hc : c ≠ 0) (M : Ix κ → Ix κ → ℤ)
    (hM : ∀ i j, (c : ℚ) * B' i j = M i j) (x' : Ix κ → Ω) (hx' : matAct B d.x = x')
    (J' : Ideal (MRing (GlobalTheory κ))) (hhom : IsMultiHomogIdeal (ι := GlobalTheory κ) J') (hnd : ¬ J' ≤ coordIdeal ℤ x')
    (hPx : ∀ z, matActC B z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ x') ↔ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x))
    (hJ' : ∀ z, matActC B z ∈ mcPts (ι := GlobalTheory κ) J' ↔ z ∈ mcPts (ι := GlobalTheory κ) d.J)
    (harith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x') (D + 1)) (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    resGram (datumTr d B B' hBB' hB'B hB c hc M hM x' hx' J' hhom hnd hPx hJ' harith) n b = resGram d n fun k => matSubst B (b k) := by
  have hpv : ∀ (k l : Fin r) (z : Ix κ → ℂ),
      pairVal (metricTr d.m B' fun v h => (matAct_eq_zero_iff hBB' v).1 h) n (b k) (b l) (matActC B z) =
        pairVal d.m n (matSubst B (b k)) (matSubst B (b l)) z := fun k l z => by
    simp only [pairVal, eval_matSubst]
    rw [show (metricTr d.m B' fun v h => (matAct_eq_zero_iff hBB' v).1 h).ρ (matActC B z) = d.m.ρ z from
      congrArg d.m.ρ (matAct_matAct hB'B z)]
  unfold datumTr
  rw [resGram_mk]
  funext k l
  simp only [resGram, resPt, ← matActC_conjPt, hpv]

theorem datumTr_m (d : HSMDatum D Ω κ) (B B' : Matrix (Ix κ) (Ix κ) ℚ) (hBB' : B * B' = 1)
    (hB'B : B' * B = 1) (hB : IsInvMat B) (c : ℕ) (hc : c ≠ 0) (M : Ix κ → Ix κ → ℤ)
    (hM : ∀ i j, (c : ℚ) * B' i j = M i j) (x' : Ix κ → Ω) (hx' : matAct B d.x = x')
    (J' : Ideal (MRing (GlobalTheory κ))) (hhom : IsMultiHomogIdeal (ι := GlobalTheory κ) J') (hnd : ¬ J' ≤ coordIdeal ℤ x')
    (hPx : ∀ z, matActC B z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ x') ↔ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x))
    (hJ' : ∀ z, matActC B z ∈ mcPts (ι := GlobalTheory κ) J' ↔ z ∈ mcPts (ι := GlobalTheory κ) d.J)
    (harith : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x') (D + 1)) (z : Ix κ → ℂ) :
    (datumTr d B B' hBB' hB'B hB c hc M hM x' hx' J' hhom hnd hPx hJ' harith).m.ρ (matActC B z) = d.m.ρ z := by
  show d.m.ρ (matActC B' (matActC B z)) = _
  rw [show matActC B' (matActC B z) = z from matAct_matAct hB'B z]

end Datum

theorem proof (hK : KrullDimMatAct.Statement) : HSMTransport.Statement := by
  intro D Ω _ _ κ _ d B hB
  classical
  obtain ⟨B', hBB', hB'B⟩ := isInvMat_mul hB
  obtain ⟨c, hc, hcl⟩ := exists_clear_den B'
  choose M hM using hcl
  have hhom := homog_tr d M
  have hnd := nondeg_tr d (B := B) hB'B hc hM
  have hJ' := hJ_tr d hBB' hB'B hc hM
  have hPx := matActC_mem_mcPts_iff d hB
  refine ⟨datumTr d B B' hBB' hB'B hB c hc M hM _ rfl _ hhom hnd hPx hJ' (arith_tr hK d hB hB'B), rfl,
    datumTr_m d B B' hBB' hB'B hB c hc M hM _ rfl _ hhom hnd hPx hJ' _,
    fun n r b => resGram_datumTr d B B' hBB' hB'B hB c hc M hM _ rfl _ hhom hnd hPx hJ' _ n r b⟩

end HSMTransport

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
