import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness.GN

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := GBasic.Hpk_herm k r

theorem hpk_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := GBasic.Hpk_sq k r

theorem hpk_isUnit_det (k r : ℕ) : IsUnit (Hpk k r).det :=
  isUnit_det_of_left_inverse (hpk_sq k r)

theorem one_mem (k r : ℕ) : (1 : B.Mat k r) ∈ B.GV k r :=
  (unitary_group_holds _ _ (hpk_isUnit_det k r)).1

theorem mul_mem {k r : ℕ} {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) :
    g * h ∈ B.GV k r :=
  (unitary_group_holds _ _ (hpk_isUnit_det k r)).2.1 g hg h hh

theorem inv_mem {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r :=
  ((unitary_group_holds _ _ (hpk_isUnit_det k r)).2.2 g hg).2

theorem det_isUnit {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : IsUnit g.det :=
  ((unitary_group_holds _ _ (hpk_isUnit_det k r)).2.2 g hg).1

theorem mul_inv {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g * g⁻¹ = 1 :=
  mul_nonsing_inv _ (det_isUnit hg)

theorem inv_mul {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ * g = 1 :=
  nonsing_inv_mul _ (det_isUnit hg)

theorem inv_eq {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, hpk_sq]
  exact Matrix.inv_eq_left_inv h1

theorem herm_mulVec {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) (g *ᵥ w) = herm (Hpk k r) v w := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec]
  rw [← Matrix.mul_assoc, h]

def hs {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

theorem hs_nonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : 0 ≤ hs M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem gN_eq {k r : ℕ} (g : B.Mat k r) : B.gN g = Real.sqrt (hs g) := rfl

theorem gN_nonneg {k r : ℕ} (g : B.Mat k r) : 0 ≤ B.gN g := Real.sqrt_nonneg _

theorem gN_sq {k r : ℕ} (g : B.Mat k r) : B.gN g ^ 2 = hs g := by
  rw [gN_eq, Real.sq_sqrt (hs_nonneg g)]

theorem hs_conjTranspose {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : hs Mᴴ = hs M := by
  unfold hs
  simp only [conjTranspose_apply, RCLike.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

theorem hs_hpk_mul {k r : ℕ} (M : B.Mat k r) : hs (Hpk k r * M) = hs M := by
  unfold hs
  have e : ∀ i j, (Hpk k r * M) i j = GBasic.sgn k r i * M (GBasic.sig k r i) j := by
    intro i j
    rw [mul_apply]
    simp only [GBasic.Hpk_eq k r i, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs1 : ∀ i, Complex.normSq (GBasic.sgn k r i) = 1 := by
    intro i; unfold GBasic.sgn; split_ifs <;> simp
  simp only [e, Complex.normSq_mul, hs1, one_mul]
  exact Equiv.sum_comp (Function.Involutive.toPerm _ (GBasic.sig_sig k r))
    (fun i => ∑ j, Complex.normSq (M i j))

theorem gN_conjTranspose {k r : ℕ} (g : B.Mat k r) : B.gN gᴴ = B.gN g := by
  rw [gN_eq, gN_eq, hs_conjTranspose]

theorem gN_hpk_mul {k r : ℕ} (g : B.Mat k r) : B.gN (Hpk k r * g) = B.gN g := by
  rw [gN_eq, gN_eq, hs_hpk_mul]

theorem gN_mul_hpk {k r : ℕ} (g : B.Mat k r) : B.gN (g * Hpk k r) = B.gN g := by
  have e : g * Hpk k r = (Hpk k r * gᴴ)ᴴ := by
    rw [conjTranspose_mul, hpk_herm, conjTranspose_conjTranspose]
  rw [e, gN_conjTranspose, gN_hpk_mul, gN_conjTranspose]

theorem gN_inv {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : B.gN g⁻¹ = B.gN g := by
  rw [inv_eq hg, gN_mul_hpk, gN_hpk_mul, gN_conjTranspose]

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing

theorem gN_eq_frob {k r : ℕ} (g : B.Mat k r) : B.gN g = ‖g‖ := by
  rw [Matrix.frobenius_norm_def, B.gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq]; norm_cast

theorem gN_mul_le {k r : ℕ} (a b : B.Mat k r) : B.gN (a * b) ≤ B.gN a * B.gN b := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact Matrix.frobenius_norm_mul a b

theorem gN_ge_one {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : 1 ≤ B.gN g := by
  rw [gN_eq_frob]
  have hH : Hpk k r ≠ 0 := by
    intro h0
    have := hpk_sq k r
    rw [h0, Matrix.zero_mul] at this
    exact zero_ne_one this
  have hpos : 0 < ‖Hpk k r‖ := norm_pos_iff.mpr hH
  have h1 : ‖Hpk k r‖ ≤ ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by
    have e : gᴴ * Hpk k r * g = Hpk k r := hg
    calc ‖Hpk k r‖ = ‖gᴴ * Hpk k r * g‖ := by rw [e]
      _ ≤ ‖gᴴ * Hpk k r‖ * ‖g‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖gᴴ‖ * ‖Hpk k r‖ * ‖g‖ :=
          mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
      _ = ‖g‖ * ‖Hpk k r‖ * ‖g‖ := by rw [Matrix.frobenius_norm_conjTranspose]
  by_contra hlt
  rw [not_le] at hlt
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg _
  have : ‖g‖ * ‖Hpk k r‖ * ‖g‖ < ‖Hpk k r‖ := by nlinarith [mul_nonneg hg0 hpos.le]
  linarith

end Frob

theorem gN_pos {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : 0 < B.gN g :=
  lt_of_lt_of_le one_pos (gN_ge_one hg)

theorem normSq_le_hs {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (i j : ι) :
    Complex.normSq (M i j) ≤ hs M := by
  unfold hs
  calc Complex.normSq (M i j) ≤ ∑ j', Complex.normSq (M i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (M i j'))
          (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (M i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (M i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem entry_le_gN {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  rw [gN_eq, Complex.norm_def]
  exact Real.sqrt_le_sqrt (normSq_le_hs g i j)

theorem hs_le_of_entry {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) {c : ℝ}
    (h : ∀ i j, ‖M i j‖ ≤ c) : hs M ≤ (Fintype.card ι : ℝ) ^ 2 * c ^ 2 := by
  unfold hs
  have h1 : ∀ i j, Complex.normSq (M i j) ≤ c ^ 2 := by
    intro i j
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  calc ∑ i, ∑ j, Complex.normSq (M i j) ≤ ∑ _i : ι, ∑ _j : ι, c ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = (Fintype.card ι : ℝ) ^ 2 * c ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem gN_le_of_entry {k r : ℕ} (g : B.Mat k r) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖g i j‖ ≤ c) :
    B.gN g ≤ (2 * r + k + 1 : ℕ) * c := by
  rw [gN_eq]
  have h1 := hs_le_of_entry g h
  rw [Fintype.card_fin] at h1
  have h2 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * c := by positivity
  calc Real.sqrt (hs g) ≤ Real.sqrt ((((2 * r + k + 1 : ℕ) : ℝ) * c) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [mul_pow]; exact h1)
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * c := Real.sqrt_sq h2

theorem mx_nonneg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ C2.mx M := norm_nonneg _

theorem entry_le_mx {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : ‖M i j‖ ≤ C2.mx M := by
  unfold C2.mx
  calc ‖M i j‖ = ‖(Matrix.of.symm M) i j‖ := rfl
    _ ≤ ‖(Matrix.of.symm M) i‖ := norm_le_pi_norm _ j
    _ ≤ ‖Matrix.of.symm M‖ := norm_le_pi_norm _ i

theorem mx_le_iff {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {c : ℝ} (hc : 0 ≤ c) :
    C2.mx M ≤ c ↔ ∀ i j, ‖M i j‖ ≤ c := by
  constructor
  · intro h i j; exact (entry_le_mx M i j).trans h
  · intro h
    unfold C2.mx
    refine (pi_norm_le_iff_of_nonneg hc).2 fun i => (pi_norm_le_iff_of_nonneg hc).2 fun j => ?_
    exact h i j

theorem mx_conjTranspose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : C2.mx Mᴴ = C2.mx M := by
  apply le_antisymm
  · refine (mx_le_iff _ (mx_nonneg M)).2 fun i j => ?_
    rw [conjTranspose_apply, norm_star]; exact entry_le_mx M j i
  · refine (mx_le_iff _ (mx_nonneg Mᴴ)).2 fun i j => ?_
    have := entry_le_mx Mᴴ j i
    rwa [conjTranspose_apply, norm_star] at this

theorem mx_mul_le {m : ℕ} (A B' : Matrix (Fin m) (Fin m) ℂ) :
    C2.mx (A * B') ≤ m * C2.mx A * C2.mx B' := by
  have h0 : 0 ≤ (m : ℝ) * C2.mx A * C2.mx B' := by
    have := mx_nonneg A; have := mx_nonneg B'; positivity
  refine (mx_le_iff _ h0).2 fun i j => ?_
  rw [mul_apply]
  calc ‖∑ l, A i l * B' l j‖ ≤ ∑ l, ‖A i l * B' l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin m, C2.mx A * C2.mx B' := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul]
        exact mul_le_mul (entry_le_mx A i l) (entry_le_mx B' l j) (norm_nonneg _) (mx_nonneg A)
    _ = m * C2.mx A * C2.mx B' := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem dot_bound {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v w : ι → ℂ) {E : ℝ}
    (hE : ∀ i j, ‖M i j‖ ≤ E) :
    ‖star w ⬝ᵥ (M *ᵥ v)‖ ≤ (∑ i, ‖w i‖) * (∑ j, ‖v j‖) * E := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  calc ‖∑ i, star (w i) * ∑ j, M i j * v j‖ ≤ ∑ i, ‖w i‖ * ∑ j, ‖v j‖ * E := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_star]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (hE i j) (norm_nonneg _)
    _ = (∑ i, ‖w i‖) * (∑ j, ‖v j‖) * E := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

theorem fvec_sum_le (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin (r + 1)) :
    ∑ i, ‖fvec k r z a i‖ ≤ 1 + ∑ i, ‖z i‖ := by
  have hz : 0 ≤ ∑ i, ‖z i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold fvec
  split_ifs with h
  · have e : ∀ i, ‖bvec (eI k r ⟨a.val, h⟩) i‖ = if i = eI k r ⟨a.val, h⟩ then 1 else 0 := by
      intro i; unfold bvec; rw [Pi.single_apply]; split_ifs <;> simp
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith
  · linarith

theorem zhat_norm_linear_bound : C2.ZhatBound := by
  intro k r z z'
  refine ⟨(1 + ∑ i, ‖z i‖) * (1 + ∑ i, ‖z' i‖), fun g => ?_⟩
  have hz : 0 ≤ ∑ i, ‖z i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hz' : 0 ≤ ∑ i, ‖z' i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC : 0 ≤ (1 + ∑ i, ‖z i‖) * (1 + ∑ i, ‖z' i‖) * B.gN g := by
    have := gN_nonneg g; positivity
  refine (mx_le_iff _ hC).2 fun a b => ?_
  show ‖herm (Hpk k r) (g *ᵥ fvec k r z' b) (fvec k r z a)‖ ≤ _
  unfold herm
  rw [mulVec_mulVec]
  have hE : ∀ i j, ‖(Hpk k r * g) i j‖ ≤ B.gN g := by
    intro i j; rw [← gN_hpk_mul g]; exact entry_le_gN _ i j
  refine (dot_bound _ _ _ hE).trans ?_
  have h1 := fvec_sum_le k r z a
  have h2 := fvec_sum_le k r z' b
  have h3 : 0 ≤ ∑ i, ‖fvec k r z a i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h4 : 0 ≤ ∑ i, ‖fvec k r z' b i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h5 := gN_nonneg g
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h4 (by linarith)) h5

theorem polynomial_normInv : C2.NormInv := fun _ _ _ hg => ⟨gN_inv hg, gN_ge_one hg⟩

end PI.PolynomialProperness.GN
