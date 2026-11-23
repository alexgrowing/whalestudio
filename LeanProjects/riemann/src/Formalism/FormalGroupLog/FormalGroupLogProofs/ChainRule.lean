import Mathlib

noncomputable section

open MvPowerSeries

namespace Formalism.G.LogCR

variable {R : Type*} [CommRing R] {σ τ : Type*}

def Agree (N : ℕ) (f g : MvPowerSeries σ R) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < N → coeff d f = coeff d g

theorem Agree.mono {N M : ℕ} {f g : MvPowerSeries σ R} (h : Agree N f g) (hMN : M ≤ N) :
    Agree M f g := fun d hd => h d (lt_of_lt_of_le hd hMN)

theorem Agree.pderiv {N : ℕ} {f g : MvPowerSeries σ R} (h : Agree (N + 1) f g) (i : σ) :
    Agree N (MvPowerSeries.pderiv R i f) (MvPowerSeries.pderiv R i g) := by
  classical
  intro d hd
  rw [coeff_pderiv, coeff_pderiv, h (d + Finsupp.single i 1) ?_]
  rw [map_add, Finsupp.degree_single]
  omega

theorem Agree.mul {N : ℕ} {x x' y y' : MvPowerSeries σ R} (hx : Agree N x x')
    (hy : Agree N y y') : Agree N (x * y) (x' * y') := by
  classical
  intro d hd
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = d := by simpa using hp
  have h1 : p.1 ≤ d := hp' ▸ le_self_add
  have h2 : p.2 ≤ d := hp' ▸ le_add_self
  rw [hx p.1 (lt_of_le_of_lt (Finsupp.degree_mono h1) hd),
    hy p.2 (lt_of_le_of_lt (Finsupp.degree_mono h2) hd)]

theorem agree_iff [Finite σ] {N : ℕ} {f g : MvPowerSeries σ R} :
    Agree N f g ↔ truncTotal N f = truncTotal N g := by
  constructor
  · intro h
    ext d
    rw [coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite]
    split_ifs with hd
    · exact h d hd
    · rfl
  · intro h d hd
    have := congrArg (MvPolynomial.coeff d) h
    rwa [coeff_truncTotal _ hd, coeff_truncTotal _ hd] at this

theorem agree_truncTotal [Finite σ] (N : ℕ) (f : MvPowerSeries σ R) :
    Agree N f (truncTotal N f : MvPowerSeries σ R) := by
  intro d hd
  rw [MvPolynomial.coeff_coe, coeff_truncTotal _ hd]

theorem Agree.subst [Finite σ] [Finite τ] {N : ℕ} {f f' : MvPowerSeries σ R}
    {a a' : σ → MvPowerSeries τ R} (ha : ∀ j, constantCoeff (a j) = 0)
    (ha' : ∀ j, constantCoeff (a' j) = 0) (hf : Agree N f f') (haa : ∀ j, Agree N (a j) (a' j)) :
    Agree N (f.subst a) (f'.subst a') := by
  rw [agree_iff, truncTotal_subst ha, truncTotal_subst ha', agree_iff.mp hf]
  have : (fun i => ((a i).truncTotal N : MvPowerSeries τ R)) =
      fun i => ((a' i).truncTotal N : MvPowerSeries τ R) := by
    funext i; rw [agree_iff.mp (haa i)]
  rw [this]

theorem pderiv_aeval [Fintype σ] (p : MvPolynomial σ R) (A : σ → MvPowerSeries τ R) (i : τ) :
    MvPowerSeries.pderiv R i (MvPolynomial.aeval A p) =
      ∑ j, MvPolynomial.aeval A (MvPolynomial.pderiv j p) * MvPowerSeries.pderiv R i (A j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, map_mul,
      MvPolynomial.aeval_X, add_mul, Finset.sum_add_distrib]
    rw [Derivation.leibniz, hp, smul_eq_mul, smul_eq_mul]
    rw [add_comm]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp [Pi.single_apply, apply_ite (MvPolynomial.aeval A), mul_ite, ite_mul]

theorem pderiv_subst [Fintype σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries σ R) (i : τ) :
    MvPowerSeries.pderiv R i (f.subst a) =
      ∑ j, (MvPowerSeries.pderiv R j f).subst a * MvPowerSeries.pderiv R i (a j) := by
  classical
  ext d
  set N := d.degree + 2 with hN
  set P : MvPolynomial σ R := truncTotal N f with hP
  set A : σ → MvPowerSeries τ R := fun j => (truncTotal N (a j) : MvPowerSeries τ R) with hA
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => by
    have := agree_truncTotal N (a j) 0 (by simp [hN])
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, ha j] at this
    exact this.symm
  have hfP : Agree N f (P : MvPowerSeries σ R) := agree_truncTotal N f
  have haA : ∀ j, Agree N (a j) (A j) := fun j => agree_truncTotal N (a j)
  have h1 : Agree (d.degree + 1) (MvPowerSeries.pderiv R i (f.subst a))
      (MvPowerSeries.pderiv R i ((P : MvPowerSeries σ R).subst A)) :=
    (Agree.subst ha hA0 hfP haA).pderiv i
  have h2 : ∀ j, Agree (d.degree + 1)
      ((MvPowerSeries.pderiv R j f).subst a * MvPowerSeries.pderiv R i (a j))
      ((MvPowerSeries.pderiv R j (P : MvPowerSeries σ R)).subst A *
        MvPowerSeries.pderiv R i (A j)) := fun j =>
    Agree.mul (Agree.subst ha hA0 (hfP.pderiv j) fun k => (haA k).mono (by omega))
      ((haA j).pderiv i)
  have key : MvPowerSeries.pderiv R i ((P : MvPowerSeries σ R).subst A) =
      ∑ j, (MvPowerSeries.pderiv R j (P : MvPowerSeries σ R)).subst A *
        MvPowerSeries.pderiv R i (A j) := by
    rw [subst_coe, pderiv_aeval]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPowerSeries.pderiv_coe P, subst_coe]
  rw [h1 d (by omega), key, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => (h2 j d (by omega)).symm

theorem pderiv_psubst [Finite τ] {a : MvPowerSeries τ R} (ha : constantCoeff a = 0)
    (f : PowerSeries R) (i : τ) :
    MvPowerSeries.pderiv R i (f.subst a) =
      (PowerSeries.derivative R f).subst a * MvPowerSeries.pderiv R i a := by
  have := pderiv_subst (σ := Unit) (a := fun _ => a) (fun _ => ha) f i
  simpa [PowerSeries.subst_def, PowerSeries.derivative] using this

end Formalism.G.LogCR
