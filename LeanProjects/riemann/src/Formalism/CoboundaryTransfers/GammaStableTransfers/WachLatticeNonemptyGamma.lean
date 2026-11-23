import Formalism.CoboundaryTransfers.StatementEx

noncomputable section

namespace Formalism.CoboundaryTransfers

namespace ExG

open Polynomial

variable (p : ℕ) [Fact p.Prime]

abbrev A := Polynomial ℤ_[p]

abbrev K := FractionRing (Polynomial ℤ_[p])

def γA : A p →ₐ[ℤ_[p]] A p := aeval (-X)

def φA : A p →ₐ[ℤ_[p]] A p := expand ℤ_[p] p

lemma γA_X : γA p X = -X := by simp [γA]

lemma φA_X : φA p X = X ^ p := by simp [φA]

lemma φA_X_eq : φA p X = X * X ^ (p - 1) := by
  rw [φA_X, ← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le]

lemma γA_γA (f : A p) : γA p (γA p f) = f := by
  have h : (γA p).comp (γA p) = AlgHom.id ℤ_[p] (A p) := by
    apply Polynomial.algHom_ext
    simp [γA_X]
  exact AlgHom.congr_fun h f

lemma γA_inj : Function.Injective (γA p) :=
  Function.LeftInverse.injective (γA_γA p)

lemma φA_inj : Function.Injective (φA p) := expand_injective (Fact.out : p.Prime).pos

lemma comm_A (hp2 : p ≠ 2) (a : A p) : φA p (γA p a) = γA p (φA p a) := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h : (φA p).comp (γA p) = (γA p).comp (φA p) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, γA_X, φA_X, map_neg, map_pow, hodd.neg_pow]
  exact AlgHom.congr_fun h a

lemma γA_sub (a : A p) : X ∣ γA p a - a := by
  rw [X_dvd_iff, coeff_sub, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, γA,
    ← comp_eq_aeval, eval_comp]
  simp

def liftK (f : A p →ₐ[ℤ_[p]] A p) (hf : Function.Injective f) : K p →ₐ[ℤ_[p]] K p :=
  IsFractionRing.liftAlgHom (K := K p)
    (g := (IsScalarTower.toAlgHom ℤ_[p] (A p) (K p)).comp f)
    (show Function.Injective ((IsScalarTower.toAlgHom ℤ_[p] (A p) (K p)).comp f) from
      fun x y h => hf (IsFractionRing.injective (A p) (K p) (by simpa using h)))

variable {p}

lemma liftK_alg (f : A p →ₐ[ℤ_[p]] A p) (hf : Function.Injective f) (a : A p) :
    liftK p f hf (algebraMap (A p) (K p) a) = algebraMap (A p) (K p) (f a) := by
  unfold liftK
  rw [IsFractionRing.coe_liftAlgHom, IsFractionRing.lift_algebraMap]
  rfl

lemma liftK_smul (f : A p →ₐ[ℤ_[p]] A p) (hf : Function.Injective f) (a : A p) (x : K p) :
    liftK p f hf (a • x) = f a • liftK p f hf x := by
  rw [Algebra.smul_def, map_mul, liftK_alg, Algebra.smul_def]

lemma liftK_comm (hp2 : p ≠ 2) (x : K p) :
    liftK p (φA p) (φA_inj p) (liftK p (γA p) (γA_inj p) x)
      = liftK p (γA p) (γA_inj p) (liftK p (φA p) (φA_inj p) x) := by
  have h : ((liftK p (φA p) (φA_inj p)).toRingHom.comp (liftK p (γA p) (γA_inj p)).toRingHom)
      = ((liftK p (γA p) (γA_inj p)).toRingHom.comp (liftK p (φA p) (φA_inj p)).toRingHom) := by
    apply IsFractionRing.ringHom_ext (A := A p)
    intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftK_alg,
      comm_A p hp2]
  exact RingHom.congr_fun h x

variable (p)

def base (hp2 : p ≠ 2) : Base ℤ_[p] (A p) where
  p := p
  hp := Fact.out
  φ := φA p
  γ := γA p
  X := X
  Q := X ^ (p - 1)
  comm := comm_A p hp2
  φX := ⟨X ^ (p - 1), φA_X_eq p⟩

lemma algX_ne : algebraMap (A p) (K p) X ≠ 0 := by
  intro h
  exact X_ne_zero ((IsFractionRing.injective (A p) (K p)) (h.trans (map_zero _).symm))

lemma algQ_ne : algebraMap (A p) (K p) (X ^ (p - 1)) ≠ 0 := by
  rw [map_pow]; exact pow_ne_zero _ (algX_ne p)

lemma γN (a : A p) : ∃ x' ∈ LinearMap.range (Algebra.linearMap (A p) (K p)),
    liftK p (γA p) (γA_inj p) (algebraMap (A p) (K p) a) - algebraMap (A p) (K p) a
      = (X : A p) • x' := by
  obtain ⟨t, ht⟩ := γA_sub p a
  refine ⟨algebraMap (A p) (K p) t, ⟨t, rfl⟩, ?_⟩
  rw [liftK_alg, ← map_sub, ht, map_mul, Algebra.smul_def]

def W (hp2 : p ≠ 2) : WachMod (base p hp2) 0 (K p) where
  N := LinearMap.range (Algebra.linearMap (A p) (K p))
  φ := (liftK p (φA p) (φA_inj p)).toLinearMap
  γ := (liftK p (γA p) (γA_inj p)).toLinearMap
  φ_smul := fun a x => liftK_smul (φA p) (φA_inj p) a x
  γ_smul := fun a x => liftK_smul (γA p) (γA_inj p) a x
  comm := fun x => liftK_comm hp2 x
  X_inj := by
    intro x hx
    simp only [base, Algebra.smul_def] at hx
    exact (mul_eq_zero.mp hx).resolve_left (algX_ne p)
  Q_bij := by
    refine ⟨fun a b h => ?_, fun b => ⟨(algebraMap (A p) (K p) (X ^ (p - 1)))⁻¹ * b, ?_⟩⟩
    · simp only [base, Algebra.smul_def] at h
      exact mul_left_cancel₀ (algQ_ne p) h
    · simp only [base, Algebra.smul_def]
      rw [← mul_assoc, mul_inv_cancel₀ (algQ_ne p), one_mul]
  φ_N := by
    rintro x ⟨a, rfl⟩
    refine ⟨φA p a, ?_⟩
    simp [liftK_alg]
  γ_N := by
    rintro x ⟨a, rfl⟩
    exact γN p a
  γ_QN := by
    intro y hy
    rw [pow_zero, one_smul] at hy
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨x', hx', he⟩ := γN p a
    exact ⟨x', by rw [pow_zero, one_smul]; exact hx', he⟩

end ExG

open Polynomial ExG in
theorem wach_lattice_nonempty_gamma : NonemptyG := by
  intro p _ hp2
  have hp := (Fact.out : p.Prime)
  refine ⟨base p hp2, W p hp2, rfl, ?_, ?_, ?_, φA_X_eq p, ?_, ?_, ?_⟩
  · intro h
    have h1 : (1 : K p) ∈ (W p hp2).N := by
      show (1 : K p) ∈ LinearMap.range (Algebra.linearMap (A p) (K p))
      exact ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact not_isUnit_X
  · show ¬ IsUnit ((X : A p) ^ (p - 1))
    rw [isUnit_pow_iff (by have := hp.two_le; omega)]
    exact not_isUnit_X
  · refine ⟨0, ?_⟩
    show γA p X = X * (algebraMap ℤ_[p] (A p) (-1) + X * 0)
    simp [γA_X]
  · refine ⟨1, isUnit_one, ⟨0, by simp⟩, ?_⟩
    show γA p (X ^ (p - 1)) = 1 * X ^ (p - 1)
    rw [map_pow, γA_X, (hp.even_sub_one hp2).neg_pow, one_mul]
  · refine ⟨algebraMap (A p) (K p) X, fun h => ?_⟩
    simp only [W, AlgHom.toLinearMap_apply] at h
    rw [liftK_alg, γA_X] at h
    have h2 := congrArg (fun f : A p => f.coeff 1) ((IsFractionRing.injective (A p) (K p)) h)
    simp only [coeff_neg, coeff_X_one] at h2
    have h3 : (2 : ℤ_[p]) = 0 := by linear_combination -h2
    exact two_ne_zero h3

end Formalism.CoboundaryTransfers
