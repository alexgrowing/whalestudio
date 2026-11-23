import Mathlib
import Formalism.PeriodIntegrals.LocLatSat

noncomputable section

open scoped nonZeroDivisors

namespace PI.LocLatSat.UnitaryGroupMassFormula

variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}

def bcG (x : Fin n → K) : Fin n → S := fun i => φ (x i)

def latG (Λ : Submodule R (Fin n → K)) : Submodule O (Fin n → S) :=
  Submodule.span O (bcG φ '' (Λ : Set (Fin n → K)))

def fP (f : (Fin n → K) →ₗ[K] K) : (Fin n → S) →ₗ[S] S where
  toFun y := ∑ k, y k * φ (f fun j => if k = j then 1 else 0)
  map_add' y z := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.mul_sum, mul_assoc]

omit [IsDedekindDomain R] [IsFractionRing R K] in
lemma baseChange_apply_baseChange (f : (Fin n → K) →ₗ[K] K) (x : Fin n → K) : fP φ f (bcG φ x) = φ (f x) := by
  have hx : x = ∑ k, x k • (fun j => if k = j then (1 : K) else 0) := by
    funext i
    simp [Finset.sum_apply]
  show ∑ k, φ (x k) * φ (f fun j => if k = j then 1 else 0) = φ (f x)
  conv_rhs => rw [hx]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_smul, smul_eq_mul, map_mul]

omit [IsDedekindDomain R] [IsFractionRing R K] in
lemma bcG_sub (x y : Fin n → K) : bcG φ (x - y) = bcG φ x - bcG φ y := by
  funext i
  simp [bcG, map_sub]

omit [IsDedekindDomain R] [IsFractionRing R K] in
lemma bcG_smulR (r : R) (x : Fin n → K) : bcG φ (r • x) = φ (algebraMap R K r) • bcG φ x := by
  funext i
  simp [bcG, Algebra.smul_def, map_mul]

theorem step (Λ : Submodule R (Fin n → K)) (f : (Fin n → K) →ₗ[K] K)
    (hI : IsFractional R⁰ (Λ.map (f.restrictScalars R)))
    {x : Fin n → S} (hx : x ∈ latG φ O Λ) (h0 : fP φ f x = 0) :
    x ∈ latG φ O (Λ ⊓ (LinearMap.ker f).restrictScalars R) := by
  set I : FractionalIdeal R⁰ K := ⟨Λ.map (f.restrictScalars R), hI⟩ with hIdef
  by_cases hI0 : I = 0
  ·
    have hv : ∀ v ∈ Λ, f v = 0 := by
      intro v hv
      have hmem : f v ∈ (I : Submodule R K) :=
        Submodule.mem_map_of_mem (f := f.restrictScalars R) hv
      rw [hI0, FractionalIdeal.coe_zero, Submodule.mem_bot] at hmem
      exact hmem
    have he : Λ ⊓ (LinearMap.ker f).restrictScalars R = Λ := by
      refine inf_eq_left.mpr (fun v hv' => ?_)
      simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker]
      exact hv v hv'
    rw [he]
    exact hx
  · have hmul : I * I⁻¹ = 1 := mul_inv_cancel₀ hI0
    have hmul' : I⁻¹ * I = 1 := by rw [mul_comm]; exact hmul
    set M := latG φ O (Λ ⊓ (LinearMap.ker f).restrictScalars R) with hMdef

    have claim : ∀ t ∈ (I : Submodule R K) * ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K),
        φ t • x ∈ M := by
      intro t ht
      refine Submodule.mul_induction_on (C := fun t => φ t • x ∈ M) ht ?_ ?_
      · intro a ha b hb
        obtain ⟨lam, hlam, hfl⟩ := Submodule.mem_map.mp ha
        have hab : a * b ∈ (1 : FractionalIdeal R⁰ K) := by
          rw [← hmul]
          exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp ha) (FractionalIdeal.mem_coe.mp hb)
        obtain ⟨r1, hr1⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hab
        have hgen : ∀ y ∈ latG φ O Λ, φ (a * b) • y - (fP φ f y * φ b) • bcG φ lam ∈ M := by
          intro y hy
          unfold latG at hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨v, hv, rfl⟩ := hy
            have hfv : f v ∈ (I : Submodule R K) :=
              Submodule.mem_map_of_mem (f := f.restrictScalars R) hv
            have hbf : b * f v ∈ (1 : FractionalIdeal R⁰ K) := by
              rw [← hmul']
              exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coe.mp hb) (FractionalIdeal.mem_coe.mp hfv)
            obtain ⟨r2, hr2⟩ := (FractionalIdeal.mem_one_iff R⁰).mp hbf
            have hfl' : f lam = a := hfl
            have hwΛ : r1 • v - r2 • lam ∈ Λ := Λ.sub_mem (Λ.smul_mem r1 hv) (Λ.smul_mem r2 hlam)
            have hwk : f (r1 • v - r2 • lam) = 0 := by
              rw [map_sub, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, Algebra.smul_def,
                Algebra.smul_def, hr1, hr2, hfl']
              ring
            have hw : bcG φ (r1 • v - r2 • lam) = φ (a * b) • bcG φ v - (fP φ f (bcG φ v) * φ b) • bcG φ lam := by
              rw [bcG_sub, bcG_smulR, bcG_smulR, hr1, hr2, baseChange_apply_baseChange, map_mul, map_mul, mul_comm (φ b)]
            rw [← hw]
            apply Submodule.subset_span
            exact ⟨r1 • v - r2 • lam, ⟨hwΛ, hwk⟩, rfl⟩
          | zero => simpa using M.zero_mem
          | add y z _ _ hy hz =>
            have e : φ (a * b) • (y + z) - (fP φ f (y + z) * φ b) • bcG φ lam =
                (φ (a * b) • y - (fP φ f y * φ b) • bcG φ lam) +
                  (φ (a * b) • z - (fP φ f z * φ b) • bcG φ lam) := by
              rw [map_add, add_mul, add_smul, smul_add]
              abel
            rw [e]
            exact M.add_mem hy hz
          | smul o y _ hy =>
            have e : φ (a * b) • (o • y) - (fP φ f (o • y) * φ b) • bcG φ lam =
                o • (φ (a * b) • y - (fP φ f y * φ b) • bcG φ lam) := by
              rw [Subring.smul_def, Subring.smul_def, map_smul, smul_eq_mul, smul_sub, smul_smul, smul_smul,
                smul_smul]
              congr 2 <;> ring
            rw [e]
            exact M.smul_mem o hy
        have := hgen x hx
        rwa [h0, zero_mul, zero_smul, sub_zero] at this
      · intro t1 t2 h1 h2
        simp only [map_add, add_smul]
        exact M.add_mem h1 h2
    have h1 : (1 : K) ∈ (I : Submodule R K) * ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
      rw [← FractionalIdeal.coe_mul, hmul]
      exact FractionalIdeal.one_mem_one _
    have := claim 1 h1
    rwa [map_one, one_smul] at this

end PI.LocLatSat.UnitaryGroupMassFormula
