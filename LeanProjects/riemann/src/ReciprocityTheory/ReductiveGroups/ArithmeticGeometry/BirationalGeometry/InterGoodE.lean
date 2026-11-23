import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

theorem intOver_trans {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (ℓ : Fin (r + 1) → R)
    (lam : Fin r → k) (h0 : IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) (ℓ 0)) {x : R}
    (hx : IntOver k ℓ x) : IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) x := by
  set ℓ' : Fin r → R := fun i => ℓ i.succ - lam i • ℓ 0 with hℓ'
  let f' : MvPolynomial (Fin r) k →+* R := (aeval ℓ' : MvPolynomial (Fin r) k →ₐ[k] R)
  letI : Algebra (MvPolynomial (Fin r) k) R := f'.toAlgebra
  let Cl := integralClosure (MvPolynomial (Fin r) k) R
  have hmem0 : ℓ 0 ∈ Cl := h0
  have hB : ∀ b, f' b ∈ Cl := fun b => Subalgebra.algebraMap_mem Cl b
  have hmem : ∀ j, ℓ j ∈ Cl := by
    intro j
    refine Fin.cases hmem0 (fun i => ?_) j
    have : ℓ i.succ = f' (X i) + f' (C (lam i)) * ℓ 0 := by
      simp [f', hℓ', Algebra.smul_def]
    rw [this]
    exact Cl.add_mem (hB _) (Cl.mul_mem (hB _) hmem0)
  have hall : ∀ p : MvPolynomial (Fin (r + 1)) k, (aeval ℓ p : R) ∈ Cl := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have := hB (C a)
      simpa [f'] using this
    | add p q hp hq => rw [map_add]; exact Cl.add_mem hp hq
    | mul_X p j hp => rw [map_mul, aeval_X]; exact Cl.mul_mem hp (hmem j)
  obtain ⟨p, hpm, hp⟩ := hx
  let g : MvPolynomial (Fin (r + 1)) k →+* Cl :=
    ((aeval ℓ : MvPolynomial (Fin (r + 1)) k →ₐ[k] R) : MvPolynomial (Fin (r + 1)) k →+* R).codRestrict
      Cl.toSubsemiring hall
  have hxC : IsIntegral Cl x := by
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  exact isIntegral_trans (R := MvPolynomial (Fin r) k) (A := Cl) x hxC

def forms {R : Type*} [CommRing R] [Algebra k R] {τ : Type*} [Fintype τ] (v : τ → R) {r : ℕ}
    (L : Fin r → τ → k) : Fin r → R :=
  fun j => ∑ t, L j t • v t

theorem exists_linear_normalization [Infinite k] {R : Type*} [CommRing R] [Algebra k R]
    {τ : Type*} [Fintype τ] (v : τ → R) (m : ℕ)
    (hdep : ∀ (r : ℕ) (L : Fin r → τ → k), m < r → ¬ AlgebraicIndependent k (forms v L)) :
    ∃ r ≤ m, ∃ L : Fin r → τ → k, ∀ t, IntOver k (forms v L) (v t) := by
  classical
  let Good : ℕ → Prop := fun r => ∃ L : Fin r → τ → k, ∀ t, IntOver k (forms v L) (v t)
  have hstart : Good (Fintype.card τ) := by
    let e := Fintype.equivFin τ
    refine ⟨fun j s => if s = e.symm j then 1 else 0, fun t => ?_⟩
    have hf : forms v (fun j s => if s = e.symm j then (1 : k) else 0) = fun j => v (e.symm j) := by
      funext j
      simp [forms, ite_smul]
    rw [hf]
    have : v t = (aeval (fun j => v (e.symm j)) : MvPolynomial (Fin _) k →ₐ[k] R) (X (e t)) := by
      simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  have hstep : ∀ r, m < r + 1 → Good (r + 1) → Good r := by
    rintro r hr ⟨L, hL⟩
    have hnot := hdep (r + 1) L hr
    rw [algebraicIndependent_iff] at hnot
    push Not at hnot
    obtain ⟨F, hF, hF0⟩ := hnot
    obtain ⟨lam, h0⟩ := exists_isIntegralElem_linear (forms v L) F hF0 hF
    refine ⟨fun i s => L i.succ s - lam i * L 0 s, fun t => ?_⟩
    have hf : forms v (fun i s => L i.succ s - lam i * L 0 s) =
        fun i => forms v L i.succ - lam i • forms v L 0 := by
      funext i
      simp [forms, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
    rw [hf]
    exact intOver_trans (forms v L) lam h0 (hL t)
  have hdesc : ∀ d, Good (m + d) → Good m := by
    intro d
    induction d with
    | zero => exact id
    | succ d ih => exact fun h => ih (hstep (m + d) (by omega) h)
  by_cases hN : Fintype.card τ ≤ m
  · exact ⟨_, hN, hstart⟩
  · refine ⟨m, le_rfl, hdesc (Fintype.card τ - m) ?_⟩
    rw [show m + (Fintype.card τ - m) = Fintype.card τ by omega]
    exact hstart

end

end ReciprocityTheory.ChartRestriction.G.Geo
