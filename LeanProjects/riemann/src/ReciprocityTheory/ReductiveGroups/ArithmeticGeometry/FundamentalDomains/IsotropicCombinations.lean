import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPairingAlgebra

namespace ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Herm

variable {n : ℕ} (G : Matrix (Fin r) (Fin r) E)

def hermLin (y : Fin r → E) : (Fin r → E) →ₗ[E] E where
  toFun x := herm G x y
  map_add' x x' := by simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

lemma herm_sum_smul (c : Fin n → E) (β : Fin n → Fin r → E) (y : Fin r → E) :
    herm G (∑ k, c k • β k) y = ∑ k, c k * herm G (β k) y := by
  have h := map_sum (hermLin G y) (fun k => c k • β k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

lemma herm_add_smul (x ξ y : Fin r → E) (e : E) : herm G (x + e • ξ) y = herm G x y + e * herm G ξ y := by
  have h := map_add (hermLin G y) x (e • ξ)
  rw [map_smul, smul_eq_mul] at h
  exact h

variable {G} (hG : ∀ a b, cc (G a b) = G b a) {ξ : Fin r → E} {β : Fin n → Fin r → E}
  (hβ : ∀ k, herm G (β k) ξ = 0) (hξξ : herm G ξ ξ = 0)

include hβ in
lemma herm_B_ξ (c : Fin n → E) : herm G (∑ k, c k • β k) ξ = 0 := by
  rw [herm_sum_smul]
  simp [hβ]

include hβ hξξ in
lemma herm_lam_ξ (c : Fin n → E) (e : E) : herm G (∑ k, c k • β k + e • ξ) ξ = 0 := by
  rw [herm_add_smul, herm_B_ξ hβ, hξξ]
  ring

include hG hβ hξξ in
lemma herm_lam_lam (c c' : Fin n → E) (e e' : E) :
    herm G (∑ k, c k • β k + e • ξ) (∑ k, c' k • β k + e' • ξ) =
      herm G (∑ k, c k • β k) (∑ k, c' k • β k) := by
  have hadd : ∀ x y y' : Fin r → E, herm G x (y + y') = herm G x y + herm G x y' := by
    intro x y y'
    simp only [herm, Pi.add_apply, cc, map_add, mul_add, Finset.sum_add_distrib]
  have hsm : ∀ (x y : Fin r → E) (a : E), herm G x (a • y) = cc a * herm G x y := by
    intro x y a
    simp only [herm, Pi.smul_apply, smul_eq_mul, cc, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hswap : ∀ x y : Fin r → E, herm G y x = cc (herm G x y) := by
    intro x y
    have hmap : ∀ s : Finset (Fin r), ∀ f : Fin r → E, cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) :=
      fun s f => by simp only [cc, map_sum]
    have hmul : ∀ a b : E, cc (a * b) = cc a * cc b := fun a b => by simp only [cc, map_mul]
    simp only [herm, hmap, hmul, cc_cc, hG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hξβ : ∀ k, herm G ξ (β k) = 0 := fun k => by
    rw [hswap, hβ k]
    simp only [cc, map_zero]
  have hξB : herm G ξ (∑ k, c' k • β k) = 0 := by
    have hs : ∀ (s : Finset (Fin n)), herm G ξ (∑ k ∈ s, c' k • β k) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty, herm, Pi.zero_apply, cc, map_zero, mul_zero, Finset.sum_const_zero]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, hadd, hsm, hξβ, ih]
        ring
    exact hs _
  rw [herm_add_smul, hadd, hadd, hsm, hsm, herm_B_ξ hβ, hξξ, hξB]
  ring

lemma ne_smul_ξ (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    {c : Fin n → E} (hc : c ≠ 0) (e e' : E) : ∑ k, c k • β k + e • ξ ≠ e' • ξ := by
  intro h
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli (Fin.cons (e - e') c) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, sub_smul]
    rw [← sub_eq_zero] at h
    rw [← h]
    abel)
  exact hc (funext fun k => by simpa using h0 k.succ)

lemma cons_li (hli : LinearIndependent E (Fin.cons ξ β : Fin (n + 1) → Fin r → E))
    {la : Fin n → Fin n → E} (hla : LinearIndependent E la) (e : Fin n → E) :
    LinearIndependent E (Fin.cons ξ (fun j => ∑ k, la j k • β k + e j • ξ) :
      Fin (n + 1) → Fin r → E) := by
  rw [Fintype.linearIndependent_iff] at hli hla ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have key := hli (Fin.cons (g 0 + ∑ j, g j.succ * e j) (fun k => ∑ j, g j.succ * la j k)) (by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hg]
    simp only [smul_add, Finset.smul_sum, smul_smul, add_smul, Finset.sum_smul,
      Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun x y => (g y.succ * la y x) • β x)]
    abel)
  have hs : ∀ j : Fin n, g j.succ = 0 := by
    refine hla (fun j => g j.succ) ?_
    funext k
    have := key k.succ
    simp only [Fin.cons_succ] at this
    simpa [Finset.sum_apply, smul_eq_mul] using this
  have h0 : g 0 = 0 := by
    have := key 0
    simpa [hs] using this
  intro i
  refine Fin.cases h0 (fun j => hs j) i

end Herm

lemma hC_comb2_ortho (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n p : ℕ} (f : Fin n → Fin r → ℂ)
    (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (b c : Fin n → ℂ) :
    hermC τ G (∑ k, b k • f k) (∑ l, c l • f l) = ReciprocityTheory.MultiplicativeHeights.jForm p c b := by
  have h1 : ∀ (w : Fin n → ℂ) (v : Fin r → ℂ),
      hermC τ G (∑ k, w k • f k) v = ∑ k, w k * hermC τ G (f k) v := by
    intro w v
    simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 : ∀ (w : Fin n → ℂ) (u : Fin r → ℂ),
      hermC τ G u (∑ l, w l • f l) = ∑ l, conj (w l) * hermC τ G u (f l) := by
    intro w u
    simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h1]
  simp_rw [h2, hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.sgn
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

lemma comb_swap {m n : ℕ} (w : Fin n → ℂ) (y : Fin n → Fin m → ℂ) (f : Fin m → Fin r → ℂ) :
    ∑ j, w j • ∑ k, y j k • f k = ∑ k, (∑ j, w j * y j k) • f k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

lemma qcomb {m n : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (w : Fin n → ℂ) (a : Fin n → Fin m → ℂ)
    (k : Fin m) : (Q *ᵥ ∑ j, w j • a j) k = ∑ j, w j * (Q *ᵥ a j) k := by
  have h := map_sum (Matrix.mulVecLin Q) (fun j => w j • a j) Finset.univ
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul] at h
  rw [h]
  simp [Finset.sum_apply]

lemma la_bound {T μ x : ℝ} (hT : 1 ≤ T) (hμ : 2 * μ ^ 2 ≤ T ^ 2) {p0 : ℕ} (hp0 : 1 ≤ p0)
    (hx : x ≤ T ^ 2 ∨ x ≤ T ^ (4 * (p0 - 1)) * (2 * μ ^ 2)) : x ≤ (T ^ (2 * p0 - 1)) ^ 2 := by
  have he : (T ^ (2 * p0 - 1)) ^ 2 = T ^ (4 * (p0 - 1)) * T ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [he]
  have h1 : 1 ≤ T ^ (4 * (p0 - 1)) := one_le_pow₀ hT
  rcases hx with hx | hx
  · calc x ≤ T ^ 2 := hx
      _ = 1 * T ^ 2 := by ring
      _ ≤ T ^ (4 * (p0 - 1)) * T ^ 2 := by gcongr
  · calc x ≤ T ^ (4 * (p0 - 1)) * (2 * μ ^ 2) := hx
      _ ≤ T ^ (4 * (p0 - 1)) * T ^ 2 := by gcongr

end

end ReciprocityTheory.ChartRestriction.G.FD.IsotropicCombinations
