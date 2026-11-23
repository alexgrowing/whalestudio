import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorIter

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.SP.Mi

variable {n : ℕ}

def alMn (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

def cMn (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def phi (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : Pm (Polynomial ℂ) ρ →ₐ[Polynomial ℂ] Fm n :=
  rename fun pq => (b, J pq.1, I pq.2)

theorem phi_X (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) : phi b I J (X (p, q)) = yv b (J p) (I q) := by
  simp [phi, yv, rename_X]

set_option maxHeartbeats 2000000 in
theorem deriv_part (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) = phi b I J (del p q f) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    simp [phi, del]
  | add f g hf hg =>
    simp only [map_add, Derivation.leibniz, mul_add, Finset.sum_add_distrib, hf, hg]
  | mul_X f pq hf =>
    have e : phi b I J (f * X pq) = phi b I J f * yv b (J pq.1) (I pq.2) := by rw [map_mul, phi_X]
    have hdx : del p q (X pq : Pm (Polynomial ℂ) ρ) = X (pq.1, p) * X (q, pq.2) := by simp [del, mkDerivation_X]
    rw [e, Derivation.leibniz (del p q), smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, ← hf, hdx, map_mul,
      phi_X, phi_X, phi_X]
    have hsplit : ∀ a d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f * yv b (J pq.1) (I pq.2)) =
        yv b (J pq.1) (I pq.2) * (yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) +
          phi b I J f * (yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (yv b (J pq.1) (I pq.2))) := by
      intro a d
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hpart : (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (yv b (J pq.1) (I pq.2))) =
        yv b (J pq.1) (I p) * yv b (J q) (I pq.2) := by
      rw [Finset.sum_eq_single (J pq.1), Finset.sum_eq_single (I pq.2)]
      · simp only [yv, pderiv_X, Pi.single_eq_same, mul_one]
      · intro d _ hd
        simp only [yv, pderiv_X]
        rw [Pi.single_eq_of_ne (fun h => hd (congrArg (fun x : Bool × Fin n × Fin n => x.2.2) h).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun d _ => ?_
        simp only [yv, pderiv_X]
        rw [Pi.single_eq_of_ne (fun h => ha (congrArg (fun x : Bool × Fin n × Fin n => x.2.1) h).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hpart, add_comm]

set_option maxHeartbeats 2000000 in
theorem opH_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    opH s m b (I p) (J q) (phi b I J f) = (-(cMn s b)) • phi b I J (opE (alMn m b) p q f) := by
  have h := deriv_part s m b I J p q f
  simp only [opH, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, Derivation.coeFn_coe, opE, map_add, map_mul]
  have hs : (∑ a : Fin n, ∑ d : Fin n, (-(if b = true then Complex.I * s else -(Complex.I * s))) •
      (yv b a (I p) * yv b (J q) d * (pderiv (b, a, d)) (phi b I J f))) =
      (-(if b = true then Complex.I * s else -(Complex.I * s))) • ∑ a : Fin n, ∑ d : Fin n,
        yv b a (I p) * yv b (J q) d * (pderiv (b, a, d)) (phi b I J f) := by
    simp only [Finset.smul_sum]
  have h1 : phi b I J (C (alMn m b)) = C (if b = true then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X) := by
    simp only [phi, rename_C, alMn]
  rw [hs, h, ← smul_add, h1, phi_X]
  rfl

theorem foldr_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ))
    (f : Pm (Polynomial ℂ) ρ) :
    (L.foldr (fun k g => opH s m b (I k) (J (σ k)) ∘ₗ g) LinearMap.id) (phi b I J f) =
      (-(cMn s b)) ^ L.length • phi b I J ((L.foldr (fun k g => opE (alMn m b) k (σ k) ∘ₗ g) LinearMap.id) f) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply, ih, map_smul, opH_phi, smul_smul, List.length_cons, pow_succ]

theorem minorOp_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (f : Pm (Polynomial ℂ) ρ) :
    minorOp s m b I J (phi b I J f) = (-(cMn s b)) ^ ρ • phi b I J (detE (alMn m b) f) := by
  simp only [minorOp, detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_phi, List.length_finRange, map_sum,
    map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, smul_comm]

theorem iter_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (N : ℕ) (f : Pm (Polynomial ℂ) ρ) :
    (minorOp s m b I J)^[N] (phi b I J f) = ((-(cMn s b)) ^ ρ) ^ N • phi b I J ((detE (alMn m b))^[N] f) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, minorOp_phi, smul_smul, Function.iterate_succ_apply', pow_succ,
      mul_comm]

theorem prodId (a : Polynomial ℂ) (c : ℂ) (ρ N : ℕ) :
    Polynomial.C (((-c) ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) =
      Polynomial.C ((c ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (-a - Polynomial.C ((l : ℂ) - i)) := by
  have e : ∀ l i : ℕ, (-a - Polynomial.C ((l : ℂ) - i)) = (-1) * (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) := by
    intro l i
    simp only [map_sub, map_natCast]
    ring
  simp_rw [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  simp only [map_pow, map_neg]
  ring

theorem minorFormula : MinorFormula := by
  intro n s hs m b ρ N I J
  have h1 : (1 : Fm n) = phi b I J 1 := (map_one _).symm
  rw [h1, iter_phi, iter]
  have hc : (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ,
      (MvPolynomial.C (alMn m b) + (l : Pm (Polynomial ℂ) ρ) - (i : Pm (Polynomial ℂ) ρ))) =
      MvPolynomial.C (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (alMn m b + (l : Polynomial ℂ) - (i : Polynomial ℂ))) := by
    simp [map_prod]
  have hdet : phi b I J ((Xm (Polynomial ℂ) ρ).det) = Matrix.det (fun p q : Fin ρ => yv b (J p) (I q)) := by
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [Xm, phi_X]
  rw [hc, map_mul, map_pow, hdet]
  simp only [phi, rename_C]
  rw [Algebra.smul_def, ← mul_assoc]
  congr 1
  rw [MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← map_mul]
  congr 1
  exact prodId _ _ ρ N

end PositivityTheory.Rg.Sw.SP
