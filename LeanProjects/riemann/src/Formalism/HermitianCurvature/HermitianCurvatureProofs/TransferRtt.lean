import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.Mx6

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M

noncomputable section

def Good (P : Par) (Y : ℂ) : Prop :=
  ∀ π : Ty P, ∀ j ∈ Icc 1 (P.k - 1), ∀ n ∈ ({-2, -1, 0, 1, 2} : Finset ℤ), Y + (rho P π j : ℂ) + (n : ℂ) ≠ 0

def dA (P : Par) (Y : ℂ) : A P := qC P Y • (ggiA P * kap P fun π => (xC P π (Y + 1))⁻¹)

def mt (P : Par) (Y : ℂ) : A P := star (lA P (star Y))

end

end Formalism.FourierDecayAlt.P.Mx6

namespace Formalism.FourierDecayAlt.P.Mx6

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M

noncomputable section

variable (P : Par)

theorem kap_eq (f : Ty P → ℂ) :
    kap P f = Matrix.diagonal fun π => algebraMap ℂ (Pr P.r) (f π) := rfl

theorem kap_mul (f g : Ty P → ℂ) : kap P f * kap P g = kap P (f * g) := (map_mul _ _ _).symm

theorem kap_comm (f g : Ty P → ℂ) : kap P f * kap P g = kap P g * kap P f := by
  rw [kap_mul, kap_mul, mul_comm]

theorem kap_diag (f : Ty P → ℂ) (n : Ty P → Pr P.r) :
    kap P f * Matrix.diagonal n = Matrix.diagonal n * kap P f := by
  rw [kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

theorem kap_sc (f : Ty P → ℂ) (w : Pr P.r) : kap P f * sc P w = sc P w * kap P f := kap_diag P f _

theorem kap_nab (f : Ty P → ℂ) : kap P f * nabA P = nabA P * kap P f := kap_diag P f _

theorem kap_nabs (f : Ty P → ℂ) : kap P f * nabsA P = nabsA P * kap P f := kap_diag P f _

theorem star_kap (f : Ty P → ℂ) : star (kap P f) = kap P (fun π => star (f π)) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext π
  simp only [Pi.star_apply]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, star_smul, star_one]

theorem S_shift (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    kap P g * SS P l = SS P l * kap P f := by
  rw [kap_eq, kap_eq]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hu : Up P l π π'
  · simp only [SS, Matrix.of_apply, if_pos hu, h π π' hu]
    exact (Algebra.commutes _ _)
  · simp [SS, hu]

theorem Ss_shift (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    star (SS P l) * kap P g = kap P f * star (SS P l) := by
  have h1 := S_shift P l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by rw [h π π' hu])
  have h2 := congrArg star h1
  rw [star_mul, star_mul, star_kap, star_kap] at h2
  simpa using h2

theorem S_sc (l : ℕ) (w : Pr P.r) : SS P l * sc P w = sc P w * SS P l := by
  ext π' π
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact (Algebra.commutes _ _)
  · simp

theorem Ss_sc (l : ℕ) (w : Pr P.r) : star (SS P l) * sc P w = sc P w * star (SS P l) := by
  have h2 := congrArg star (S_sc P l (star w))
  rw [star_mul, star_mul, Mx1.star_sc, star_star] at h2
  exact h2.symm

theorem rho_up {l : ℕ} {π π' : Ty P} (h : Up P l π π') {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) :
    (rho P π' i : ℂ) = (rho P π i : ℂ) + if i = l then 1 else 0 := by
  rw [Mx3.rhoUp P l π π' h i hi]
  split_ifs <;> simp

theorem xC_split (π : Ty P) (u : ℂ) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    xC P π u = (u + (rho P π j : ℂ)) * xEx P {j} π u := by
  rw [xC, xEx, Finset.sdiff_singleton_eq_erase]
  exact (Finset.mul_prod_erase _ (fun i => u + (rho P π i : ℂ)) hj).symm

theorem xEx_split (π : Ty P) (u : ℂ) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hlj : j ≠ l) :
    xEx P {l} π u = (u + (rho P π j : ℂ)) * xEx P {l, j} π u := by
  have h1 : Icc 1 (P.k - 1) \ {l, j} = (Icc 1 (P.k - 1) \ {l}).erase j := by
    ext x; simp only [mem_sdiff, mem_insert, mem_singleton, mem_erase]; tauto
  have h2 : j ∈ Icc 1 (P.k - 1) \ {l} := by simp only [mem_sdiff, mem_singleton]; exact ⟨hj, hlj⟩
  rw [xEx, xEx, h1]
  exact (Finset.mul_prod_erase _ (fun i => u + (rho P π i : ℂ)) h2).symm

theorem xEx_up {j : ℕ} {π π' : Ty P} (h : Up P j π π') (ex : Finset ℕ) (hj : j ∈ ex) (u : ℂ) :
    xEx P ex π' u = xEx P ex π u := by
  unfold xEx
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_sdiff.1 hi
  have hne : i ≠ j := fun e => hi'.2 (e ▸ hj)
  rw [rho_up P h hi'.1, if_neg hne, add_zero]

def rr (j : ℕ) (u : ℂ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ))⁻¹

def lam (j : ℕ) (u : ℂ) : A P := kap P (rr P j u) * SS P j

def abelian₂ (u : ℂ) : A P := ∑ j ∈ Icc 1 (P.k - 1), lam P j u

def lams (j : ℕ) (u : ℂ) : A P := star (SS P j) * kap P (rr P j u)

def Lams (u : ℂ) : A P := ∑ j ∈ Icc 1 (P.k - 1), lams P j u

theorem lA_eq (u : ℂ) : lA P u = l0A P u + ggiA P * abelian₂ P u := rfl

theorem star_Lam (u : ℂ) : star (abelian₂ P (star u)) = Lams P u := by
  unfold abelian₂ Lams lam lams
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul, star_kap]
  congr 2
  funext π
  simp [rr]

theorem good0 {u : ℂ} (h : Good P u) (π : Ty P) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    u + (rho P π j : ℂ) ≠ 0 := by simpa using h π j hj 0 (by decide)
theorem good1 {u : ℂ} (h : Good P u) (π : Ty P) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    u + (rho P π j : ℂ) + 1 ≠ 0 := by simpa using h π j hj 1 (by decide)
theorem goodm1 {u : ℂ} (h : Good P u) (π : Ty P) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    u + (rho P π j : ℂ) - 1 ≠ 0 := by simpa [sub_eq_add_neg] using h π j hj (-1) (by decide)

theorem good_star {u : ℂ} (h : Good P u) : Good P (star u) := by
  intro π j hj n hn h0
  apply h π j hj n hn
  have := congrArg star h0
  simpa using this

theorem xC_ne {u : ℂ} (h : Good P u) (π : Ty P) : xC P π u ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hj => good0 P h π hj

theorem coordinate_shift_ne_zero {u : ℂ} (h : Good P u) (π : Ty P) : xC P π (u + 1) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j hj => by
    have := good1 P h π hj
    intro h0; apply this; rw [← h0]; ring

end

end Formalism.FourierDecayAlt.P.Mx6

namespace Formalism.FourierDecayAlt.P.Mx6
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem lc {a b : B} (h : a * b = b * a) (x : B) : a * (b * x) = b * (a * x) := by
  rw [← mul_assoc, h, mul_assoc]

theorem lc1 {a b : B} (h : a * b = 1) (x : B) : a * (b * x) = x := by
  rw [← mul_assoc, h, one_mul]

theorem lcs {a b p q : B} (h : a * b = b * a - p * q) (x : B) : a * (b * x) = b * (a * x) - p * (q * x) := by
  rw [← mul_assoc, h, sub_mul, mul_assoc, mul_assoc]

theorem lca {a b p q : B} (h : a * b = b * a + p * q) (x : B) : a * (b * x) = b * (a * x) + p * (q * x) := by
  rw [← mul_assoc, h, add_mul, mul_assoc, mul_assoc]

theorem commutator_identity_one (N c g G X L L' : B) (α β : ℂ)
    (hNg : N * g = g * N + g * c) (hNX : N * X = X * N)
    (hgG : g * G = 1) (hGg : G * g = 1) (hcg : c * g = g * c)
    (hXg : X * g = g * X) (hXG : X * G = G * X) (hXc : X * c = c * X)
    (hLg : L * g = g * L) (hLg' : L' * g = g * L')
    (h1 : (α - β) • (X * L' - L' * X) = -(X * (L - L'))) :
    (α - β) • (g * X * (-N - β • c + G * L') - (-N - β • c + G * L') * (g * X)) =
      -(g * X * ((-N - α • c + G * L) - (-N - β • c + G * L'))) := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNg, lca hNg, hNX, lc hNX, hgG, lc1 hgG, hGg, lc1 hGg, hcg, lc hcg,
    hXg, lc hXg, hXG, lc hXG, hXc, lc hXc, hLg, lc hLg, hLg', lc hLg'] at h1 ⊢
  linear_combination (norm := module) h1

theorem commutator_identity_two (N c G X L L' : B) (α β q : ℂ)
    (hNG : N * G = G * N - c * G) (hNX : N * X = X * N)
    (hGc : G * c = c * G)
    (hXG : X * G = G * X) (hXc : X * c = c * X)
    (hLG : L * G = G * L) (hLG' : L' * G = G * L')
    (h1 : (α - β) • (X * L' - L' * X) = X * (L - L')) :
    (α - β) • (q • (G * X) * (-N - β • c + G * L') - (-N - β • c + G * L') * (q • (G * X))) =
      q • (G * X) * ((-N - α • c + G * L) - (-N - β • c + G * L')) := by
  have h1' := congrArg (fun x => q • (G * (G * x))) h1
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNG, lcs hNG, hNX, lc hNX, hGc, lc hGc,
    hXG, lc hXG, hXc, lc hXc, hLG, lc hLG, hLG', lc hLG'] at h1' ⊢
  linear_combination (norm := module) h1'

theorem raising_pair_relation (N c G L L' : B) (α β : ℂ)
    (hNc : N * c = c * N - c * c) (hNG : N * G = G * N - c * G)
    (hNL : N * L = L * N - c * L) (hNL' : N * L' = L' * N - c * L')
    (hGc : G * c = c * G) (hLc : L * c = c * L) (hLc' : L' * c = c * L')
    (hLG : L * G = G * L) (hLG' : L' * G = G * L')
    (h3 : (α - β) • (L * L' - L' * L) = (L - L') * (L - L')) :
    (α - β) • ((-N - α • c + G * L) * (-N - β • c + G * L') - (-N - β • c + G * L') * (-N - α • c + G * L)) =
      ((-N - α • c + G * L) - (-N - β • c + G * L')) * ((-N - α • c + G * L) - (-N - β • c + G * L')) := by
  have h3' := congrArg (fun x => G * (G * x)) h3
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNc, lcs hNc, hNG, lcs hNG, hNL, hNL', hGc, lc hGc, hLc, lc hLc,
    hLc', lc hLc', hLG, lc hLG, hLG', lc hLG'] at h3' ⊢
  linear_combination (norm := module) h3'

theorem commutator_identity_four (N Ns c cz G K Ls L' : B) (α β t : ℂ)
    (hcurv : Ns * N = N * Ns + K * (G * G))
    (hNsc : Ns * c = c * Ns + t • (G * G)) (hNcz : N * cz = cz * N - t • (G * G))
    (hNG : N * G = G * N - c * G) (hNsG : Ns * G = G * Ns + cz * G)
    (hNsL' : Ns * L' = L' * Ns - cz * L') (hNLs : N * Ls = Ls * N + c * Ls)
    (hGc : G * c = c * G) (hGcz : G * cz = cz * G) (hczc : cz * c = c * cz)
    (hLc' : L' * c = c * L') (hLcz' : L' * cz = cz * L') (hLG' : L' * G = G * L')
    (hLsc : Ls * c = c * Ls) (hLscz : Ls * cz = cz * Ls) (hLsG : Ls * G = G * Ls) :
    (-Ns - α • cz + G * Ls) * (-N - β • c + G * L') - (-N - β • c + G * L') * (-Ns - α • cz + G * Ls) =
      K * (G * G) + ((α + β) * t) • (G * G) + G * (G * (Ls * L' - L' * Ls)) := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hcurv, hNsc, hNcz, hNG, lcs hNG, hNsG, lca hNsG, hNsL', hNLs,
    hGc, lc hGc, hGcz, lc hGcz, hczc, lc hczc, hLc', lc hLc', hLcz', lc hLcz', hLG', lc hLG',
    hLsc, lc hLsc, hLscz, lc hLscz, hLsG, lc hLsG]
  module

theorem diagonal_lowering_absorb (g G X l0 L : B) (hgG : g * G = 1) (hXG : X * G = G * X) :
    g * X * (l0 + G * L) = g * X * l0 + X * L := by
  simp only [mul_add, mul_assoc, lc hXG, lc1 hgG]

theorem raising_operator_absorb (Ns cz g G X Ls : B) (α : ℂ)
    (hNsg : Ns * g = g * Ns - g * cz) (hNsX : Ns * X = X * Ns) (hGg : G * g = 1) (hczg : cz * g = g * cz)
    (hczX : cz * X = X * cz) (hLsg : Ls * g = g * Ls) :
    (-Ns - α • cz + G * Ls) * (g * X) = g * X * (-Ns - (α - 1) • cz) + Ls * X := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNsg, lcs hNsg, hNsX, hGg, lc1 hGg, hczg, lc hczg, hczX, hLsg, lc hLsg]
  module

end Formalism.FourierDecayAlt.P.Mx6

namespace Formalism.FourierDecayAlt.P.Mx6.GA

section Gauss

variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem solve_right {D : ℂ} (hD : D ≠ 0) {x y z : B} (h : D • (x - y) = z) : y = x - D⁻¹ • z := by
  rw [← h, smul_smul, inv_mul_cancel₀ hD, one_smul]; abel

theorem solve_left {D : ℂ} (hD : D ≠ 0) {x y z : B} (h : D • (x - y) = z) : x = y + D⁻¹ • z := by
  rw [← h, smul_smul, inv_mul_cancel₀ hD, one_smul]; abel

theorem assoc_var {a b R : B} (h : a * b = R) (x : B) : a * (b * x) = R * x := by
  rw [← mul_assoc, h]

theorem mul_assoc_four_right {a b c e R : B} (h : a * (b * (c * e)) = R) (x : B) : a * (b * (c * (e * x))) = R * x := by
  rw [← h]; simp only [mul_assoc]

theorem gauss_rtt (D : ℂ) (hD0 : D ≠ 0) (hD1 : D ≠ 1) (hD2 : D ≠ -1) (τ τ' d d' l l' m m' : B)
    (c1 : τ' * τ = τ * τ') (c2 : d' * d = d * d') (c3 : d' * τ = τ * d') (c4 : d * τ' = τ' * d)
    (D1 : D • (τ * l' - l' * τ) = -(τ * (l - l'))) (D1s : D • (τ' * l - l * τ') = -(τ' * (l - l')))
    (D2 : D • (d * l' - l' * d) = d * (l - l')) (D2s : D • (d' * l - l * d') = d' * (l - l'))
    (E1 : D • (τ * m' - m' * τ) = (m - m') * τ) (TwistedContraction : D • (τ' * m - m * τ') = (m - m') * τ')
    (E2 : D • (d * m' - m' * d) = -((m - m') * d)) (E2VanishingOtherColumns : D • (d' * m - m * d') = -((m - m') * d'))
    (D3 : D • (l * l' - l' * l) = (l - l') * (l - l')) (E3 : D • (m * m' - m' * m) = -((m - m') * (m - m')))
    (D4 : D • (τ' * m * l' * τ - τ' * l' * m * τ) = d' * τ - τ' * d)
    (D4s : D • (τ * m' * l * τ' - τ * l * m' * τ') = τ * d' - d * τ') :
    ∀ i j k n : Fin 2,
      D • ((!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i j *
            (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k n -
          (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k n *
            (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i j) =
        (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) k j *
            (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) i n -
          (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k j *
            (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i n := by
  have hm1 : D - 1 ≠ 0 := sub_ne_zero.mpr hD1
  have hp1 : D + 1 ≠ 0 := by intro h; exact hD2 (by linear_combination h)
  have r1 : l' * τ = τ * l' - D⁻¹ • -(τ * (l - l')) := solve_right hD0 D1
  have r2 : l * τ' = τ' * l - D⁻¹ • -(τ' * (l - l')) := solve_right hD0 D1s
  have r3 : l' * d = d * l' - D⁻¹ • (d * (l - l')) := solve_right hD0 D2
  have r4 : l * d' = d' * l - D⁻¹ • (d' * (l - l')) := solve_right hD0 D2s
  have r5 : τ * m' = m' * τ + D⁻¹ • ((m - m') * τ) := solve_left hD0 E1
  have r6 : τ' * m = m * τ' + D⁻¹ • ((m - m') * τ') := solve_left hD0 TwistedContraction
  have r7 : d * m' = m' * d + D⁻¹ • -((m - m') * d) := solve_left hD0 E2
  have r8 : d' * m = m * d' + D⁻¹ • -((m - m') * d') := solve_left hD0 E2VanishingOtherColumns
  have s1 : τ' * (l' * (m * τ)) = τ' * (m * (l' * τ)) - D⁻¹ • (d' * τ - τ' * d) := by
    have := solve_right hD0 D4
    simpa only [mul_assoc] using this
  have s2 : τ * (l * (m' * τ')) = τ * (m' * (l * τ')) - D⁻¹ • (τ * d' - d * τ') := by
    have := solve_right hD0 D4s
    simpa only [mul_assoc] using this
  have o1 : l' * l = (D - 1)⁻¹ • ((D + 1) • (l * l') - l * l - l' * l') := by
    have h : (D - 1) • (l' * l) = (D + 1) • (l * l') - l * l - l' * l' := by
      have h2 : D • (l * l') - D • (l' * l) = l * l - l * l' - l' * l + l' * l' := by
        rw [← smul_sub, D3]; noncomm_ring
      rw [sub_smul, add_smul, one_smul, one_smul]
      have h3 : D • (l' * l) = D • (l * l') - (l * l - l * l' - l' * l + l' * l') := by rw [← h2]; abel
      rw [h3]; abel
    rw [← h, smul_smul, inv_mul_cancel₀ hm1, one_smul]
  have o2 : m' * m = (D + 1)⁻¹ • ((D - 1) • (m * m') + m * m + m' * m') := by
    have h : (D + 1) • (m' * m) = (D - 1) • (m * m') + m * m + m' * m' := by
      have h2 : D • (m * m') - D • (m' * m) = -(m * m - m * m' - m' * m + m' * m') := by
        rw [← smul_sub, E3]; noncomm_ring
      rw [sub_smul, add_smul, one_smul, one_smul]
      have h3 : D • (m' * m) = D • (m * m') + (m * m - m * m' - m' * m + m' * m') := by
        have : D • (m' * m) = D • (m * m') - (D • (m * m') - D • (m' * m)) := by abel
        rw [this, h2]; abel
      rw [h3]; abel
    rw [← h, smul_smul, inv_mul_cancel₀ hp1, one_smul]
  intro i j k n
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases n <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, smul_add, smul_sub, smul_neg, smul_smul,
    smul_mul_assoc, mul_smul_comm, mul_assoc,
    s1, s2, mul_assoc_four_right s1, mul_assoc_four_right s2,
    r1, r2, r3, r4, r5, r6, r7, r8, assoc_var r1, assoc_var r2, assoc_var r3, assoc_var r4,
    assoc_var r5, assoc_var r6, assoc_var r7, assoc_var r8, o1, o2, assoc_var o1, assoc_var o2,
    c1, c2, c3, c4, assoc_var c1, assoc_var c2, assoc_var c3, assoc_var c4]
  all_goals (match_scalars <;> field_simp <;> ring)

end Gauss

end Formalism.FourierDecayAlt.P.Mx6.GA

namespace Formalism.FourierDecayAlt.P.Mx6.WB

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt

noncomputable section

def pX (I : Finset ℕ) (ρ : ℕ → ℂ) : ℂ[X] := ∏ i ∈ I, (X + C (ρ i))

theorem pX_eval (I : Finset ℕ) (ρ : ℕ → ℂ) (u : ℂ) : (pX I ρ).eval u = ∏ i ∈ I, (u + ρ i) := by
  simp [pX, eval_prod]

theorem pX_erase (I : Finset ℕ) (ρ : ℕ → ℂ) {l : ℕ} (hl : l ∈ I) :
    pX I ρ = (X + C (ρ l)) * pX (I.erase l) ρ := by
  unfold pX; exact (Finset.mul_prod_erase I _ hl).symm

theorem pX_monic (I : Finset ℕ) (ρ : ℕ → ℂ) : (pX I ρ).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

theorem pX_natDegree (I : Finset ℕ) (ρ : ℕ → ℂ) : (pX I ρ).natDegree = I.card := by
  unfold pX; rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]; simp

theorem pX_nextCoeff (I : Finset ℕ) (ρ : ℕ → ℂ) : (pX I ρ).nextCoeff = ∑ i ∈ I, ρ i := by
  unfold pX; rw [Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C _)]; simp

def W1 (I : Finset ℕ) (ρ : ℕ → ℂ) (q w : ℂ[X]) (N : ℕ → ℂ) : Prop :=
  w * pX I (fun i => ρ i + 1) = q + ∑ l ∈ I, C (N l) * (pX (I.erase l) ρ * pX (I.erase l) (fun i => ρ i + 1))

theorem W1.eval {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (h : W1 I ρ q w N) (u : ℂ) :
    w.eval u * ∏ i ∈ I, (u + (ρ i + 1)) = q.eval u +
      ∑ l ∈ I, N l * ((∏ j ∈ I.erase l, (u + ρ j)) * ∏ j ∈ I.erase l, (u + (ρ j + 1))) := by
  have := congrArg (Polynomial.eval u) h
  simpa [eval_finsetSum, pX_eval] using this

theorem rootA {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) {l : ℕ} (hl : l ∈ I)
    (hE1 : ∏ j ∈ I.erase l, (ρ j - ρ l + 1) ≠ 0)
    (hNd : Nd l * ((∏ j ∈ I.erase l, (ρ j - ρ l + 1)) * ∏ j ∈ I.erase l, (ρ j - ρ l)) = -(q.eval (-ρ l))) :
    w.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
  have h1 := h.eval (-ρ l)
  rw [← Finset.mul_prod_erase I _ hl, Finset.sum_eq_single l] at h1
  · have e1 : ∏ j ∈ I.erase l, (-ρ l + (ρ j + 1)) = ∏ j ∈ I.erase l, (ρ j - ρ l + 1) :=
      Finset.prod_congr rfl (fun j _ => by ring)
    have e2 : ∏ j ∈ I.erase l, (-ρ l + ρ j) = ∏ j ∈ I.erase l, (ρ j - ρ l) :=
      Finset.prod_congr rfl (fun j _ => by ring)
    rw [e1, e2] at h1
    apply mul_right_cancel₀ hE1
    linear_combination h1 + hNd
  · intro m _ hml
    have : ∏ j ∈ I.erase m, (-ρ l + ρ j) = 0 :=
      Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)
    rw [this]; simp
  · intro h; exact absurd hl h

theorem rootB {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (h : W1 I ρ q w N)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {l j0 : ℕ} (hl : l ∈ I) (hj0 : j0 ∈ I) (hne : j0 ≠ l)
    (hρ : ρ j0 + 1 = ρ l) (hq : (X + C (ρ l)) ^ 2 ∣ q) (hN0 : N j0 = 0) :
    w.eval (-ρ l) = N l * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
  set ρ1 : ℕ → ℂ := fun i => ρ i + 1 with hρ1
  have hx1 : pX I ρ1 = (X + C (ρ l)) * pX (I.erase j0) ρ1 := by
    rw [pX_erase I ρ1 hj0, hρ1]; simp only [hρ]
  have hF : pX (I.erase j0) ρ1 = (X + C (ρ l + 1)) * pX ((I.erase j0).erase l) ρ1 :=
    pX_erase _ _ (Finset.mem_erase.2 ⟨hne.symm, hl⟩)
  have hE : pX (I.erase l) ρ1 = (X + C (ρ l)) * pX ((I.erase j0).erase l) ρ1 := by
    rw [pX_erase (I.erase l) ρ1 (Finset.mem_erase.2 ⟨hne, hj0⟩), Finset.erase_right_comm, hρ1]; simp only [hρ]
  have hdiv : (X + C (ρ l)) ^ 2 ∣ q + ∑ m ∈ I.erase l, C (N m) * (pX (I.erase m) ρ * pX (I.erase m) ρ1) := by
    refine dvd_add hq (Finset.dvd_sum fun m hm => ?_)
    by_cases hm0 : m = j0
    · rw [hm0, hN0]; simp
    · have hm' := Finset.mem_erase.1 hm
      rw [pX_erase (I.erase m) ρ (Finset.mem_erase.2 ⟨fun e => hm'.1 e.symm, hl⟩),
        pX_erase (I.erase m) ρ1 (Finset.mem_erase.2 ⟨fun e => hm0 e.symm, hj0⟩)]
      have : (ρ1 j0) = ρ l := hρ
      rw [this]
      exact ⟨C (N m) * (pX ((I.erase m).erase l) ρ * pX ((I.erase m).erase j0) ρ1), by ring⟩
  obtain ⟨Aq, hA⟩ := hdiv
  have h2 : w * pX I ρ1 = (q + ∑ m ∈ I.erase l, C (N m) * (pX (I.erase m) ρ * pX (I.erase m) ρ1)) +
      C (N l) * (pX (I.erase l) ρ * pX (I.erase l) ρ1) := by
    have := h
    unfold W1 at this
    rw [this, ← Finset.add_sum_erase I _ hl]; ring
  rw [hA, hx1, hE] at h2
  have h3 : w * pX (I.erase j0) ρ1 = (X + C (ρ l)) * Aq + C (N l) * (pX (I.erase l) ρ * pX ((I.erase j0).erase l) ρ1) := by
    apply mul_left_cancel₀ (monic_X_add_C (ρ l)).ne_zero
    linear_combination h2
  rw [hF] at h3
  have h4 := congrArg (Polynomial.eval (-ρ l)) h3
  simp only [eval_mul, eval_add, eval_X, eval_C, pX_eval] at h4
  have hG : ∏ j ∈ (I.erase j0).erase l, (-ρ l + ρ1 j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj h0
    have hj' := Finset.mem_erase.1 hj
    have hj'' := Finset.mem_erase.1 hj'.2
    apply hj''.1
    apply hinj j hj''.2 j0 hj0
    have : ρ1 j = ρ j + 1 := rfl
    rw [this] at h0
    linear_combination h0 - hρ
  have e2 : ∏ j ∈ I.erase l, (-ρ l + ρ j) = ∏ j ∈ I.erase l, (ρ j - ρ l) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [e2] at h4
  apply mul_right_cancel₀ hG
  linear_combination h4

theorem add_low {p r : ℂ[X]} (hp : p.Monic) (hr : r.natDegree + 1 < p.natDegree) :
    (p + r).Monic ∧ (p + r).natDegree = p.natDegree ∧ (p + r).nextCoeff = p.nextCoeff := by
  have hd : (p + r).natDegree = p.natDegree := natDegree_add_eq_left_of_natDegree_lt (by omega)
  refine ⟨hp.add_of_left (degree_lt_degree (by omega)), hd, ?_⟩
  rw [nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), hd, coeff_add,
    coeff_eq_zero_of_natDegree_lt (p := r) (by omega), add_zero]

theorem pX_dvd {I : Finset ℕ} {ρ : ℕ → ℂ} (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {R : ℂ[X]}
    (hR : ∀ l ∈ I, R.eval (-ρ l) = 0) : pX I ρ ∣ R := by
  unfold pX
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    show IsCoprime (X + C (ρ i)) (X + C (ρ j))
    have e : ∀ a : ℂ, (X + C a : ℂ[X]) = X - C (-a) := by intro a; simp
    rw [e, e]
    apply isCoprime_X_sub_C_of_isUnit_sub
    apply IsUnit.mk0
    intro h0
    exact hij (hinj i hi j hj (by linear_combination -h0))
  · intro l hl
    have e : (X + C (ρ l) : ℂ[X]) = X - C (-(ρ l)) := by rw [C_neg, sub_neg_eq_add]
    rw [e, dvd_iff_isRoot, IsRoot.def]
    exact hR l hl

theorem quad {I : Finset ℕ} {ρ : ℕ → ℂ} (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {q1 w : ℂ[X]} (hq1 : q1.Monic)
    (hdeg : q1.natDegree = 2 * I.card + 2) {c : ℂ} (hc : c ≠ 0) {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ (C c * q1) w N)
    (hroot : ∀ l ∈ I, w.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l)) :
    ∃ c0 : ℂ, ∀ u : ℂ, w.eval u = (∏ i ∈ I, (u + ρ i)) *
      (c * (u ^ 2 + (q1.nextCoeff - ∑ i ∈ I, (ρ i + 1) - ∑ i ∈ I, ρ i) * u) + c0) +
      ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) := by
  set ρ1 : ℕ → ℂ := fun i => ρ i + 1 with hρ1
  set S1 : ℂ[X] := ∑ l ∈ I, C (N l) * (pX (I.erase l) ρ * pX (I.erase l) ρ1) with hS1
  set S2 : ℂ[X] := ∑ l ∈ I, C (N l - Nd l) * pX (I.erase l) ρ with hS2
  have hcc : (C c⁻¹ * C c : ℂ[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have dS1 : (C c⁻¹ * S1).natDegree ≤ I.card + I.card := by
    refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun l _ => ?_)
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    rw [pX_natDegree, pX_natDegree]
    exact add_le_add (Finset.card_erase_le) (Finset.card_erase_le)
  have dS2 : (-(C c⁻¹ * S2)).natDegree ≤ I.card := by
    rw [natDegree_neg]
    refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun l _ => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [pX_natDegree]
    exact Finset.card_erase_le
  have hM : (C c⁻¹ * w) * pX I ρ1 = q1 + C c⁻¹ * S1 := by
    have := h
    unfold W1 at this
    calc (C c⁻¹ * w) * pX I ρ1 = C c⁻¹ * (w * pX I ρ1) := by ring
      _ = C c⁻¹ * (C c * q1 + S1) := by rw [this]
      _ = (C c⁻¹ * C c) * q1 + C c⁻¹ * S1 := by ring
      _ = q1 + C c⁻¹ * S1 := by rw [hcc, one_mul]
  obtain ⟨m1, m2, m3⟩ := add_low (p := q1) (r := C c⁻¹ * S1) hq1 (by omega)
  rw [← hM] at m1 m2 m3
  have hw1 : (C c⁻¹ * w).Monic := Monic.of_mul_monic_right (pX_monic I ρ1) m1
  rw [hw1.natDegree_mul (pX_monic I ρ1), pX_natDegree] at m2
  rw [hw1.nextCoeff_mul (pX_monic I ρ1), pX_nextCoeff] at m3
  obtain ⟨r1, r2, r3⟩ := add_low (p := C c⁻¹ * w) (r := -(C c⁻¹ * S2)) hw1 (by omega)
  have hdvd : pX I ρ ∣ C c⁻¹ * w + -(C c⁻¹ * S2) := by
    apply pX_dvd hinj
    intro l hl
    have : S2.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
      rw [hS2, eval_finsetSum, Finset.sum_eq_single l]
      · rw [eval_mul, eval_C, pX_eval]
        congr 1
        exact Finset.prod_congr rfl (fun j _ => by ring)
      · intro m _ hml
        rw [eval_mul, eval_C, pX_eval, Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)]
        simp
      · intro h; exact absurd hl h
    simp only [eval_add, eval_neg, eval_mul, eval_C, this, hroot l hl]
    ring
  obtain ⟨Q, hQ⟩ := hdvd
  rw [hQ] at r1 r2 r3
  have hQm : Q.Monic := Monic.of_mul_monic_left (pX_monic I ρ) r1
  rw [(pX_monic I ρ).natDegree_mul hQm, pX_natDegree] at r2
  rw [(pX_monic I ρ).nextCoeff_mul hQm, pX_nextCoeff] at r3
  have hQd : Q.natDegree = 2 := by omega
  have hQ2 : Q.coeff 2 = 1 := by rw [← hQd]; exact hQm
  have hQ1 : Q.coeff 1 = Q.nextCoeff := by rw [nextCoeff_of_natDegree_pos (by omega), hQd]
  refine ⟨c * Q.coeff 0, fun u => ?_⟩
  have hQe : Q.eval u = Q.coeff 0 + Q.nextCoeff * u + u ^ 2 := by
    rw [eval_eq_sum_range, hQd]
    simp [Finset.sum_range_succ, hQ2, hQ1]
  have hS2e : S2.eval u = ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) := by
    rw [hS2, eval_finsetSum]
    exact Finset.sum_congr rfl (fun l _ => by rw [eval_mul, eval_C, pX_eval])
  have h5 := congrArg (Polynomial.eval u) hQ
  simp only [eval_add, eval_neg, eval_mul, eval_C, pX_eval, hQe, hS2e] at h5
  rw [← hS2e] at h5 ⊢
  have hn : Q.nextCoeff = q1.nextCoeff - ∑ i ∈ I, (ρ i + 1) - ∑ i ∈ I, ρ i := by
    have : ∑ i ∈ I, ρ1 i = ∑ i ∈ I, (ρ i + 1) := rfl
    rw [this] at m3
    linear_combination r3 + m3
  rw [← hn]
  have : w.eval u = c * (c⁻¹ * w.eval u) := by field_simp
  rw [this]
  have h6 : c⁻¹ * w.eval u = (∏ i ∈ I, (u + ρ i)) * (Q.coeff 0 + Q.nextCoeff * u + u ^ 2) + c⁻¹ * S2.eval u := by
    linear_combination h5
  rw [h6]
  field_simp
  ring

theorem absH {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) (Qf : ℂ → ℂ)
    (hw : ∀ u, w.eval u = (∏ i ∈ I, (u + ρ i)) * Qf u + ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j))
    (u : ℂ) (h0 : ∀ i ∈ I, u + ρ i ≠ 0) (h1 : ∀ i ∈ I, u + ρ i + 1 ≠ 0) :
    q.eval u / ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) =
      Qf u + ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) := by
  have hx0 : ∏ i ∈ I, (u + ρ i) ≠ 0 := Finset.prod_ne_zero_iff.2 h0
  have hx1 : ∏ i ∈ I, (u + (ρ i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun i hi => by rw [← add_assoc]; exact h1 i hi)
  have s1 : ∑ l ∈ I, N l * ((∏ j ∈ I.erase l, (u + ρ j)) * ∏ j ∈ I.erase l, (u + (ρ j + 1))) =
      ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) * ∑ l ∈ I, N l / ((u + ρ l) * (u + ρ l + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← Finset.mul_prod_erase I (fun i => u + ρ i) hl, ← Finset.mul_prod_erase I (fun i => u + (ρ i + 1)) hl]
    have a0 := h0 l hl
    have a1 := h1 l hl
    have a2 : u + (ρ l + 1) = u + ρ l + 1 := by ring
    rw [a2]
    field_simp
  have s2 : ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) =
      (∏ i ∈ I, (u + ρ i)) * ∑ l ∈ I, (N l - Nd l) / (u + ρ l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← Finset.mul_prod_erase I (fun i => u + ρ i) hl]
    have a0 := h0 l hl
    field_simp
  have s3 : ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) =
      ∑ l ∈ I, (N l - Nd l) / (u + ρ l) - ∑ l ∈ I, N l / ((u + ρ l) * (u + ρ l + 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have a0 := h0 l hl
    have a1 := h1 l hl
    field_simp
    ring
  have e1 := h.eval u
  rw [s1, hw u, s2] at e1
  rw [div_eq_iff (mul_ne_zero hx0 hx1), s3]
  linear_combination -e1

theorem weighted_sum_difference_identity {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) (c s c0 : ℂ)
    (hw : ∀ u, w.eval u = (∏ i ∈ I, (u + ρ i)) * (c * (u ^ 2 + s * u) + c0) +
      ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j))
    (u v : ℂ) (h0 : ∀ i ∈ I, u + ρ i ≠ 0) (h1 : ∀ i ∈ I, u + ρ i + 1 ≠ 0)
    (k0 : ∀ i ∈ I, v + ρ i ≠ 0) (k1 : ∀ i ∈ I, v + ρ i + 1 ≠ 0) :
    (u - v) * ((u + v + s) * (-c) + ∑ j ∈ I, (N j / ((u + ρ j + 1) * (v + ρ j + 1)) - Nd j / ((u + ρ j) * (v + ρ j)))) =
      q.eval v / ((∏ i ∈ I, (v + ρ i)) * ∏ i ∈ I, (v + (ρ i + 1))) -
      q.eval u / ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) := by
  rw [absH Nd h (fun u => c * (u ^ 2 + s * u) + c0) hw u h0 h1, absH Nd h (fun u => c * (u ^ 2 + s * u) + c0) hw v k0 k1]
  have s4 : (u - v) * ∑ j ∈ I, (N j / ((u + ρ j + 1) * (v + ρ j + 1)) - Nd j / ((u + ρ j) * (v + ρ j))) =
      ∑ l ∈ I, (N l / (v + ρ l + 1) - Nd l / (v + ρ l)) - ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have a0 := h0 l hl
    have a1 := h1 l hl
    have b0 := k0 l hl
    have b1 := k1 l hl
    field_simp
    ring
  linear_combination s4

def rc (P : Par) (π : Ty P) : ℕ → ℂ := fun i => (rho P π i : ℂ)

def q1P (P : Par) : ℂ[X] :=
  ∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))

theorem rc_inj (P : Par) (hP : P.OK) (π : Ty P) :
    ∀ i ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), rc P π i = rc P π j → i = j := by
  intro i hi j hj h
  have h2 : rho P π i = rho P π j := by
    unfold rc at h; exact_mod_cast h
  by_contra hij
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact absurd h2 (ne_of_gt (Mx3.rho_inj P hP π i j hi hj h'))
  · exact absurd h2 (ne_of_lt (Mx3.rho_inj P hP π j i hj hi h'))

theorem weight_model_identity (P : Par) (hP : P.OK) (π : Ty P) :
    W1 (Icc 1 (P.k - 1)) (rc P π) (C (-((P.T : ℂ) * P.T')) * q1P P) (wNum P π /ₘ coordinatePolynomial P π)
      (fun l => ((Nrm P l π : ℝ) : ℂ)) := by
  have := Mx3.wExact P hP π
  unfold W1
  rw [mul_comm]
  exact this.symm

theorem q_polynomial_monic (P : Par) : (q1P P).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))

theorem natDegree_q1_polynomial (P : Par) (hP : P.OK) : (q1P P).natDegree = 2 * (Icc 1 (P.k - 1)).card + 2 := by
  unfold q1P
  rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  have : ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := by
    intro i _
    rw [(monic_X_add_C _).natDegree_mul (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  rw [Finset.sum_congr rfl this]
  have := hP.k_pos
  simp
  omega

theorem q_polynomial_next_coeff (P : Par) :
    (q1P P).nextCoeff = ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) := by
  unfold q1P
  rw [Monic.nextCoeff_prod _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(monic_X_add_C _).nextCoeff_mul (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]

theorem q_eval (P : Par) (u : ℂ) : (C (-((P.T : ℂ) * P.T')) * q1P P).eval u = qC P u := by
  unfold q1P qC
  simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by ring)

theorem model_root (P : Par) (hP : P.OK) (π : Ty P) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    (wNum P π /ₘ coordinatePolynomial P π).eval (-(rc P π l)) = (((Nrm P l π : ℝ) : ℂ) - ((NrmDown P l π : ℝ) : ℂ)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rc P π j - rc P π l) := by
  have hl' := Finset.mem_Icc.1 hl
  by_cases hdeg : ∃ j0 ∈ (Icc 1 (P.k - 1)).erase l, rho P π j0 + 1 = rho P π l
  · obtain ⟨j0, hj0, hρ⟩ := hdeg
    have hj0' := Finset.mem_erase.1 hj0
    have hNd : NrmDown P l π = 0 := by
      unfold NrmDown
      have hz : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1) = 0 :=
        Finset.prod_eq_zero hj0 (by linarith)
      rw [hz, zero_mul, div_zero]
    have hN0 : Nrm P j0 π = 0 := by
      unfold Nrm
      have hz : ∏ j ∈ (Icc 1 (P.k - 1)).erase j0, (rho P π j - rho P π j0 - 1) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun e => hj0'.1 e.symm, hl⟩) (by linarith)
      rw [hz, mul_zero, div_zero]
    have hI := Mx3.tyInterlaces P hP π
    have hlt : l < j0 := by
      by_contra hcon
      have : j0 < l := lt_of_le_of_ne (not_lt.1 hcon) hj0'.1
      have := Mx3.rho_inj P hP π j0 l hj0'.2 hl this
      linarith
    have o := (Mx3.ord P.k P.u P.u' (rho P π) hI l hl).2.2.2 j0 hj0'.2 hlt
    have b := hI l hl
    have hu : P.u (l + 1) = rho P π l - 1 / 2 := by linarith [o.1, b.2.2.1]
    have hu' : P.u' (l + 1) = rho P π l - 1 / 2 := by linarith [o.2, b.2.2.2]
    have hq : (X + C (rc P π l)) ^ 2 ∣ C (-((P.T : ℂ) * P.T')) * q1P P := by
      apply Dvd.dvd.mul_left
      have hm : l + 1 ∈ Icc 1 P.k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hd := Finset.dvd_prod_of_mem
        (fun i => ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))) : ℂ[X])) hm
      have e1 : (1 / 2 + (P.u (l + 1) : ℂ)) = rc P π l := by rw [hu]; unfold rc; push_cast; ring
      have e2 : (1 / 2 + (P.u' (l + 1) : ℂ)) = rc P π l := by rw [hu']; unfold rc; push_cast; ring
      simp only [e1, e2] at hd
      rw [pow_two]
      exact hd
    have := rootB (weight_model_identity P hP π) (rc_inj P hP π) hl hj0'.2 hj0'.1
      (by unfold rc; exact_mod_cast hρ) hq (by simp only [hN0]; simp)
    rw [this, hNd]; simp
  · push Not at hdeg
    have hA1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj h0
      exact hdeg j hj (by linarith)
    have hA0 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj h0
      have hj' := Finset.mem_erase.1 hj
      apply hj'.1
      apply rc_inj P hP π j hj'.2 l hl
      unfold rc
      have : rho P π j = rho P π l := by linarith
      rw [this]
    have hk : NrmDown P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) = -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) := by
      unfold NrmDown
      exact div_mul_cancel₀ _ (mul_ne_zero hA1 hA0)
    have hk' := congrArg (fun x : ℝ => (x : ℂ)) hk
    simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg,
      Complex.ofReal_one] at hk'
    have hA1c : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rc P π j - rc P π l + 1) ≠ 0 := by
      have := hA1
      unfold rc
      intro h0
      apply this
      exact_mod_cast h0
    refine rootA (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) hl hA1c ?_
    rw [q_eval]
    have hr := (Mx3.realPoints P π (-rho P π l)).2
    have e : (((-rho P π l : ℝ)) : ℂ) = -(rc P π l) := by unfold rc; push_cast; ring
    rw [e] at hr
    rw [hr]
    exact hk'

theorem s_eq (P : Par) (hP : P.OK) (π : Ty P) :
    (q1P P).nextCoeff - ∑ i ∈ Icc 1 (P.k - 1), (rc P π i + 1) - ∑ i ∈ Icc 1 (P.k - 1), rc P π i =
      1 + 2 * (aC P π : ℂ) := by
  rw [q_polynomial_next_coeff]
  have e1 : ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      ∑ i ∈ Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ)) + (P.k : ℂ) := by
    rw [Finset.sum_congr rfl (fun i _ => (by ring : (1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ)) =
      ((P.u i : ℂ) + P.u' i) + 1)), Finset.sum_add_distrib]
    simp
  have e2 : ∑ i ∈ Icc 1 (P.k - 1), (rc P π i + 1) = ∑ i ∈ Icc 1 (P.k - 1), rc P π i + ((P.k : ℂ) - 1) := by
    rw [Finset.sum_add_distrib]
    simp [Nat.cast_sub hP.k_pos]
  rw [e1, e2]
  unfold aC rc
  push_cast
  ring

theorem good0 {P : Par} {u : ℂ} (hu : Good P u) (π : Ty P) : ∀ i ∈ Icc 1 (P.k - 1), u + rc P π i ≠ 0 := by
  intro i hi
  have := hu π i hi 0 (by simp)
  simpa [rc] using this

theorem good1 {P : Par} {u : ℂ} (hu : Good P u) (π : Ty P) : ∀ i ∈ Icc 1 (P.k - 1), u + rc P π i + 1 ≠ 0 := by
  intro i hi
  have := hu π i hi 1 (by simp)
  simpa [rc] using this

theorem coordinate_product_eq (P : Par) (π : Ty P) (u : ℂ) : xC P π u = ∏ i ∈ Icc 1 (P.k - 1), (u + rc P π i) := rfl

theorem x_eval_shift_prod (P : Par) (π : Ty P) (u : ℂ) : xC P π (u + 1) = ∏ i ∈ Icc 1 (P.k - 1), (u + (rc P π i + 1)) := by
  unfold xC rc
  exact Finset.prod_congr rfl (fun i _ => by ring)

theorem wC_eq (P : Par) (hP : P.OK) (π : Ty P) (u : ℂ) (hu : Good P u) :
    wC P π u = qC P u / xC P π (u + 1) +
      ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have e1 := (weight_model_identity P hP π).eval u
  have hx1 : ∏ i ∈ Icc 1 (P.k - 1), (u + (rc P π i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun i hi => by rw [← add_assoc]; exact good1 hu π i hi)
  rw [q_eval] at e1
  rw [x_eval_shift_prod]
  show (wNum P π /ₘ coordinatePolynomial P π).eval u = _
  apply mul_right_cancel₀ hx1
  rw [e1, add_mul, div_mul_cancel₀ _ hx1, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [← Finset.mul_prod_erase (Icc 1 (P.k - 1)) (fun i => u + (rc P π i + 1)) hl]
  have a1 := good1 hu π l hl
  have a2 : u + (rc P π l + 1) = u + rc P π l + 1 := by ring
  have a3 : xEx P {l} π u = ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (u + rc P π j) := by
    unfold xEx rc
    rw [Finset.sdiff_singleton_eq_erase]
  have a4 : (rho P π l : ℂ) = rc P π l := rfl
  rw [a2, a3, a4]
  field_simp

theorem scalar_partial_fraction_identity (P : Par) (hP : P.OK) (π : Ty P) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) * ((u + v + 1 + 2 * (aC P π : ℂ)) * (P.TT : ℂ) + ∑ j ∈ Icc 1 (P.k - 1),
      (((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ))))) =
      qC P v / (xC P π v * xC P π (v + 1)) - qC P u / (xC P π u * xC P π (u + 1)) := by
  have hc : -((P.T : ℂ) * P.T') ≠ 0 := by
    have h1 : (P.T : ℂ) ≠ 0 := by exact_mod_cast hP.T_pos.ne'
    have h2 : (P.T' : ℂ) ≠ 0 := by exact_mod_cast hP.T'_pos.ne'
    exact neg_ne_zero.2 (mul_ne_zero h1 h2)
  obtain ⟨c0, hw⟩ := quad (rc_inj P hP π) (q_polynomial_monic P) (natDegree_q1_polynomial P hP) hc
    (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) (model_root P hP π)
  rw [s_eq P hP π] at hw
  have h := weighted_sum_difference_identity (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) _ _ c0 hw u v
    (good0 hu π) (good1 hu π) (good0 hv π) (good1 hv π)
  rw [q_eval, q_eval, ← coordinate_product_eq, ← coordinate_product_eq, ← x_eval_shift_prod, ← x_eval_shift_prod] at h
  rw [← h]
  have hT : (P.TT : ℂ) = (P.T : ℂ) * P.T' := by unfold Par.TT; push_cast; ring
  rw [hT]
  have : ∀ j, (rho P π j : ℂ) = rc P π j := fun _ => rfl
  simp only [this]
  ring

end

end Formalism.FourierDecayAlt.P.Mx6.WB

namespace Formalism.FourierDecayAlt.P.Mx6.PC

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W

noncomputable section

section Poly

variable {B : Type*} [Ring B] [Algebra ℂ B]

def ev (y : ℂ) : B[X] →+* B :=
  Polynomial.eval₂RingHom' (RingHom.id B) (algebraMap ℂ B y) fun a => (Algebra.commutes y a).symm

def IsPoly (f : ℂ → B) : Prop := ∃ p : B[X], ∀ y, f y = ev y p

def IsPolyS (a : ℂ → ℂ) : Prop := ∃ s : ℂ[X], ∀ y, a y = s.eval y

theorem ev_apply (y : ℂ) (p : B[X]) : ev y p = p.eval₂ (RingHom.id B) (algebraMap ℂ B y) := rfl

theorem ev_C (y : ℂ) (b : B) : ev y (C b) = b := by rw [ev_apply, Polynomial.eval₂_C]; rfl

theorem ev_map (y : ℂ) (s : ℂ[X]) : ev y (s.map (algebraMap ℂ B)) = algebraMap ℂ B (s.eval y) := by
  rw [ev_apply, Polynomial.eval₂_map, RingHom.id_comp]
  exact Polynomial.eval₂_at_apply (algebraMap ℂ B) y

theorem IsPoly.const (b : B) : IsPoly fun _ => b := ⟨C b, fun y => (ev_C y b).symm⟩

theorem IsPoly.add {f g : ℂ → B} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun y => f y + g y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun y => by show f y + g y = _; rw [hp, hq, map_add]⟩

theorem IsPoly.sub {f g : ℂ → B} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun y => f y - g y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun y => by show f y - g y = _; rw [hp, hq, map_sub]⟩

theorem IsPoly.neg {f : ℂ → B} (hf : IsPoly f) : IsPoly fun y => -f y := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun y => by show -f y = _; rw [hp, map_neg]⟩

theorem IsPoly.mul {f g : ℂ → B} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun y => f y * g y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun y => by show f y * g y = _; rw [hp, hq, map_mul]⟩

theorem IsPoly.algMap {a : ℂ → ℂ} (ha : IsPolyS a) : IsPoly fun y => algebraMap ℂ B (a y) := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨s.map (algebraMap ℂ B), fun y => by show algebraMap ℂ B (a y) = _; rw [hs, ev_map]⟩

theorem IsPoly.smul {a : ℂ → ℂ} {f : ℂ → B} (ha : IsPolyS a) (hf : IsPoly f) : IsPoly fun y => a y • f y := by
  have := (IsPoly.algMap (B := B) ha).mul hf
  simpa only [Algebra.smul_def] using this

theorem IsPoly.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → B} (hf : ∀ i ∈ s, IsPoly (f i)) :
    IsPoly fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPoly.const (0 : B)
  | insert a s ha ih =>
    have h1 := (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine (funext fun y => ?_ : (fun y => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y) ▸ h1
    rw [Finset.sum_insert ha]

theorem IsPolyS.id : IsPolyS fun y => y := ⟨X, fun y => by simp⟩
theorem IsPolyS.const (c : ℂ) : IsPolyS fun _ => c := ⟨C c, fun y => by simp⟩
theorem IsPolyS.add {a b : ℂ → ℂ} (ha : IsPolyS a) (hb : IsPolyS b) : IsPolyS fun y => a y + b y := by
  obtain ⟨p, hp⟩ := ha; obtain ⟨q, hq⟩ := hb
  exact ⟨p + q, fun y => by show a y + b y = _; rw [hp, hq, eval_add]⟩
theorem IsPolyS.sub {a b : ℂ → ℂ} (ha : IsPolyS a) (hb : IsPolyS b) : IsPolyS fun y => a y - b y := by
  obtain ⟨p, hp⟩ := ha; obtain ⟨q, hq⟩ := hb
  exact ⟨p - q, fun y => by show a y - b y = _; rw [hp, hq, eval_sub]⟩
theorem IsPolyS.prod {ι : Type*} (s : Finset ι) {a : ι → ℂ → ℂ} (ha : ∀ i ∈ s, IsPolyS (a i)) :
    IsPolyS fun y => ∏ i ∈ s, a i y := by
  classical
  choose! p hp using ha
  exact ⟨∏ i ∈ s, p i, fun y => by show ∏ i ∈ s, a i y = _; rw [eval_prod]; exact Finset.prod_congr rfl fun i hi => hp i hi y⟩

theorem IsPoly.dual {f : ℂ → B} (hf : IsPoly f) (φ : Module.Dual ℂ B) : IsPolyS fun y => φ (f y) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨∑ n ∈ p.support, monomial n (φ (p.coeff n)), fun y => ?_⟩
  show φ (f y) = _
  rw [hp, ev_apply]
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def, RingHom.id_apply,
    map_sum, eval_finsetSum, eval_monomial]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem IsPoly.eq_zero {f : ℂ → B} (hf : IsPoly f) (S : Set ℂ) (hS : S.Finite) (h : ∀ y, y ∉ S → f y = 0) (y : ℂ) :
    f y = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨s, hs⟩ := hf.dual φ
  have h0 : s = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot s (Set.Infinite.mono ?_ hS.infinite_compl)
    intro z hz
    show s.eval z = 0
    rw [← hs]
    show φ (f z) = 0
    rw [h z hz, map_zero]
  have h1 : φ (f y) = s.eval y := hs y
  rw [h1, h0, eval_zero]

end Poly

variable (P : Par)

theorem kap_sum (f : Ty P → ℂ) : kap P f = ∑ π, f π • kap P (Pi.single π 1) := by
  conv_lhs => rw [pi_eq_sum_univ' f]
  simp only [map_sum, map_smul]

theorem isPoly_kap {F : Ty P → ℂ → ℂ} (hF : ∀ π, IsPolyS (F π)) : IsPoly fun Y => kap P fun π => F π Y := by
  have : (fun Y => kap P fun π => F π Y) = fun Y => ∑ π, F π Y • kap P (Pi.single π 1) := by
    funext Y; exact kap_sum P _
  rw [this]
  exact IsPoly.sum _ fun π _ => IsPoly.smul (hF π) (IsPoly.const _)

theorem isPolyS_xC (π : Ty P) : IsPolyS fun Y => xC P π Y :=
  IsPolyS.prod _ fun _ _ => IsPolyS.id.add (IsPolyS.const _)

theorem isPolyS_xEx (ex : Finset ℕ) (π : Ty P) : IsPolyS fun Y => xEx P ex π Y :=
  IsPolyS.prod _ fun _ _ => IsPolyS.id.add (IsPolyS.const _)

theorem isPolyS_wC (π : Ty P) : IsPolyS fun Y => wC P π Y := ⟨_, fun _ => rfl⟩

theorem isPoly_xA : IsPoly fun Y => xA P Y := isPoly_kap P (isPolyS_xC P)

theorem isPoly_l0A : IsPoly fun Y => l0A P Y :=
  (IsPoly.const _).sub ((IsPoly.algMap (IsPolyS.id.add (IsPolyS.const _))).mul (IsPoly.const _))

theorem isPoly_m0A : IsPoly fun Y => m0A P Y :=
  (IsPoly.const _).sub ((IsPoly.algMap (IsPolyS.id.sub (IsPolyS.const _))).mul (IsPoly.const _))

theorem isPoly_S21 : IsPoly fun Y => weightedSumBis P Y :=
  IsPoly.sum _ fun l _ => (IsPoly.const _).mul (isPoly_kap P (isPolyS_xEx P {l}))

theorem isPoly_S12 : IsPoly fun Y => S12 P Y :=
  IsPoly.sum _ fun l _ => (isPoly_kap P (isPolyS_xEx P {l})).mul (IsPoly.const _)

theorem isPoly_quartic_sum : IsPoly fun Y => S4 P Y :=
  IsPoly.sum _ fun l _ => IsPoly.sum _ fun j _ => (IsPoly.const _).mul (isPoly_kap P (isPolyS_xEx P {l, j}))

theorem isPoly_diagonal_entry : IsPoly fun Y => t22 P Y := (IsPoly.const _).mul (isPoly_xA P)

theorem isPoly_t21 : IsPoly fun Y => t21 P Y :=
  (((IsPoly.const _).mul (isPoly_xA P)).mul (isPoly_l0A P)).add (isPoly_S21 P)

theorem isPoly_upper_right_entry : IsPoly fun Y => t12 P Y :=
  (((IsPoly.const _).mul (isPoly_xA P)).mul (isPoly_m0A P)).add (isPoly_S12 P)

theorem isPoly_upper_left_entry : IsPoly fun Y => t11 P Y :=
  (((((IsPoly.const _).mul (isPoly_kap P (isPolyS_wC P))).add
    ((((IsPoly.const _).mul (isPoly_xA P)).mul (isPoly_m0A P)).mul (isPoly_l0A P))).add
    ((((IsPoly.const _).mul (isPoly_m0A P)).mul (IsPoly.const _)).mul (isPoly_S21 P))).add
    ((isPoly_S12 P).mul (isPoly_l0A P))).add ((IsPoly.const _).mul (isPoly_quartic_sum P))

theorem isPoly_QQr (i j : Fin 2) : IsPoly fun Y => QQr P Y i j := by
  fin_cases i <;> fin_cases j
  · exact isPoly_upper_left_entry P
  · exact isPoly_upper_right_entry P
  · exact isPoly_t21 P
  · exact isPoly_diagonal_entry P

theorem bad_finite : {Y : ℂ | ¬ Good P Y}.Finite := by
  classical
  refine Set.Finite.subset (Finset.finite_toSet ((Finset.univ : Finset (Ty P)).biUnion fun π =>
    (Icc 1 (P.k - 1)).biUnion fun j => ({-2, -1, 0, 1, 2} : Finset ℤ).image fun n : ℤ => -(rho P π j : ℂ) - (n : ℂ))) ?_
  intro Y hY
  simp only [Set.mem_ofPred_eq, Good, not_forall, not_not] at hY
  obtain ⟨π, j, hj, n, hn, h⟩ := hY
  exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨π, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨j, hj,
    Finset.mem_image.mpr ⟨n, hn, by linear_combination -h⟩⟩⟩)

theorem entries_of_generic
    (h : ∀ u v : ℂ, Good P u → Good P v → u - v ≠ 0 → u - v ≠ 1 → u - v ≠ -1 → ∀ i j k l : Fin 2,
      (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) =
        QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l)
    (u v : ℂ) (i j k l : Fin 2) :
    (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) =
      QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l := by
  set F : ℂ → ℂ → A P := fun u v => (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) -
    (QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l) with hF
  have hu : ∀ v, IsPoly fun u => F u v := fun v =>
    (IsPoly.smul (IsPolyS.id.sub (IsPolyS.const v))
      (((isPoly_QQr P i j).mul (IsPoly.const _)).sub ((IsPoly.const _).mul (isPoly_QQr P i j)))).sub
      (((isPoly_QQr P k j).mul (IsPoly.const _)).sub ((IsPoly.const _).mul (isPoly_QQr P i l)))
  have hv : ∀ u, IsPoly fun v => F u v := fun u =>
    (IsPoly.smul ((IsPolyS.const u).sub IsPolyS.id)
      (((IsPoly.const _).mul (isPoly_QQr P k l)).sub ((isPoly_QQr P k l).mul (IsPoly.const _)))).sub
      (((IsPoly.const _).mul (isPoly_QQr P i l)).sub ((isPoly_QQr P k j).mul (IsPoly.const _)))
  have h1 : ∀ v, Good P v → ∀ u, F u v = 0 := by
    intro v gv
    refine (hu v).eq_zero ({Y : ℂ | ¬ Good P Y} ∪ {v, v + 1, v - 1})
      ((bad_finite P).union (by simp)) ?_
    intro u hu'
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, not_not] at hu'
    obtain ⟨gu, a0, a1, a2⟩ := hu'
    exact sub_eq_zero.mpr (h u v gu gv (fun e => a0 (by linear_combination e)) (fun e => a1 (by linear_combination e))
      (fun e => a2 (by linear_combination e)) i j k l)
  have h2 : F u v = 0 := by
    refine (hv u).eq_zero {Y : ℂ | ¬ Good P Y} (bad_finite P) ?_ v
    intro v' hv'
    simp only [Set.mem_ofPred_eq, not_not] at hv'
    exact h1 v' hv' u
  exact sub_eq_zero.mp h2

section Entries

variable {B : Type} [Ring B]

theorem kronecker_E1_E2_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E1 M * E2 N) (i, k) (j, l) = M i j * N k l := by
  simp [Matrix.mul_apply, E1, E2, Fintype.sum_prod_type]

theorem kronecker_embed_mul_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E2 N * E1 M) (i, k) (j, l) = N k l * M i j := by
  simp [Matrix.mul_apply, E1, E2, Fintype.sum_prod_type]

theorem Pf_mul_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i k : Fin 2) (p : Fin 2 × Fin 2) :
    (Pf B * X) (i, k) p = X (k, i) p := by
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Pf, Fintype.sum_prod_type]

theorem mul_Pf_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (p : Fin 2 × Fin 2) (j l : Fin 2) :
    (X * Pf B) p (j, l) = X p (l, j) := by
  fin_cases j <;> fin_cases l <;> simp [Matrix.mul_apply, Pf, Fintype.sum_prod_type]

end Entries

theorem ofEntries : Formalism.FourierDecayAlt.M.QQRTTOfEntries := by
  intro H P hP Y Y'
  apply Matrix.ext
  rintro ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.smul_apply, Pf_mul_apply, mul_Pf_apply, kronecker_E1_E2_apply, kronecker_E1_E2_apply, kronecker_embed_mul_apply,
    kronecker_embed_mul_apply]
  have h := H P hP Y' Y i j k l
  rw [smul_sub] at h
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact h

end

end Formalism.FourierDecayAlt.P.Mx6.PC

namespace Formalism.FourierDecayAlt.P.Mx6.L3

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M

noncomputable section

variable (P : Par)

theorem comm_term (j : ℕ) (f f' : Ty P → ℂ) (hs : ∀ π π', Up P j π π' → f' π' = f π) (c u v : ℂ)
    (hf : ∀ π, (u - v) * ((f π - f' π) * rr P j v π) = c * (f π * (rr P j u π - rr P j v π))) :
    (u - v) • (kap P f * lam P j v - lam P j v * kap P f) = c • (kap P f * (lam P j u - lam P j v)) := by
  unfold lam
  have e1 : kap P f * (kap P (rr P j v) * SS P j) = kap P (f * rr P j v) * SS P j := by
    rw [← mul_assoc, kap_mul]
  have e2 : (kap P (rr P j v) * SS P j) * kap P f = kap P (rr P j v * f') * SS P j := by
    rw [mul_assoc, ← S_shift P j f f' hs, ← mul_assoc, kap_mul]
  have e3 : kap P f * (kap P (rr P j u) * SS P j - kap P (rr P j v) * SS P j) =
      kap P (f * (rr P j u - rr P j v)) * SS P j := by
    rw [← sub_mul, ← map_sub, ← mul_assoc, kap_mul]
  rw [e1, e2, e3, ← sub_mul, ← map_sub, ← smul_mul_assoc, ← smul_mul_assoc, ← map_smul, ← map_smul]
  congr 2
  funext π
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  linear_combination hf π

theorem comm_sum (f : Ty P → ℂ) (f' : ℕ → Ty P → ℂ) (c u v : ℂ)
    (hs : ∀ j ∈ Icc 1 (P.k - 1), ∀ π π', Up P j π π' → f' j π' = f π)
    (hf : ∀ j ∈ Icc 1 (P.k - 1), ∀ π,
      (u - v) * ((f π - f' j π) * rr P j v π) = c * (f π * (rr P j u π - rr P j v π))) :
    (u - v) • (kap P f * abelian₂ P v - abelian₂ P v * kap P f) = c • (kap P f * (abelian₂ P u - abelian₂ P v)) := by
  unfold abelian₂
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j hj => comm_term P j f (f' j) (hs j hj) c u v (hf j hj)

theorem Lam1 (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (xA P u * abelian₂ P v - abelian₂ P v * xA P u) = -(xA P u * (abelian₂ P u - abelian₂ P v)) := by
  have h := comm_sum P (fun π => xC P π u)
    (fun j π => (u + (rho P π j : ℂ) - 1) * xEx P {j} π u) (-1) u v
    (fun j hj π π' hU => by
      rw [xEx_up P hU {j} (Finset.mem_singleton_self j), rho_up P hU hj, if_pos rfl, xC_split P π u hj]
      ring)
    (fun j hj π => by
      have h1 := good0 P hu π hj
      have h2 := good0 P hv π hj
      simp only [rr]
      rw [xC_split P π u hj]
      field_simp
      ring)
  rw [neg_one_smul] at h
  exact h

theorem Lam2 (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • ((kap P fun π => (xC P π (u + 1))⁻¹) * abelian₂ P v -
      abelian₂ P v * (kap P fun π => (xC P π (u + 1))⁻¹)) =
      (kap P fun π => (xC P π (u + 1))⁻¹) * (abelian₂ P u - abelian₂ P v) := by
  have h := comm_sum P (fun π => (xC P π (u + 1))⁻¹)
    (fun j π => (u + (rho P π j : ℂ) + 1) * (u + (rho P π j : ℂ))⁻¹ * (xC P π (u + 1))⁻¹) 1 u v
    (fun j hj π π' hU => by
      have h0 := good0 P hu π' hj
      have h1 := good1 P hu π' hj
      rw [xC_split P π' (u + 1) hj, xC_split P π (u + 1) hj,
        xEx_up P hU {j} (Finset.mem_singleton_self j), mul_inv, mul_inv]
      rw [rho_up P hU hj, if_pos rfl] at h0 h1 ⊢
      generalize (xEx P {j} π (u + 1))⁻¹ = Ei
      have h2 : u + 1 + ((rho P π j : ℂ) + 1) ≠ 0 := by intro h; apply h1; rw [← h]; ring
      have h3 : u + 1 + (rho P π j : ℂ) ≠ 0 := by intro h; apply h0; rw [← h]; ring
      field_simp
      ring)
    (fun j hj π => by
      have h1 := good0 P hu π hj
      have h2 := good0 P hv π hj
      simp only [rr]
      generalize (xC P π (u + 1))⁻¹ = Xi
      field_simp
      ring)
  rw [one_smul] at h
  exact h

def sh (i j : ℕ) (b : ℂ) : Ty P → ℂ := fun π => (b + (rho P π j : ℂ) - if j = i then 1 else 0)⁻¹

theorem lam_mul (i : ℕ) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (a b : ℂ) :
    lam P i a * lam P j b = kap P (rr P i a * sh P i j b) * (SS P i * SS P j) := by
  have h := S_shift P i (rr P j b) (sh P i j b) (fun π π' hU => by
    simp only [sh, rr]
    rw [rho_up P hU hj]
    congr 1
    ring)
  unfold lam
  calc kap P (rr P i a) * SS P i * (kap P (rr P j b) * SS P j)
      = kap P (rr P i a) * (SS P i * kap P (rr P j b)) * SS P j := by simp only [mul_assoc]
    _ = kap P (rr P i a) * (kap P (sh P i j b) * SS P i) * SS P j := by rw [h]
    _ = _ := by rw [← kap_mul]; simp only [mul_assoc]

def ee (i j : ℕ) (u v : ℂ) : Ty P → ℂ :=
  (u - v) • (rr P i u * sh P i j v - rr P i v * sh P i j u) -
    (rr P i u * sh P i j u - rr P i u * sh P i j v - (rr P i v * sh P i j u - rr P i v * sh P i j v))

def FF (i j : ℕ) (u v : ℂ) : A P :=
  (u - v) • (lam P i u * lam P j v - lam P i v * lam P j u) -
    (lam P i u - lam P i v) * (lam P j u - lam P j v)

theorem FF_eq (i : ℕ) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (u v : ℂ) :
    FF P i j u v = kap P (ee P i j u v) * (SS P i * SS P j) := by
  unfold FF ee
  simp only [sub_mul, mul_sub, lam_mul P _ hj, map_sub, map_smul, smul_mul_assoc]
  abel

theorem ee_diag {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    ee P i i u v = 0 := by
  funext π
  have h1 := good0 P hu π hi
  have h2 := good0 P hv π hi
  have h3 := goodm1 P hu π hi
  have h4 := goodm1 P hv π hi
  simp only [ee, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.zero_apply, if_true]
  field_simp
  ring

def cc (i j : ℕ) (u v : ℂ) : Ty P → ℂ := fun π =>
  -((u - v) ^ 2) * (rr P i u π * rr P i v π * rr P j u π * rr P j v π)

theorem ee_off_diagonal_first {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    ee P i j u v = cc P i j u v * fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1 := by
  funext π
  have h1 := good0 P hu π hi
  have h2 := good0 P hv π hi
  have h3 := good0 P hu π hj
  have h4 := good0 P hv π hj
  simp only [ee, cc, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, if_neg hne, sub_zero]
  field_simp
  ring

theorem ee_off_diagonal_second {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    ee P j i u v = -(cc P i j u v * fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) := by
  funext π
  have h1 := good0 P hu π hi
  have h2 := good0 P hv π hi
  have h3 := good0 P hu π hj
  have h4 := good0 P hv π hj
  simp only [ee, cc, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.neg_apply, smul_eq_mul,
    if_neg hne.symm, sub_zero]
  field_simp
  ring

theorem comm_tgt (hC : SSComm) (hP : P.OK) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i) :
    (kap P fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) * (SS P j * SS P i) =
      (kap P fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1) * (SS P i * SS P j) := by
  have h := hC P hP i hi j hj hne
  have a1 := S_shift P i (fun π => ((rho P π j - rho P π i - 1 : ℝ) : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne, if_pos rfl]
      push_cast
      ring)
  have a2 := S_shift P j (fun π => (rho P π j : ℂ) - (rho P π i : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne.symm, if_pos rfl]
      ring)
  have b1 := S_shift P j (fun π => ((rho P π j - rho P π i + 1 : ℝ) : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne.symm, if_pos rfl]
      push_cast
      ring)
  have b2 := S_shift P i (fun π => (rho P π j : ℂ) - (rho P π i : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne, if_pos rfl]
      ring)
  rw [← mul_assoc, a2, mul_assoc, a1, ← mul_assoc, h, mul_assoc, ← b1, ← mul_assoc, ← b2, mul_assoc]

theorem FF_pair (hC : SSComm) (hP : P.OK) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    FF P i j u v + FF P j i u v = 0 := by
  by_cases hne : j = i
  · subst hne
    rw [FF_eq P _ hj, ee_diag P hj u v hu hv, map_zero, zero_mul, add_zero]
  · rw [FF_eq P _ hj, FF_eq P _ hi, ee_off_diagonal_first P hi hj hne u v hu hv, ee_off_diagonal_second P hi hj hne u v hu hv,
      map_neg, ← kap_mul, ← kap_mul, neg_mul, mul_assoc, mul_assoc, comm_tgt P hC hP hi hj hne,
      add_neg_cancel]

theorem sum_antisymm {M : Type*} [AddCommGroup M] [Module ℂ M] (I : Finset ℕ) (F : ℕ → ℕ → M)
    (h : ∀ i ∈ I, ∀ j ∈ I, F i j + F j i = 0) : ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by
  have h1 : ∑ i ∈ I, ∑ j ∈ I, F i j + ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j hj => h i hi j hj
  have h2 : (2 : ℂ) • ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by rw [two_smul]; exact h1
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem Lam3 (hC : SSComm) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (abelian₂ P u * abelian₂ P v - abelian₂ P v * abelian₂ P u) = (abelian₂ P u - abelian₂ P v) * (abelian₂ P u - abelian₂ P v) := by
  have h := sum_antisymm (Icc 1 (P.k - 1)) (fun i j => FF P i j u v)
    (fun i hi j hj => FF_pair P hC hP hi hj u v hu hv)
  rw [← sub_eq_zero, ← h]
  unfold abelian₂ FF
  simp only [← Finset.sum_sub_distrib, Finset.sum_mul_sum, Finset.smul_sum]

end

end Formalism.FourierDecayAlt.P.Mx6.L3

namespace Formalism.FourierDecayAlt.P.Mx6.L4

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M

noncomputable section

variable (P : Par)

theorem kap_sum' (s : Finset ℕ) (f : ℕ → Ty P → ℂ) :
    kap P (fun π => ∑ l ∈ s, f l π) = ∑ l ∈ s, kap P (f l) := by
  rw [← map_sum]
  congr 1
  funext π
  simp [Finset.sum_apply]

def rr1 (j : ℕ) (u : ℂ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ) + 1)⁻¹

theorem rr_up_same {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) {π π' : Ty P} (h : Up P j π π') (u : ℂ) :
    rr P j u π' = rr1 P j u π := by
  unfold rr rr1
  rw [rho_up P h hj, if_pos rfl, add_assoc]

theorem rr_up_ne {i j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i) {π π' : Ty P} (h : Up P i π π') (u : ℂ) :
    rr P j u π' = rr P j u π := by
  unfold rr
  rw [rho_up P h hj, if_neg hne, add_zero]

theorem rho_unchanged_off_index {i j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i) {π π' : Ty P} (h : Up P i π π') (u : ℂ) :
    rr1 P j u π' = rr1 P j u π := by
  unfold rr1
  rw [rho_up P h hj, if_neg hne, add_zero]

theorem xC_rr {u : ℂ} (hu : Good P u) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (π : Ty P) :
    xC P π u * rr P j u π = xEx P {j} π u := by
  unfold rr
  rw [xC_split P π u hj]
  field_simp [good0 P hu π hj]

theorem xEx_rr {u : ℂ} (hu : Good P u) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ l) (π : Ty P) :
    xEx P {l} π u * rr P j u π = xEx P {l, j} π u := by
  unfold rr
  rw [xEx_split P π u hj hne]
  field_simp [good0 P hu π hj]

theorem xLam {u : ℂ} (hu : Good P u) : xA P u * abelian₂ P u = weightedSumBis P u := by
  unfold abelian₂ weightedSumBis lam xA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, kap_mul]
  refine S_shift P j _ _ fun π π' h => ?_
  show xC P π' u * rr P j u π' = xEx P {j} π u
  rw [xC_rr P hu hj, xEx_up P h {j} (by simp)]

theorem Lamsx {u : ℂ} (hu : Good P u) : Lams P u * xA P u = S12 P u := by
  unfold Lams S12 lams xA
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mul_assoc, kap_mul]
  refine Ss_shift P j _ _ fun π π' h => ?_
  show rr P j u π' * xC P π' u = xEx P {j} π u
  rw [mul_comm, xC_rr P hu hj, xEx_up P h {j} (by simp)]

theorem E_Ss (l : ℕ) (u : ℂ) :
    (kap P fun π => xEx P {l} π u) * star (SS P l) = star (SS P l) * kap P fun π => xEx P {l} π u :=
  (Ss_shift P l (fun π => xEx P {l} π u) (fun π => xEx P {l} π u)
    fun _ _ h => xEx_up P h {l} (Finset.mem_singleton_self l) u).symm

theorem T_ne {u : ℂ} (hu : Good P u) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ l) :
    (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P j u) * SS P j) =
      star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π u := by
  have h1 : kap P ((fun π => xEx P {l} π u) * rr P j u) * SS P j = SS P j * kap P fun π => xEx P {l, j} π u :=
    S_shift P j (fun π => xEx P {l, j} π u) ((fun π => xEx P {l} π u) * rr P j u) fun π π' h => by
      rw [Pi.mul_apply, xEx_rr P hu hj hne, xEx_up P h {l, j} (by simp)]
  rw [E_Ss, mul_assoc, ← mul_assoc (kap P _) (kap P _), kap_mul, h1, mul_assoc]

theorem T_eq (hP : P.OK) (hN : SSNorm) (u : ℂ) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) :
    (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P l u) * SS P l) =
      kap P fun π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have h1 : kap P ((fun π => xEx P {l} π u) * rr P l u) * SS P l =
      SS P l * kap P ((fun π => xEx P {l} π u) * rr1 P l u) :=
    S_shift P l ((fun π => xEx P {l} π u) * rr1 P l u) ((fun π => xEx P {l} π u) * rr P l u) fun π π' h => by
      rw [Pi.mul_apply, Pi.mul_apply, xEx_up P h {l} (by simp), rr_up_same P hl h]
  rw [E_Ss, mul_assoc, ← mul_assoc (kap P _) (kap P _), kap_mul, h1, ← mul_assoc, (hN P hP l hl).1, kap_mul]
  congr 1
  funext π
  simp only [Pi.mul_apply, rr1]
  rw [div_eq_mul_inv, mul_assoc]

theorem upper_sum_mul_lambda (hP : P.OK) {u : ℂ} (hu : Good P u) (hN : SSNorm) :
    S12 P u * abelian₂ P u = S4 P u + kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
      ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have e1 : S12 P u * abelian₂ P u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P j u) * SS P j) :=
    Finset.sum_mul_sum _ _ _ _
  have e2 : ∀ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      (kap P fun π => xEx P {l} π u) * star (SS P l) * (kap P (rr P j u) * SS P j) =
      (∑ j ∈ (Icc 1 (P.k - 1)).erase l, star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π u) +
        kap P fun π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
    intro l hl
    rw [← Finset.sum_erase_add _ _ hl, T_eq P hP hN u hl]
    refine congrArg (· + _) ?_
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_erase.1 hj
    exact T_ne P hu hj'.2 hj'.1
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib,
    kap_sum' P _ (fun l π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1))]
  rfl

theorem Lam4 (hP : P.OK) (u v : ℂ) (hN : SSNorm) (hM : SSMixed) :
    Lams P u * abelian₂ P v - abelian₂ P v * Lams P u = kap P fun π => ∑ j ∈ Icc 1 (P.k - 1),
      (((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ)))) := by
  rw [kap_sum' P _ (fun j π => ((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ))))]
  have e1 : Lams P u * abelian₂ P v =
      ∑ i ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), lams P i u * lam P j v := Finset.sum_mul_sum _ _ _ _
  have e2 : abelian₂ P v * Lams P u =
      ∑ i ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), lam P j v * lams P i u := by
    unfold Lams abelian₂
    rw [Finset.sum_mul_sum, Finset.sum_comm]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_sub_distrib]
  have hlam : ∀ j ∈ Icc 1 (P.k - 1), lam P j v = SS P j * kap P (rr1 P j v) := fun j hj =>
    S_shift P j _ _ fun π π' h => rr_up_same P hj h v
  rw [Finset.sum_eq_single_of_mem i hi]
  ·
    have h1 : lams P i u * lam P i v = kap P ((fun π => ((Nrm P i π : ℝ) : ℂ)) * (rr1 P i u * rr1 P i v)) := by
      unfold lams lam
      rw [mul_assoc, ← mul_assoc (kap P _) (kap P _), kap_mul,
        S_shift P i (rr1 P i u * rr1 P i v) _ (fun π π' h => by
          show rr P i u π' * rr P i v π' = rr1 P i u π * rr1 P i v π
          rw [rr_up_same P hi h, rr_up_same P hi h]),
        ← mul_assoc, (hN P hP i hi).1, kap_mul]
    have h2 : lam P i v * lams P i u = kap P (rr P i v * (fun π => ((NrmDown P i π : ℝ) : ℂ)) * rr P i u) := by
      unfold lams lam
      rw [mul_assoc, ← mul_assoc (SS P i), (hN P hP i hi).2, kap_mul, kap_mul, mul_assoc]
    rw [h1, h2, ← map_sub]
    congr 1
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply, rr, rr1]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]
    ring
  · intro j hj hne
    rw [sub_eq_zero, hlam j hj]
    unfold lams
    have h3 : kap P (rr P i u) * SS P j = SS P j * kap P (rr P i u) :=
      S_shift P j _ _ fun π π' h => rr_up_ne P hi (Ne.symm hne) h u
    have h4 : kap P (rr1 P j v) * star (SS P i) = star (SS P i) * kap P (rr1 P j v) :=
      (Ss_shift P i _ _ fun π π' h => rho_unchanged_off_index P hj hne h v).symm
    calc star (SS P i) * kap P (rr P i u) * (SS P j * kap P (rr1 P j v))
        = star (SS P i) * (kap P (rr P i u) * SS P j) * kap P (rr1 P j v) := by simp only [mul_assoc]
      _ = star (SS P i) * SS P j * (kap P (rr P i u) * kap P (rr1 P j v)) := by rw [h3]; simp only [mul_assoc]
      _ = SS P j * star (SS P i) * (kap P (rr1 P j v) * kap P (rr P i u)) := by
          rw [hM P hP i hi j hj hne, kap_comm]
      _ = SS P j * (star (SS P i) * kap P (rr1 P j v)) * kap P (rr P i u) := by simp only [mul_assoc]
      _ = SS P j * kap P (rr1 P j v) * (star (SS P i) * kap P (rr P i u)) := by rw [← h4]; simp only [mul_assoc]

end

end Formalism.FourierDecayAlt.P.Mx6.L4

namespace Formalism.FourierDecayAlt.P.Mx6

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M

section Abs
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem abs_Nc (N w G : B) (hNw : N * w = w * N) (hNG : N * G = G * N - w * G * G) (hGw : G * w = w * G) :
    N * (w * G) = (w * G) * N - (w * G) * (w * G) := by
  simp only [mul_assoc, lc hNw, hNG, mul_sub, lc hGw]

theorem smul_GG_sq_identity (g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1) :
    t • (G * G) = z * (w * (G * G)) - G := by
  have h : algebraMap ℂ B t = z * w - g := by rw [hg]; abel
  rw [Algebra.smul_def, h]
  simp only [sub_mul, mul_assoc, lc1 hgG]

theorem abs_Nsc (Ns g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1)
    (hNsw : Ns * w = w * Ns - 1) (hNsG : Ns * G = G * Ns + z * G * G) (hwz : w * z = z * w) :
    Ns * (w * G) = (w * G) * Ns + t • (G * G) := by
  rw [smul_GG_sq_identity g G z w t hg hgG, ← mul_assoc, hNsw]
  simp only [sub_mul, mul_assoc, hNsG, mul_add, one_mul, lc hwz]
  abel

theorem abs_Ncz (N g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1)
    (hNz : N * z = z * N + 1) (hNG : N * G = G * N - w * G * G) :
    N * (z * G) = (z * G) * N - t • (G * G) := by
  rw [smul_GG_sq_identity g G z w t hg hgG, ← mul_assoc, hNz]
  simp only [add_mul, mul_assoc, hNG, mul_sub, one_mul]
  abel

end Abs

noncomputable section

variable (P : Par)

def cc : A P := zbA P * ggiA P

def cz : A P := zA P * ggiA P

theorem sc_mul (a b : Pr P.r) : sc P a * sc P b = sc P (a * b) := by
  unfold sc; exact (map_mul _ _ _).symm

theorem cc_sc : cc P = sc P (zbP * ggiP P.TT) := sc_mul P _ _
theorem cz_sc : cz P = sc P (zP * ggiP P.TT) := sc_mul P _ _

theorem lowering_constant_eq_shift (u : ℂ) : l0A P u = -nabA P - (u + 1 / 2) • cc P := by
  unfold l0A cc; rw [Algebra.smul_def]

theorem raising_constant_eq_shift (u : ℂ) : m0A P u = -nabsA P - (u - 1 / 2) • cz P := by
  unfold m0A cz; rw [Algebra.smul_def]

theorem lam_sc (j : ℕ) (u : ℂ) (a : Pr P.r) : lam P j u * sc P a = sc P a * lam P j u := by
  unfold lam; rw [mul_assoc, S_sc, ← mul_assoc, kap_sc, mul_assoc]

theorem Lam_sc (u : ℂ) (a : Pr P.r) : abelian₂ P u * sc P a = sc P a * abelian₂ P u := by
  unfold abelian₂; rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => lam_sc P j u a

theorem lams_sc (j : ℕ) (u : ℂ) (a : Pr P.r) : lams P j u * sc P a = sc P a * lams P j u := by
  unfold lams; rw [mul_assoc, kap_sc, ← mul_assoc, Ss_sc, mul_assoc]

theorem Lams_sc (u : ℂ) (a : Pr P.r) : Lams P u * sc P a = sc P a * Lams P u := by
  unfold Lams; rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => lams_sc P j u a

theorem zeta_mem_function_algebra : zA P ∈ fnsA P := by simp [fnsA]
theorem mem_zb : zbA P ∈ fnsA P := by simp [fnsA]
theorem mem_g : ggA P ∈ fnsA P := by simp [fnsA]
theorem mem_G : ggiA P ∈ fnsA P := by simp [fnsA]

theorem fcomm {x y : A P} (hx : x ∈ fnsA P) (hy : y ∈ fnsA P) : x * y = y * x := (Mx2.levFns P).1 x hx y hy

theorem gG : ggA P * ggiA P = 1 := (Mx2.levFns P).2.2.2.2.2.2.1
theorem Gg : ggiA P * ggA P = 1 := (Mx2.levFns P).2.2.2.2.2.2.2.1
theorem g_def : ggA P = zA P * zbA P - algebraMap ℂ (A P) (P.TT : ℂ) := (Mx2.levFns P).2.2.2.2.2.2.2.2

theorem besselUnipotent_mulVec_middle_vec : nabA P * zA P = zA P * nabA P + 1 := (Mx2.levNab P).1
theorem N_zb : nabA P * zbA P = zbA P * nabA P := (Mx2.levNab P).2.2.1
theorem nabla_gamma_relations : nabA P * ggA P = ggA P * nabA P + zbA P := (Mx2.levNab P).2.2.2.2.1
theorem nabla_star_gamma_relations : nabA P * ggiA P = ggiA P * nabA P - zbA P * ggiA P * ggiA P := (Mx2.levNab P).2.2.2.2.2.1
theorem Ns_zb : nabsA P * zbA P = zbA P * nabsA P - 1 := (Mx2.levNabs P).1
theorem nabla_star_mul_GG : nabsA P * ggA P = ggA P * nabsA P - zA P := (Mx2.levNabs P).2.2.2.2.1
theorem nabla_star_gamma_inv_comm : nabsA P * ggiA P = ggiA P * nabsA P + zA P * ggiA P * ggiA P := (Mx2.levNabs P).2.2.2.2.2.1

theorem g_cc : ggA P * cc P = zbA P := by
  unfold cc; rw [lc (fcomm P (mem_g P) (mem_zb P)), gG, mul_one]
theorem g_cz : ggA P * cz P = zA P := by
  unfold cz; rw [lc (fcomm P (mem_g P) (zeta_mem_function_algebra P)), gG, mul_one]

theorem N_g : nabA P * ggA P = ggA P * nabA P + ggA P * cc P := by rw [g_cc, nabla_gamma_relations]
theorem N_G : nabA P * ggiA P = ggiA P * nabA P - cc P * ggiA P := nabla_star_gamma_relations P
theorem Ns_g : nabsA P * ggA P = ggA P * nabsA P - ggA P * cz P := by rw [g_cz, nabla_star_mul_GG]
theorem Ns_G : nabsA P * ggiA P = ggiA P * nabsA P + cz P * ggiA P := nabla_star_gamma_inv_comm P
theorem N_cc : nabA P * cc P = cc P * nabA P - cc P * cc P :=
  abs_Nc _ _ _ (N_zb P) (nabla_star_gamma_relations P) (fcomm P (mem_G P) (mem_zb P))
theorem Ns_cc : nabsA P * cc P = cc P * nabsA P + (P.TT : ℂ) • (ggiA P * ggiA P) :=
  abs_Nsc _ _ _ _ _ _ (g_def P) (gG P) (Ns_zb P) (nabla_star_gamma_inv_comm P) (fcomm P (mem_zb P) (zeta_mem_function_algebra P))
theorem N_cz : nabA P * cz P = cz P * nabA P - (P.TT : ℂ) • (ggiA P * ggiA P) :=
  abs_Ncz _ _ _ _ _ _ (g_def P) (gG P) (besselUnipotent_mulVec_middle_vec P) (nabla_star_gamma_relations P)

theorem G_cc : ggiA P * cc P = cc P * ggiA P := by
  unfold cc; rw [lc (fcomm P (mem_G P) (mem_zb P)), mul_assoc]
theorem G_cz : ggiA P * cz P = cz P * ggiA P := by
  unfold cz; rw [lc (fcomm P (mem_G P) (zeta_mem_function_algebra P)), mul_assoc]
theorem cc_g : cc P * ggA P = ggA P * cc P := by
  unfold cc; rw [mul_assoc, Gg, mul_one, lc (fcomm P (mem_g P) (mem_zb P)), gG, mul_one]
theorem cz_g : cz P * ggA P = ggA P * cz P := by
  unfold cz; rw [mul_assoc, Gg, mul_one, lc (fcomm P (mem_g P) (zeta_mem_function_algebra P)), gG, mul_one]
theorem cz_cc : cz P * cc P = cc P * cz P := by
  rw [cc_sc, cz_sc, sc_mul, sc_mul]
  congr 1
  simp only [zP, zbP, ggiP]
  rw [Mx2.multiplierPair_mul, Mx2.multiplierPair_mul]
  exact Mx2.multiplierPair_comm _ _ _ _

theorem G_sc : ggiA P = sc P (ggiP P.TT) := rfl

theorem star_g : star (ggA P) = ggA P := (star_generators P).2.2.2.1
theorem star_G : star (ggiA P) = ggiA P := (star_generators P).2.2.2.2.1
theorem star_alt : star (zA P) = zbA P := (star_generators P).2.1
theorem star_N : star (nabA P) = nabsA P := (star_generators P).2.2.2.2.2
theorem star_Ns : star (nabsA P) = nabA P := by rw [← star_N, star_star]
theorem star_zb : star (zbA P) = zA P := by rw [← star_alt, star_star]
theorem star_cc : star (cc P) = cz P := by
  unfold cc cz; rw [star_mul, star_G, star_zb, fcomm P (mem_G P) (zeta_mem_function_algebra P)]
theorem star_cz : star (cz P) = cc P := by rw [← star_cc, star_star]

theorem N_Lam (hS : NabSS) (u : ℂ) : nabA P * abelian₂ P u = abelian₂ P u * nabA P - cc P * abelian₂ P u := by
  unfold abelian₂; rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold lam
  rw [← mul_assoc, ← kap_nab, mul_assoc, (hS P j hj).1, mul_sub, cc_sc, ← mul_assoc (sc P _), ← kap_sc, ← cc_sc]
  simp only [mul_assoc, cc]

theorem Ns_Lam (hS : NabSS) (u : ℂ) : nabsA P * abelian₂ P u = abelian₂ P u * nabsA P - cz P * abelian₂ P u := by
  unfold abelian₂; rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold lam
  rw [← mul_assoc, ← kap_nabs, mul_assoc, (hS P j hj).2, mul_sub, cz_sc, ← mul_assoc (sc P _), ← kap_sc, ← cz_sc]
  simp only [mul_assoc, cz]

theorem N_Lams (hS : NabSS) (u : ℂ) : nabA P * Lams P u = Lams P u * nabA P + cc P * Lams P u := by
  have h := congrArg star (Ns_Lam P hS (star u))
  rw [star_mul, star_sub, star_mul, star_mul, star_Lam, star_Ns, star_cz] at h
  rw [h, cc_sc, Lams_sc]; abel

theorem mt_eq (u : ℂ) : mt P u = -nabsA P - (u + 1 / 2) • cz P + ggiA P * Lams P u := by
  unfold mt
  rw [lA_eq, lowering_constant_eq_shift, star_add, star_sub, star_neg, star_N, star_smul, star_cc, star_mul, star_Lam, star_G, G_sc, Lams_sc]
  congr 3
  simp

end

end Formalism.FourierDecayAlt.P.Mx6

namespace Formalism.FourierDecayAlt.P.Mx6

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M

section Abs2
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem absSand (g G K1 K2 K3 : B) (hgG : g * G = 1) (hGg : G * g = 1)
    (h1 : K1 * G = G * K1) (h2 : K2 * G = G * K2) (h1g : K1 * g = g * K1) (h2g : K2 * g = g * K2) :
    g * K1 * (K2 * (G * G)) * (g * K3) = K1 * K2 * K3 := by
  simp only [mul_assoc, lc h1, lc h2, lc1 hgG, lc1 hGg, lc h1g, lc h2g]

theorem absN (g G X m0 l0 S12 L : B) (hXm : X * m0 = m0 * X) (hXG : X * G = G * X) (hSG : S12 * G = G * S12) :
    (g * X * m0 + S12) * (l0 + G * L) = g * X * m0 * l0 + g * m0 * G * (X * L) + S12 * l0 + G * (S12 * L) := by
  simp only [mul_add, add_mul, mul_assoc, lc hXm, lc hXG, lc hSG]
  abel

end Abs2

noncomputable section

variable (P : Par)

theorem x_N (u : ℂ) : nabA P * xA P u = xA P u * nabA P := (kap_nab P _).symm
theorem x_Ns (u : ℂ) : nabsA P * xA P u = xA P u * nabsA P := (kap_nabs P _).symm
theorem kap_g (f : Ty P → ℂ) : kap P f * ggA P = ggA P * kap P f := kap_sc P _ _
theorem kap_G (f : Ty P → ℂ) : kap P f * ggiA P = ggiA P * kap P f := kap_sc P _ _
theorem kap_cc (f : Ty P → ℂ) : kap P f * cc P = cc P * kap P f := by rw [cc_sc]; exact kap_sc P _ _
theorem kap_cz (f : Ty P → ℂ) : kap P f * cz P = cz P * kap P f := by rw [cz_sc]; exact kap_sc P _ _
theorem Lam_cc (u : ℂ) : abelian₂ P u * cc P = cc P * abelian₂ P u := by rw [cc_sc]; exact Lam_sc P _ _
theorem Lam_cz (u : ℂ) : abelian₂ P u * cz P = cz P * abelian₂ P u := by rw [cz_sc]; exact Lam_sc P _ _
theorem Lams_cc (u : ℂ) : Lams P u * cc P = cc P * Lams P u := by rw [cc_sc]; exact Lams_sc P _ _
theorem Lams_cz (u : ℂ) : Lams P u * cz P = cz P * Lams P u := by rw [cz_sc]; exact Lams_sc P _ _

theorem half (u v : ℂ) : (u + 1 / 2) - (v + 1 / 2) = u - v := by ring

theorem lowering_relation_diagonal_left (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (t22 P u * lA P v - lA P v * t22 P u) = -(t22 P u * (lA P u - lA P v)) := by
  have h := commutator_identity_one (nabA P) (cc P) (ggA P) (ggiA P) (xA P u) (abelian₂ P u) (abelian₂ P v) (u + 1 / 2) (v + 1 / 2)
    (N_g P) (x_N P u) (gG P) (Gg P) (cc_g P) (kap_sc P _ _) (kap_sc P _ _) (kap_cc P _)
    (Lam_sc P _ _) (Lam_sc P _ _) (by rw [half]; exact L3.Lam1 P u v hu hv)
  rw [half] at h
  rw [t22, lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]
  exact h

theorem lowering_relation_diagonal_right (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (dA P u * lA P v - lA P v * dA P u) = dA P u * (lA P u - lA P v) := by
  have h := commutator_identity_two (nabA P) (cc P) (ggiA P) (kap P fun π => (xC P π (u + 1))⁻¹) (abelian₂ P u) (abelian₂ P v)
    (u + 1 / 2) (v + 1 / 2) (qC P u)
    (N_G P) (kap_nab P _).symm (G_cc P) (kap_sc P _ _) (kap_cc P _)
    (Lam_sc P _ _) (Lam_sc P _ _) (by rw [half]; exact L3.Lam2 P u v hu hv)
  rw [half] at h
  rw [dA, lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]
  exact h

theorem commutator_l_sq (hC : SSComm) (hS : NabSS) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (lA P u * lA P v - lA P v * lA P u) = (lA P u - lA P v) * (lA P u - lA P v) := by
  have h := raising_pair_relation (nabA P) (cc P) (ggiA P) (abelian₂ P u) (abelian₂ P v) (u + 1 / 2) (v + 1 / 2)
    (N_cc P) (N_G P) (N_Lam P hS u) (N_Lam P hS v) (G_cc P) (Lam_cc P u) (Lam_cc P v)
    (Lam_sc P _ _) (Lam_sc P _ _) (by rw [half]; exact L3.Lam3 P hC hP u v hu hv)
  rw [half] at h
  rw [lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]
  exact h

def hh (u : ℂ) : Ty P → ℂ := fun π => qC P u / (xC P π u * xC P π (u + 1))

theorem relD4core (hN : SSNorm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (mt P u * lA P v - lA P v * mt P u) = kap P (hh P v - hh P u) * (ggiA P * ggiA P) := by
  have hcurv : nabsA P * nabA P = nabA P * nabsA P +
      (kap P fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) * (ggiA P * ggiA P) := by
    rw [← mul_assoc, ← hK P]; abel
  have h := commutator_identity_four (nabA P) (nabsA P) (cc P) (cz P) (ggiA P) (kap P fun π => ((2 * aC P π * P.TT : ℝ) : ℂ))
    (Lams P u) (abelian₂ P v) (u + 1 / 2) (v + 1 / 2) (P.TT : ℂ) hcurv (Ns_cc P) (N_cz P) (N_G P) (Ns_G P)
    (Ns_Lam P hS v) (N_Lams P hS u) (G_cc P) (G_cz P) (cz_cc P) (Lam_cc P v) (Lam_cz P v) (Lam_sc P _ _)
    (Lams_cc P u) (Lams_cz P u) (Lams_sc P _ _)
  rw [mt_eq, lA_eq, lowering_constant_eq_shift, h, L4.Lam4 P hP u v hN hM]
  have e1 : ∀ f : Ty P → ℂ, ggiA P * (ggiA P * kap P f) = kap P f * (ggiA P * ggiA P) := fun f => by
    rw [← mul_assoc, G_sc, sc_mul, kap_sc]
  have e2 : ∀ z : ℂ, z • (ggiA P * ggiA P) = kap P (fun _ => z) * (ggiA P * ggiA P) := fun z => by
    have : kap P (fun _ => z) = algebraMap ℂ (A P) z := (kap P).commutes z
    rw [this, Algebra.smul_def]
  rw [e1, e2, ← add_mul, ← add_mul, ← map_add, ← map_add, ← smul_mul_assoc, ← map_smul]
  congr 2
  funext π
  have hs := WB.scalar_partial_fraction_identity P hP π u v hu hv
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hh]
  rw [← hs]
  push_cast
  ring

theorem mixed_relation_diagonal_four (hN : SSNorm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (t22 P v * mt P u * lA P v * t22 P u - t22 P v * lA P v * mt P u * t22 P u) =
      dA P v * t22 P u - t22 P v * dA P u := by
  have h := relD4core P hN hM hS hK hP u v hu hv
  have e : (u - v) • (t22 P v * mt P u * lA P v * t22 P u - t22 P v * lA P v * mt P u * t22 P u) =
      t22 P v * ((u - v) • (mt P u * lA P v - lA P v * mt P u)) * t22 P u := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [e, h, t22, t22, xA, xA, absSand _ _ _ _ _ (gG P) (Gg P) (kap_sc P _ _) (kap_sc P _ _) (kap_sc P _ _) (kap_sc P _ _)]
  have e3 : dA P v * (ggA P * kap P fun π => xC P π u) = kap P fun π => qC P v * (xC P π (v + 1))⁻¹ * xC P π u := by
    rw [dA, smul_mul_assoc, mul_assoc, lc (kap_g P _), lc1 (Gg P), kap_mul, ← map_smul]
    congr 1
    funext π
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  have e4 : (ggA P * kap P fun π => xC P π v) * dA P u = kap P fun π => xC P π v * (qC P u * (xC P π (u + 1))⁻¹) := by
    rw [dA, mul_smul_comm, mul_assoc, lc (kap_G P _), lc1 (gG P), kap_mul, ← map_smul]
    congr 1
    funext π
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  rw [e3, e4, kap_mul, kap_mul, ← map_sub]
  congr 1
  funext π
  have h1 := xC_ne P hu π
  have h2 := xC_ne P hv π
  have h3 := coordinate_shift_ne_zero P hu π
  have h4 := coordinate_shift_ne_zero P hv π
  simp only [Pi.mul_apply, Pi.sub_apply, hh]
  field_simp

end

end Formalism.FourierDecayAlt.P.Mx6

namespace Formalism.FourierDecayAlt.P.Mx6

open Matrix Finset Polynomial Formalism.FourierDecayAlt.M

section Abs3
variable {B : Type*} [Ring B] [Algebra ℂ B]

theorem absCC (a b K1 K2 : B) (hab : a * b = b * a) (hK : K1 * K2 = K2 * K1) (h1 : K1 * b = b * K1)
    (h2 : K2 * a = a * K2) : (a * K1) * (b * K2) = (b * K2) * (a * K1) :=
  calc a * K1 * (b * K2) = a * b * (K1 * K2) := by rw [mul_assoc, lc h1, mul_assoc]
    _ = b * a * (K2 * K1) := by rw [hab, hK]
    _ = b * K2 * (a * K1) := by rw [mul_assoc b K2, lc h2, mul_assoc]

end Abs3

noncomputable section

variable (P : Par)

theorem star_xC (π : Ty P) (u : ℂ) : star (xC P π (star u)) = xC P π u := by
  unfold xC
  rw [← starRingEnd_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => by simp

theorem star_qC (u : ℂ) : star (qC P (star u)) = qC P u := by
  unfold qC
  rw [← starRingEnd_apply, map_mul, map_prod]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun i _ => by simp [map_ofNat]

theorem star_t22 (u : ℂ) : star (t22 P (star u)) = t22 P u := by
  rw [t22, t22, star_mul, star_g, xA, xA, star_kap, kap_g]
  congr 2
  funext π
  exact star_xC P π u

theorem star_dA (u : ℂ) : star (dA P (star u)) = dA P u := by
  rw [dA, dA, star_smul, star_qC, star_mul, star_G, star_kap, kap_G]
  congr 3
  funext π
  have : star u + 1 = star (u + 1) := by simp
  rw [star_inv₀, this, star_xC]

theorem star_lA (u : ℂ) : star (lA P (star u)) = mt P u := rfl

theorem commutator_t22_m (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (t22 P u * mt P v - mt P v * t22 P u) = (mt P u - mt P v) * t22 P u := by
  have h := congrArg star (lowering_relation_diagonal_left P (star u) (star v) (good_star P hu) (good_star P hv))
  simp only [star_smul, star_sub, star_mul, star_neg, star_star, star_t22, star_lA] at h
  simp only [mul_sub, sub_mul, smul_sub] at h ⊢
  linear_combination (norm := module) (-1 : ℂ) • h

theorem commutator_d_m (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (dA P u * mt P v - mt P v * dA P u) = -((mt P u - mt P v) * dA P u) := by
  have h := congrArg star (lowering_relation_diagonal_right P (star u) (star v) (good_star P hu) (good_star P hv))
  simp only [star_smul, star_sub, star_mul, star_neg, star_star, star_dA, star_lA] at h
  simp only [mul_sub, sub_mul, smul_sub] at h ⊢
  linear_combination (norm := module) (-1 : ℂ) • h

theorem raising_relation_self (hC : SSComm) (hS : NabSS) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (mt P u * mt P v - mt P v * mt P u) = -((mt P u - mt P v) * (mt P u - mt P v)) := by
  have h := congrArg star (commutator_l_sq P hC hS hP (star u) (star v) (good_star P hu) (good_star P hv))
  simp only [star_smul, star_sub, star_mul, star_neg, star_star, star_lA] at h
  simp only [mul_sub, sub_mul, smul_sub] at h ⊢
  linear_combination (norm := module) (-1 : ℂ) • h

theorem nf21 {u : ℂ} (hu : Good P u) : t21 P u = t22 P u * lA P u := by
  rw [t21, t22, lA_eq, diagonal_lowering_absorb (ggA P) (ggiA P) (xA P u) _ _ (gG P) (kap_G P _), L4.xLam P hu]

theorem nf12 {u : ℂ} (hu : Good P u) : t12 P u = mt P u * t22 P u := by
  rw [t12, t22, mt_eq, raising_operator_absorb _ _ _ _ _ _ _ (Ns_g P) (x_Ns P u) (Gg P) (cz_g P) (kap_cz P _).symm (Lams_sc P _ _),
    L4.Lamsx P hu, raising_constant_eq_shift]
  congr 4
  ring

theorem coordinate_commute_raising_constant (u v : ℂ) : xA P u * m0A P v = m0A P v * xA P u := by
  rw [raising_constant_eq_shift]
  simp only [mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, x_Ns]
  rw [xA, kap_cz]

theorem S12_commute_GGinv (u : ℂ) : S12 P u * ggiA P = ggiA P * S12 P u := by
  unfold S12
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, G_sc, Ss_sc, ← mul_assoc, kap_sc, mul_assoc]

theorem nf11 (hN : SSNorm) (hP : P.OK) {u : ℂ} (hu : Good P u) :
    t11 P u = dA P u + mt P u * t22 P u * lA P u := by
  rw [← nf12 P hu, t12, lA_eq, absN _ _ _ _ _ _ _ (coordinate_commute_raising_constant P u u) (kap_G P _) (S12_commute_GGinv P u), L4.xLam P hu,
    L4.upper_sum_mul_lambda P hP hu hN, t11, mul_add]
  have e : ggiA P * (kap P fun π => wC P π u) = dA P u + ggiA P * kap P fun π =>
      ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
    rw [dA, ← mul_smul_comm, ← map_smul, ← mul_add, ← map_add]
    congr 2
    funext π
    rw [WB.wC_eq P hP π u hu]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  rw [e]
  abel

theorem comm_tt (u v : ℂ) : t22 P v * t22 P u = t22 P u * t22 P v :=
  absCC _ _ _ _ rfl (kap_comm P _ _) (kap_g P _) (kap_g P _)

theorem comm_dd (u v : ℂ) : dA P v * dA P u = dA P u * dA P v := by
  simp only [dA, smul_mul_assoc, mul_smul_comm]
  rw [smul_comm, absCC _ _ _ _ rfl (kap_comm P _ _) (kap_G P _) (kap_G P _)]

theorem comm_dt (u v : ℂ) : dA P v * t22 P u = t22 P u * dA P v := by
  simp only [dA, t22, xA, smul_mul_assoc, mul_smul_comm]
  rw [absCC _ _ _ _ ((Gg P).trans (gG P).symm) (kap_comm P _ _) (kap_g P _) (kap_G P _)]

theorem generic (hN : SSNorm) (hC : SSComm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) (h0 : u - v ≠ 0) (h1 : u - v ≠ 1) (h2 : u - v ≠ -1)
    (i j k l : Fin 2) :
    (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) =
      QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l := by
  have eU : ∀ {y : ℂ}, Good P y → QQr P y =
      !![dA P y + mt P y * t22 P y * lA P y, mt P y * t22 P y; t22 P y * lA P y, t22 P y] := fun {y} hy => by
    rw [QQr, nf11 P hN hP hy, nf12 P hy, nf21 P hy]
  have e : v - u = -(u - v) := by ring
  rw [eU hu, eU hv]
  refine GA.gauss_rtt (u - v) h0 h1 h2 (t22 P u) (t22 P v) (dA P u) (dA P v) (lA P u) (lA P v) (mt P u) (mt P v)
    (comm_tt P u v) (comm_dd P u v) (comm_dt P u v) (comm_dt P v u)
    (lowering_relation_diagonal_left P u v hu hv) ?_ (lowering_relation_diagonal_right P u v hu hv) ?_ (commutator_t22_m P u v hu hv) ?_ (commutator_d_m P u v hu hv) ?_
    (commutator_l_sq P hC hS hP u v hu hv) (raising_relation_self P hC hS hP u v hu hv) (mixed_relation_diagonal_four P hN hM hS hK hP u v hu hv) ?_ i j k l
  · have h := lowering_relation_diagonal_left P v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := lowering_relation_diagonal_right P v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := commutator_t22_m P v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := commutator_d_m P v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := mixed_relation_diagonal_four P hN hM hS hK hP v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h

theorem entries_of (hN : SSNorm) (hC : SSComm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) : QQRTTEntries :=
  fun P hP => PC.entries_of_generic P fun u v hu hv h0 h1 h2 i j k l =>
    generic P hN hC hM hS hK hP u v hu hv h0 h1 h2 i j k l

end

end Formalism.FourierDecayAlt.P.Mx6

namespace Formalism.FourierDecayAlt.P

theorem transfer_rtt_entries : Formalism.FourierDecayAlt.M.QQRTTEntries :=
  Mx6.entries_of shift_norm_relation shift_commute_relation shift_mixed_relation nabla_shift_relation m_curvature_proof

theorem transfer_rtt_of_entries : Formalism.FourierDecayAlt.M.QQRTTOfEntries := Mx6.PC.ofEntries

theorem transfer_rtt : Formalism.FourierDecayAlt.M.QQRTT := transfer_rtt_of_entries transfer_rtt_entries

end Formalism.FourierDecayAlt.P
