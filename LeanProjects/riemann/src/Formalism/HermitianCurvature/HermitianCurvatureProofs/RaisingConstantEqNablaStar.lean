import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial

namespace Formalism.FourierDecayAlt.P.Mx5

variable (P : Par)

theorem kap_eq (f : Ty P → ℂ) :
    kap P f = Matrix.diagonal fun π => algebraMap ℂ (Pr P.r) (f π) := rfl

theorem kap_diag (f : Ty P → ℂ) (d : Ty P → Pr P.r) :
    Commute (kap P f) (Matrix.diagonal d) := by
  rw [kap_eq]
  show Matrix.diagonal _ * Matrix.diagonal d = Matrix.diagonal d * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

theorem kap_sc (f : Ty P → ℂ) (w : Pr P.r) : Commute (kap P f) (sc P w) := by
  unfold sc
  rw [Matrix.scalar_apply]
  exact kap_diag P f _

theorem kap_kap (f g : Ty P → ℂ) : Commute (kap P f) (kap P g) := (Commute.all f g).map (kap P)

theorem star_kap (f : Ty P → ℂ) : star (kap P f) = kap P fun π => star (f π) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext π
  simp only [Pi.star_apply]
  exact (algebraMap_star_comm (f π)).symm

theorem kap_const (c : ℂ) : (kap P fun _ => c) = algebraMap ℂ (A P) c := (kap P).commutes c

theorem kap_mul (f g : Ty P → ℂ) : (kap P fun π => f π * g π) = kap P f * kap P g := map_mul (kap P) f g

theorem kap_add (f g : Ty P → ℂ) : (kap P fun π => f π + g π) = kap P f + kap P g := map_add (kap P) f g

theorem kap_smul (c : ℂ) (f : Ty P → ℂ) : (kap P fun π => c * f π) = c • kap P f := map_smul (kap P) c f

theorem kap_sum {ι : Type} (s : Finset ι) (f : ι → Ty P → ℂ) :
    (kap P fun π => ∑ i ∈ s, f i π) = ∑ i ∈ s, kap P (f i) := by
  rw [← map_sum]
  congr 1
  funext π
  rw [Finset.sum_apply]

theorem ss_sc (l : ℕ) (w : Pr P.r) : Commute (SS P l) (sc P w) := by
  unfold sc
  show SS P l * Matrix.scalar _ w = Matrix.scalar _ w * SS P l
  ext i j
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold SS
  rw [Matrix.of_apply]
  split_ifs
  · exact Algebra.commutes (R := ℂ) _ _
  · rw [zero_mul, mul_zero]

private theorem star_sc_lemma (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  rfl

theorem sss_sc (l : ℕ) (w : Pr P.r) : Commute (star (SS P l)) (sc P w) := by
  have h := (ss_sc P l (star w)).star_star
  rwa [star_sc_lemma, star_star] at h

theorem ss_shift (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    kap P g * SS P l = SS P l * kap P f := by
  rw [kap_eq, kap_eq]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  unfold SS
  rw [Matrix.of_apply]
  split_ifs with hu
  · rw [h j i hu, ← map_mul, ← map_mul, mul_comm]
  · rw [zero_mul, mul_zero]

theorem sss_shift (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    star (SS P l) * kap P g = kap P f * star (SS P l) := by
  have h2 := ss_shift P l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by rw [h π π' hu])
  have h3 := congrArg star h2
  rw [star_mul, star_mul, star_kap, star_kap] at h3
  simp only [star_star] at h3
  exact h3

theorem sc_mul (w w' : Pr P.r) : sc P w * sc P w' = sc P (w * w') := by
  unfold sc
  exact (map_mul (Matrix.scalar (Ty P)) w w').symm

theorem fn_comm (f fb g gb : Fn P.r) : Commute (sc P (fnP f fb)) (sc P (fnP g gb)) := by
  have key : ∀ a b : Fn P.r, mulOp a * mulOp b = mulOp b * mulOp a := by
    intro a b
    apply LinearMap.ext
    intro x
    simp only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply]
    ring
  unfold sc
  apply Commute.map _ (Matrix.scalar (Ty P))
  unfold fnP Formalism.FourierDecayAlt.M.mk
  exact Prod.ext (key f g) (congrArg MulOpposite.op (key gb fb))

theorem gg_ggi : ggA P * ggiA P = 1 := by
  obtain ⟨-, -, -, -, -, -, h, -, -⟩ := level_function_relations P; exact h
theorem ggi_gg : ggiA P * ggA P = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := level_function_relations P; exact h
theorem gg_def : ggA P = zA P * zbA P - algebraMap ℂ (A P) (P.TT : ℂ) := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := level_function_relations P; exact h
theorem nabla_zeta_comm : nabA P * zA P = zA P * nabA P + 1 := (level_nabla_relations P).1
theorem nab_gg : nabA P * ggA P = ggA P * nabA P + zbA P := by
  obtain ⟨-, -, -, -, h, -, -⟩ := level_nabla_relations P; exact h
theorem nabs_alt : nabsA P * zA P = zA P * nabsA P := by
  obtain ⟨-, -, h, -, -, -, -⟩ := level_nabla_star_relations P; exact h
theorem nabs_gg : nabsA P * ggA P = ggA P * nabsA P - zA P := by
  obtain ⟨-, -, -, -, h, -, -⟩ := level_nabla_star_relations P; exact h
theorem star_alt : star (zA P) = zbA P := by
  unfold zA zbA
  rw [star_sc_lemma]
  rfl
theorem star_zb : star (zbA P) = zA P := by rw [← star_alt, star_star]
theorem star_gg : star (ggA P) = ggA P := by
  unfold ggA
  rw [star_sc_lemma]
  rfl
theorem star_ggi : star (ggiA P) = ggiA P := by
  unfold ggiA
  rw [star_sc_lemma]
  rfl
theorem star_nab : star (nabA P) = nabsA P := (star_generators P).2.2.2.2.2
theorem star_nabs : star (nabsA P) = nabA P := by rw [← star_nab, star_star]

theorem l0_eq_neg_nabla_sub (Y : ℂ) : l0A P Y = -nabA P - (Y + 1 / 2) • (zbA P * ggiA P) := by
  unfold l0A
  rw [← Algebra.smul_def]
theorem raising_constant_eq_nabla_star (Y : ℂ) : m0A P Y = -nabsA P - (Y - 1 / 2) • (zA P * ggiA P) := by
  unfold m0A
  rw [← Algebra.smul_def]

theorem lowering_constant_zeta_comm (Y : ℂ) : l0A P Y * zA P = zA P * l0A P Y - 1 := by
  have hc : (zbA P * ggiA P) * zA P = zA P * (zbA P * ggiA P) := by
    have h1 : Commute (zbA P) (zA P) := by
      unfold zbA zA zbP zP
      exact fn_comm P _ _ _ _
    have h2 : Commute (ggiA P) (zA P) := by
      unfold ggiA zA ggiP zP
      exact fn_comm P _ _ _ _
    exact (h1.mul_left h2).eq
  rw [l0_eq_neg_nabla_sub, sub_mul, mul_sub, neg_mul, mul_neg, nabla_zeta_comm, smul_mul_assoc, hc, mul_smul_comm]
  abel

theorem raising_constant_commute_zeta (Y : ℂ) : Commute (m0A P Y) (zA P) := by
  rw [raising_constant_eq_nabla_star]
  have hn : Commute (nabsA P) (zA P) := nabs_alt P
  have h2 : Commute (zA P * ggiA P) (zA P) := (Commute.refl _).mul_left (by
    unfold ggiA zA ggiP zP
    exact fn_comm P _ _ _ _)
  exact hn.neg_left.sub_left (h2.smul_left _)

theorem S21_commute_scalar (Y : ℂ) (w : Pr P.r) : Commute (weightedSumBis P Y) (sc P w) := by
  unfold weightedSumBis
  exact Commute.sum_left _ _ _ fun l _ => (ss_sc P l w).mul_left (kap_sc P _ w)

theorem upper_sum_commute_scalar (Y : ℂ) (w : Pr P.r) : Commute (S12 P Y) (sc P w) := by
  unfold S12
  exact Commute.sum_left _ _ _ fun l _ => (kap_sc P _ w).mul_left (sss_sc P l w)

theorem quartic_sum_commute_scalar (Y : ℂ) (w : Pr P.r) : Commute (S4 P Y) (sc P w) := by
  unfold S4
  exact Commute.sum_left _ _ _ fun l _ => Commute.sum_left _ _ _ fun j _ =>
    ((sss_sc P l w).mul_left (ss_sc P j w)).mul_left (kap_sc P _ w)

theorem commGroup_mul_eq_mul_mul_div {R : Type*} [Ring R] (a B c D e l z : R) (ha : Commute a z) (hB : Commute B z)
    (hc : Commute c z) (hD : Commute D z) (he : Commute e z) (hl : l * z = z * l - 1) :
    (a + B * l + c + D * l + e) * z - z * (a + B * l + c + D * l + e) = -(B + D) := by
  have h1 : B * l * z = z * (B * l) - B := by
    rw [mul_assoc, hl, mul_sub, mul_one, ← mul_assoc, hB.eq, mul_assoc]
  have h2 : D * l * z = z * (D * l) - D := by
    rw [mul_assoc, hl, mul_sub, mul_one, ← mul_assoc, hD.eq, mul_assoc]
  rw [add_mul, add_mul, add_mul, add_mul, h1, h2, ha.eq, hc.eq, he.eq]
  simp only [mul_add]
  abel

theorem qQZeta : QQZeta := by
  intro P Y
  have hg : Commute (ggA P) (zA P) := by
    unfold ggA zA ggP zP
    exact fn_comm P _ _ _ _
  have hgi : Commute (ggiA P) (zA P) := by
    unfold ggiA zA ggiP zP
    exact fn_comm P _ _ _ _
  have hx : Commute (xA P Y) (zA P) := by
    unfold xA zA
    exact kap_sc P _ _
  have hW : Commute (kap P fun π => wC P π Y) (zA P) := by
    unfold zA
    exact kap_sc P _ _
  have hS21 : Commute (weightedSumBis P Y) (zA P) := by
    unfold zA
    exact S21_commute_scalar P Y _
  have hS12 : Commute (S12 P Y) (zA P) := by
    unfold zA
    exact upper_sum_commute_scalar P Y _
  have hS4 : Commute (S4 P Y) (zA P) := by
    unfold zA
    exact quartic_sum_commute_scalar P Y _
  have hm := raising_constant_commute_zeta P Y
  have h1 := commGroup_mul_eq_mul_mul_div 0 (ggA P * xA P Y) (weightedSumBis P Y) 0 0 (l0A P Y) (zA P) (Commute.zero_left _)
    (hg.mul_left hx) hS21 (Commute.zero_left _) (Commute.zero_left _) (lowering_constant_zeta_comm P Y)
  simp only [zero_add, add_zero, zero_mul] at h1
  have h2 := commGroup_mul_eq_mul_mul_div (ggiA P * kap P fun π => wC P π Y) (ggA P * xA P Y * m0A P Y)
    (ggA P * m0A P Y * ggiA P * weightedSumBis P Y) (S12 P Y) (ggiA P * S4 P Y) (l0A P Y) (zA P)
    (hgi.mul_left hW) ((hg.mul_left hx).mul_left hm) (((hg.mul_left hm).mul_left hgi).mul_left hS21) hS12
    (hgi.mul_left hS4) (lowering_constant_zeta_comm P Y)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold t21 t22
    exact h1
  · unfold t11 t12
    exact h2
  · unfold t12
    exact ((hg.mul_left hx).mul_left hm).add_left hS12
  · unfold t22
    exact hg.mul_left hx

theorem block_frame_conjugation_identity {R : Type*} [Ring R] [Algebra ℂ R] (g gi z N : R) (a e : ℂ) (h1 : g * gi = 1)
    (hN : N * g = g * N - e • z) (hzg : Commute z g) (hzgi : Commute z gi) :
    g * (-N - a • (z * gi)) * gi = -N - (a + e) • (gi * z) := by
  have hgN : g * N = N * g + e • z := by rw [hN]; abel
  have e1 : g * N * gi = N + e • (z * gi) := by
    rw [hgN, add_mul, mul_assoc, h1, mul_one, smul_mul_assoc]
  have e2 : g * (z * gi) * gi = z * gi := by
    rw [← mul_assoc, ← hzg.eq, mul_assoc z g gi, h1, mul_one]
  calc g * (-N - a • (z * gi)) * gi = -(g * N * gi) - a • (g * (z * gi) * gi) := by
        rw [mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
    _ = -N - (a + e) • (gi * z) := by
        rw [e1, e2, ← hzgi.eq, add_smul]
        abel

theorem star_half : star (1 / 2 : ℂ) = 1 / 2 := by
  first
  | simp
  | norm_num [Complex.ext_iff]

theorem conj_two : (starRingEnd ℂ) 2 = 2 := by
  first
  | simp
  | exact map_ofNat (starRingEnd ℂ) 2

theorem star_lowering_constant (Y : ℂ) : star (l0A P Y) = ggA P * m0A P (star Y) * ggiA P := by
  rw [raising_constant_eq_nabla_star, block_frame_conjugation_identity (ggA P) (ggiA P) (zA P) (nabsA P) (star Y - 1 / 2) 1 (gg_ggi P)
    (by rw [nabs_gg, one_smul]) (by unfold zA ggA zP ggP; exact fn_comm P _ _ _ _) (by unfold zA ggiA zP ggiP; exact fn_comm P _ _ _ _),
    l0_eq_neg_nabla_sub, star_sub, star_neg, star_smul, star_mul, star_nab, star_ggi, star_zb,
    show star (Y + 1 / 2 : ℂ) = star Y - 1 / 2 + 1 by rw [star_add, star_half]; ring]

theorem star_raising_constant (Y : ℂ) : star (m0A P Y) = ggA P * l0A P (star Y) * ggiA P := by
  rw [l0_eq_neg_nabla_sub, block_frame_conjugation_identity (ggA P) (ggiA P) (zbA P) (nabA P) (star Y + 1 / 2) (-1) (gg_ggi P)
    (by rw [nab_gg, neg_one_smul, sub_neg_eq_add]) (by unfold zbA ggA zbP ggP; exact fn_comm P _ _ _ _) (by unfold zbA ggiA zbP ggiP; exact fn_comm P _ _ _ _),
    raising_constant_eq_nabla_star, star_sub, star_neg, star_smul, star_mul, star_nabs, star_ggi, star_alt,
    show star (Y - 1 / 2 : ℂ) = star Y + 1 / 2 + -1 by rw [star_sub, star_half]; ring]

theorem kappa_commute_l0 (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P f) (l0A P Y) := by
  unfold l0A nabA zbA ggiA
  exact ((kap_diag P f _).neg_right).sub_right
    ((Algebra.commute_algebraMap_right _ _).mul_right ((kap_sc P f _).mul_right (kap_sc P f _)))

theorem kappa_commute_raising_constant (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P f) (m0A P Y) := by
  unfold m0A nabsA zA ggiA
  exact ((kap_diag P f _).neg_right).sub_right
    ((Algebra.commute_algebraMap_right _ _).mul_right ((kap_sc P f _).mul_right (kap_sc P f _)))

theorem star_xEx (ex : Finset ℕ) (π : Ty P) (Y : ℂ) : star (xEx P ex π Y) = xEx P ex π (star Y) := by
  unfold xEx
  rw [star_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [star_add, Complex.star_def, Complex.conj_ofReal]

theorem star_xC (π : Ty P) (Y : ℂ) : star (xC P π Y) = xC P π (star Y) := by
  unfold xC
  rw [star_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [star_add, Complex.star_def, Complex.conj_ofReal]

theorem star_xA (Y : ℂ) : star (xA P Y) = xA P (star Y) := by
  unfold xA
  rw [star_kap]
  simp only [star_xC]

theorem star_lower_sum (Y : ℂ) : star (weightedSumBis P Y) = S12 P (star Y) := by
  unfold weightedSumBis S12
  rw [star_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul, star_kap]
  simp only [star_xEx]

theorem star_upper_sum (Y : ℂ) : star (S12 P Y) = weightedSumBis P (star Y) := by
  unfold weightedSumBis S12
  rw [star_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul, star_star, star_kap]
  simp only [star_xEx]

theorem xEx_up (l : ℕ) (ex : Finset ℕ) (hl : l ∈ ex) (Y : ℂ) (π π' : Ty P) (h : Up P l π π') :
    xEx P ex π' Y = xEx P ex π Y := by
  unfold xEx
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_sdiff, Finset.mem_Icc] at hi
  have hil : i ≠ l := fun e => hi.2 (by rw [e]; exact hl)
  have key : rho P π' i = rho P π i := by
    unfold rho
    simp only [dif_pos hi.1]
    have := h ⟨i - 1, by omega⟩
    simp only [Fin.val_mk] at this
    rw [if_neg (by omega), add_zero] at this
    rw [this]
  rw [key]

theorem kap_ss (l : ℕ) (f : Ty P → ℂ) (h : ∀ π π', Up P l π π' → f π' = f π) :
    Commute (kap P f) (SS P l) := ss_shift P l f f h

theorem kap_sss (l : ℕ) (f : Ty P → ℂ) (h : ∀ π π', Up P l π π' → f π' = f π) :
    Commute (kap P f) (star (SS P l)) := (sss_shift P l f f h).symm

theorem star_quartic_sum (Y : ℂ) : star (S4 P Y) = S4 P (star Y) := by
  unfold S4
  simp only [star_sum, star_mul, star_star, star_kap, star_xEx]
  rw [Finset.sum_comm' (t' := Icc 1 (P.k - 1)) (s' := fun y => (Icc 1 (P.k - 1)).erase y)
    (fun x y => by simp only [Finset.mem_erase, ne_comm]; tauto)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.pair_comm b a]
  exact ((kap_sss P a _ fun π π' h => xEx_up P a {a, b} (by simp) (star Y) π π' h).mul_right
    (kap_ss P b _ fun π π' h => xEx_up P b {a, b} (by simp) (star Y) π π' h)).eq

theorem coordinate_polynomial_monic (π : Ty P) : (coordinatePolynomial P π).Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _

theorem star_wC (π : Ty P) (Y : ℂ) : star (wC P π Y) = wC P π (star Y) := by
  have h1 : (wNum P π).map (starRingEnd ℂ) = wNum P π := by
    simp [wNum, qP, Polynomial.map_sum, Polynomial.map_prod, conj_two]
  have h2 : (coordinatePolynomial P π).map (starRingEnd ℂ) = coordinatePolynomial P π := by simp [coordinatePolynomial, Polynomial.map_prod]
  have h3 : (wNum P π /ₘ coordinatePolynomial P π).map (starRingEnd ℂ) = wNum P π /ₘ coordinatePolynomial P π := by
    rw [Polynomial.map_divByMonic _ (coordinate_polynomial_monic P π), h1, h2]
  show (starRingEnd ℂ) ((wNum P π /ₘ coordinatePolynomial P π).eval Y) = (wNum P π /ₘ coordinatePolynomial P π).eval ((starRingEnd ℂ) Y)
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h3]

theorem kap_ggi (f : Ty P → ℂ) : kap P f * ggiA P = ggiA P * kap P f := by
  unfold ggiA
  exact kap_sc P f _
theorem kap_gg (f : Ty P → ℂ) : kap P f * ggA P = ggA P * kap P f := by
  unfold ggA
  exact kap_sc P f _
theorem quartic_sum_gamma_inv_comm (Y : ℂ) : S4 P Y * ggiA P = ggiA P * S4 P Y := by
  unfold ggiA
  exact quartic_sum_commute_scalar P Y _

theorem ggi_kap_gg (f : Ty P → ℂ) : ggiA P * (kap P f * ggA P) = kap P f := by rw [kap_gg, ← mul_assoc, ggi_gg, one_mul]

theorem star_t22 (Y : ℂ) : star (t22 P Y) = t22 P (star Y) := by
  unfold t22
  rw [star_mul, star_gg, star_xA]
  exact kap_gg P _

theorem star_t21 (Y : ℂ) : star (t21 P Y) = t12 P (star Y) := by
  unfold t21 t12 xA
  rw [star_add, star_mul, star_mul, star_lowering_constant, star_kap, star_gg, star_lower_sum]
  simp only [star_xC]
  rw [add_left_inj]
  rw [mul_assoc (ggA P * m0A P (star Y)), ggi_kap_gg, mul_assoc, mul_assoc, (kappa_commute_raising_constant P _ _).eq]

theorem star_t12 (Y : ℂ) : star (t12 P Y) = t21 P (star Y) := by
  unfold t21 t12 xA
  rw [star_add, star_mul, star_mul, star_raising_constant, star_kap, star_gg, star_upper_sum]
  simp only [star_xC]
  rw [add_left_inj]
  rw [mul_assoc (ggA P * l0A P (star Y)), ggi_kap_gg, mul_assoc, mul_assoc, (kappa_commute_l0 P _ _).eq]

theorem conj_eq_of_nonneg_real {R : Type*} [Ring R] (g gi x M L : R) (h2 : gi * g = 1)
    (e1 : gi * (x * g) = x) (hxM : Commute x M) (hxL : Commute x L) :
    g * M * gi * (g * L * gi * (x * g)) = g * x * M * L := by
  calc g * M * gi * (g * L * gi * (x * g)) = g * M * (gi * g) * L * (gi * (x * g)) := by
        simp only [mul_assoc]
    _ = g * (M * L * x) := by
        rw [h2, e1, mul_one]
        simp only [mul_assoc]
    _ = g * x * M * L := by
        rw [(hxM.mul_right hxL).symm.eq]
        simp only [mul_assoc]

theorem star_t11 (Y : ℂ) : star (t11 P Y) = t11 P (star Y) := by
  have e1 : star (ggiA P * kap P fun π => wC P π Y) = ggiA P * kap P fun π => wC P π (star Y) := by
    rw [star_mul, star_ggi, star_kap]
    simp only [star_wC]
    exact kap_ggi P _
  have e2 : star (ggA P * xA P Y * m0A P Y * l0A P Y) =
      ggA P * xA P (star Y) * m0A P (star Y) * l0A P (star Y) := by
    rw [star_mul, star_mul, star_mul, star_lowering_constant, star_raising_constant, star_xA, star_gg]
    exact conj_eq_of_nonneg_real (ggA P) (ggiA P) (xA P (star Y)) (m0A P (star Y)) (l0A P (star Y)) (ggi_gg P)
      (by unfold xA; exact ggi_kap_gg P _) (by unfold xA; exact kappa_commute_raising_constant P _ _) (by unfold xA; exact kappa_commute_l0 P _ _)
  have e3 : star (ggA P * m0A P Y * ggiA P * weightedSumBis P Y) = S12 P (star Y) * l0A P (star Y) := by
    rw [star_mul, star_mul, star_mul, star_lower_sum, star_ggi, star_raising_constant, star_gg]
    simp only [mul_assoc]
    rw [← mul_assoc (ggiA P) (ggA P), ggi_gg, one_mul, mul_one]
  have e4 : star (S12 P Y * l0A P Y) = ggA P * m0A P (star Y) * ggiA P * weightedSumBis P (star Y) := by
    rw [star_mul, star_lowering_constant, star_upper_sum]
  have e5 : star (ggiA P * S4 P Y) = ggiA P * S4 P (star Y) := by
    rw [star_mul, star_quartic_sum, star_ggi, quartic_sum_gamma_inv_comm]
  unfold t11
  rw [star_add, star_add, star_add, star_add, e1, e2, e3, e4, e5]
  abel

theorem qQHerm : QQHerm := by
  intro P _ Y
  unfold QQr
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, star_t11, star_t12, star_t21, star_t22]

section lead

variable {R : Type*} [Ring R] [Algebra ℂ R]

def Lead (n : ℕ) (c : R) (f : ℂ → R) : Prop :=
  ∃ a : ℕ → R, ∀ Y, f Y = Y ^ n • c + ∑ i ∈ range n, Y ^ i • a i

theorem mon_eval (c : R) (n : ℕ) (Y : ℂ) : c * (algebraMap ℂ R Y) ^ n = Y ^ n • c := by
  rw [← map_pow, ← Algebra.commutes, Algebra.smul_def]

theorem lead_iff (n : ℕ) (c : R) (f : ℂ → R) : Lead n c f ↔
    ∃ p : R[X], p.natDegree ≤ n ∧ p.coeff n = c ∧ ∀ Y, f Y = p.eval (algebraMap ℂ R Y) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨monomial n c + ∑ i ∈ range n, monomial i (a i), ?_, ?_, fun Y => ?_⟩
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le (Polynomial.natDegree_monomial_le _) ?_)
      exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
        (Polynomial.natDegree_monomial_le _).trans (Finset.mem_range.1 hi).le
    · rw [Polynomial.coeff_add, Polynomial.coeff_monomial, if_pos rfl, Polynomial.finset_sum_coeff,
        Finset.sum_eq_zero fun i hi => ?_, add_zero]
      rw [Polynomial.coeff_monomial, if_neg (Finset.mem_range.1 hi).ne]
    · rw [ha, Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.eval_finset_sum, mon_eval]
      simp only [Polynomial.eval_monomial, mon_eval]
  · rintro ⟨p, hp1, hp2, hp3⟩
    refine ⟨fun i => p.coeff i, fun Y => ?_⟩
    rw [hp3, Polynomial.eval_eq_sum_range' (show p.natDegree < n + 1 by omega), Finset.sum_range_succ, hp2,
      mon_eval, add_comm]
    simp only [mon_eval]

variable {n m : ℕ} {c d : R} {f g : ℂ → R}

theorem Lead.mul (hf : Lead n c f) (hg : Lead m d g) : Lead (n + m) (c * d) fun Y => f Y * g Y := by
  rw [lead_iff] at hf hg ⊢
  obtain ⟨p, hp1, hp2, hp3⟩ := hf
  obtain ⟨q, hq1, hq2, hq3⟩ := hg
  refine ⟨p * q, Polynomial.natDegree_mul_le.trans (add_le_add hp1 hq1), ?_, fun Y => ?_⟩
  · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp1 hq1, hp2, hq2]
  · rw [hp3, hq3]
    exact (map_mul (Polynomial.eval₂RingHom' (RingHom.id R) (algebraMap ℂ R Y)
      fun a => Algebra.commute_algebraMap_right Y a) p q).symm

theorem Lead.add (hf : Lead n c f) (hg : Lead n d g) : Lead n (c + d) fun Y => f Y + g Y := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun i => a i + b i, fun Y => ?_⟩
  simp only [ha, hb, smul_add, Finset.sum_add_distrib]
  abel

theorem Lead.const (c : R) : Lead 0 c fun _ => c := ⟨fun _ => 0, fun Y => by simp⟩

theorem Lead.succ (hf : Lead n c f) : Lead (n + 1) 0 f := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun i => if i = n then c else a i, fun Y => ?_⟩
  beta_reduce
  rw [ha, smul_zero, zero_add, Finset.sum_range_succ, if_pos rfl, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [if_neg (Finset.mem_range.1 hi).ne]

theorem Lead.lt (hf : Lead n c f) (h : n < m) : Lead m 0 f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  clear h
  induction k with
  | zero => exact hf.succ
  | succ k ih => exact ih.succ

theorem Lead.congr (hf : Lead n c f) (hn : n = m) (hc : c = d) (hg : ∀ Y, g Y = f Y) : Lead m d g := by
  subst hn hc
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun Y => by rw [hg, ha]⟩

theorem Lead.const_mul (a : R) (hf : Lead n c f) : Lead n (a * c) fun Y => a * f Y := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨fun i => a * b i, fun Y => by simp only [hb, mul_add, Finset.mul_sum, mul_smul_comm]⟩

theorem Lead.mul_const (a : R) (hf : Lead n c f) : Lead n (c * a) fun Y => f Y * a := by
  obtain ⟨b, hb⟩ := hf
  exact ⟨fun i => b i * a, fun Y => by simp only [hb, add_mul, Finset.sum_mul, smul_mul_assoc]⟩

theorem Lead.sum {ι : Type} (s : Finset ι) (F : ι → ℂ → R) (h : ∀ i ∈ s, Lead n 0 (F i)) :
    Lead n 0 fun Y => ∑ i ∈ s, F i Y := by
  classical
  choose! a ha using h
  refine ⟨fun j => ∑ i ∈ s, a i j, fun Y => ?_⟩
  show ∑ i ∈ s, F i Y = Y ^ n • (0 : R) + ∑ j ∈ range n, Y ^ j • ∑ i ∈ s, a i j
  rw [Finset.sum_congr rfl (fun i hi => ha i hi Y)]
  simp only [smul_zero, zero_add, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem Lead.lin (a b : R) : Lead 1 b fun Y => a + Y • b := ⟨fun _ => a, fun Y => by simp [add_comm]⟩

end lead

theorem lead_kap (n : ℕ) (p : Ty P → ℂ[X]) (c : Ty P → ℂ) (hp : ∀ π, (p π).natDegree ≤ n)
    (hc : ∀ π, (p π).coeff n = c π) : Lead n (kap P c) fun Y => kap P fun π => (p π).eval Y := by
  refine ⟨fun i => kap P fun π => (p π).coeff i, fun Y => ?_⟩
  have e : ∀ π, (p π).eval Y = Y ^ n * c π + ∑ i ∈ range n, Y ^ i * (p π).coeff i := by
    intro π
    rw [Polynomial.eval_eq_sum_range' (show (p π).natDegree < n + 1 by have := hp π; omega), Finset.sum_range_succ, hc π,
      Finset.sum_congr rfl fun i _ => mul_comm ((p π).coeff i) (Y ^ i)]
    ring
  have e2 : (fun π => (p π).eval Y) = Y ^ n • c + ∑ i ∈ range n, Y ^ i • (fun π => (p π).coeff i) := by
    funext π
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    exact e π
  show kap P (fun π => (p π).eval Y) = _
  rw [e2, map_add, map_smul, map_sum]
  simp only [map_smul]

theorem lead_prod (s : Finset ℕ) :
    Lead s.card (1 : A P) fun Y => kap P fun π => ∏ i ∈ s, (Y + (rho P π i : ℂ)) := by
  have hm : ∀ π : Ty P, (∏ i ∈ s, (X + C (rho P π i : ℂ))).Monic := fun π =>
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _
  have hd : ∀ π : Ty P, (∏ i ∈ s, (X + C (rho P π i : ℂ))).natDegree = s.card := fun π => by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
    simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  have h := lead_kap P s.card (fun π => ∏ i ∈ s, (X + C (rho P π i : ℂ))) (fun _ => 1)
    (fun π => (hd π).le) (fun π => by rw [← hd π]; exact (hm π).coeff_natDegree)
  refine h.congr rfl (map_one (kap P)) fun Y => ?_
  congr 1
  funext π
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

theorem card_I : (Icc 1 (P.k - 1)).card = P.k - 1 := by
  rw [Nat.card_Icc]
  omega

theorem lead_xA : Lead (P.k - 1) (1 : A P) (xA P) := (lead_prod P (Icc 1 (P.k - 1))).congr (card_I P) rfl fun Y => rfl

theorem lead_xEx (ex : Finset ℕ) (m : ℕ) (hm : P.k - 1 < m) :
    Lead m (0 : A P) fun Y => kap P fun π => xEx P ex π Y := ((lead_prod P (Icc 1 (P.k - 1) \ ex)).lt
    (lt_of_le_of_lt ((Finset.card_le_card Finset.sdiff_subset).trans (card_I P).le) hm)).congr rfl rfl
    fun Y => rfl

theorem leading_coeff_S21 (m : ℕ) (hm : P.k - 1 < m) : Lead m (0 : A P) (weightedSumBis P) := by
  refine (Lead.sum (Icc 1 (P.k - 1)) (fun l Y => SS P l * kap P fun π => xEx P {l} π Y)
    fun l _ => ?_).congr rfl rfl fun Y => rfl
  exact ((lead_xEx P {l} m hm).const_mul (SS P l)).congr rfl (mul_zero _) fun Y => rfl

theorem leading_term_upper_sum (m : ℕ) (hm : P.k - 1 < m) : Lead m (0 : A P) (S12 P) := by
  refine (Lead.sum (Icc 1 (P.k - 1)) (fun l Y => (kap P fun π => xEx P {l} π Y) * star (SS P l))
    fun l _ => ?_).congr rfl rfl fun Y => rfl
  exact ((lead_xEx P {l} m hm).mul_const (star (SS P l))).congr rfl (zero_mul _) fun Y => rfl

theorem leading_coeff_S4 (m : ℕ) (hm : P.k - 1 < m) : Lead m (0 : A P) (S4 P) := by
  refine (Lead.sum (Icc 1 (P.k - 1)) (fun l Y => ∑ j ∈ (Icc 1 (P.k - 1)).erase l,
      star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π Y) fun l _ => ?_).congr rfl rfl fun Y => rfl
  refine Lead.sum _ (fun j Y => star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π Y) fun j _ => ?_
  exact ((lead_xEx P {l, j} m hm).const_mul (star (SS P l) * SS P j)).congr rfl (mul_zero _) fun Y => rfl

theorem leading_coeff_l0 : Lead 1 (-(zbA P * ggiA P)) (l0A P) := by
  refine (Lead.lin (-nabA P - (1 / 2 : ℂ) • (zbA P * ggiA P)) (-(zbA P * ggiA P))).congr rfl rfl fun Y => ?_
  unfold l0A
  rw [← Algebra.smul_def, add_smul, smul_neg]
  abel

theorem leading_term_lowering_constant : Lead 1 (-(zA P * ggiA P)) (m0A P) := by
  refine (Lead.lin (-nabsA P + (1 / 2 : ℂ) • (zA P * ggiA P)) (-(zA P * ggiA P))).congr rfl rfl fun Y => ?_
  unfold m0A
  rw [← Algebra.smul_def, sub_smul, smul_neg]
  abel

theorem natDegree_x_polynomial (π : Ty P) : (coordinatePolynomial P π).natDegree = P.k - 1 := by
  unfold coordinatePolynomial
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Nat.card_Icc]
  omega

theorem wNum_deg (hk : 1 ≤ P.k) (π : Ty P) : (wNum P π).natDegree ≤ 2 * P.k ∧
    (wNum P π).coeff (2 * P.k) = -((P.T : ℂ) * P.T') := by
  have hm : (∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))).Monic :=
    monic_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _)
  have hd : (∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))).natDegree
      = 2 * P.k := by
    rw [natDegree_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _)]
    have : ∀ i ∈ Icc 1 P.k,
        ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := fun i _ => by
      rw [(monic_X_add_C _).natDegree_mul (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
    rw [sum_congr rfl this]
    simp [mul_comm]
  have he : ∀ (l : ℕ) (ρ : ℕ → ℂ), (∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (ρ j))).natDegree ≤ P.k - 1 := by
    intro l ρ
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]
    exact (card_le_card (erase_subset _ _)).trans (card_I P).le
  have ht : (∑ l ∈ Icc 1 (P.k - 1), C ((Nrm P l π : ℝ) : ℂ) *
      ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (rho P π j : ℂ))) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C ((rho P π j : ℂ) + 1)))).natDegree ≤
      (P.k - 1) + (P.k - 1) :=
    natDegree_sum_le_of_forall_le _ _ fun l _ => (natDegree_C_mul_le _ _).trans
      (natDegree_mul_le_of_le (he l _) (he l _))
  have hq : (qP P).natDegree ≤ 2 * P.k := (natDegree_C_mul_le _ _).trans hd.le
  constructor
  · exact natDegree_add_le_of_degree_le hq (ht.trans (by omega))
  · unfold wNum
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ht (by omega)), add_zero, qP,
      coeff_C_mul, ← hd, hm.coeff_natDegree, mul_one]

theorem wq_deg (hP : P.OK) (π : Ty P) : (wNum P π /ₘ coordinatePolynomial P π).natDegree ≤ P.k + 1 ∧
    (wNum P π /ₘ coordinatePolynomial P π).coeff (P.k + 1) = -((P.T : ℂ) * P.T') := by
  have hk := hP.k_pos
  have hm := coordinate_polynomial_monic P π
  have hd := natDegree_x_polynomial P π
  obtain ⟨h1, h2⟩ := wNum_deg P hk π
  have h3 : (wNum P π /ₘ coordinatePolynomial P π).natDegree ≤ P.k + 1 := by
    rw [natDegree_divByMonic _ hm, hd]; omega
  refine ⟨h3, ?_⟩
  have h6 := coeff_mul_add_eq_of_natDegree_le hd.le h3
  rw [← weight_exact P hP π] at h6
  have h7 : (coordinatePolynomial P π).coeff (P.k - 1) = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have e : P.k - 1 + (P.k + 1) = 2 * P.k := by omega
  rw [h7, one_mul, e, h2] at h6
  exact h6.symm

theorem gg_zb : ggA P * zbA P = zbA P * ggA P := by
  unfold ggA zbA ggP zbP
  exact fn_comm P _ _ _ _
theorem GG_commute_z : ggA P * zA P = zA P * ggA P := by
  unfold ggA zA ggP zP
  exact fn_comm P _ _ _ _

theorem gg_zb_ggi : ggA P * (zbA P * ggiA P) = zbA P := by rw [← mul_assoc, gg_zb, mul_assoc, gg_ggi, mul_one]

theorem gg_z_ggi : ggA P * (zA P * ggiA P) = zA P := by rw [← mul_assoc, GG_commute_z, mul_assoc, gg_ggi, mul_one]

theorem leading_coeff_t22 : Lead (P.k - 1) (ggA P) (t22 P) := ((lead_xA P).const_mul (ggA P)).congr rfl (mul_one _) fun Y => rfl

theorem leading_term_lower_left (hk : 1 ≤ P.k) : Lead P.k (-zbA P) (t21 P) := by
  have h1 := ((leading_coeff_t22 P).mul (leading_coeff_l0 P)).congr (Nat.sub_add_cancel hk) rfl fun Y => rfl
  refine (h1.add (leading_coeff_S21 P P.k (by omega))).congr rfl ?_ fun Y => rfl
  rw [add_zero, mul_neg, gg_zb_ggi]

theorem leading_coeff_t12 (hk : 1 ≤ P.k) : Lead P.k (-zA P) (t12 P) := by
  have h1 := ((leading_coeff_t22 P).mul (leading_term_lowering_constant P)).congr (Nat.sub_add_cancel hk) rfl fun Y => rfl
  refine (h1.add (leading_term_upper_sum P P.k (by omega))).congr rfl ?_ fun Y => rfl
  rw [add_zero, mul_neg, gg_z_ggi]

theorem lead_coef : ggiA P * (kap P fun _ => -((P.T : ℂ) * P.T')) +
    ggA P * 1 * -(zA P * ggiA P) * -(zbA P * ggiA P) = 1 := by
  have h2 : zA P * ggiA P = ggiA P * zA P := by
    unfold zA ggiA zP ggiP
    exact fn_comm P _ _ _ _
  have h1 : zbA P * ggiA P = ggiA P * zbA P := by
    unfold zbA ggiA zbP ggiP
    exact fn_comm P _ _ _ _
  have hc : zA P * (zbA P * ggiA P) = ggiA P * (zA P * zbA P) := by
    rw [h1, ← mul_assoc, h2, mul_assoc]
  have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * P.T' := by
    unfold Par.TT
    push_cast
    ring
  rw [kap_const, mul_one, mul_neg, mul_neg, neg_mul, neg_neg, gg_z_ggi, hc, ← ggi_gg P, gg_def, hT, mul_sub, map_neg, mul_neg]
  abel

theorem leading_coeff_t11 (hP : P.OK) : Lead (P.k + 1) (1 : A P) (t11 P) := by
  have hk := hP.k_pos
  have h1 : Lead (P.k + 1) (ggiA P * kap P fun _ => -((P.T : ℂ) * P.T'))
      (fun Y => ggiA P * kap P fun π => (wNum P π /ₘ coordinatePolynomial P π).eval Y) :=
    (lead_kap P (P.k + 1) (fun π => wNum P π /ₘ coordinatePolynomial P π) (fun _ => -((P.T : ℂ) * P.T'))
      (fun π => (wq_deg P hP π).1) (fun π => (wq_deg P hP π).2)).const_mul (ggiA P)
  have h2 : Lead (P.k + 1) (ggA P * 1 * -(zA P * ggiA P) * -(zbA P * ggiA P))
      (fun Y => ggA P * xA P Y * m0A P Y * l0A P Y) :=
    ((((lead_xA P).const_mul (ggA P)).mul (leading_term_lowering_constant P)).mul (leading_coeff_l0 P)).congr (by omega) rfl fun Y => rfl
  have h3 : Lead (P.k + 1) (0 : A P) (fun Y => ggA P * m0A P Y * ggiA P * weightedSumBis P Y) :=
    ((((leading_term_lowering_constant P).const_mul (ggA P)).mul_const (ggiA P)).mul (leading_coeff_S21 P P.k (by omega))).congr
      (by omega) (mul_zero _) fun Y => rfl
  have h4 : Lead (P.k + 1) (0 : A P) (fun Y => S12 P Y * l0A P Y) :=
    ((leading_term_upper_sum P P.k (by omega)).mul (leading_coeff_l0 P)).congr rfl (zero_mul _) fun Y => rfl
  have h5 : Lead (P.k + 1) (0 : A P) (fun Y => ggiA P * S4 P Y) :=
    ((leading_coeff_S4 P (P.k + 1) (by omega)).const_mul (ggiA P)).congr rfl (mul_zero _) fun Y => rfl
  refine ((((h1.add h2).add h3).add h4).add h5).congr rfl ?_ fun Y => rfl
  rw [add_zero, add_zero, add_zero, lead_coef]

theorem qQLeading : QQLeading := by
  intro P hP
  obtain ⟨a11, h11⟩ := leading_coeff_t11 P hP
  obtain ⟨a12, h12⟩ := leading_coeff_t12 P hP.k_pos
  obtain ⟨a21, h21⟩ := leading_term_lower_left P hP.k_pos
  obtain ⟨a22, h22⟩ := leading_coeff_t22 P
  refine ⟨a11, a12, a21, a22, fun Y => ⟨h11 Y, ?_, ?_, h22 Y⟩⟩
  · rw [h12, smul_neg]
  · rw [h21, smul_neg]

theorem xC_split (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (π : Ty P) (Y : ℂ) :
    xC P π Y = (Y + (rho P π j : ℂ)) * xEx P {j} π Y := by
  unfold xC xEx
  rw [Finset.sdiff_singleton_eq_erase]
  exact (Finset.mul_prod_erase _ (fun i => Y + (rho P π i : ℂ)) hj).symm

theorem xEx_insert (ex : Finset ℕ) (a : ℕ) (ha : a ∈ Icc 1 (P.k - 1) \ ex) (π : Ty P) (Y : ℂ) :
    xEx P ex π Y = (Y + (rho P π a : ℂ)) * xEx P (insert a ex) π Y := by
  unfold xEx
  rw [Finset.sdiff_insert]
  exact (Finset.mul_prod_erase _ (fun i => Y + (rho P π i : ℂ)) ha).symm

theorem fac_ne {π : Ty P} {Y : ℂ} (hx : xC P π Y ≠ 0) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    Y + (rho P π j : ℂ) ≠ 0 := by
  unfold xC at hx
  exact Finset.prod_ne_zero_iff.mp hx j hj

theorem x_iv (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) :
    xA P Y * (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) = kap P fun π => xEx P {j} π Y := by
  unfold xA
  rw [← kap_mul]
  congr 1
  funext π
  rw [xC_split P j hj π Y, mul_right_comm, mul_inv_cancel₀ (fac_ne P (hx π) hj), one_mul]

theorem x_sl (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    xA P Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j = weightedSumBis P Y := by
  unfold weightedSumBis
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, x_iv P Y hx j hj]
  exact kap_ss P j _ (fun π π' h => xEx_up P j {j} (Finset.mem_singleton_self j) Y π π' h)

theorem x_sm (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    xA P Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P j) =
      S12 P Y := by
  unfold S12
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, x_iv P Y hx j hj]

theorem gxg (f : Ty P → ℂ) (Z : A P) : ggA P * kap P f * (ggiA P * Z) = kap P f * Z := by rw [← kap_gg, mul_assoc, ← mul_assoc (ggA P), gg_ggi, one_mul]

theorem gxg' (Y : ℂ) (Z : A P) : ggA P * xA P Y * (ggiA P * Z) = xA P Y * Z := by
  unfold xA
  exact gxg P _ Z

theorem lower_left_normal_form (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) : t21 P Y = t22 P Y * lA P Y := by
  unfold t21 t22 lA
  rw [mul_add, gxg', x_sl P Y hx]

theorem upper_right_normal_form (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) : t12 P Y = t22 P Y * mA P Y := by
  unfold t12 t22 mA
  rw [mul_add, gxg', x_sm P Y hx]

theorem eval_x_polynomial (π : Ty P) (Y : ℂ) : (coordinatePolynomial P π).eval Y = xC P π (Y + 1) := by
  unfold coordinatePolynomial xC
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  ring

theorem eval_qP (Y : ℂ) : (qP P).eval Y = qC P Y := by
  unfold qP qC
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  ring

theorem eval_wNum (π : Ty P) (Y : ℂ) : (wNum P π).eval Y = qC P Y +
    ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1)) := by
  unfold wNum
  rw [Polynomial.eval_add, eval_qP, Polynomial.eval_finset_sum]
  refine congrArg (qC P Y + ·) (Finset.sum_congr rfl fun l _ => ?_)
  unfold xEx
  rw [Finset.sdiff_singleton_eq_erase]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X]
  rw [Finset.prod_congr rfl fun j _ => (add_assoc Y 1 (rho P π j : ℂ)).trans (by rw [add_comm 1])]

theorem wC_id (hP : P.OK) (π : Ty P) (Y : ℂ) (h1 : xC P π (Y + 1) ≠ 0) :
    wC P π Y = qC P Y * (xC P π (Y + 1))⁻¹ +
      ∑ l ∈ Icc 1 (P.k - 1), xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
  have hW : (wNum P π).eval Y = xC P π (Y + 1) * wC P π Y := by
    have h := congrArg (eval Y) (weight_exact P hP π)
    rw [eval_mul, eval_x_polynomial] at h
    exact h
  apply mul_left_cancel₀ h1
  rw [← hW, eval_wNum, mul_add, mul_sum]
  congr 1
  · rw [mul_comm (qC P Y), ← mul_assoc, mul_inv_cancel₀ h1, one_mul]
  · refine sum_congr rfl fun l hl => ?_
    have hne : Y + 1 + (rho P π l : ℂ) ≠ 0 := fac_ne P h1 hl
    have e : Y + (rho P π l : ℂ) + 1 = Y + 1 + (rho P π l : ℂ) := by ring
    rw [xC_split P l hl π (Y + 1), e]
    calc ((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1))
        = ((Y + 1 + (rho P π l : ℂ)) * (Y + 1 + (rho P π l : ℂ))⁻¹) *
          (((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1))) := by
          rw [mul_inv_cancel₀ hne, one_mul]
      _ = _ := by ring

theorem rho_up_same {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {π π' : Ty P} (h : Up P l π π') :
    rho P π' l = rho P π l + 1 := by
  rw [Finset.mem_Icc] at hl
  unfold rho
  simp only [dif_pos hl]
  have := h ⟨l - 1, by omega⟩
  simp only [Fin.val_mk] at this
  rw [if_pos (by omega)] at this
  rw [this]
  push_cast
  ring

theorem rho_up_ne {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) {π π' : Ty P} (h : Up P l π π') :
    rho P π' j = rho P π j := by
  rw [Finset.mem_Icc] at hj
  unfold rho
  simp only [dif_pos hj]
  have := h ⟨j - 1, by omega⟩
  simp only [Fin.val_mk] at this
  rw [if_neg (by omega), add_zero] at this
  rw [this]

theorem diag_term {l : ℕ} (hN : star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ)) (Y : ℂ)
    (hl : l ∈ Icc 1 (P.k - 1)) :
    (kap P fun π => xEx P {l} π Y) * star (SS P l) * ((kap P fun π => (Y + (rho P π l : ℂ))⁻¹) * SS P l) =
      kap P fun π => xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
  have hs := sss_shift P l (fun π => (Y + (rho P π l : ℂ) + 1)⁻¹) (fun π => (Y + (rho P π l : ℂ))⁻¹)
    (fun π π' h => by
      beta_reduce
      rw [rho_up_same P hl h]
      push_cast
      ring)
  rw [← mul_assoc, mul_assoc (kap P _) (star (SS P l)), hs, ← mul_assoc, mul_assoc _ (star (SS P l)), hN,
    ← kap_mul, ← kap_mul]
  refine congrArg (kap P) (funext fun π => ?_)
  ring

theorem off_term (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) {l j : ℕ}
    (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    (kap P fun π => xEx P {l} π Y) * star (SS P l) * ((kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) =
      star (SS P l) * SS P j * kap P fun π => xEx P {l, j} π Y := by
  have hjl' : j ∈ Icc 1 (P.k - 1) \ {l} := Finset.mem_sdiff.2 ⟨hj, by simpa using hjl⟩
  have e : (fun π => xEx P {l} π Y * (Y + (rho P π j : ℂ))⁻¹) = fun π => xEx P {l, j} π Y := by
    funext π
    rw [xEx_insert P {l} j hjl' π Y, Finset.pair_comm, mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (fac_ne P (hx π) hj), one_mul]
  rw [(kap_sss P l _ fun π π' h => xEx_up P l {l} (Finset.mem_singleton_self l) Y π π' h).eq, mul_assoc,
    ← mul_assoc (kap P _), ← kap_mul, e,
    (kap_ss P j _ fun π π' h => xEx_up P j {l, j} (by simp) Y π π' h).eq, ← mul_assoc]

theorem upper_sum_mul_inverse_sum (hN : ∀ l ∈ Icc 1 (P.k - 1), star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ))
    (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    S12 P Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j =
      (kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹) + S4 P Y := by
  unfold S12 S4
  rw [Finset.sum_mul, kap_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ hl, diag_term P (hN l hl) Y hl, add_right_inj]
  exact Finset.sum_congr rfl fun j hj =>
    off_term P Y hx (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)

theorem coordinate_commute_raising (Y Y' : ℂ) : xA P Y * m0A P Y' = m0A P Y' * xA P Y := by
  unfold xA
  exact kappa_commute_raising_constant P _ Y'
theorem xA_ggi (Y : ℂ) : xA P Y * ggiA P = ggiA P * xA P Y := by
  unfold xA
  exact kap_ggi P _

theorem upper_sum_gamma_inv_comm (Y : ℂ) : S12 P Y * ggiA P = ggiA P * S12 P Y := by
  unfold ggiA
  exact upper_sum_commute_scalar P Y _

theorem upper_left_normal_form (hP : P.OK)
    (hN : ∀ l ∈ Icc 1 (P.k - 1), star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ))
    (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) (hx1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    t11 P Y = qC P Y • (ggiA P * kap P fun π => (xC P π (Y + 1))⁻¹) + t22 P Y * mA P Y * lA P Y := by
  have hw : ggiA P * (kap P fun π => wC P π Y) = qC P Y • (ggiA P * kap P fun π => (xC P π (Y + 1))⁻¹) +
      ggiA P * kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
    rw [← mul_smul_comm, ← mul_add, ← kap_smul, ← kap_add]
    exact congrArg (fun F => ggiA P * kap P F) (funext fun π => wC_id P hP π Y (hx1 π))
  have ha : ggA P * xA P Y * m0A P Y *
      (ggiA P * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) =
      ggA P * m0A P Y * ggiA P * weightedSumBis P Y := by
    rw [← x_sl P Y hx]
    simp only [mul_assoc]
    rw [← mul_assoc (xA P Y) (m0A P Y), coordinate_commute_raising, mul_assoc, ← mul_assoc (xA P Y) (ggiA P), xA_ggi, mul_assoc]
  have hb : S12 P Y *
      (ggiA P * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j) =
      ggiA P * (kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹) + ggiA P * S4 P Y := by
    rw [← mul_assoc, upper_sum_gamma_inv_comm, mul_assoc, upper_sum_mul_inverse_sum P hN Y hx, mul_add]
  rw [← upper_right_normal_form P Y hx]
  unfold t11 t12 lA
  rw [hw, add_mul, mul_add, mul_add, ha, hb]
  abel

theorem gamma_inv_commute_zeta : ggiA P * zA P = zA P * ggiA P := by
  unfold ggiA zA ggiP zP
  exact fn_comm P _ _ _ _

theorem star_l0_shift (Y : ℂ) (hY : star Y = Y) : star (l0A P (Y - 1)) = m0A P Y := by
  rw [star_lowering_constant, star_sub, hY, star_one, raising_constant_eq_nabla_star, raising_constant_eq_nabla_star,
    block_frame_conjugation_identity (ggA P) (ggiA P) (zA P) (nabsA P) (Y - 1 - 1 / 2) 1 (gg_ggi P) (by rw [nabs_gg, one_smul])
      (GG_commute_z P).symm (gamma_inv_commute_zeta P).symm, gamma_inv_commute_zeta P, show Y - 1 - 1 / 2 + 1 = Y - 1 / 2 by ring]

theorem mA_star (Y : ℂ) (hY : star Y = Y) : mA P Y = star (lA P (Y - 1)) := by
  have hY' : (starRingEnd ℂ) Y = Y := hY
  unfold mA lA
  rw [star_add, star_l0_shift P Y hY, star_mul, star_ggi, star_sum, Finset.sum_mul, Finset.mul_sum,
    add_right_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [star_mul, star_kap]
  have hs := sss_shift P j (fun π => (Y + (rho P π j : ℂ))⁻¹) (fun π => star ((Y - 1 + (rho P π j : ℂ))⁻¹))
    (fun π π' h => by
      beta_reduce
      rw [rho_up_same P hj h]
      simp [hY, hY', Complex.conj_ofReal]
      try ring)
  rw [hs]
  unfold ggiA
  exact ((kap_sc P _ _).mul_left (sss_sc P j _)).eq.symm

theorem qQNormal_of (hN : SSNorm) : QQNormal := by
  intro P hP Y hx
  have hN' : ∀ l ∈ Icc 1 (P.k - 1), star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ) :=
    fun l hl => (hN P hP l hl).1
  exact ⟨lower_left_normal_form P Y hx, upper_right_normal_form P Y hx, fun hx1 => upper_left_normal_form P hP hN' Y hx hx1,
    fun hY => mA_star P Y hY⟩

end Formalism.FourierDecayAlt.P.Mx5

namespace Formalism.FourierDecayAlt.P

theorem transfer_normal_alt : Formalism.FourierDecayAlt.M.QQNormal := Mx5.qQNormal_of shift_norm_relation

theorem transfer_hermitian : Formalism.FourierDecayAlt.M.QQHerm := Mx5.qQHerm

theorem transfer_leading : Formalism.FourierDecayAlt.M.QQLeading := Mx5.qQLeading

theorem transfer_zeta : Formalism.FourierDecayAlt.M.QQZeta := Mx5.qQZeta

end Formalism.FourierDecayAlt.P
