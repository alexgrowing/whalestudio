import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingConstantEqNablaStar

namespace Formalism.FourierDecayAlt.P.Mx7

section PartT

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

theorem kap_eq (P : Par) (f : Ty P → ℂ) :
    kap P f = Matrix.diagonal fun π => algebraMap ℂ (Pr P.r) (f π) := rfl

theorem kap_comm_diagonal (P : Par) (f : Ty P → ℂ) (d : Ty P → Pr P.r) :
    Commute (kap P f) (Matrix.diagonal d) := by
  show kap P f * Matrix.diagonal d = Matrix.diagonal d * kap P f
  rw [kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

theorem kap_comm_sc (P : Par) (f : Ty P → ℂ) (w : Pr P.r) : Commute (kap P f) (sc P w) := by
  have : sc P w = Matrix.diagonal fun _ => w := by simp [sc, Matrix.scalar_apply]
  rw [this]; exact kap_comm_diagonal P f _

theorem kap_comm_nab (P : Par) (f : Ty P → ℂ) : Commute (kap P f) (nabA P) := kap_comm_diagonal P f _

theorem kap_comm_nabs (P : Par) (f : Ty P → ℂ) : Commute (kap P f) (nabsA P) := kap_comm_diagonal P f _

theorem kap_comm_kap (P : Par) (f g : Ty P → ℂ) : Commute (kap P f) (kap P g) := by
  show kap P f * kap P g = kap P g * kap P f
  rw [← map_mul, ← map_mul, mul_comm]

theorem xC_eq (P : Par) (π : Ty P) (Y : ℂ) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    xC P π Y = xEx P {l} π Y * (Y + (rho P π l : ℂ)) := by
  unfold xC xEx
  calc ∏ i ∈ Icc 1 (P.k - 1), (Y + (rho P π i : ℂ))
      = (∏ i ∈ Icc 1 (P.k - 1) \ {l}, (Y + (rho P π i : ℂ))) * ∏ i ∈ {l}, (Y + (rho P π i : ℂ)) :=
        (Finset.prod_sdiff (Finset.singleton_subset_iff.2 hl)).symm
    _ = _ := by rw [Finset.prod_singleton]

theorem xEx_pair (P : Par) (π : Ty P) (Y : ℂ) (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    xEx P {l} π Y = xEx P {l, j} π Y * (Y + (rho P π j : ℂ)) := by
  unfold xEx
  have hset : Icc 1 (P.k - 1) \ {l, j} = (Icc 1 (P.k - 1) \ {l}) \ {j} := by
    ext i; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1) \ {l} :=
    Finset.singleton_subset_iff.2 (Finset.mem_sdiff.2 ⟨hj, by simpa using hjl⟩)
  rw [hset]
  calc ∏ i ∈ Icc 1 (P.k - 1) \ {l}, (Y + (rho P π i : ℂ))
      = (∏ i ∈ (Icc 1 (P.k - 1) \ {l}) \ {j}, (Y + (rho P π i : ℂ))) * ∏ i ∈ {j}, (Y + (rho P π i : ℂ)) :=
        (Finset.prod_sdiff hsub).symm
    _ = _ := by rw [Finset.prod_singleton]

theorem xEx_pair' (P : Par) (π : Ty P) (Y : ℂ) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    xEx P {j} π Y = xEx P {l, j} π Y * (Y + (rho P π l : ℂ)) := by
  rw [Finset.pair_comm l j]; exact xEx_pair P π Y j l hl (Ne.symm hjl)

theorem xEx_up (hR : RhoUp) (P : Par) (l : ℕ) (π π' : Ty P) (hU : Up P l π π') (ex : Finset ℕ) (hl : l ∈ ex)
    (Y : ℂ) : xEx P ex π' Y = xEx P ex π Y := by
  unfold xEx
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hi' := Finset.mem_sdiff.1 hi
  have hne : i ≠ l := fun h => hi'.2 (h ▸ hl)
  rw [hR P l π π' hU i hi'.1, if_neg hne, add_zero]

theorem rho_up (hR : RhoUp) (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    rho P π' l = rho P π l + 1 := by
  rw [hR P l π π' hU l hl, if_pos rfl]

theorem sh_same (hSh : SSShift) (hR : RhoUp) (P : Par) (l : ℕ) (ex : Finset ℕ) (hl : l ∈ ex) (Y : ℂ) :
    (kap P fun π => xEx P ex π Y) * SS P l = SS P l * kap P fun π => xEx P ex π Y :=
  hSh P l _ _ (fun π π' hU => xEx_up hR P l π π' hU ex hl Y)

theorem shift_x_identity (hSh : SSShift) (hR : RhoUp) (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (Y : ℂ) :
    xA P Y * SS P l = SS P l * kap P fun π => xEx P {l} π Y * (Y + 1 + (rho P π l : ℂ)) :=
  hSh P l _ _ (fun π π' hU => by
    show xC P π' Y = _
    rw [xC_eq P π' Y l hl, xEx_up hR P l π π' hU {l} (Finset.mem_singleton_self l), rho_up hR P l hl π π' hU]
    push_cast; ring)

theorem sh_pair (hSh : SSShift) (hR : RhoUp) (P : Par) (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) (Y : ℂ) :
    (kap P fun π => xEx P {l} π Y) * SS P j = SS P j * kap P fun π => xEx P {l, j} π Y * (Y + 1 + (rho P π j : ℂ)) :=
  hSh P j _ _ (fun π π' hU => by
    show xEx P {l} π' Y = _
    rw [xEx_pair P π' Y l j hj hjl, xEx_up hR P j π π' hU {l, j} (by simp), rho_up hR P j hj π π' hU]
    push_cast; ring)

theorem lowering_constant_eq_shift (P : Par) (Y : ℂ) : l0A P Y = -nabA P - (Y + 1 / 2) • (zbA P * ggiA P) := by
  rw [l0A, Algebra.smul_def]

section abs

variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem absW (G b zb N : R) (hGb : G * b = zb) (hNb : N * b = b * N - b * b) (cu cv : ℂ) :
    (G * (-N - cu • b) - zb) * (-N - cv • b) =
      G * N * N + (cu + cv + 1) • (zb * N) + (cu * cv) • (zb * b) := by
  have h1 : G * (-N - cu • b) - zb = -(G * N) - (cu + 1) • zb := by
    rw [mul_sub, mul_neg, mul_smul_comm, hGb]; module
  have h2 : G * N * b = zb * N - zb * b := by
    rw [mul_assoc, hNb, mul_sub, ← mul_assoc, ← mul_assoc, hGb]
  rw [h1]
  simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, h2]
  module

theorem absLG (G b zb N : R) (hNG : N * G = G * N + zb) (hbG : b * G = G * b) (c : ℂ) :
    (-N - c • b) * G = G * (-N - c • b) - zb := by
  rw [sub_mul, neg_mul, smul_mul_assoc, hNG, hbG, mul_sub, mul_neg, mul_smul_comm]; abel

theorem absA (G b zb N X X' : R) (hNG : N * G = G * N + zb) (hbG : b * G = G * b)
    (hG : Commute X' G) (hb : Commute X' b) (hN : Commute X' N) (hzb : Commute X' zb) (cu cv : ℂ) :
    (G * X * (-N - cu • b)) * (G * X' * (-N - cv • b)) =
      G * (X * X') * ((G * (-N - cu • b) - zb) * (-N - cv • b)) := by
  have hc : (G * (-N - cu • b) - zb) * X' = X' * (G * (-N - cu • b) - zb) :=
    ((hG.mul_right ((hN.neg_right).sub_right (hb.smul_right cu))).sub_right hzb).eq.symm
  calc (G * X * (-N - cu • b)) * (G * X' * (-N - cv • b))
      = G * X * ((-N - cu • b) * G) * X' * (-N - cv • b) := by simp only [mul_assoc]
    _ = G * X * ((G * (-N - cu • b) - zb) * X') * (-N - cv • b) := by
        rw [absLG G b zb N hNG hbG]; simp only [mul_assoc]
    _ = _ := by rw [hc]; simp only [mul_assoc]

theorem absNb (zb Gi N : R) (hNzb : N * zb = zb * N) (hNGi : N * Gi = Gi * N - zb * Gi * Gi)
    (hc : Gi * zb = zb * Gi) : N * (zb * Gi) = (zb * Gi) * N - (zb * Gi) * (zb * Gi) := by
  rw [← mul_assoc, hNzb, mul_assoc, hNGi, mul_sub, ← mul_assoc zb Gi N, mul_assoc zb Gi (zb * Gi),
    ← mul_assoc Gi zb Gi, hc]

theorem absLS (b N S : R) (hNS : N * S = S * N - b * S) (hbS : b * S = S * b) (c : ℂ) :
    (-N - c • b) * S = S * ((-N - c • b) + b) := by
  rw [sub_mul, neg_mul, smul_mul_assoc, hNS, hbS, mul_add, mul_sub, mul_neg, mul_smul_comm]; abel

theorem weighted_sum_difference_identity (G b N S X Xp E : R) (hNS : N * S = S * N - b * S) (hbS : b * S = S * b)
    (hXS : X * S = S * Xp) (hSG : S * G = G * S) (hEN : Commute E N) (hEb : Commute E b) (c : ℂ) :
    G * X * (-N - c • b) * (S * E) = S * G * (Xp * E * ((-N - c • b) + b)) := by
  have hE : ((-N - c • b) + b) * E = E * ((-N - c • b) + b) :=
    (((hEN.neg_right).sub_right (hEb.smul_right c)).add_right hEb).eq.symm
  calc G * X * (-N - c • b) * (S * E) = G * X * ((-N - c • b) * S) * E := by simp only [mul_assoc]
    _ = G * (X * S) * (((-N - c • b) + b) * E) := by rw [absLS b N S hNS hbS]; simp only [mul_assoc]
    _ = G * (S * Xp) * (E * ((-N - c • b) + b)) := by rw [hXS, hE]
    _ = (G * S) * (Xp * E * ((-N - c • b) + b)) := by simp only [mul_assoc]
    _ = _ := by rw [← hSG]

theorem mul_assoc_commute_middle (G S X E L : R) (hEG : E * G = G * E) :
    (S * E) * (G * X * L) = S * G * (E * X * L) := by
  calc (S * E) * (G * X * L) = S * (E * G) * (X * L) := by simp only [mul_assoc]
    _ = S * (G * E) * (X * L) := by rw [hEG]
    _ = _ := by simp only [mul_assoc]

theorem absCombo {C : Type*} [CommRing C] [Algebra ℂ C] (κ : C →ₐ[ℂ] R) (N b : R) (φ1 φ2 ψ1 ψ2 : C) (cu cv : ℂ)
    (h1 : φ1 + φ2 = ψ1 + ψ2) (h2 : (1 - cu) • φ1 - cv • φ2 = (1 - cv) • ψ1 - cu • ψ2) :
    κ φ1 * ((-N - cu • b) + b) + κ φ2 * (-N - cv • b) = κ ψ1 * ((-N - cv • b) + b) + κ ψ2 * (-N - cu • b) := by
  have e1 := congrArg (fun f => κ f * N) h1
  have e2 := congrArg (fun f => κ f * b) h2
  simp only [map_add, map_sub, map_smul, add_mul, sub_mul, smul_mul_assoc] at e1 e2
  simp only [mul_add, mul_sub, mul_neg, mul_smul_comm]
  linear_combination (norm := module) -e1 + e2

theorem sum_anti {M : Type*} [AddCommGroup M] [Module ℂ M] (s : Finset ℕ) (D : ℕ → ℕ → M)
    (h : ∀ l ∈ s, ∀ j ∈ s, D l j + D j l = 0) : ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by
  have hc : ∑ l ∈ s, ∑ j ∈ s, D l j = ∑ l ∈ s, ∑ j ∈ s, D j l := Finset.sum_comm
  have h2 : ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by
    calc ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D l j
        = ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D j l := by rw [← hc]
      _ = ∑ l ∈ s, ∑ j ∈ s, (D l j + D j l) := by simp only [Finset.sum_add_distrib]
      _ = 0 := Finset.sum_eq_zero (fun l hl => Finset.sum_eq_zero (fun j hj => h l hl j hj))
  have h3 : (2 : ℂ) • ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

end abs

theorem TT_eq (P : Par) (l j : ℕ) (f g f' : Ty P → ℂ) (h : kap P f * SS P j = SS P j * kap P f') :
    (SS P l * kap P f) * (SS P j * kap P g) = SS P l * SS P j * kap P (f' * g) := by
  rw [map_mul]
  calc (SS P l * kap P f) * (SS P j * kap P g) = SS P l * (kap P f * SS P j) * kap P g := by
        simp only [mul_assoc]
    _ = _ := by rw [h]; simp only [mul_assoc]

theorem compA (hLN : LevNab) (hLF : LevFns) (P : Par) (u v : ℂ) :
    (ggA P * xA P u * l0A P u) * (ggA P * xA P v * l0A P v) =
      (ggA P * xA P v * l0A P v) * (ggA P * xA P u * l0A P u) := by
  obtain ⟨_, _, hNzb, _, hNG, hNGi, _⟩ := hLN P
  obtain ⟨hcomm, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P
  have mzb : zbA P ∈ fnsA P := by unfold fnsA; simp
  have mG : ggA P ∈ fnsA P := by unfold fnsA; simp
  have mGi : ggiA P ∈ fnsA P := by unfold fnsA; simp
  have hGb : ggA P * (zbA P * ggiA P) = zbA P := by
    rw [← mul_assoc, hcomm _ mG _ mzb, mul_assoc, hGGi, mul_one]
  have hbG : (zbA P * ggiA P) * ggA P = ggA P * (zbA P * ggiA P) := by
    rw [hGb, mul_assoc, hGiG, mul_one]
  have hNb : nabA P * (zbA P * ggiA P) = (zbA P * ggiA P) * nabA P - (zbA P * ggiA P) * (zbA P * ggiA P) :=
    absNb _ _ _ hNzb hNGi (hcomm _ mGi _ mzb)
  have cX : ∀ w : ℂ, Commute (xA P w) (ggA P) ∧ Commute (xA P w) (zbA P * ggiA P) ∧ Commute (xA P w) (nabA P) ∧
      Commute (xA P w) (zbA P) := fun w =>
    ⟨kap_comm_sc P _ _, (kap_comm_sc P _ _).mul_right (kap_comm_sc P _ _), kap_comm_nab P _, kap_comm_sc P _ _⟩
  have hXX : xA P u * xA P v = xA P v * xA P u := (kap_comm_kap P _ _).eq
  rw [lowering_constant_eq_shift, lowering_constant_eq_shift,
    absA _ _ _ _ _ _ hNG hbG (cX v).1 (cX v).2.1 (cX v).2.2.1 (cX v).2.2.2,
    absA _ _ _ _ _ _ hNG hbG (cX u).1 (cX u).2.1 (cX u).2.2.1 (cX u).2.2.2,
    absW _ _ _ _ hGb hNb, absW _ _ _ _ hGb hNb, hXX,
    add_comm (u + 1 / 2) (v + 1 / 2), mul_comm (u + 1 / 2) (v + 1 / 2)]

theorem compB (hSc : SSScalar) (hSh : SSShift) (hN : NabSS) (hR : RhoUp) (P : Par) (u v : ℂ) (l : ℕ)
    (hl : l ∈ Icc 1 (P.k - 1)) :
    (ggA P * xA P u * l0A P u) * (SS P l * kap P fun π => xEx P {l} π v) +
      (SS P l * kap P fun π => xEx P {l} π u) * (ggA P * xA P v * l0A P v) =
    (ggA P * xA P v * l0A P v) * (SS P l * kap P fun π => xEx P {l} π u) +
      (SS P l * kap P fun π => xEx P {l} π v) * (ggA P * xA P u * l0A P u) := by
  have hNS := (hN P l hl).1
  have hbS : (zbA P * ggiA P) * SS P l = SS P l * (zbA P * ggiA P) :=
    ((hSc P l zbP).mul_right (hSc P l (ggiP P.TT))).eq.symm
  have hSG : SS P l * ggA P = ggA P * SS P l := (hSc P l (ggP P.TT)).eq
  have cE : ∀ w : ℂ, Commute (kap P fun π => xEx P {l} π w) (nabA P) ∧
      Commute (kap P fun π => xEx P {l} π w) (zbA P * ggiA P) ∧
      (kap P fun π => xEx P {l} π w) * ggA P = ggA P * kap P fun π => xEx P {l} π w := fun w =>
    ⟨kap_comm_nab P _, (kap_comm_sc P _ _).mul_right (kap_comm_sc P _ _), (kap_comm_sc P _ _).eq⟩
  rw [lowering_constant_eq_shift, lowering_constant_eq_shift,
    weighted_sum_difference_identity _ _ _ _ _ _ _ hNS hbS (shift_x_identity hSh hR P l hl u) hSG (cE v).1 (cE v).2.1,
    weighted_sum_difference_identity _ _ _ _ _ _ _ hNS hbS (shift_x_identity hSh hR P l hl v) hSG (cE u).1 (cE u).2.1,
    mul_assoc_commute_middle _ _ _ _ _ (cE u).2.2, mul_assoc_commute_middle _ _ _ _ _ (cE v).2.2, ← mul_add, ← mul_add]
  refine congrArg (fun t => SS P l * ggA P * t) ?_
  unfold xA
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  apply absCombo
  · funext π
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [xC_eq P π u l hl, xC_eq P π v l hl]; ring
  · funext π
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [xC_eq P π u l hl, xC_eq P π v l hl]; ring

theorem compC_diag (hSh : SSShift) (hR : RhoUp) (P : Par) (u v : ℂ) (l : ℕ) :
    (SS P l * kap P fun π => xEx P {l} π u) * (SS P l * kap P fun π => xEx P {l} π v) =
      (SS P l * kap P fun π => xEx P {l} π v) * (SS P l * kap P fun π => xEx P {l} π u) := by
  rw [TT_eq P l l _ _ _ (sh_same hSh hR P l {l} (Finset.mem_singleton_self l) u),
    TT_eq P l l _ _ _ (sh_same hSh hR P l {l} (Finset.mem_singleton_self l) v), mul_comm]

theorem compC_off (hSh : SSShift) (hC : SSComm) (hR : RhoUp) (P : Par) (hP : P.OK) (u v : ℂ) (l j : ℕ)
    (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    ((SS P l * kap P fun π => xEx P {l} π u) * (SS P j * kap P fun π => xEx P {j} π v) -
      (SS P l * kap P fun π => xEx P {l} π v) * (SS P j * kap P fun π => xEx P {j} π u)) +
    ((SS P j * kap P fun π => xEx P {j} π u) * (SS P l * kap P fun π => xEx P {l} π v) -
      (SS P j * kap P fun π => xEx P {j} π v) * (SS P l * kap P fun π => xEx P {l} π u)) = 0 := by
  rw [TT_eq P l j _ _ _ (sh_pair hSh hR P l j hj hjl u), TT_eq P l j _ _ _ (sh_pair hSh hR P l j hj hjl v),
    TT_eq P j l _ _ _ (sh_pair hSh hR P j l hl (Ne.symm hjl) u),
    TT_eq P j l _ _ _ (sh_pair hSh hR P j l hl (Ne.symm hjl) v), ← mul_sub, ← mul_sub, ← map_sub, ← map_sub]
  have h12 : ((fun π => xEx P {l, j} π u * (u + 1 + (rho P π j : ℂ))) * fun π => xEx P {j} π v) -
      ((fun π => xEx P {l, j} π v * (v + 1 + (rho P π j : ℂ))) * fun π => xEx P {j} π u) =
      -((fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)) *
        fun π => (u - v) * (xEx P {l, j} π u * xEx P {l, j} π v)) := by
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
    rw [xEx_pair' P π v l j hl hjl, xEx_pair' P π u l j hl hjl]
    push_cast; ring
  have h34 : ((fun π => xEx P {j, l} π u * (u + 1 + (rho P π l : ℂ))) * fun π => xEx P {l} π v) -
      ((fun π => xEx P {j, l} π v * (v + 1 + (rho P π l : ℂ))) * fun π => xEx P {l} π u) =
      (fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) *
        fun π => (u - v) * (xEx P {l, j} π u * xEx P {l, j} π v) := by
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [xEx_pair P π v l j hj hjl, xEx_pair P π u l j hj hjl, Finset.pair_comm j l]
    push_cast; ring
  rw [h12, h34, map_neg, map_mul, map_mul, ← mul_assoc (SS P j * SS P l), hC P hP l hl j hj hjl, mul_neg,
    mul_assoc (SS P l * SS P j), neg_add_cancel]

theorem compC (hSh : SSShift) (hC : SSComm) (hR : RhoUp) (P : Par) (hP : P.OK) (u v : ℂ) :
    weightedSumBis P u * weightedSumBis P v = weightedSumBis P v * weightedSumBis P u := by
  unfold weightedSumBis
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  apply sum_anti
  intro l hl j hj
  by_cases hjl : j = l
  · subst hjl
    rw [compC_diag hSh hR P u v j, sub_self, add_zero]
  · exact compC_off hSh hC hR P hP u v l j hl hj hjl

theorem lower_left_commute_of_laws (hSc : SSScalar) (hSh : SSShift) (hC : SSComm) (hN : NabSS) (hLN : LevNab) (hLF : LevFns)
    (hR : RhoUp) : T21Commute := by
  intro P hP u v
  show t21 P u * t21 P v = t21 P v * t21 P u
  have hA := compA hLN hLF P u v
  have hB : (ggA P * xA P u * l0A P u) * weightedSumBis P v + weightedSumBis P u * (ggA P * xA P v * l0A P v) =
      (ggA P * xA P v * l0A P v) * weightedSumBis P u + weightedSumBis P v * (ggA P * xA P u * l0A P u) := by
    unfold weightedSumBis
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l hl => compB hSc hSh hN hR P u v l hl)
  have hCC := compC hSh hC hR P hP u v
  unfold t21
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, hA, hCC]
  calc _ = (ggA P * xA P v * l0A P v) * (ggA P * xA P u * l0A P u) +
        ((ggA P * xA P u * l0A P u) * weightedSumBis P v + weightedSumBis P u * (ggA P * xA P v * l0A P v)) +
        weightedSumBis P v * weightedSumBis P u := by abel
    _ = _ := by rw [hB]; abel

end PartT

section PartF

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial

noncomputable section

theorem natDegree_sub_le_of_next (p1 p2 : ℂ[X]) (N : ℕ) (h1 : p1.Monic) (h2 : p2.Monic)
    (d1 : p1.natDegree = N + 2) (d2 : p2.natDegree = N + 2) (hn : p1.nextCoeff = p2.nextCoeff) :
    (p1 - p2).natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_sub]
  rcases Nat.lt_or_ge (N + 2) m with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
  · have : m = N + 1 ∨ m = N + 2 := by omega
    rcases this with rfl | rfl
    · rw [nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), d1, d2] at hn
      have e : N + 2 - 1 = N + 1 := by omega
      rw [e] at hn
      rw [hn, sub_self]
    · have a1 : p1.coeff (N + 2) = 1 := by rw [← d1]; exact h1.coeff_natDegree
      have a2 : p2.coeff (N + 2) = 1 := by rw [← d2]; exact h2.coeff_natDegree
      rw [a1, a2, sub_self]

def pa (s : Finset ℕ) (ρ : ℕ → ℂ) : ℂ[X] := ∏ i ∈ s, (X + C (ρ i))

theorem pa_monic (s : Finset ℕ) (ρ : ℕ → ℂ) : (pa s ρ).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

theorem pa_natDegree (s : Finset ℕ) (ρ : ℕ → ℂ) : (pa s ρ).natDegree = s.card := by
  unfold pa
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  simp

theorem pa_nextCoeff (s : Finset ℕ) (ρ : ℕ → ℂ) : (pa s ρ).nextCoeff = ∑ i ∈ s, ρ i := by
  unfold pa
  rw [Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C _)]
  simp

theorem pa_eval (s : Finset ℕ) (ρ : ℕ → ℂ) (Y : ℂ) : (pa s ρ).eval Y = ∏ i ∈ s, (Y + ρ i) := by
  simp [pa, eval_prod]

theorem pa_erase (s : Finset ℕ) (ρ : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    pa s ρ = (X + C (ρ l)) * pa (s.erase l) ρ := (Finset.mul_prod_erase s _ hl).symm

theorem fac_dvd (s : Finset ℕ) (ρ : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) : X + C (ρ l) ∣ pa s ρ :=
  Finset.dvd_prod_of_mem _ hl

theorem pa_dvd (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j) (F : ℂ[X])
    (h : ∀ l ∈ s, F.eval (-ρ l) = 0) : pa s ρ ∣ F := by
  unfold pa
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
    have e : (X + C (ρ l) : ℂ[X]) = X - C (-ρ l) := by simp
    rw [e, dvd_iff_isRoot]
    exact h l hl

def DD (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) : ℂ[X] :=
  C c * q1 + (∑ l ∈ s, C (M l) * (pa (s.erase l) ρ * pa s (fun i => ρ i + 1))) -
    (∑ l ∈ s, C (N l) * (pa s ρ * pa (s.erase l) (fun i => ρ i + 1)))

theorem DD_eval (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (Y : ℂ) :
    (DD s ρ c q1 N M).eval Y =
    c * q1.eval Y + (∑ l ∈ s, M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1)))) -
      (∑ l ∈ s, N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1)))) := by
  simp only [DD, eval_sub, eval_add, eval_mul, eval_C, eval_finsetSum, pa_eval]

theorem DD_eval_a (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    (DD s ρ c q1 N M).eval (-ρ l) =
    c * q1.eval (-ρ l) + M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) := by
  rw [DD_eval]
  have z : ∏ j ∈ s, (-ρ l + ρ j) = 0 := Finset.prod_eq_zero hl (by ring)
  have z2 : (∑ m ∈ s, N m * ((∏ j ∈ s, (-ρ l + ρ j)) * ∏ j ∈ s.erase m, (-ρ l + (ρ j + 1)))) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [z]; ring)
  have z3 : (∑ m ∈ s, M m * ((∏ j ∈ s.erase m, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1)))) =
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) := by
    apply Finset.sum_eq_single l
    · intro j _ hj
      rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hj h.symm, hl⟩) (by ring)]; ring
    · intro h; exact absurd hl h
  rw [z2, z3, sub_zero]

theorem DD_eval_b (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    (DD s ρ c q1 N M).eval (-(ρ l + 1)) =
    c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) := by
  rw [DD_eval]
  have z : ∏ j ∈ s, (-(ρ l + 1) + (ρ j + 1)) = 0 := Finset.prod_eq_zero hl (by ring)
  have z2 : (∑ m ∈ s, M m * ((∏ j ∈ s.erase m, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s, (-(ρ l + 1) + (ρ j + 1)))) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [z]; ring)
  have z3 : (∑ m ∈ s, N m * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase m, (-(ρ l + 1) + (ρ j + 1)))) =
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) := by
    apply Finset.sum_eq_single l
    · intro j _ hj
      rw [Finset.prod_eq_zero (s := s.erase j) (i := l) (Finset.mem_erase.2 ⟨fun h => hj h.symm, hl⟩) (by ring)]; ring
    · intro h; exact absurd hl h
  rw [z2, z3, add_zero]

theorem DD_dvd (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1) :
    pa s ρ * pa s (fun i => ρ i + 1) ∣ DD s ρ c q1 N M := by
  obtain ⟨D1, hD1⟩ := pa_dvd s ρ hinj (DD s ρ c q1 N M)
    (fun l hl => by rw [DD_eval_a _ _ _ _ _ _ l hl]; exact H1 l hl)
  have key : pa s (fun i => ρ i + 1) ∣ D1 := by
    apply pa_dvd s (fun i => ρ i + 1) (fun i hi j hj h => hinj i hi j hj (add_right_cancel h))
    intro l hl
    show D1.eval (-(ρ l + 1)) = 0
    have hD0 : (DD s ρ c q1 N M).eval (-(ρ l + 1)) = 0 := by
      rw [DD_eval_b _ _ _ _ _ _ l hl]; exact H2 l hl
    by_cases hdeg : ∃ m ∈ s, ρ m = ρ l + 1
    · obtain ⟨m, hm, hml⟩ := hdeg
      obtain ⟨hN, hM, hq⟩ := H3 l hl m hm hml
      have ht0 : (X + C (ρ l + 1) : ℂ[X]) ≠ 0 := (monic_X_add_C _).ne_zero
      have hta : ∀ s' : Finset ℕ, m ∈ s' → (X + C (ρ l + 1) : ℂ[X]) ∣ pa s' ρ := by
        intro s' h; have := fac_dvd s' ρ m h; rwa [hml] at this
      have htb : ∀ s' : Finset ℕ, l ∈ s' → (X + C (ρ l + 1) : ℂ[X]) ∣ pa s' (fun i => ρ i + 1) :=
        fun s' h => fac_dvd s' (fun i => ρ i + 1) l h
      have htt : (X + C (ρ l + 1) : ℂ[X]) * (X + C (ρ l + 1)) ∣ DD s ρ c q1 N M := by
        unfold DD
        refine dvd_sub (dvd_add (Dvd.dvd.mul_left hq _) (Finset.dvd_sum ?_)) (Finset.dvd_sum ?_)
        · intro j hj
          by_cases hjm : j = m
          · rw [hjm, hM]; simp
          · exact Dvd.dvd.mul_left (mul_dvd_mul (hta _ (Finset.mem_erase.2 ⟨fun h => hjm h.symm, hm⟩)) (htb _ hl)) _
        · intro j hj
          by_cases hjl : j = l
          · rw [hjl, hN]; simp
          · exact Dvd.dvd.mul_left (mul_dvd_mul (hta _ hm) (htb _ (Finset.mem_erase.2 ⟨fun h => hjl h.symm, hl⟩))) _
      have hpa : pa s ρ = (X + C (ρ l + 1)) * pa (s.erase m) ρ := by rw [pa_erase s ρ m hm, hml]
      rw [hD1, hpa, mul_assoc] at htt
      have h3 : (X + C (ρ l + 1) : ℂ[X]) ∣ pa (s.erase m) ρ * D1 := (mul_dvd_mul_iff_left ht0).1 htt
      have e : (X + C (ρ l + 1) : ℂ[X]) = X - C (-(ρ l + 1)) := by rw [C_neg, sub_neg_eq_add]
      rw [e, dvd_iff_isRoot, IsRoot.def, eval_mul, pa_eval] at h3
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h4
        obtain ⟨j, hj, hj0⟩ := h4
        have : ρ j = ρ m := by rw [hml]; linear_combination hj0
        exact (Finset.mem_erase.1 hj).1 (hinj j (Finset.mem_erase.1 hj).2 m hm this)
      · exact h4
    · have hdeg : ∀ j ∈ s, ρ j ≠ ρ l + 1 := fun j hj h => hdeg ⟨j, hj, h⟩
      rw [hD1, eval_mul, pa_eval] at hD0
      rcases mul_eq_zero.1 hD0 with h4 | h4
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h4
        obtain ⟨j, hj, hj0⟩ := h4
        exact hdeg j hj (by linear_combination hj0)
      · exact h4
  rw [hD1]
  exact mul_dvd_mul_left _ key

theorem DD_quot (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1)
    (hq1 : q1.Monic) (hdeg : q1.natDegree = 2 * s.card + 2) (e : ℂ)
    (he : e = q1.nextCoeff - ∑ i ∈ s, ρ i - ∑ i ∈ s, (ρ i + 1)) :
    ∃ r : ℂ, DD s ρ c q1 N M = pa s ρ * pa s (fun i => ρ i + 1) *
      (C c * ((X + C 0) * (X + C e)) + C r) := by
  have hdv := DD_dvd s ρ hinj c q1 N M H1 H2 H3
  generalize hX12 : pa s ρ * pa s (fun i => ρ i + 1) = coord_mul_inv_coord_eq_one at hdv ⊢
  have hXm : coord_mul_inv_coord_eq_one.Monic := by rw [← hX12]; exact (pa_monic _ _).mul (pa_monic _ _)
  have hXd : coord_mul_inv_coord_eq_one.natDegree = 2 * s.card := by
    rw [← hX12, Monic.natDegree_mul (pa_monic _ _) (pa_monic _ _), pa_natDegree, pa_natDegree]; ring
  have hXn : coord_mul_inv_coord_eq_one.nextCoeff = ∑ i ∈ s, ρ i + ∑ i ∈ s, (ρ i + 1) := by
    rw [← hX12, Monic.nextCoeff_mul (pa_monic _ _) (pa_monic _ _), pa_nextCoeff, pa_nextCoeff]
  generalize hg : ((X + C 0) * (X + C e) : ℂ[X]) = g
  have hgm : g.Monic := by rw [← hg]; exact (monic_X_add_C _).mul (monic_X_add_C _)
  have hgd : g.natDegree = 2 := by
    rw [← hg, Monic.natDegree_mul (monic_X_add_C _) (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  have hgn : g.nextCoeff = e := by
    rw [← hg, Monic.nextCoeff_mul (monic_X_add_C _) (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]; ring
  have h1 : (q1 - coord_mul_inv_coord_eq_one * g).natDegree ≤ 2 * s.card := by
    apply natDegree_sub_le_of_next _ _ _ hq1 (hXm.mul hgm) hdeg
    · rw [Monic.natDegree_mul hXm hgm, hXd, hgd]
    · rw [Monic.nextCoeff_mul hXm hgm, hXn, hgn, he]; ring
  have hR : (DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g)).natDegree ≤ 2 * s.card := by
    have : DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g) = C c * (q1 - coord_mul_inv_coord_eq_one * g) +
        ((∑ l ∈ s, C (M l) * (pa (s.erase l) ρ * pa s (fun i => ρ i + 1))) -
          (∑ l ∈ s, C (N l) * (pa s ρ * pa (s.erase l) (fun i => ρ i + 1)))) := by
      unfold DD; ring
    rw [this]
    refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans h1) ((natDegree_sub_le_of_le ?_ ?_).trans (le_of_eq (max_self _)))
    · apply natDegree_sum_le_of_forall_le
      intro l hl
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      rw [pa_natDegree, pa_natDegree, Finset.card_erase_of_mem hl]; omega
    · apply natDegree_sum_le_of_forall_le
      intro l hl
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      rw [pa_natDegree, pa_natDegree, Finset.card_erase_of_mem hl]; omega
  obtain ⟨S, hS⟩ : coord_mul_inv_coord_eq_one ∣ DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g) :=
    dvd_sub hdv (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  have hS0 : S.natDegree = 0 := by
    by_cases h0 : S = 0
    · rw [h0]; simp
    · rw [hS, Monic.natDegree_mul' hXm h0, hXd] at hR; omega
  refine ⟨S.coeff 0, ?_⟩
  rw [← eq_C_of_natDegree_eq_zero hS0]
  linear_combination hS

theorem pf_abs (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1)
    (hq1 : q1.Monic) (hdeg : q1.natDegree = 2 * s.card + 2) (e : ℂ)
    (he : e = q1.nextCoeff - ∑ i ∈ s, ρ i - ∑ i ∈ s, (ρ i + 1)) :
    ∃ r : ℂ, ∀ Y : ℂ, (∀ i ∈ s, Y + ρ i ≠ 0) → (∀ i ∈ s, Y + (ρ i + 1) ≠ 0) →
      c * q1.eval Y * ((∏ i ∈ s, (Y + ρ i))⁻¹ * (∏ i ∈ s, (Y + (ρ i + 1)))⁻¹) =
        c * (Y * (Y + e)) + r - (∑ l ∈ s, M l * (Y + ρ l)⁻¹) + (∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹) := by
  obtain ⟨r, hr⟩ := DD_quot s ρ hinj c q1 N M H1 H2 H3 hq1 hdeg e he
  refine ⟨r, fun Y ha hb => ?_⟩
  have hE := congrArg (eval Y) hr
  rw [DD_eval] at hE
  simp only [eval_mul, eval_add, eval_C, eval_X, pa_eval, add_zero] at hE
  have hA0 : (∏ i ∈ s, (Y + ρ i)) ≠ 0 := Finset.prod_ne_zero_iff.2 ha
  have hB0 : (∏ i ∈ s, (Y + (ρ i + 1))) ≠ 0 := Finset.prod_ne_zero_iff.2 hb
  have e1 : (∑ l ∈ s, M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1)))) =
      (∏ i ∈ s, (Y + ρ i)) * (∏ i ∈ s, (Y + (ρ i + 1))) * ∑ l ∈ s, M l * (Y + ρ l)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [← Finset.mul_prod_erase s (fun i => Y + ρ i) hl]
    have hinv := mul_inv_cancel₀ (ha l hl)
    linear_combination (-(M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1))))) * hinv
  have e2 : (∑ l ∈ s, N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1)))) =
      (∏ i ∈ s, (Y + ρ i)) * (∏ i ∈ s, (Y + (ρ i + 1))) * ∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [← Finset.mul_prod_erase s (fun i => Y + (ρ i + 1)) hl]
    have hinv := mul_inv_cancel₀ (hb l hl)
    linear_combination (-(N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1))))) * hinv
  rw [e1, e2] at hE
  generalize (∏ i ∈ s, (Y + ρ i)) = A at hE hA0 ⊢
  generalize (∏ i ∈ s, (Y + (ρ i + 1))) = B at hE hB0 ⊢
  have hAB : A * B * (A⁻¹ * B⁻¹) = 1 := by
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hA0, mul_inv_cancel₀ hB0, mul_one]
  have h5 : c * eval Y q1 = (c * (Y * (Y + e)) + r - (∑ l ∈ s, M l * (Y + ρ l)⁻¹) +
      (∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹)) * (A * B) := by linear_combination hE
  rw [h5, mul_assoc, hAB, mul_one]

def q1P (P : Par) : ℂ[X] :=
  ∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))

theorem q_polynomial_monic (P : Par) : (q1P P).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))

theorem natDegree_q1_polynomial (P : Par) : (q1P P).natDegree = 2 * P.k := by
  unfold q1P
  rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  have : ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := by
    intro i _
    rw [Monic.natDegree_mul (monic_X_add_C _) (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  rw [Finset.sum_congr rfl this]
  simp [mul_comm]

theorem q_polynomial_next_coeff (P : Par) :
    (q1P P).nextCoeff = ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) := by
  unfold q1P
  rw [Monic.nextCoeff_prod _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Monic.nextCoeff_mul (monic_X_add_C _) (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]

theorem qC_eq (P : Par) (Y : ℂ) : qC P Y = -((P.T : ℂ) * P.T') * (q1P P).eval Y := by
  unfold qC q1P
  simp only [eval_prod, eval_mul, eval_add, eval_X, eval_C]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by ring)

theorem nrmDown_key (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) :
    NrmDown P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) =
      -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) := by
  have hl' := Finset.mem_Icc.1 hl
  by_cases h : ∃ π', Up P l π' π
  · obtain ⟨π', hU⟩ := h
    have hp := (Mx3.nrmFacts P hP l hl π').1 π hU
    have hpos : 0 < NrmDown P l π := by rw [hp.2]; exact hp.1
    have hD : ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) ≠ 0 := by
      intro h0
      unfold NrmDown at hpos
      rw [h0, div_zero] at hpos
      exact lt_irrefl _ hpos
    unfold NrmDown
    exact div_mul_cancel₀ _ hD
  · rw [(Mx3.nrmFacts P hP l hl π).2.2 h]
    have ht := Mx3.bot P l hl π h
    have h0 : I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) = 0 := by
      unfold I.qpoly
      have : ∏ i ∈ Icc 1 P.k, ((-rho P π l + 1 / 2 + P.u i) * (-rho P π l + 1 / 2 + P.u' i)) = 0 := by
        apply Finset.prod_eq_zero (i := l + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
        rw [ht]; unfold Par.lo
        rcases max_choice (P.u (l + 1)) (P.u' (l + 1)) with h | h <;> rw [h] <;> ring
      rw [this]; simp
    rw [h0]; simp

theorem rhoC_inj (P : Par) (hP : P.OK) (π : Ty P) : ∀ i ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1),
    (rho P π i : ℂ) = (rho P π j : ℂ) → i = j := by
  intro i hi j hj h
  have h2 : rho P π i = rho P π j := by exact_mod_cast h
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd h2 (ne_of_gt (Mx3.rho_inj P hP π i j hi hj h1))
  · exact h1
  · exact absurd h2 (ne_of_lt (Mx3.rho_inj P hP π j i hj hi h1))

theorem moduleH1Alt (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1),
    -((P.T : ℂ) * P.T') * (q1P P).eval (-(rho P π l : ℂ)) + (NrmDown P l π : ℂ) *
      ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + (rho P π j : ℂ))) *
        ∏ j ∈ Icc 1 (P.k - 1), (-(rho P π l : ℂ) + ((rho P π j : ℂ) + 1))) = 0 := by
  intro l hl
  have hk := congrArg (fun x : ℝ => (x : ℂ)) (nrmDown_key P hP l hl π)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_neg, Complex.ofReal_one] at hk
  have hq := (Mx3.realPoints P π (-rho P π l)).2
  rw [Complex.ofReal_neg] at hq
  rw [← qC_eq, hq, ← Finset.mul_prod_erase _ _ hl]
  have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + (rho P π j : ℂ)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + ((rho P π j : ℂ) + 1)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l + 1) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [e1, e2]
  linear_combination hk

theorem residue_quadratic_identity (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1),
    -((P.T : ℂ) * P.T') * (q1P P).eval (-((rho P π l : ℂ) + 1)) - (Nrm P l π : ℂ) *
      ((∏ j ∈ Icc 1 (P.k - 1), (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ))) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1))) = 0 := by
  intro l hl
  have hk := congrArg (fun x : ℝ => (x : ℂ)) (Mx3.nrm_key P hP l hl π)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_one] at hk
  have hq := (Mx3.realPoints P π (-rho P π l - 1)).2
  have e0 : ((-rho P π l - 1 : ℝ) : ℂ) = -((rho P π l : ℂ) + 1) := by push_cast; ring
  rw [e0] at hq
  rw [← qC_eq, hq, ← Finset.mul_prod_erase _ _ hl]
  have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l - 1) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [e1, e2]
  linear_combination hk

theorem double_root_of_adjacent_rho (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1), ∀ m ∈ Icc 1 (P.k - 1),
    (rho P π m : ℂ) = (rho P π l : ℂ) + 1 → (Nrm P l π : ℂ) = 0 ∧ (NrmDown P m π : ℂ) = 0 ∧
      (X + C ((rho P π l : ℂ) + 1)) * (X + C ((rho P π l : ℂ) + 1)) ∣ q1P P := by
  intro l hl m hm h
  have hl' := Finset.mem_Icc.1 hl
  have hr : rho P π m = rho P π l + 1 := by exact_mod_cast h
  have hml : m < l := by
    rcases lt_trichotomy m l with h1 | h1 | h1
    · exact h1
    · rw [h1] at hr; linarith
    · have := Mx3.rho_inj P hP π l m hl hm h1; linarith
  refine ⟨?_, ?_, ?_⟩
  · have : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1) = 0 :=
      Finset.prod_eq_zero (i := m) (Finset.mem_erase.2 ⟨ne_of_lt hml, hm⟩) (by rw [hr]; ring)
    unfold Nrm
    rw [this, mul_zero, div_zero, Complex.ofReal_zero]
  · have : ∏ j ∈ (Icc 1 (P.k - 1)).erase m, (rho P π j - rho P π m + 1) = 0 :=
      Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨ne_of_gt hml, hl⟩) (by rw [hr]; ring)
    unfold NrmDown
    rw [this, zero_mul, div_zero, Complex.ofReal_zero]
  · have hI := Mx3.tyInterlaces P hP π
    have o3 := (Mx3.ord P.k P.u P.u' (rho P π) hI l hl).2.2.1 m hm hml
    have b := hI l hl
    have hu : P.u l = rho P π l + 1 / 2 := by linarith [o3.1, b.1]
    have hu' : P.u' l = rho P π l + 1 / 2 := by linarith [o3.2, b.2.1]
    have hd : (X + C (1 / 2 + (P.u l : ℂ))) * (X + C (1 / 2 + (P.u' l : ℂ))) ∣ q1P P :=
      Finset.dvd_prod_of_mem (fun i => (X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))
        (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)
    have e1 : (1 / 2 + (P.u l : ℂ)) = (rho P π l : ℂ) + 1 := by rw [hu]; push_cast; ring
    have e2 : (1 / 2 + (P.u' l : ℂ)) = (rho P π l : ℂ) + 1 := by rw [hu']; push_cast; ring
    rwa [e1, e2] at hd

theorem modE (P : Par) (hP : P.OK) (π : Ty P) :
    2 * (aC P π : ℂ) + 1 = (q1P P).nextCoeff - ∑ i ∈ Icc 1 (P.k - 1), (rho P π i : ℂ) -
      ∑ i ∈ Icc 1 (P.k - 1), ((rho P π i : ℂ) + 1) := by
  rw [q_polynomial_next_coeff]
  have s1 : ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      (P.k : ℂ) + ∑ i ∈ Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ)) := by
    rw [Finset.sum_congr rfl (fun i _ => show ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      1 + ((P.u i : ℂ) + (P.u' i : ℂ)) by ring), Finset.sum_add_distrib]
    simp
  have s2 : ∑ i ∈ Icc 1 (P.k - 1), ((rho P π i : ℂ) + 1) =
      (∑ i ∈ Icc 1 (P.k - 1), (rho P π i : ℂ)) + ((P.k : ℂ) - 1) := by
    rw [Finset.sum_add_distrib]
    simp [Nat.cast_sub hP.k_pos]
  rw [s1, s2]
  unfold aC
  push_cast
  ring

theorem pf (P : Par) (hP : P.OK) (π : Ty P) (u : ℂ) (h0 : xC P π (u - 1) ≠ 0) (h1 : xC P π u ≠ 0)
    (h2 : xC P π (u + 1) ≠ 0) :
    qC P (u - 1) * ((xC P π (u - 1))⁻¹ * (xC P π u)⁻¹) - qC P u * ((xC P π u)⁻¹ * (xC P π (u + 1))⁻¹) =
      (2 * (aC P π : ℂ) + 2 * u) * (P.TT : ℂ) + ∑ l ∈ Icc 1 (P.k - 1),
        ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
          (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) := by
  obtain ⟨r, hr⟩ := pf_abs (Icc 1 (P.k - 1)) (fun i => (rho P π i : ℂ)) (rhoC_inj P hP π)
    (-((P.T : ℂ) * P.T')) (q1P P) (fun l => (Nrm P l π : ℂ)) (fun l => (NrmDown P l π : ℂ))
    (moduleH1Alt P hP π) (residue_quadratic_identity P hP π) (double_root_of_adjacent_rho P hP π) (q_polynomial_monic P)
    (by rw [natDegree_q1_polynomial, Nat.card_Icc]; have := hP.k_pos; omega) (2 * (aC P π : ℂ) + 1) (modE P hP π)
  have f0 : ∀ i ∈ Icc 1 (P.k - 1), u - 1 + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h0
  have f1 : ∀ i ∈ Icc 1 (P.k - 1), u + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h1
  have f2 : ∀ i ∈ Icc 1 (P.k - 1), u + 1 + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h2
  have E0 := hr (u - 1) f0 (fun i hi h => f1 i hi (by linear_combination h))
  have E1 := hr u f1 (fun i hi h => f2 i hi (by linear_combination h))
  have p0 : ∏ i ∈ Icc 1 (P.k - 1), (u - 1 + ((rho P π i : ℂ) + 1)) = xC P π u :=
    Finset.prod_congr rfl (fun i _ => by ring)
  have p1 : ∏ i ∈ Icc 1 (P.k - 1), (u + ((rho P π i : ℂ) + 1)) = xC P π (u + 1) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  have x0 : ∏ i ∈ Icc 1 (P.k - 1), (u - 1 + (rho P π i : ℂ)) = xC P π (u - 1) := rfl
  have x1 : ∏ i ∈ Icc 1 (P.k - 1), (u + (rho P π i : ℂ)) = xC P π u := rfl
  rw [p0, x0, ← qC_eq] at E0
  rw [p1, x1, ← qC_eq] at E1
  rw [E0, E1]
  have T : ∀ l ∈ Icc 1 (P.k - 1),
      ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
          (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) =
      -((NrmDown P l π : ℂ) * (u - 1 + (rho P π l : ℂ))⁻¹) + (Nrm P l π : ℂ) * (u - 1 + ((rho P π l : ℂ) + 1))⁻¹ +
        (NrmDown P l π : ℂ) * (u + (rho P π l : ℂ))⁻¹ - (Nrm P l π : ℂ) * (u + ((rho P π l : ℂ) + 1))⁻¹ := by
    intro l hl
    rw [show u - 1 + ((rho P π l : ℂ) + 1) = u + rho P π l by ring,
      show u + ((rho P π l : ℂ) + 1) = u + rho P π l + 1 by ring,
      show u - 1 + (rho P π l : ℂ) = u + rho P π l - 1 by ring]
    have hx := mul_inv_cancel₀ (f1 l hl)
    have hy : (u + rho P π l + 1) * (u + rho P π l + 1)⁻¹ = 1 :=
      mul_inv_cancel₀ (fun h => f2 l hl (by linear_combination h))
    have hz : (u + rho P π l - 1) * (u + rho P π l - 1)⁻¹ = 1 :=
      mul_inv_cancel₀ (fun h => f0 l hl (by linear_combination h))
    have hxy : (u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹ = (u + rho P π l)⁻¹ - (u + rho P π l + 1)⁻¹ := by
      linear_combination (-(u + rho P π l + 1)⁻¹) * hx + (u + rho P π l)⁻¹ * hy
    have hxz : (u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹ = (u + rho P π l - 1)⁻¹ - (u + rho P π l)⁻¹ := by
      linear_combination (u + rho P π l - 1)⁻¹ * hx - (u + rho P π l)⁻¹ * hz
    linear_combination (Nrm P l π : ℂ) * hxy - (NrmDown P l π : ℂ) * hxz
  rw [Finset.sum_congr rfl T, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have hTT : (P.TT : ℂ) = (P.T : ℂ) * P.T' := by unfold Par.TT; push_cast; ring
  rw [hTT]
  ring

end

end PartF

section PartA

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial

section Poly

variable {B : Type} [Ring B] [Algebra ℂ B]

noncomputable def ev (Y : ℂ) : B[X] →+* B :=
  eval₂RingHom' (RingHom.id B) (algebraMap ℂ B Y) (fun a => (Algebra.commutes Y a).symm)

theorem ev_apply (Y : ℂ) (p : B[X]) : ev Y p = eval₂ (RingHom.id B) (algebraMap ℂ B Y) p := rfl

theorem ev_C (Y : ℂ) (a : B) : ev Y (C a) = a := by rw [ev_apply, eval₂_C]; rfl

theorem ev_X (Y : ℂ) : ev Y (X : B[X]) = algebraMap ℂ B Y := by rw [ev_apply, eval₂_X]

theorem ev_monomial (Y : ℂ) (n : ℕ) (a : B) : ev Y (monomial n a) = a * algebraMap ℂ B Y ^ n := by
  rw [ev_apply, eval₂_monomial]; rfl

theorem ev_eq_sum (Y : ℂ) (p : B[X]) : ev Y p = ∑ i ∈ p.support, Y ^ i • p.coeff i := by
  rw [ev_apply, eval₂_eq_sum, Polynomial.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, Algebra.smul_def]

theorem ev_comp (Y c : ℂ) (p : B[X]) : ev Y (p.comp (X + C (algebraMap ℂ B c))) = ev (Y + c) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, map_add, hp, hq]
  | monomial n a => rw [monomial_comp, map_mul, map_pow, map_add, ev_C, ev_X, ev_C, ev_monomial, map_add]

def IsPoly (F : ℂ → B) : Prop := ∃ p : B[X], ∀ Y, F Y = ev Y p

theorem IsPoly.congr {F G : ℂ → B} (hF : IsPoly F) (h : ∀ Y, G Y = F Y) : IsPoly G := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p, fun Y => by rw [h, hp]⟩

theorem IsPoly.const (a : B) : IsPoly (fun _ => a) := ⟨C a, fun Y => (ev_C Y a).symm⟩

theorem IsPoly.add {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y + G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun Y => by show F Y + G Y = _; rw [map_add, hp, hq]⟩

theorem IsPoly.sub {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y - G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p - q, fun Y => by show F Y - G Y = _; rw [map_sub, hp, hq]⟩

theorem IsPoly.neg {F : ℂ → B} (hF : IsPoly F) : IsPoly (fun Y => -F Y) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨-p, fun Y => by show -F Y = _; rw [map_neg, hp]⟩

theorem IsPoly.mul {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y * G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p * q, fun Y => by show F Y * G Y = _; rw [map_mul, hp, hq]⟩

theorem IsPoly.sum {ι : Type} (s : Finset ι) (F : ι → ℂ → B) (h : ∀ i ∈ s, IsPoly (F i)) :
    IsPoly (fun Y => ∑ i ∈ s, F i Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPoly.const (0 : B)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsPoly.scalar (p : ℂ[X]) : IsPoly (fun Y => algebraMap ℂ B (p.eval Y)) :=
  ⟨p.map (algebraMap ℂ B), fun Y => by rw [ev_apply, eval₂_map, RingHom.id_comp, eval₂_at_apply]⟩

theorem IsPoly.shift {F : ℂ → B} (hF : IsPoly F) (c : ℂ) : IsPoly (fun Y => F (Y + c)) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p.comp (X + C (algebraMap ℂ B c)), fun Y => by show F (Y + c) = _; rw [ev_comp, hp]⟩

theorem IsPoly.eq_zero {F : ℂ → B} (hF : IsPoly F) {S : Set ℂ} (hS : S.Finite) (h : ∀ Y, Y ∉ S → F Y = 0)
    (Y : ℂ) : F Y = 0 := by
  obtain ⟨p, hp⟩ := hF
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hev : ∀ Z, φ (F Z) = (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]).eval Z := by
    intro Z
    rw [hp, ev_eq_sum, map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, eval_monomial, smul_eq_mul, mul_comm]
  have h0 : (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]) = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine hS.infinite_compl.mono ?_
    intro Z hZ
    show eval Z _ = 0
    rw [← hev, h Z hZ, map_zero]
  rw [hev, h0, eval_zero]

theorem IsPoly.ext {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) {S : Set ℂ} (hS : S.Finite)
    (h : ∀ Y, Y ∉ S → F Y = G Y) (Y : ℂ) : F Y = G Y :=
  sub_eq_zero.1 ((hF.sub hG).eq_zero hS (fun Z hZ => sub_eq_zero.2 (h Z hZ)) Y)

end Poly

section AbsDet

variable {B : Type} [Ring B] [Algebra ℂ B]

theorem det_abs (τ0 τ1 i0 i1 i2 l0 l1 m0 m1 : B) (q0 q1 : ℂ)
    (h00 : τ0 * i0 = 1) (h00' : i0 * τ0 = 1) (h11 : τ1 * i1 = 1) (h11' : i1 * τ1 = 1)
    (hi : i0 * i1 = i1 * i0)
    (Y1 : l0 * τ1 = τ1 * l1) (Y1' : m1 * τ0 = τ0 * m0)
    (Y3 : m1 * l1 - l1 * m1 = q0 • (i0 * i1) - q1 • (i1 * i2)) :
    (q1 • i2 + τ1 * m1 * l1) * (τ0 * l0) - τ1 * l1 * (q0 • i1 + τ0 * m0 * l0) = 0 ∧
    (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) = algebraMap ℂ B q0 ∧
    τ1 * m1 * (τ0 * l0) - τ1 * (q0 • i1 + τ0 * m0 * l0) = -algebraMap ℂ B q0 ∧
    τ1 * m1 * τ0 - τ1 * (τ0 * m0) = 0 ∧
    (q0 • i1 + τ0 * m0 * l0) * (τ1 * m1) - τ0 * m0 * (q1 • i2 + τ1 * m1 * l1) = 0 ∧
    (q0 • i1 + τ0 * m0 * l0) * τ1 - τ0 * m0 * (τ1 * l1) = algebraMap ℂ B q0 ∧
    τ0 * l0 * (τ1 * m1) - τ0 * (q1 • i2 + τ1 * m1 * l1) = -algebraMap ℂ B q0 ∧
    τ0 * l0 * τ1 - τ0 * (τ1 * l1) = 0 := by
  have T5 : τ1 * (i0 * i1) = i0 := by rw [hi, ← mul_assoc, h11, one_mul]
  have FreeQuotientRank : τ1 * (i1 * i2) = i2 := by rw [← mul_assoc, h11, one_mul]
  have K : τ1 * (m1 * l1 - l1 * m1) = q0 • i0 - q1 • i2 := by
    rw [Y3, mul_sub, mul_smul_comm, mul_smul_comm, T5, FreeQuotientRank]
  have e2 : (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) = algebraMap ℂ B q0 := by
    have s : (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) =
        q1 • (i2 * τ0) + τ1 * (m1 * l1 - l1 * m1) * τ0 := by
      rw [← Y1']
      simp only [add_mul, smul_mul_assoc, mul_sub, sub_mul, mul_assoc]
      abel
    rw [s, K, sub_mul, smul_mul_assoc, smul_mul_assoc, h00', Algebra.algebraMap_eq_smul_one]
    abel
  have F1 : τ1 * l1 * i1 = l0 := by rw [← Y1, mul_assoc, h11, mul_one]
  have F2 : τ0 * m0 * i0 = m1 := by rw [← Y1', mul_assoc, h00, mul_one]
  refine ⟨?_, e2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have s : (q1 • i2 + τ1 * m1 * l1) * (τ0 * l0) - τ1 * l1 * (q0 • i1 + τ0 * m0 * l0) =
        ((q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0)) * l0 - q0 • (τ1 * l1 * i1) := by
      simp only [mul_add, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
      abel
    rw [s, e2, F1, ← Algebra.smul_def, sub_self]
  · have s : τ1 * m1 * (τ0 * l0) = τ1 * (τ0 * m0 * l0) := by
      rw [mul_assoc τ1, ← mul_assoc m1, Y1']
    rw [s, mul_add, mul_smul_comm, h11, Algebra.algebraMap_eq_smul_one]
    abel
  · rw [mul_assoc, Y1', sub_self]
  · have s : (q0 • i1 + τ0 * m0 * l0) * (τ1 * m1) - τ0 * m0 * (q1 • i2 + τ1 * m1 * l1) =
        q0 • (i1 * τ1 * m1) - τ0 * m0 * (τ1 * (m1 * l1 - l1 * m1)) - q1 • (τ0 * m0 * i2) := by
      have s2 : τ0 * m0 * l0 * (τ1 * m1) = τ0 * m0 * (τ1 * (l1 * m1)) := by
        rw [mul_assoc (τ0 * m0), ← mul_assoc l0, Y1, mul_assoc τ1]
      rw [add_mul, s2]
      simp only [mul_add, mul_sub, mul_smul_comm, smul_mul_assoc, mul_assoc]
      abel
    rw [s, K, h11', one_mul, mul_sub, mul_smul_comm, mul_smul_comm, F2]
    abel
  · rw [add_mul, smul_mul_assoc, h11', mul_assoc (τ0 * m0) l0 τ1, Y1, Algebra.algebraMap_eq_smul_one]
    abel
  · have s : τ0 * l0 * (τ1 * m1) - τ0 * (q1 • i2 + τ1 * m1 * l1) =
        -(τ0 * (τ1 * (m1 * l1 - l1 * m1))) - q1 • (τ0 * i2) := by
      have s2 : τ0 * l0 * (τ1 * m1) = τ0 * (τ1 * (l1 * m1)) := by
        rw [mul_assoc τ0, ← mul_assoc l0, Y1, mul_assoc]
      rw [s2]
      simp only [mul_add, mul_sub, mul_smul_comm, mul_assoc]
      abel
    rw [s, K, mul_sub, mul_smul_comm, mul_smul_comm, h00, Algebra.algebraMap_eq_smul_one]
    abel
  · rw [mul_assoc, Y1, sub_self]

open Matrix in
theorem isSymplectic_of_eight_relations (a b c d a' b' c' d' q : B)
    (e1 : a' * c - c' * a = 0) (e2 : a' * d - c' * b = q) (e3 : b' * c - d' * a = -q) (e4 : b' * d - d' * b = 0)
    (e5 : a * b' - b * a' = 0) (e6 : a * d' - b * c' = q) (e7 : c * b' - d * a' = -q) (e8 : c * d' - d * c' = 0) :
    (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) B)ᵀ * Formalism.YangianSpanCharacter.T.J B * !![a, b; c, d] = q • Formalism.YangianSpanCharacter.T.J B ∧
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * Formalism.YangianSpanCharacter.T.J B * (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) B)ᵀ = q • Formalism.YangianSpanCharacter.T.J B := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (norm := noncomm_ring) e1
    · linear_combination (norm := noncomm_ring) e2
    · linear_combination (norm := noncomm_ring) e3
    · linear_combination (norm := noncomm_ring) e4
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (norm := noncomm_ring) e5
    · linear_combination (norm := noncomm_ring) e6
    · linear_combination (norm := noncomm_ring) e7
    · linear_combination (norm := noncomm_ring) e8

end AbsDet

end PartA

section PartB

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

section abs2

variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem lowering_intertwine_gamma (G Gi X L0 L1 U U' : R) (hLG : L0 * G = G * L1) (hXL : Commute X L1) (hUX : U * X = X * U')
    (hGU : Commute G U) (hGiX : Commute Gi X) (hGGi : Commute G Gi) :
    (L0 + Gi * U) * (G * X) = (G * X) * (L1 + Gi * U') := by
  have a : L0 * (G * X) = G * X * L1 := by rw [← mul_assoc, hLG, mul_assoc, mul_assoc, hXL.eq]
  have b : Gi * U * (G * X) = G * X * (Gi * U') := by
    calc Gi * U * (G * X) = Gi * (U * G) * X := by simp only [mul_assoc]
      _ = Gi * (G * U) * X := by rw [hGU.eq]
      _ = (Gi * G) * (U * X) := by simp only [mul_assoc]
      _ = (G * Gi) * (X * U') := by rw [hUX, hGGi.eq]
      _ = G * (Gi * X) * U' := by simp only [mul_assoc]
      _ = G * (X * Gi) * U' := by rw [hGiX.eq]
      _ = _ := by simp only [mul_assoc]
  rw [add_mul, mul_add, a, b]

theorem nabla_star_commute_gamma_inv (Gi z Ns S : R) (nsGi : Ns * Gi = Gi * Ns + z * Gi * Gi) (hS : Ns * S = S * Ns - z * Gi * S)
    (c : Gi * z = z * Gi) : Commute Ns (Gi * S) := by
  show Ns * (Gi * S) = Gi * S * Ns
  calc Ns * (Gi * S) = (Ns * Gi) * S := (mul_assoc _ _ _).symm
    _ = Gi * (Ns * S) + z * Gi * Gi * S := by rw [nsGi, add_mul, mul_assoc Gi Ns S]
    _ = Gi * S * Ns - (Gi * z) * Gi * S + z * Gi * Gi * S := by rw [hS, mul_sub]; simp only [mul_assoc]
    _ = _ := by rw [c]; abel

theorem absC (G Gi z zb N Ns K : R) (t : ℂ) (hGGi : G * Gi = 1) (hGdef : G = z * zb - algebraMap ℂ R t)
    (czzb : z * zb = zb * z) (cGiz : Gi * z = z * Gi) (cGizb : Gi * zb = zb * Gi)
    (nz : N * z = z * N + 1) (nGi : N * Gi = Gi * N - zb * Gi * Gi)
    (nszb : Ns * zb = zb * Ns - 1) (nsGi : Ns * Gi = Gi * Ns + z * Gi * Gi)
    (hcurv : Ns * N - N * Ns = K * Gi * Gi) (cu cv : ℂ) :
    (-Ns - cu • (z * Gi)) * (-N - cv • (zb * Gi)) - (-N - cv • (zb * Gi)) * (-Ns - cu • (z * Gi)) =
      K * Gi * Gi + ((cu + cv) * t) • (Gi * Gi) := by
  have hzz : z * zb = G + t • 1 := by rw [hGdef, Algebra.algebraMap_eq_smul_one]; abel
  have w1 : z * zb * Gi * Gi = Gi + t • (Gi * Gi) := by
    rw [hzz, add_mul, add_mul, hGGi, one_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
  have k1 : Ns * (zb * Gi) = (zb * Gi) * Ns + t • (Gi * Gi) := by
    calc Ns * (zb * Gi) = (Ns * zb) * Gi := (mul_assoc _ _ _).symm
      _ = zb * (Ns * Gi) - Gi := by rw [nszb, sub_mul, one_mul, mul_assoc]
      _ = zb * Gi * Ns + (zb * z) * Gi * Gi - Gi := by rw [nsGi, mul_add]; simp only [mul_assoc]
      _ = _ := by rw [← czzb, w1]; abel
  have k2 : N * (z * Gi) = (z * Gi) * N - t • (Gi * Gi) := by
    calc N * (z * Gi) = (N * z) * Gi := (mul_assoc _ _ _).symm
      _ = z * (N * Gi) + Gi := by rw [nz, add_mul, one_mul, mul_assoc]
      _ = z * Gi * N - (z * zb) * Gi * Gi + Gi := by rw [nGi, mul_sub]; simp only [mul_assoc]
      _ = _ := by rw [w1]; abel
  have k3 : (z * Gi) * (zb * Gi) = (zb * Gi) * (z * Gi) := by
    calc (z * Gi) * (zb * Gi) = z * (Gi * zb) * Gi := by simp only [mul_assoc]
      _ = (z * zb) * Gi * Gi := by rw [cGizb]; simp only [mul_assoc]
      _ = zb * (z * Gi) * Gi := by rw [czzb]; simp only [mul_assoc]
      _ = zb * (Gi * z) * Gi := by rw [cGiz]
      _ = _ := by simp only [mul_assoc]
  have ex : (-Ns - cu • (z * Gi)) * (-N - cv • (zb * Gi)) - (-N - cv • (zb * Gi)) * (-Ns - cu • (z * Gi)) =
      (Ns * N - N * Ns) + cv • (Ns * (zb * Gi) - (zb * Gi) * Ns) - cu • (N * (z * Gi) - (z * Gi) * N) +
        (cu * cv) • ((z * Gi) * (zb * Gi) - (zb * Gi) * (z * Gi)) := by
    simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    module
  rw [ex, hcurv, k1, k2, k3]
  module

theorem commutator_perturbed_product (M0 L0 Gi Sl Sm : R) (hA : Commute M0 (Gi * Sl)) (hB : Commute L0 (Gi * Sm))
    (hGm : Commute Gi Sm) (hGl : Commute Gi Sl) :
    (M0 + Gi * Sm) * (L0 + Gi * Sl) - (L0 + Gi * Sl) * (M0 + Gi * Sm) =
      (M0 * L0 - L0 * M0) + Gi * Gi * (Sm * Sl - Sl * Sm) := by
  have a : Gi * Sm * (Gi * Sl) = Gi * Gi * (Sm * Sl) := by
    calc Gi * Sm * (Gi * Sl) = Gi * (Sm * Gi) * Sl := by simp only [mul_assoc]
      _ = Gi * (Gi * Sm) * Sl := by rw [hGm.eq]
      _ = _ := by simp only [mul_assoc]
  have b : Gi * Sl * (Gi * Sm) = Gi * Gi * (Sl * Sm) := by
    calc Gi * Sl * (Gi * Sm) = Gi * (Sl * Gi) * Sm := by simp only [mul_assoc]
      _ = Gi * (Gi * Sl) * Sm := by rw [hGl.eq]
      _ = _ := by simp only [mul_assoc]
  simp only [add_mul, mul_add]
  rw [a, b, hA.eq, hB.eq, mul_sub]
  abel

theorem commutator_four_commuting (a b S Ss : R) (h1 : Ss * b = b * Ss) (h2 : S * a = a * S) (hab : a * b = b * a)
    (hm : Ss * S = S * Ss) : a * Ss * (b * S) - b * S * (a * Ss) = 0 := by
  have e1 : a * Ss * (b * S) = a * b * (Ss * S) := by
    calc a * Ss * (b * S) = a * (Ss * b) * S := by simp only [mul_assoc]
      _ = _ := by rw [h1]; simp only [mul_assoc]
  have e2 : b * S * (a * Ss) = b * a * (S * Ss) := by
    calc b * S * (a * Ss) = b * (S * a) * Ss := by simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [mul_assoc]
  rw [e1, e2, hab, hm, sub_self]

theorem commutator_expansion_identity (a ap am S Ss Nn Nd : R) (h1 : Ss * a = ap * Ss) (h2 : S * a = am * S) (hn : Ss * S = Nn)
    (hd : S * Ss = Nd) : a * Ss * (a * S) - a * S * (a * Ss) = a * ap * Nn - a * am * Nd := by
  have e1 : a * Ss * (a * S) = a * ap * (Ss * S) := by
    calc a * Ss * (a * S) = a * (Ss * a) * S := by simp only [mul_assoc]
      _ = _ := by rw [h1]; simp only [mul_assoc]
  have e2 : a * S * (a * Ss) = a * am * (S * Ss) := by
    calc a * S * (a * Ss) = a * (S * a) * Ss := by simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [mul_assoc]
  rw [e1, e2, hn, hd]

theorem absUX (a g S X a' e : R) (s1 : g * S = S * X) (s2 : a * g = e) (s3 : X * a' = e) :
    a * S * X = X * (a' * S) := by
  calc a * S * X = a * (S * X) := mul_assoc _ _ _
    _ = a * (g * S) := by rw [s1]
    _ = (a * g) * S := (mul_assoc _ _ _).symm
    _ = (X * a') * S := by rw [s2, s3]
    _ = _ := mul_assoc _ _ _

theorem absInv (G Gi X Xi : R) (hG : G * Gi = 1) (hG' : Gi * G = 1) (hX : X * Xi = 1) (hX' : Xi * X = 1)
    (c : Commute X Gi) (c' : Commute Xi G) : (G * X) * (Gi * Xi) = 1 ∧ (Gi * Xi) * (G * X) = 1 := by
  constructor
  · calc (G * X) * (Gi * Xi) = G * (X * Gi) * Xi := by simp only [mul_assoc]
      _ = (G * Gi) * (X * Xi) := by rw [c.eq]; simp only [mul_assoc]
      _ = 1 := by rw [hG, hX, one_mul]
  · calc (Gi * Xi) * (G * X) = Gi * (Xi * G) * X := by simp only [mul_assoc]
      _ = (Gi * G) * (Xi * X) := by rw [c'.eq]; simp only [mul_assoc]
      _ = 1 := by rw [hG', hX', one_mul]

theorem absTi (Gi a b : R) (c : Commute a Gi) : (Gi * a) * (Gi * b) = Gi * Gi * (a * b) := by
  calc (Gi * a) * (Gi * b) = Gi * (a * Gi) * b := by simp only [mul_assoc]
    _ = _ := by rw [c.eq]; simp only [mul_assoc]

theorem absTerm (X k Gi S : R) (h1 : Commute X k) (h2 : Commute X (Gi * S)) (c : Commute Gi k) :
    Commute X (Gi * (k * S)) := by
  have : Gi * (k * S) = k * (Gi * S) := by rw [← mul_assoc, c.eq, mul_assoc]
  rw [this]; exact h1.mul_right h2

theorem absLG2 (G b zb N : R) (hNG : N * G = G * N + zb) (hbG : b * G = G * b) (hGb : G * b = zb) (c c' : ℂ)
    (hc : c' = c + 1) : (-N - c • b) * G = G * (-N - c' • b) := by
  rw [absLG G b zb N hNG hbG, hc, add_smul, one_smul, ← sub_sub, mul_sub G _ b, hGb]

theorem absLG3 (G b z N : R) (hNG : N * G = G * N - z) (hbG : b * G = G * b) (hGb : G * b = z) (c c' : ℂ)
    (hc : c = c' + 1) : (-N - c • b) * G = G * (-N - c' • b) := by
  have hNG' : N * G = G * N + -z := by rw [hNG, sub_eq_add_neg]
  rw [absLG G b (-z) N hNG' hbG, hc, add_smul, one_smul, ← sub_sub, mul_sub G _ b, hGb]
  abel

theorem absFin (Gi K S : R) (c : ℂ) (h : Commute K Gi) :
    K * Gi * Gi + c • (Gi * Gi) + Gi * Gi * S = Gi * Gi * (K + c • 1 + S) := by
  have : K * Gi * Gi = Gi * Gi * K := by rw [h.eq, mul_assoc, h.eq, mul_assoc]
  rw [this, mul_add, mul_add, mul_smul_comm, mul_one]

end abs2

theorem kap_mul (P : Par) (f g h : Ty P → ℂ) (e : ∀ π, f π * g π = h π) : kap P f * kap P g = kap P h := by
  rw [← map_mul]; exact congrArg (kap P) (funext e)

theorem star_kap (P : Par) (f : Ty P → ℂ) : star (kap P f) = kap P (fun π => star (f π)) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun π => ?_)
  exact (algebraMap_star_comm (f π)).symm

theorem fn_comm (P : Par) (f fb g gb : Fn P.r) : Commute (sc P (fnP f fb)) (sc P (fnP g gb)) := by
  show sc P _ * sc P _ = sc P _ * sc P _
  have h : ∀ a b : Pr P.r, sc P a * sc P b = sc P (a * b) := fun a b => (map_mul (Matrix.scalar (Ty P)) a b).symm
  rw [h, h, Mx2.multiplierPair_comm]

theorem sc_SSs (hSc : SSScalar) (P : Par) (l : ℕ) (w : Pr P.r) : Commute (sc P w) (star (SS P l)) := by
  have h := (hSc P l (star w)).star_star
  rw [Mx1.star_sc, star_star] at h
  exact h.symm

theorem shS (hSh : SSShift) (P : Par) (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    star (SS P l) * kap P g = kap P f * star (SS P l) := by
  have h1 := hSh P l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by simp only [h π π' hu])
  have h2 := congrArg star h1
  rw [star_mul, star_mul, star_kap, star_kap] at h2
  simpa only [star_star] using h2

theorem fac_ne (P : Par) (π : Ty P) (Y : ℂ) (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (h : xC P π Y ≠ 0) :
    Y + (rho P π j : ℂ) ≠ 0 := by
  rw [xC_eq P π Y j hj] at h; exact right_ne_zero_of_mul h

noncomputable def ti (P : Par) (Y : ℂ) : A P := ggiA P * kap P fun π => (xC P π Y)⁻¹

noncomputable def Ul (P : Par) (Y : ℂ) : A P :=
  ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j

noncomputable def Um (P : Par) (Y : ℂ) : A P :=
  ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P j)

theorem lA_eq (P : Par) (Y : ℂ) : lA P Y = l0A P Y + ggiA P * Ul P Y := rfl
theorem mA_eq (P : Par) (Y : ℂ) : mA P Y = m0A P Y + ggiA P * Um P Y := rfl

theorem raising_constant_eq_shift (P : Par) (Y : ℂ) : m0A P Y = -nabsA P - (Y - 1 / 2) • (zA P * ggiA P) := by
  rw [m0A, Algebra.smul_def]

theorem sc_Ul (hSc : SSScalar) (P : Par) (w : Pr P.r) (Y : ℂ) : Commute (sc P w) (Ul P Y) := by
  unfold Ul
  exact Commute.sum_right _ _ _ (fun j _ => ((kap_comm_sc P _ w).symm).mul_right (hSc P j w).symm)

theorem sc_Um (hSc : SSScalar) (P : Par) (w : Pr P.r) (Y : ℂ) : Commute (sc P w) (Um P Y) := by
  unfold Um
  exact Commute.sum_right _ _ _ (fun j _ => ((kap_comm_sc P _ w).symm).mul_right (sc_SSs hSc P j w))

theorem lower_shift_commute_coordinate (hSh : SSShift) (hR : RhoUp) (P : Par) (Y : ℂ) (h0 : ∀ π, xC P π Y ≠ 0)
    (h1 : ∀ π, xC P π (Y + 1) ≠ 0) : Ul P Y * xA P (Y + 1) = xA P (Y + 1) * Ul P (Y + 1) := by
  unfold Ul
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have s1 : (kap P fun π => xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) * SS P j = SS P j * xA P (Y + 1) :=
    hSh P j _ _ (fun π π' hU => by
      show xEx P {j} π' (Y + 1) * (Y + (rho P π' j : ℂ)) = xC P π (Y + 1)
      rw [xC_eq P π (Y + 1) j hj, xEx_up hR P j π π' hU {j} (Finset.mem_singleton_self j), rho_up hR P j hj π π' hU]
      push_cast; ring)
  have s2 : (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * (kap P fun π => xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) =
      kap P fun π => xEx P {j} π (Y + 1) :=
    kap_mul P _ _ _ (fun π => by
      show (Y + (rho P π j : ℂ))⁻¹ * (xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) = xEx P {j} π (Y + 1)
      have := fac_ne P π Y j hj (h0 π)
      field_simp)
  have s3 : xA P (Y + 1) * (kap P fun π => (Y + 1 + (rho P π j : ℂ))⁻¹) = kap P fun π => xEx P {j} π (Y + 1) :=
    kap_mul P _ _ _ (fun π => by
      show xC P π (Y + 1) * (Y + 1 + (rho P π j : ℂ))⁻¹ = xEx P {j} π (Y + 1)
      have := fac_ne P π (Y + 1) j hj (h1 π)
      rw [xC_eq P π (Y + 1) j hj]; field_simp)
  exact absUX _ _ _ _ _ _ s1 s2 s3

theorem upper_shift_commute_coordinate (hSh : SSShift) (hR : RhoUp) (P : Par) (Y : ℂ) (h0 : ∀ π, xC P π Y ≠ 0)
    (h1 : ∀ π, xC P π (Y + 1) ≠ 0) : Um P (Y + 1) * xA P Y = xA P Y * Um P Y := by
  unfold Um
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have s1 : (kap P fun π => xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) * star (SS P j) = star (SS P j) * xA P Y :=
    (shS hSh P j _ _ (fun π π' hU => by
      show xC P π' Y = xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))
      rw [xC_eq P π' Y j hj, xEx_up hR P j π π' hU {j} (Finset.mem_singleton_self j), rho_up hR P j hj π π' hU]
      push_cast; ring)).symm
  have s2 : (kap P fun π => (Y + 1 + (rho P π j : ℂ))⁻¹) * (kap P fun π => xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) =
      kap P fun π => xEx P {j} π Y :=
    kap_mul P _ _ _ (fun π => by
      show (Y + 1 + (rho P π j : ℂ))⁻¹ * (xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) = xEx P {j} π Y
      have := fac_ne P π (Y + 1) j hj (h1 π)
      field_simp)
  have s3 : xA P Y * (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) = kap P fun π => xEx P {j} π Y :=
    kap_mul P _ _ _ (fun π => by
      show xC P π Y * (Y + (rho P π j : ℂ))⁻¹ = xEx P {j} π Y
      have := fac_ne P π Y j hj (h0 π)
      rw [xC_eq P π Y j hj]; field_simp)
  exact absUX _ _ _ _ _ _ s1 s2 s3

theorem monodromy_diagonal_inverse (hLF : LevFns) (P : Par) (Y : ℂ) (h : ∀ π, xC P π Y ≠ 0) :
    t22 P Y * ti P Y = 1 ∧ ti P Y * t22 P Y = 1 := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P
  have hX : xA P Y * (kap P fun π => (xC P π Y)⁻¹) = 1 :=
    (kap_mul P _ _ (fun _ => 1) (fun π => mul_inv_cancel₀ (h π))).trans (map_one (kap P))
  have hX' : (kap P fun π => (xC P π Y)⁻¹) * xA P Y = 1 :=
    (kap_mul P _ _ (fun _ => 1) (fun π => inv_mul_cancel₀ (h π))).trans (map_one (kap P))
  exact absInv _ _ _ _ hGGi hGiG hX hX' (kap_comm_sc P _ _) (kap_comm_sc P _ _)

theorem ti_mul (P : Par) (a b : ℂ) :
    ti P a * ti P b = ggiA P * ggiA P * kap P fun π => (xC P π a)⁻¹ * (xC P π b)⁻¹ := by
  unfold ti
  have c : Commute (kap P fun π => (xC P π a)⁻¹) (ggiA P) := kap_comm_sc P _ _
  rw [absTi _ _ _ c, kap_mul P _ _ _ (fun π => rfl)]

theorem ti_comm (P : Par) (a b : ℂ) : ti P a * ti P b = ti P b * ti P a := by
  rw [ti_mul, ti_mul]
  exact congrArg (fun t => ggiA P * ggiA P * kap P t) (funext fun π => mul_comm _ _)

theorem kappa_commute_l0 (P : Par) (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P f) (l0A P Y) := by
  rw [lowering_constant_eq_shift]
  exact ((kap_comm_nab P f).neg_right).sub_right
    (((kap_comm_sc P f _).mul_right (kap_comm_sc P f _)).smul_right _)

theorem kappa_commute_raising_constant (P : Par) (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P f) (m0A P Y) := by
  rw [raising_constant_eq_shift]
  exact ((kap_comm_nabs P f).neg_right).sub_right
    (((kap_comm_sc P f _).mul_right (kap_comm_sc P f _)).smul_right _)

theorem l_mul_t22_shift (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (P : Par) (Y : ℂ)
    (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    lA P Y * t22 P (Y + 1) = t22 P (Y + 1) * lA P (Y + 1) := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P
  obtain ⟨_, _, _, _, nG, _, _⟩ := hLN P
  have cGzb : Commute (ggA P) (zbA P) := fn_comm P _ _ _ _
  have cGGi : Commute (ggA P) (ggiA P) := fn_comm P _ _ _ _
  have hGb : ggA P * (zbA P * ggiA P) = zbA P := by rw [← mul_assoc, cGzb.eq, mul_assoc, hGGi, mul_one]
  have hbG : (zbA P * ggiA P) * ggA P = ggA P * (zbA P * ggiA P) := (cGzb.mul_right cGGi).eq.symm
  have hLG : l0A P Y * ggA P = ggA P * l0A P (Y + 1) := by
    rw [lowering_constant_eq_shift, lowering_constant_eq_shift]
    exact absLG2 _ _ _ _ nG hbG hGb _ _ (by ring)
  rw [lA_eq, lA_eq, t22]
  exact lowering_intertwine_gamma _ _ _ _ _ _ _ hLG (kappa_commute_l0 P _ _) (lower_shift_commute_coordinate hSh hR P Y h0 h1) (sc_Ul hSc P _ _)
    (kap_comm_sc P _ _).symm cGGi

theorem modY1' (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLNs : LevNabs) (P : Par) (Y : ℂ)
    (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    mA P (Y + 1) * t22 P Y = t22 P Y * mA P Y := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P
  obtain ⟨_, _, _, _, nG, _, _⟩ := hLNs P
  have cGz : Commute (ggA P) (zA P) := fn_comm P _ _ _ _
  have cGGi : Commute (ggA P) (ggiA P) := fn_comm P _ _ _ _
  have hGb : ggA P * (zA P * ggiA P) = zA P := by rw [← mul_assoc, cGz.eq, mul_assoc, hGGi, mul_one]
  have hbG : (zA P * ggiA P) * ggA P = ggA P * (zA P * ggiA P) := (cGz.mul_right cGGi).eq.symm
  have hLG : m0A P (Y + 1) * ggA P = ggA P * m0A P Y := by
    rw [raising_constant_eq_shift, raising_constant_eq_shift]
    exact absLG3 _ _ _ _ nG hbG hGb _ _ (by ring)
  rw [mA_eq, mA_eq, t22]
  exact lowering_intertwine_gamma _ _ _ _ _ _ _ hLG (kappa_commute_raising_constant P _ _) (upper_shift_commute_coordinate hSh hR P Y h0 h1) (sc_Um hSc P _ _)
    (kap_comm_sc P _ _).symm cGGi

end PartB

section PartC

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

theorem nab_SSs (hSc : SSScalar) (hN : NabSS) (hSG : StarGens) (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    nabA P * star (SS P l) = star (SS P l) * nabA P + zbA P * ggiA P * star (SS P l) := by
  obtain ⟨_, hz, _, _, hGi, hnab⟩ := hSG P
  have h := congrArg star (hN P l hl).2
  have hns : star (nabsA P) = nabA P := by rw [← hnab, star_star]
  simp only [star_mul, star_sub] at h
  rw [hns, hz, hGi] at h
  have cg : Commute (ggiA P) (star (SS P l)) := sc_SSs hSc P l _
  have cz : Commute (zbA P) (star (SS P l)) := sc_SSs hSc P l _
  have cc : Commute (ggiA P) (zbA P) := fn_comm P _ _ _ _
  have c1 : star (SS P l) * (ggiA P * zbA P) = zbA P * ggiA P * star (SS P l) := by
    rw [(cg.mul_left cz).eq.symm, cc.eq]
  rw [c1] at h
  rw [h]; abel

theorem commute_m0_Ul (hSc : SSScalar) (hN : NabSS) (hLNs : LevNabs) (P : Par) (u : ℂ) :
    Commute (m0A P u) (ggiA P * Ul P u) := by
  obtain ⟨_, _, _, _, _, nsGi, _⟩ := hLNs P
  have cGiz : Commute (ggiA P) (zA P) := fn_comm P _ _ _ _
  have h1 : Commute (nabsA P) (ggiA P * Ul P u) := by
    unfold Ul; rw [Finset.mul_sum]
    exact Commute.sum_right _ _ _ (fun j hj => absTerm _ _ _ _ (kap_comm_nabs P _).symm
      (nabla_star_commute_gamma_inv _ _ _ _ nsGi (hN P j hj).2 cGiz.eq) (kap_comm_sc P _ _).symm)
  have h2 : Commute (zA P * ggiA P) (ggiA P * Ul P u) :=
    (cGiz.symm.mul_right (sc_Ul hSc P _ _)).mul_left ((Commute.refl _).mul_right (sc_Ul hSc P _ _))
  rw [raising_constant_eq_shift]; exact (h1.neg_left).sub_left (h2.smul_left _)

theorem commute_l0_Um (hSc : SSScalar) (hN : NabSS) (hSG : StarGens) (hLN : LevNab) (P : Par) (u : ℂ) :
    Commute (l0A P u) (ggiA P * Um P u) := by
  obtain ⟨_, _, _, _, _, nGi, _⟩ := hLN P
  have cGiz : Commute (ggiA P) (zbA P) := fn_comm P _ _ _ _
  have nGi' : nabA P * ggiA P = ggiA P * nabA P + -zbA P * ggiA P * ggiA P := by
    rw [nGi, neg_mul, neg_mul, sub_eq_add_neg]
  have h1 : Commute (nabA P) (ggiA P * Um P u) := by
    unfold Um; rw [Finset.mul_sum]
    exact Commute.sum_right _ _ _ (fun j hj => absTerm _ _ _ _ (kap_comm_nab P _).symm
      (nabla_star_commute_gamma_inv _ _ _ _ nGi' (by rw [nab_SSs hSc hN hSG P j hj, neg_mul, neg_mul, sub_neg_eq_add])
        (by rw [mul_neg, neg_mul, cGiz.eq])) (kap_comm_sc P _ _).symm)
  have h2 : Commute (zbA P * ggiA P) (ggiA P * Um P u) :=
    (cGiz.symm.mul_right (sc_Um hSc P _ _)).mul_left ((Commute.refl _).mul_right (sc_Um hSc P _ _))
  rw [lowering_constant_eq_shift]; exact (h1.neg_left).sub_left (h2.smul_left _)

noncomputable def bb (P : Par) (u : ℂ) (j : ℕ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ))⁻¹

theorem per_l (hSh : SSShift) (hR : RhoUp) (hNorm : SSNorm) (hMix : SSMixed) (P : Par) (hP : P.OK) (u : ℂ)
    (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ j ∈ Icc 1 (P.k - 1), kap P (bb P u l) * star (SS P l) * (kap P (bb P u j) * SS P j) -
      ∑ j ∈ Icc 1 (P.k - 1), kap P (bb P u j) * SS P j * (kap P (bb P u l) * star (SS P l)) =
    kap P fun π => (Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
      (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l]
  · have h1 : star (SS P l) * kap P (bb P u l) = (kap P fun π => (u + rho P π l + 1)⁻¹) * star (SS P l) :=
      shS hSh P l _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ))⁻¹ = (u + rho P π l + 1)⁻¹
        rw [rho_up hR P l hl π π' hU]; push_cast; rw [add_assoc])
    have h2 : SS P l * kap P (bb P u l) = (kap P fun π => (u + rho P π l - 1)⁻¹) * SS P l :=
      (hSh P l _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ) - 1)⁻¹ = (u + (rho P π l : ℂ))⁻¹
        rw [rho_up hR P l hl π π' hU]; push_cast; congr 1; ring)).symm
    rw [commutator_expansion_identity _ _ _ _ _ _ _ h1 h2 (hNorm P hP l hl).1 (hNorm P hP l hl).2, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, ← map_sub]
    refine congrArg (kap P) (funext fun π => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply, bb]
    ring
  · intro j hj hjl
    have h1 : star (SS P l) * kap P (bb P u j) = kap P (bb P u j) * star (SS P l) :=
      shS hSh P l _ _ (fun π π' hU => by
        show (u + (rho P π' j : ℂ))⁻¹ = (u + (rho P π j : ℂ))⁻¹
        rw [hR P l π π' hU j hj, if_neg hjl, add_zero])
    have h2 : SS P j * kap P (bb P u l) = kap P (bb P u l) * SS P j :=
      (hSh P j _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ))⁻¹ = (u + (rho P π l : ℂ))⁻¹
        rw [hR P j π π' hU l hl, if_neg (Ne.symm hjl), add_zero])).symm
    exact commutator_four_commuting _ _ _ _ h1 h2 (kap_comm_kap P _ _).eq (hMix P hP l hl j hj hjl)
  · intro h; exact absurd hl h

theorem UmUl (hSh : SSShift) (hR : RhoUp) (hNorm : SSNorm) (hMix : SSMixed) (P : Par) (hP : P.OK) (u : ℂ) :
    Um P u * Ul P u - Ul P u * Um P u =
      kap P fun π => ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
        (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) := by
  have e1 : Um P u * Ul P u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      kap P (bb P u l) * star (SS P l) * (kap P (bb P u j) * SS P j) := Finset.sum_mul_sum _ _ _ _
  have e2 : Ul P u * Um P u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      kap P (bb P u j) * SS P j * (kap P (bb P u l) * star (SS P l)) :=
    (Finset.sum_mul_sum _ _ _ _).trans Finset.sum_comm
  rw [e1, e2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (per_l hSh hR hNorm hMix P hP u), ← map_sum]
  exact congrArg (kap P) (funext fun π => Finset.sum_apply _ _ _)

theorem raising_lowering_commutator_alt (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature)
    (P : Par) (hP : P.OK) (u : ℂ) (h0 : ∀ π, xC P π (u - 1) ≠ 0) (h1 : ∀ π, xC P π u ≠ 0)
    (h2 : ∀ π, xC P π (u + 1) ≠ 0) :
    mA P u * lA P u - lA P u * mA P u =
      qC P (u - 1) • (ti P (u - 1) * ti P u) - qC P u • (ti P u * ti P (u + 1)) := by
  obtain ⟨_, _, _, _, _, _, hGGi, _, hGdef⟩ := hLF P
  obtain ⟨nz, _, _, _, _, nGi, _⟩ := hLN P
  obtain ⟨nszb, _, _, _, _, nsGi, _⟩ := hLNs P
  have czzb : Commute (zA P) (zbA P) := fn_comm P _ _ _ _
  have cGiz : Commute (ggiA P) (zA P) := fn_comm P _ _ _ _
  have cGizb : Commute (ggiA P) (zbA P) := fn_comm P _ _ _ _
  have cK : Commute (kap P fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) (ggiA P) := kap_comm_sc P _ _
  have cm : Commute (ggiA P) (Um P u) := sc_Um hSc P _ _
  have cl : Commute (ggiA P) (Ul P u) := sc_Ul hSc P _ _
  rw [mA_eq, lA_eq, commutator_perturbed_product _ _ _ _ _ (commute_m0_Ul hSc hN hLNs P u) (commute_l0_Um hSc hN hSG hLN P u) cm cl,
    UmUl hSh hR hNorm hMix P hP u, raising_constant_eq_shift, lowering_constant_eq_shift,
    absC _ _ _ _ _ _ _ _ hGGi hGdef czzb.eq cGiz.eq cGizb.eq nz nGi nszb nsGi (hCurv P), ti_mul, ti_mul,
    absFin _ _ _ _ cK, ← mul_smul_comm, ← mul_smul_comm, ← mul_sub]
  refine congrArg (fun t => ggiA P * ggiA P * t) ?_
  rw [← map_smul, ← map_smul, ← map_sub, ← map_one (kap P), ← map_smul, ← map_add, ← map_add]
  refine congrArg (kap P) (funext fun π => ?_)
  have := pf P hP π u (h0 π) (h1 π) (h2 π)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
  rw [this]; push_cast; ring

def Det8 (P : Par) (Y : ℂ) : Prop :=
  t11 P (Y + 1) * t21 P Y - t21 P (Y + 1) * t11 P Y = 0 ∧
  t11 P (Y + 1) * t22 P Y - t21 P (Y + 1) * t12 P Y = algebraMap ℂ (A P) (qC P Y) ∧
  t12 P (Y + 1) * t21 P Y - t22 P (Y + 1) * t11 P Y = -algebraMap ℂ (A P) (qC P Y) ∧
  t12 P (Y + 1) * t22 P Y - t22 P (Y + 1) * t12 P Y = 0 ∧
  t11 P Y * t12 P (Y + 1) - t12 P Y * t11 P (Y + 1) = 0 ∧
  t11 P Y * t22 P (Y + 1) - t12 P Y * t21 P (Y + 1) = algebraMap ℂ (A P) (qC P Y) ∧
  t21 P Y * t12 P (Y + 1) - t22 P Y * t11 P (Y + 1) = -algebraMap ℂ (A P) (qC P Y) ∧
  t21 P Y * t22 P (Y + 1) - t22 P Y * t21 P (Y + 1) = 0

theorem det_eight_at_good_point (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal)
    (P : Par) (hP : P.OK) (Y : ℂ) (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0)
    (h2 : ∀ π, xC P π (Y + 1 + 1) ≠ 0) : Det8 P Y := by
  obtain ⟨a21, a12, a11, _⟩ := hQN P hP Y h0
  obtain ⟨b21, b12, b11, _⟩ := hQN P hP (Y + 1) h1
  have a11' : t11 P Y = qC P Y • ti P (Y + 1) + t22 P Y * mA P Y * lA P Y := a11 h1
  have b11' : t11 P (Y + 1) = qC P (Y + 1) • ti P (Y + 1 + 1) + t22 P (Y + 1) * mA P (Y + 1) * lA P (Y + 1) := b11 h2
  have y3 := raising_lowering_commutator_alt hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv P hP (Y + 1)
    (by rw [add_sub_cancel_right]; exact h0) h1 h2
  rw [add_sub_cancel_right] at y3
  unfold Det8
  rw [a21, a12, a11', b21, b12, b11']
  exact det_abs _ _ _ _ _ _ _ _ _ _ _ (monodromy_diagonal_inverse hLF P Y h0).1 (monodromy_diagonal_inverse hLF P Y h0).2 (monodromy_diagonal_inverse hLF P (Y + 1) h1).1
    (monodromy_diagonal_inverse hLF P (Y + 1) h1).2 (ti_comm P _ _) (l_mul_t22_shift hSc hSh hR hLF hLN P Y h0 h1)
    (modY1' hSc hSh hR hLF hLNs P Y h0 h1) y3

end PartC

section PartD

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial

theorem isPoly_kap (P : Par) (p : Ty P → ℂ[X]) : IsPoly (fun Y => kap P fun π => (p π).eval Y) := by
  have h : ∀ Y, (kap P fun π => (p π).eval Y) =
      ∑ π : Ty P, algebraMap ℂ (A P) ((p π).eval Y) * kap P (fun j => if π = j then 1 else 0) := by
    intro Y
    conv_lhs => rw [pi_eq_sum_univ (fun π => (p π).eval Y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [map_smul, Algebra.smul_def]
  exact (IsPoly.sum _ _ fun π _ => (IsPoly.scalar (p π)).mul (IsPoly.const _)).congr h

theorem xEx_poly (P : Par) (ex : Finset ℕ) (π : Ty P) (Y : ℂ) :
    xEx P ex π Y = (∏ i ∈ Icc 1 (P.k - 1) \ ex, (X + C (rho P π i : ℂ))).eval Y := by
  simp [xEx, eval_prod]

theorem xC_poly (P : Par) (π : Ty P) (Y : ℂ) :
    xC P π Y = (∏ i ∈ Icc 1 (P.k - 1), (X + C (rho P π i : ℂ))).eval Y := by
  simp [xC, eval_prod]

theorem qC_poly (P : Par) (Y : ℂ) : qC P Y = (qP P).eval Y := by
  simp only [qC, qP, eval_mul, eval_C, eval_prod, eval_add, eval_X]
  refine congrArg (fun t => -((P.T : ℂ) * P.T') * t) (Finset.prod_congr rfl fun i _ => ?_)
  ring

theorem isPoly_xEx (P : Par) (ex : Finset ℕ) : IsPoly (fun Y => kap P fun π => xEx P ex π Y) :=
  (isPoly_kap P _).congr (fun Y => congrArg (kap P) (funext fun π => xEx_poly P ex π Y))

theorem isPoly_xA (P : Par) : IsPoly (xA P) :=
  (isPoly_kap P _).congr (fun Y => congrArg (kap P) (funext fun π => xC_poly P π Y))

theorem isPoly_w (P : Par) : IsPoly (fun Y => kap P fun π => wC P π Y) := isPoly_kap P _

theorem isPoly_q (P : Par) : IsPoly (fun Y => algebraMap ℂ (A P) (qC P Y)) :=
  (IsPoly.scalar (qP P)).congr (fun Y => by rw [qC_poly])

theorem isPoly_lowering_constant (P : Par) : IsPoly (l0A P) :=
  ((IsPoly.const (-nabA P)).sub (((IsPoly.scalar (X + C (1 / 2))).mul (IsPoly.const (zbA P * ggiA P))))).congr
    (fun Y => by simp [l0A])

theorem isPoly_raising_constant (P : Par) : IsPoly (m0A P) :=
  ((IsPoly.const (-nabsA P)).sub (((IsPoly.scalar (X - C (1 / 2))).mul (IsPoly.const (zA P * ggiA P))))).congr
    (fun Y => by simp [m0A])

theorem isPoly_S21 (P : Par) : IsPoly (weightedSumBis P) :=
  IsPoly.sum _ _ fun l _ => (IsPoly.const (SS P l)).mul (isPoly_xEx P {l})

theorem isPoly_S12 (P : Par) : IsPoly (S12 P) :=
  IsPoly.sum _ _ fun l _ => (isPoly_xEx P {l}).mul (IsPoly.const (star (SS P l)))

theorem isPoly_quartic_sum (P : Par) : IsPoly (S4 P) :=
  IsPoly.sum _ _ fun l _ => IsPoly.sum _ _ fun j _ =>
    (IsPoly.const (star (SS P l) * SS P j)).mul (isPoly_xEx P {l, j})

theorem isPoly_diagonal_entry (P : Par) : IsPoly (t22 P) := (IsPoly.const (ggA P)).mul (isPoly_xA P)

theorem isPoly_t21 (P : Par) : IsPoly (t21 P) :=
  (((IsPoly.const (ggA P)).mul (isPoly_xA P)).mul (isPoly_lowering_constant P)).add (isPoly_S21 P)

theorem isPoly_upper_right_entry (P : Par) : IsPoly (t12 P) :=
  (((IsPoly.const (ggA P)).mul (isPoly_xA P)).mul (isPoly_raising_constant P)).add (isPoly_S12 P)

theorem isPoly_upper_left_entry (P : Par) : IsPoly (t11 P) :=
  (((((IsPoly.const (ggiA P)).mul (isPoly_w P)).add
    ((((IsPoly.const (ggA P)).mul (isPoly_xA P)).mul (isPoly_raising_constant P)).mul (isPoly_lowering_constant P))).add
    ((((IsPoly.const (ggA P)).mul (isPoly_raising_constant P)).mul (IsPoly.const (ggiA P))).mul (isPoly_S21 P))).add
    ((isPoly_S12 P).mul (isPoly_lowering_constant P))).add ((IsPoly.const (ggiA P)).mul (isPoly_quartic_sum P))

noncomputable def badSet (P : Par) : Finset ℂ :=
  (Finset.univ : Finset (Ty P)).biUnion fun π => (Icc 1 (P.k - 1)).biUnion fun i =>
    {-(rho P π i : ℂ), -(rho P π i : ℂ) - 1, -(rho P π i : ℂ) - 2}

theorem good_of (P : Par) (Y : ℂ) (hY : Y ∉ badSet P) (c : ℂ) (hc : c = 0 ∨ c = 1 ∨ c = 2) (π : Ty P) :
    xC P π (Y + c) ≠ 0 := by
  unfold xC
  rw [Finset.prod_ne_zero_iff]
  intro i hi h0
  apply hY
  simp only [badSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨π, i, hi, ?_⟩
  rcases hc with rfl | rfl | rfl
  · left; linear_combination h0
  · right; left; linear_combination h0
  · right; right; linear_combination h0

theorem det8 (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal)
    (P : Par) (hP : P.OK) (Y : ℂ) : Det8 P Y := by
  have hg : ∀ Z, Z ∉ (↑(badSet P) : Set ℂ) → Det8 P Z := by
    intro Z hZ
    have hZ' : Z ∉ badSet P := by simpa using hZ
    refine det_eight_at_good_point hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv hQN P hP Z ?_ ?_ ?_
    · intro π; have := good_of P Z hZ' 0 (Or.inl rfl) π; rwa [add_zero] at this
    · exact good_of P Z hZ' 1 (Or.inr (Or.inl rfl))
    · intro π; have := good_of P Z hZ' 2 (Or.inr (Or.inr rfl)) π
      rwa [show Z + 2 = Z + 1 + 1 by ring] at this
  have hfin : (↑(badSet P) : Set ℂ).Finite := Finset.finite_toSet _
  have p11 := isPoly_upper_left_entry P
  have p12 := isPoly_upper_right_entry P
  have p21 := isPoly_t21 P
  have p22 := isPoly_diagonal_entry P
  have s11 := p11.shift 1
  have s12 := p12.shift 1
  have s21 := p21.shift 1
  have s22 := p22.shift 1
  have pq := isPoly_q P
  have p0 : IsPoly (fun _ : ℂ => (0 : A P)) := IsPoly.const 0
  exact ⟨((s11.mul p21).sub (s21.mul p11)).ext p0 hfin (fun Z hZ => (hg Z hZ).1) Y,
    ((s11.mul p22).sub (s21.mul p12)).ext pq hfin (fun Z hZ => (hg Z hZ).2.1) Y,
    ((s12.mul p21).sub (s22.mul p11)).ext pq.neg hfin (fun Z hZ => (hg Z hZ).2.2.1) Y,
    ((s12.mul p22).sub (s22.mul p12)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.1) Y,
    ((p11.mul s12).sub (p12.mul s11)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.2.1) Y,
    ((p11.mul s22).sub (p12.mul s21)).ext pq hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.1) Y,
    ((p21.mul s12).sub (p22.mul s11)).ext pq.neg hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.2.1) Y,
    ((p21.mul s22).sub (p22.mul s21)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.2.2) Y⟩

theorem qQDet_of (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal) :
    QQDet := by
  intro P hP Y
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := det8 hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv hQN P hP Y
  exact isSymplectic_of_eight_relations _ _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8

end PartD

end Formalism.FourierDecayAlt.P.Mx7

namespace Formalism.FourierDecayAlt.P

theorem transfer_determinant : Formalism.FourierDecayAlt.M.QQDet :=
  Mx7.qQDet_of shift_scalar_relation shift_shift_relation rho_raise level_function_relations level_nabla_relations level_nabla_star_relations
    star_generators nabla_shift_relation shift_norm_relation shift_mixed_relation m_curvature_proof transfer_normal_alt

theorem lower_left_commute_model : Formalism.FourierDecayAlt.M.T21Commute :=
  Mx7.lower_left_commute_of_laws shift_scalar_relation shift_shift_relation shift_commute_relation nabla_shift_relation level_nabla_relations level_function_relations
    rho_raise

end Formalism.FourierDecayAlt.P
