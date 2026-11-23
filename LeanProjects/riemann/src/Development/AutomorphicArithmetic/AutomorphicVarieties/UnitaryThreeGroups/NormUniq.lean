import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjugateStarMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ZetaReducibleRepEqSubInvAndIsUnit
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TransposeInverseTheta
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalTranspose

open Matrix UpperTheory.V.U3

private theorem conj_left {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG m R) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ :=
  _root_.UpperTheory.Reformulated.B.TransposeInverseTheta.conj_left h r g

private theorem conj_right {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG m R) (g : G) : (conjBy h r g).right = (r g).right :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalTranspose.conj_right h r g

private theorem conj_mat {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R)
    (r : G →* GG m R) (g : G) (hg : (r g).right = 1) :
    (conjBy h r g).mat * (h : Matrix (Fin m) (Fin m) R) = (h : Matrix (Fin m) (Fin m) R) * (r g).mat := by
  unfold GG.mat
  rw [conj_left, hg, sgnAct_one, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul]

private theorem unit_of_sub_mem {R : Type} [CommRing R] [IsLocalRing R] {a b : R} (hb : IsUnit b)
    (h : a - b ∈ IsLocalRing.maximalIdeal R) : IsUnit a := by
  by_contra ha
  have ha' : a ∈ IsLocalRing.maximalIdeal R := ha
  have : b ∈ IsLocalRing.maximalIdeal R := by
    simpa using Ideal.sub_mem _ ha' h
  exact this hb

theorem UpperTheory.V.U3.normalised_unique :
    ∀ {G R : Type} [Group G] [CommRing R] [IsLocalRing R]
      (η : G →* ℤˣ) (Ψ : G →* (IsLocalRing.ResidueField R)ˣ) (c g₁ : G) (r : G →* GG 3 R) (h : GL (Fin 3) R), IsUnit (2 : R) → Marks η Ψ c g₁ →
      (GG.map (IsLocalRing.residue R)).comp r = r0 η Ψ → CongOne (IsLocalRing.maximalIdeal R) h →
      Normalised c g₁ r → Normalised c g₁ (conjBy h r) → ∃ t : Rˣ, (t : R) - 1 ∈ IsLocalRing.maximalIdeal R ∧ h = tor R t := by
  intro G R _ _ _ η Ψ c g₁ r h h2 hM hred hc hN hN'
  have hright : ∀ g, (r g).right = η g := fun g => by
    have := congrArg (fun f : G →* GG 3 _ => (f g).right) hred
    simpa using this
  have hrc : (r c).right = -1 := (hright c).trans hM.ηc
  have hrg : (r g₁).right = 1 := (hright g₁).trans hM.ηg
  have hrs : (r (gstar c g₁)).right = 1 := by
    rw [hright, gstar, map_mul, map_mul, map_inv, hM.ηc, hM.ηg]; simp
  have hz := zmat_diag r c g₁ h2 hrc hrg hN
  have hz' := zmat_diag (conjBy h r) c g₁ h2 ((conj_right h r c).trans hrc)
    ((conj_right h r g₁).trans hrg) hN'
  have hζ : IsUnit (zeta c g₁ r) := by
    have h1 := (zeta_reducible_rep_eq_sub_inv_and_isUnit η Ψ c g₁ hM).2
    rw [← hred] at h1
    have h3 : zeta c g₁ ((GG.map (IsLocalRing.residue R)).comp r) =
        IsLocalRing.residue R (zeta c g₁ r) := by
      simp [zeta, zmat]
    rw [h3] at h1
    exact (isUnit_map_iff _ _).1 h1
  have hcomm : zmat c g₁ (conjBy h r) * (h : Matrix (Fin 3) (Fin 3) R) =
      (h : Matrix (Fin 3) (Fin 3) R) * zmat c g₁ r := by
    rw [zmat, zmat, Matrix.sub_mul, Matrix.mul_sub, conj_mat h r _ hrg, conj_mat h r _ hrs]
  rw [hz, hz'] at hcomm
  generalize zeta c g₁ r = ζ at hζ hcomm
  generalize zeta c g₁ (conjBy h r) = ζ' at hcomm
  have he : ∀ a b, ![ζ', 0, -ζ'] a * h.val a b = h.val a b * ![ζ, 0, -ζ] b := fun a b => by
    have := congrFun (congrFun hcomm a) b
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  have hd : ∀ a, h.val a a - 1 ∈ IsLocalRing.maximalIdeal R := fun a => by
    simpa using hc a a
  have hu0 : IsUnit (h.val 0 0) := unit_of_sub_mem isUnit_one (hd 0)
  have hζζ : ζ' = ζ := by
    have := he 0 0
    simp only [Matrix.cons_val_zero] at this
    exact hu0.mul_left_cancel (by rw [← this, mul_comm])
  subst hζζ
  have h2ζ : IsUnit (2 * ζ') := h2.mul hζ
  have e01 : h.val 0 1 = 0 := by
    have := he 0 1
    simp at this
    exact hζ.mul_left_cancel (by simpa using this)
  have e10 : h.val 1 0 = 0 := by
    have := he 1 0
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination -this)
  have e12 : h.val 1 2 = 0 := by
    have := he 1 2
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination this)
  have e21 : h.val 2 1 = 0 := by
    have := he 2 1
    simp only [Matrix.cons_val] at this
    exact hζ.mul_left_cancel (by linear_combination -this)
  have e02 : h.val 0 2 = 0 := by
    have := he 0 2
    simp only [Matrix.cons_val] at this
    exact h2ζ.mul_left_cancel (by linear_combination this)
  have e20 : h.val 2 0 = 0 := by
    have := he 2 0
    simp only [Matrix.cons_val] at this
    exact h2ζ.mul_left_cancel (by linear_combination -this)
  have hθ : theta h⁻¹ = h⁻¹ := by
    have h1 : (r c).left = 1 := Units.ext hN.atc
    have h3 : (conjBy h r c).left = 1 := Units.ext hN'.atc
    rw [conj_left, h1, hrc, sgnAct_neg_one, mul_one] at h3
    exact (eq_inv_of_mul_eq_one_right h3)
  have hJ : h.val * (Jmat R 3 * h.valᵀ * Jmat R 3) = 1 := by
    have := theta_val h⁻¹
    rw [hθ, inv_inv] at this
    rw [← this, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have p0 : h.val 0 0 * h.val 2 2 = 1 := by
    have := congrFun (congrFun hJ 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev, e01, e10, e12, e21, e02, e20] using this
  have p1 : h.val 1 1 * h.val 1 1 = 1 := by
    have := congrFun (congrFun hJ 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev, e01, e10, e12, e21, e02, e20] using this
  have e11 : h.val 1 1 = 1 := by
    have hu : IsUnit (h.val 1 1 + 1) :=
      unit_of_sub_mem h2 (by convert hd 1 using 1; ring)
    exact hu.mul_left_cancel (by linear_combination p1)
  refine ⟨Units.mkOfMulEqOne _ _ p0, hd 0, Units.ext ?_⟩
  rw [tor_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [wt1, e01, e10, e12, e21, e02, e20, e11, Units.mkOfMulEqOne]
