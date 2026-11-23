import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.AdjEqConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_gsp_conj_inv_scaled {R Γ : Type} [CommRing R] [Group Γ] (r : Γ →* M4 R) (x y : Γ) (ν s s' t : R)
    (hr : IsGSp ν (r x)) (hs : s * s' = 1) (ht : t = s * ν) :
    (t • r (y * x * y⁻¹)⁻¹).charpoly = (s • r x).charpoly := by
  have h1 : IsGSp (s * s * ν) (s • r x) := by
    have ha : adj (s • r x) = s • adj (r x) := by
      ext i j
      simp only [adj_apply, Matrix.smul_apply]
      rw [smul_comm]
    unfold IsGSp at hr ⊢
    rw [ha, Matrix.smul_mul, Matrix.mul_smul, hr, smul_smul, smul_smul]
  have h2 : (s • r x) * (s' • r x⁻¹) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul, ← map_mul, mul_inv_cancel, map_one]
  have h3 := phiAdj _ _ _ h1 h2
  rw [← h3, smul_smul]
  have h4 : s * s * ν * s' = t := by rw [ht]; linear_combination (s * ν) * hs
  rw [h4]
  have h5 : t • r (y * x * y⁻¹)⁻¹ = r y * ((t • r x⁻¹) * r y⁻¹) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h5, Matrix.charpoly_mul_comm, Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]

theorem UpperTheory.V.Ws.phiPol :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, ∃ g', K.V.pr g' = (K.V.frame.conj (K.V.pr g))⁻¹ ∧ (((K.V.frame.eps c'.O X.A (K.V.pr g) ^ (1 - ((4 : ℕ) : ℤ)) : X.Aˣ) : X.A) • K.rho X n g').charpoly = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  obtain ⟨cF, hc⟩ := phiConj T K.s
  obtain ⟨g₂, h1, h2⟩ := hc g
  refine ⟨g₂⁻¹, ?_, ?_⟩
  · rw [map_inv]
    congr 1
    apply Subtype.ext
    change toGS Ω K.V.S' (W.resP T.L Ω g₂) = toGS Ω K.V.S' K.s.c * toGS Ω K.V.S' (W.resP T.L Ω g) * (toGS Ω K.V.S' K.s.c)⁻¹
    rw [h1, map_mul, map_mul, map_inv]
  · obtain ⟨k1, k2, -⟩ := K.conj g g₂ h1
    have he : K.V.frame.eps c'.O X.A (K.V.pr g) =
        Units.map (algebraMap c'.O X.A : c'.O →* X.A) (chiO T.L Ω l c'.O g) := by
      have : K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) = cycZ T.L Ω l g := DFunLike.congr_fun K.V.hε (W.resP T.L Ω g)
      apply Units.ext
      change algebraMap c'.O X.A (algebraMap ℤ_[l] c'.O (K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) : ℤ_[l]ˣ)) = _
      rw [this]
      rfl
    rw [Link.rho_apply, Link.rho_apply, smul_smul, map_inv, h2, he]
    refine charpoly_gsp_conj_inv_scaled X.P.r _ _ _ _ (algebraMap c'.O X.A (K.sc n g⁻¹)) _ (X.pair.mult (resLe T.F_le g)) ?_ ?_
    · rw [← map_mul, ← Link.sc_mul, mul_inv_cancel, Link.sc_one, map_one]
    · have hb : K.β g₂⁻¹ = K.β g := by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left k2).symm
      rw [← map_zpow, Units.coe_map]
      change algebraMap c'.O X.A _ * _ = _ * algebraMap c'.O X.A (inc h (D.th (resQ T.L g)))
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [Link.sc, hb]
      set e := chiO T.L Ω l c'.O g
      have e1 : ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) * (e : c'.O) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        norm_num
      have e2 : ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) * K.κ g₂ = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      generalize ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) = u at e1 ⊢
      generalize ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) = v at e2 ⊢
      generalize (inc h (D.th (resQ T.L g)) : c'.O) = θ at k1 ⊢
      generalize ((K.β g : c'.Oˣ) : c'.O) ^ n = b
      linear_combination (-u * v * b) * k1 + (b * (K.κ g : c'.O) * θ * u * (e : c'.O) ^ 3) * e2 + (b * (K.κ g : c'.O) * θ) * e1
