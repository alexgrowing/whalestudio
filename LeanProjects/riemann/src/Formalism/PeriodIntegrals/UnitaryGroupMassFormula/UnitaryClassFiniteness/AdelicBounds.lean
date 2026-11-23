import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.HermASingleLeft

noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

theorem adelic_bounds : AdelBounds := by
  intro F E _ _ _ _ _ _ σ M J L _h1 _h2 h3 h4 h5
  classical
  obtain ⟨k, hk, hkL⟩ := low_nat L h5
  obtain ⟨u, hu, huL⟩ := up_nat L h4
  obtain ⟨dJ, hdJ, hdJi⟩ := mat_den J
  have hJdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (posDefOfDefiniteSignature_holds M _ (h3 τ)).isUnit
    have e : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [e, h0, map_zero] at hu'
    exact not_isUnit_zero hu'
  obtain ⟨dI, hdI, hdIi⟩ := mat_den J⁻¹
  refine ⟨u * u * dJ, k * (dI * (u * u * dJ) * k), k * u, by positivity, by positivity, by positivity,
    fun h => ?_⟩
  set D := u * u * dJ with hDdef
  set g' := finMat σ J h⁻¹ with hg'def
  set g := finMat σ J h with hgdef
  have hgg' : g * g' = 1 := by rw [hgdef, hg'def, ← finMat_mul, mul_inv_cancel, finMat_one]
  have hg'g : g' * g = 1 := by rw [hgdef, hg'def, ← finMat_mul, inv_mul_cancel, finMat_one]
  have hU : cT (sigR (Af F) σ) g * JR (Af F) J * g = JR (Af F) J := finMat_unitary σ J h
  have hvs : ∀ (c : E) (x : Fin M → E), vinc (F := F) (c • x) = inclR (F := F) (Af F) c • vinc (F := F) x := by
    intro c x
    funext i
    simp [vinc, map_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro x hx e he
    show g'.mulVec (vinc ((((k * u : ℕ) : E) * e) • x)) ∈ latHat F E L
    have hw : g'.mulVec (vinc x) ∈ latHat F E L := hx
    rw [hvs, Matrix.mulVec_smul]
    have : inclR (F := F) (Af F) (((k * u : ℕ) : E) * e) • g'.mulVec (vinc x) =
        k • (fun i => inclR (F := F) (Af F) e * (u • (g'.mulVec (vinc x)) i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [this]
    exact low_vec L hkL fun i => Oh_mul (incl_mem_Oh he) (up_Oh L huL hw i)
  ·
    obtain ⟨m, hm, hmO⟩ := den_mat g'
    refine ⟨k * m, Nat.mul_pos hk hm, fun i e he => ?_⟩
    show g'.mulVec (vinc (Pi.single i (((k * m : ℕ) : E) * e))) ∈ latHat F E L
    have hv : vinc (F := F) (Pi.single i (((k * m : ℕ) : E) * e)) =
        Pi.single i (inclR (F := F) (Af F) (((k * m : ℕ) : E) * e)) := by
      funext l
      show inclR (F := F) (Af F) ((Pi.single i (((k * m : ℕ) : E) * e) : Fin M → E) l) = _
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hv, mulVec_single']
    have : (fun l => g' l i * inclR (F := F) (Af F) (((k * m : ℕ) : E) * e)) =
        k • (fun l => (m • g' l i) * inclR (F := F) (Af F) e) := by
      funext l
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [this]
    exact low_vec L hkL fun l => Oh_mul (hmO l i) (incl_mem_Oh he)
  ·
    intro x hx y hy
    have hX : g'.mulVec (vinc x) ∈ latHat F E L := hx
    have hY : g'.mulVec (vinc y) ∈ latHat F E L := hy
    have e1 : hermA σ J (vinc (F := F) x) (vinc y) = hermA σ J (g'.mulVec (vinc x)) (g'.mulVec (vinc y)) := by
      rw [← hermA_unitary σ J g hU (g'.mulVec (vinc x)) (g'.mulVec (vinc y)), Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec,
        Matrix.one_mulVec]
    have e2 : D • hermA σ J (g'.mulVec (vinc x)) (g'.mulVec (vinc y)) ∈ Oh F E :=
      hermA_Oh σ J hdJi (up_Oh L huL hX) (up_Oh L huL hY)
    apply oh_inter (F := F)
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← hermA_vinc, e1]
    exact e2
  ·
    intro y hy
    set Z := g'.mulVec (vinc (F := F) y) with hZdef
    have d1 : ∀ W ∈ latHat F E (abelian₂ σ J L h), D • hermA σ J W (vinc y) ∈ Oh F E := by
      intro W hW
      induction hW using AddSubgroup.closure_induction with
      | mem W hW =>
        obtain ⟨a, ha, x, hx, rfl⟩ := hW
        have e3 : (fun i => a ⊗ₜ[F] x i) = (a ⊗ₜ[F] (1 : E)) • vinc (F := F) x := by
          funext i
          simp [vinc, inclR, Algebra.TensorProduct.tmul_mul_tmul]
        rw [e3, hermA_smul_left, hermA_vinc]
        have e4 : D • (sigR (Af F) σ (a ⊗ₜ[F] (1 : E)) * inclR (F := F) (Af F) (PI.HermLatFin.herm (σ : E →+* E) J x y)) =
            sigR (Af F) σ (a ⊗ₜ[F] (1 : E)) * inclR (F := F) (Af F) ((D : E) * PI.HermLatFin.herm (σ : E →+* E) J x y) := by
          rw [nsmul_eq_mul, map_mul, map_natCast]
          ring
        rw [e4]
        exact Oh_mul (sigR_Oh σ (tmul_mem_Oh ha isIntegral_one)) (incl_mem_Oh (hy x hx))
      | zero => rw [hermA_zero_left, smul_zero]; exact zero_mem _
      | add W W' _ _ h1 h2 => rw [hermA_add_left, smul_add]; exact add_mem h1 h2
      | neg W _ h1 => rw [hermA_neg_left, smul_neg]; exact neg_mem h1
    have hRD := rational_points_dense F E σ M J L h4 h5 h
    have d2 : ∀ V ∈ latHat F E L, D • hermA σ J V Z ∈ Oh F E := by
      intro V hV
      have hgV : g.mulVec V ∈ latHat F E (abelian₂ σ J L h) :=
        (hRD (g.mulVec V)).1 (by rwa [← hg'def, Matrix.mulVec_mulVec, hg'g, Matrix.one_mulVec])
      have := d1 _ hgV
      have e5 : vinc (F := F) y = g.mulVec Z := by
        rw [hZdef, Matrix.mulVec_mulVec, hgg', Matrix.one_mulVec]
      rwa [e5, hermA_unitary σ J g hU] at this
    have d3 : ∀ i, (D * k) • ((JR (Af F) J).mulVec Z) i ∈ Oh F E := by
      intro i
      have hV : (Pi.single i (k • (1 : Af F ⊗[F] E)) : Fin M → Af F ⊗[F] E) ∈ latHat F E L :=
        single_mem L hkL one_mem_Oh i
      have := d2 _ hV
      rw [hermA_single_left, map_nsmul, map_one] at this
      have e6 : (D * k) • ((JR (Af F) J).mulVec Z) i =
          D • ((k • (1 : Af F ⊗[F] E)) * ((JR (Af F) J).mulVec Z) i) := by
        rw [smul_mul_assoc, one_mul, mul_smul]
      rw [e6]
      exact this
    have hJinv : (J⁻¹).map (inclR (F := F) (Af F)) * JR (Af F) J = 1 := by
      rw [JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJdet)]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have d4 : ∀ l, (dI * D * k) • Z l ∈ Oh F E := by
      intro l
      have hZ : Z = ((J⁻¹).map (inclR (F := F) (Af F))).mulVec ((JR (Af F) J).mulVec Z) := by
        rw [Matrix.mulVec_mulVec, hJinv, Matrix.one_mulVec]
      have e7 : (dI * D * k) • Z l = ∑ i, (inclR (F := F) (Af F) ((dI : E) * J⁻¹ l i)) *
          ((D * k) • ((JR (Af F) J).mulVec Z) i) := by
        conv_lhs => rw [hZ]
        rw [Matrix.mulVec, dotProduct, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.map_apply, nsmul_eq_mul, Nat.cast_mul, map_mul, map_natCast]
        ring
      rw [e7]
      exact AddSubgroup.sum_mem _ fun i _ => Oh_mul (incl_mem_Oh (hdIi l i)) (d3 i)
    show g'.mulVec (vinc (((k * (dI * D * k) : ℕ) : E) • y)) ∈ latHat F E L
    have hv : vinc (F := F) (((k * (dI * D * k) : ℕ) : E) • y) = (k * (dI * D * k)) • vinc (F := F) y := by
      funext i
      simp [vinc, map_mul, map_natCast, nsmul_eq_mul]
    rw [hv, Matrix.mulVec_smul, mul_smul]
    exact low_vec L hkL fun l => d4 l

end PI.UnitaryGroupMassFormula.UJClassFin
