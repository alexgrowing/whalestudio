import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FinMulSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.JstdTrace

open NumberField UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem tau_eq {K : Type} [Field K] {Δ τ τ' : K} (hr : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} {j} (hγ : HasTr γ τ) (hj : IsEmb τ γ j)
    {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) (y : DX Δ)
    (h : (mt (y⁻¹ * j z * y)).trace ^ 2 = algebraMap K _ (2 + τ') * (mt (y⁻¹ * j z * y)).det) : τ' = τ := by
  have e : mt (y⁻¹ * j z * y) = mt y⁻¹ * mt (j z) * mt y := rfl
  have e' : mt y * mt y⁻¹ = 1 := by
    change mt (y * y⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e1 : mt (j z) = 1 + mt γ := by rw [hj, hz]; simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have h1 := hγ.1
  have h2 := hγ.2
  rw [Matrix.det_fin_two] at h1
  rw [Matrix.trace_fin_two] at h2
  have t1 : (mt (j z)).trace = algebraMap K _ (2 + τ) := by
    rw [e1, Matrix.trace_fin_two, map_add, map_ofNat, ← h2]; simp; ring
  have t2 : (mt (j z)).det = algebraMap K _ (2 + τ) := by
    rw [e1, Matrix.det_fin_two, map_add, map_ofNat, ← h2]; simp; linear_combination h1
  rw [e, Matrix.trace_mul_cycle, e', one_mul, Matrix.det_mul, mul_comm _ (mt y).det, Matrix.det_mul, ← mul_assoc (mt y).det,
    ← Matrix.det_mul, e', Matrix.det_one, one_mul, t1, t2, ← map_pow, ← map_mul] at h
  have h3 := (algebraMap K (Lsq K Δ)).injective h
  have h4 : 2 + τ ≠ 0 := fun e => hr (by linear_combination (τ - 2) * e)
  exact mul_right_cancel₀ h4 (by linear_combination -h3)

theorem UpperTheory.V.Z.Sym.Glob.gqK :
    UpperTheory.V.Z.Sym.Glob.GqK := by
  classical
  intro F _ _ Δ D hD ι hι t ht τ hτ γ j hγ hj z hz
  haveI := hD.real
  have hr := cm_ne hτ
  have htr : ∀ v, HasTr ((ι γ).1 v) (cv v τ) := fun v => hasTr_map _ (hι γ v) hγ
  have f1 : ∀ v ∈ D.Sg, D.fKv t v = (D.S v).fK (t v) := fun v hv => funext fun g => if_pos hv
  have f2 : ∀ v ∉ D.Sg, D.fKv t v = fZD (Ov v) (D.χ v) := fun v hv => funext fun g => if_neg hv
  have J1 : ∀ v ∈ D.Sg, D.J2v v = (D.S v).J2 := fun v hv => if_pos hv
  have J2 : ∀ v ∉ D.Sg, D.J2v v = KD _ (Ov v) := fun v hv => if_neg hv
  choose zv hzv using fun v => zEx (cv_reg hr v)
  have ez : ∀ v jv, IsEmb (cv v τ) ((ι γ).1 v) jv → (ι (j z)).1 v = jv (zv v) := fun v jv hjv =>
    dx_ext ((hι (j z) v).trans (emb_map _ (hι γ v) hj hjv z _ (by
      rw [hzv, hz]; ext <;> simp [emap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])).symm)
  have k1 : ∀ v ∉ D.Sg, ∀ k ∈ KD _ (Ov v), fZD (Ov v) (D.χ v) k = 1 := fun v hv k hk => by
    have := (Loc.fzdLaw _ _ _ (hD.off v hv) _ (hD.chi v).1).2 1 1 k (by simp [IsScal, mt]) hk
    simpa using this
  by_cases hA : D.admitted t τ
  · rw [show one (D.admitted t τ) = 1 from if_pos hA, one_mul]
    refine gqD D hD ι hι t ht τ hτ hA γ j hγ hj (j z) (D.fKv t) (fun v => ?_) _ _ fun v jv hjv => ?_
    · by_cases hv : v ∈ D.Sg
      · rw [f1 v hv, J1 v hv]
        intro u hu x
        rw [(((hD.sig v hv).K_inv _ (ht v hv)).1 u hu _).2, (((hD.sig v hv).K_inv _ (ht v hv)).1 _ (inv_mem hu) _).1]
      · rw [f2 v hv, J2 v hv]
        exact fZD_conj _ (hD.off v hv) _ (hD.chi v).1
    · rw [ez v jv hjv]
      refine ⟨fun s => by rw [← map_mul, ← map_mul, mul_comm], ?_⟩
      by_cases hv : v ∈ D.Sg
      · rw [f1 v hv, J1 v hv]
        obtain ⟨-, h1, -, h3, -⟩ := (hD.sig v hv).D_orb _ (ht v hv) _ _ _ (cv_reg hr v) (htr v) hjv _ (hzv v)
        exact ⟨h1, fun _ => by rw [h3, show one (Ind _ _ _) = 1 from if_pos (hA v hv), mul_one], fun h => absurd hv h⟩
      · rw [f2 v hv, J2 v hv]
        refine ⟨(Loc.finD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv).2.1 _ (hzv v) _, fun h => absurd h hv, fun _ =>
          ⟨(locD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv _ (hD.chi v).1 _ (hzv v)).2, fun h1 h2 => ?_⟩⟩
        obtain ⟨h3, h4⟩ := (Loc.oneD _ _ _ _ (hD.off v hv) (cv_reg hr v) _ _ (htr v) hjv h1 h2).2.2 _ (hzv v)
        refine ⟨k1 v hv _ h3, fun y hy => h4 y ?_⟩
        by_contra h
        exact hy ((Loc.fzdLaw _ _ _ (hD.off v hv) _ (hD.chi v).1).1 _ h)
  · rw [show one (D.admitted t τ) = 0 from if_neg hA, zero_mul, mul_zero]
    refine gqOn_zero _ _ _ _ fun y => ?_
    obtain ⟨v, hv⟩ := not_forall.1 hA
    obtain ⟨hv, hI⟩ := Classical.not_imp.1 hv
    refine fin_mulSupp (D.fKv t) D.Sg (fun v hv k hk => by rw [f2 v hv]; exact k1 v hv k hk) _ (v := v) ?_
    rw [f1 v hv]
    by_contra h
    haveI : CharZero (Kv v) := algebraRat.charZero _
    obtain ⟨jv, hjv⟩ := (embAlg (Kv v) _ _ ((map_ne_zero _).2 hD.ne0) (cv_reg hr v) _ (htr v)).1
    have h' : (D.S v).fK (t v) ((y.out.1 v)⁻¹ * (ι (j z)).1 v * y.out.1 v) ≠ 0 := h
    rw [ez v jv hjv] at h'
    obtain ⟨τ', h1, h2⟩ := (hD.sig v hv).K_supp _ (ht v hv) _ h'
    exact hI (tau_eq (cv_reg hr v) (htr v) hjv (hzv v) _ h2 ▸ h1)
