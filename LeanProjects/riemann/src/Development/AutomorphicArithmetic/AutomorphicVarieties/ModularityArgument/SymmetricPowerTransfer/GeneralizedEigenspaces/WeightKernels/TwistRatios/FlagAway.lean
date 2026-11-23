import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tri

variable {k : Type} [Field k]

local notation "M2" => Matrix (Fin 2) (Fin 2) k

private theorem tri_diag_ne (M : GL (Fin 2) k) (h : (M : M2) 1 0 = 0) (j : Fin 2) :
    (M : M2) j j ≠ 0 := by
  have hd : (M : M2).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hd
  fin_cases j
  · exact left_ne_zero_of_mul hd
  · exact right_ne_zero_of_mul hd

private theorem tri_chars {W : Type} [Group W] (ρ : W →* GL (Fin 2) k)
    (hT : ∀ s, (ρ s : M2) 1 0 = 0) :
    ∃ η : Fin 2 → W →* kˣ, ∀ i s, (η i s : k) = (ρ s : M2) i i := by
  refine ⟨fun i =>
    { toFun := fun s => Units.mk0 _ (tri_diag_ne (ρ s) (hT s) i)
      map_one' := ?_
      map_mul' := ?_ }, fun i s => rfl⟩
  · ext; simp
  · intro s t
    ext
    simp only [map_mul, Units.val_mul, Units.val_mk0, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> simp [hT]

private theorem tri_charpoly (P M : GL (Fin 2) k)
    (h : ((P * M * P⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0) :
    (M : M2).charpoly = ∏ i, (X - C (((P * M * P⁻¹ : GL (Fin 2) k) : M2) i i)) := by
  have hc : ((P * M * P⁻¹ : GL (Fin 2) k) : M2).charpoly = (M : M2).charpoly := by
    simpa using Matrix.charpoly_units_conj P (M : M2)
  rw [← hc, Matrix.charpoly_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two, h,
    Fin.prod_univ_two]
  simp only [mul_zero, sub_zero, C_add, C_mul]
  ring

private theorem tri_exists [IsAlgClosed k] (M : GL (Fin 2) k) :
    ∃ Q : GL (Fin 2) k, ((Q * M * Q⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0 := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (M : M2))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hMv : (M : M2).mulVec v = μ • v := by
    simpa [Matrix.toLin'_apply] using hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  obtain ⟨R, hR⟩ : ∃ R : GL (Fin 2) k, ∀ i, (R : M2) i 0 = v i := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv0 (by ext i; fin_cases i <;> simp [h0, h1])
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 1; v 1, 0]
        (by simp [Matrix.det_fin_two, h1]), ?_⟩
      intro i
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1]
        (by simp [Matrix.det_fin_two, h0]), ?_⟩
      intro i
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  refine ⟨R⁻¹, ?_⟩
  have hRT : (R : M2) * ((R⁻¹ * M * R⁻¹⁻¹ : GL (Fin 2) k) : M2) = (M : M2) * (R : M2) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  set T : M2 := ((R⁻¹ * M * R⁻¹⁻¹ : GL (Fin 2) k) : M2) with hTdef
  have hcol : (R : M2).mulVec ![T 0 0 - μ, T 1 0] = 0 := by
    ext i
    have h1 : ((R : M2) * T) i 0 = ((M : M2) * (R : M2)) i 0 := by rw [hRT]
    have h2 : ((M : M2) * (R : M2)) i 0 = μ * v i := by
      have := congrFun hMv i
      simp only [Matrix.mul_apply, hR, Pi.smul_apply, smul_eq_mul] at this ⊢
      simpa [Matrix.mulVec, dotProduct] using this
    rw [h2, Matrix.mul_apply, Fin.sum_univ_two, hR] at h1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hR, Pi.zero_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination h1
  have hdet : (R : M2).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 R.isUnit).ne_zero
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet hcol
  simpa using congrFun this 1

private def triSub : Subgroup (GL (Fin 2) k) where
  carrier := {M | (M : M2) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ha]

private theorem tri_core [IsAlgClosed k] {W : Type} [Group W] (ρ : W →* GL (Fin 2) k)
    (τ : Fin 2 → W →* kˣ) (I : Subgroup W) (hI : I.Normal) (φ : W)
    (hgen : ∀ s, ∃ n : ℤ, ∃ i ∈ I, s = φ ^ n * i) (g : GL (Fin 2) k)
    (hg : ∀ s ∈ I, ((g * ρ s * g⁻¹ : GL (Fin 2) k) : M2) = Matrix.diagonal fun i => (τ i s : k)) :
    ∃ P : GL (Fin 2) k, (∀ s, ((P * ρ s * P⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0) ∧
      ∀ s ∈ I, ∀ j, ((P * ρ s * P⁻¹ : GL (Fin 2) k) : M2) j j = (τ j s : k) := by
  by_cases hsep : ∃ i ∈ I, (τ 0 i : k) ≠ (τ 1 i : k)
  · obtain ⟨i, hi, hne⟩ := hsep
    refine ⟨g, fun s => ?_, fun s hs j => by rw [hg s hs]; simp⟩
    have hc := hg (s * i * s⁻¹) (hI.conj_mem i hi s)
    have hτ : ∀ j, (τ j (s * i * s⁻¹) : k) = (τ j i : k) := by
      intro j
      simp [mul_comm]
    have hcomm : (g * ρ s * g⁻¹) * (g * ρ i * g⁻¹) = (g * ρ (s * i * s⁻¹) * g⁻¹) * (g * ρ s * g⁻¹) := by
      simp only [map_mul, map_inv]
      group
    have hm := congrArg (fun x : GL (Fin 2) k => (x : M2) 1 0) hcomm
    simp only [Units.val_mul (g * ρ s * g⁻¹)] at hm
    rw [Units.val_mul (g * ρ (s * i * s⁻¹) * g⁻¹), hg i hi, hc] at hm
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hτ] at hm
    have : (((g * ρ s * g⁻¹ : GL (Fin 2) k) : M2) 1 0) * ((τ 0 i : k) - (τ 1 i : k)) = 0 := by
      linear_combination hm
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  · push_neg at hsep
    obtain ⟨Q, hQ⟩ := tri_exists (g * ρ φ * g⁻¹)
    have hsc : ∀ s ∈ I, ((Q * g) * ρ s * (Q * g)⁻¹ : GL (Fin 2) k) =
        g * ρ s * g⁻¹ := by
      intro s hs
      have hz : ((g * ρ s * g⁻¹ : GL (Fin 2) k) : M2) = (τ 0 s : k) • (1 : M2) := by
        rw [hg s hs]
        ext a b
        fin_cases a <;> fin_cases b <;> simp [hsep s hs]
      have hcm : Q * (g * ρ s * g⁻¹) = (g * ρ s * g⁻¹) * Q := by
        apply Units.ext
        rw [Units.val_mul Q (g * ρ s * g⁻¹), Units.val_mul (g * ρ s * g⁻¹) Q, hz]
        simp
      calc ((Q * g) * ρ s * (Q * g)⁻¹ : GL (Fin 2) k)
          = Q * (g * ρ s * g⁻¹) * Q⁻¹ := by group
        _ = g * ρ s * g⁻¹ := by rw [hcm]; group
    refine ⟨Q * g, fun s => ?_, fun s hs j => ?_⟩
    · obtain ⟨n, i, hi, rfl⟩ := hgen s
      have hφ : (Q * g) * ρ φ * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k)) := by
        change (((Q * g) * ρ φ * (Q * g)⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0
        have : ((Q * g) * ρ φ * (Q * g)⁻¹ : GL (Fin 2) k) = Q * (g * ρ φ * g⁻¹) * Q⁻¹ := by group
        rw [this]; exact hQ
      have hi' : (Q * g) * ρ i * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k)) := by
        change (((Q * g) * ρ i * (Q * g)⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0
        rw [hsc i hi, hg i hi]
        simp
      have hall : (Q * g) * ρ (φ ^ n * i) * (Q * g)⁻¹ =
          ((Q * g) * ρ φ * (Q * g)⁻¹) ^ n * ((Q * g) * ρ i * (Q * g)⁻¹) := by
        rw [map_mul, map_zpow]
        have := (MulAut.conj (Q * g)).toMonoidHom.map_zpow (ρ φ) n
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
        rw [← this]
        group
      have : (Q * g) * ρ (φ ^ n * i) * (Q * g)⁻¹ ∈ (triSub : Subgroup (GL (Fin 2) k)) := by
        rw [hall]; exact mul_mem (zpow_mem hφ n) hi'
      exact this
    · rw [hsc s hs, hg s hs]
      simp

end Tri

theorem UpperTheory.V.Z.Sym.Ga.flagAway :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → ∀ τ : Fin 2 → G L Ω →* (Qbar l)ˣ, ∀ (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w), IsDiagOn r (Ine (F := L) A) τ → ∃ η : Fin 2 → Weil h →* (Qbar l)ˣ, (∀ i (s : Ine (F := L) A), η i (ineIncl h s) = τ i s) ∧ ∀ s : Weil h, (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = ∏ i, (X - C (η i s : Qbar l)) := by
  intro L Ω _ _ _ _ _ l _ r _ τ w A h hD
  obtain ⟨g, hg⟩ := hD
  have hdegc : ∀ (s : Weil h) (i : Ine (F := L) A), deg (s * ineIncl h i * s⁻¹) = 0 := by
    intro s i
    rw [deg_mul, deg_mul, deg_ineIncl, deg_inv]
    ring
  have hN : (ineIncl h).range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨i, rfl⟩ s
    refine ⟨inePart (deg_frob (h := h)) (s * ineIncl h i * s⁻¹), ?_⟩
    rw [ineIncl_inePart, hdegc]
    simp
  have hgen : ∀ s : Weil h, ∃ n : ℤ, ∃ i ∈ (ineIncl h).range, s = frob h ^ n * i := by
    intro s
    refine ⟨deg s, _, ⟨inePart (deg_frob (h := h)) s, rfl⟩, ?_⟩
    rw [ineIncl_inePart, mul_inv_cancel_left]
  obtain ⟨P, hP1, hP2⟩ := tri_core (r.comp (Weil h).subtype)
    (fun i => (τ i).comp (Weil h).subtype) (ineIncl h).range hN (frob h) hgen g (by
      rintro _ ⟨i, rfl⟩
      exact hg i i.2)
  obtain ⟨η, hη⟩ := tri_chars ((MulAut.conj P).toMonoidHom.comp (r.comp (Weil h).subtype)) hP1
  refine ⟨η, fun i s => ?_, fun s => ?_⟩
  · apply Units.ext
    rw [hη]
    exact hP2 _ ⟨s, rfl⟩ i
  · have := tri_charpoly P (r s) (hP1 s)
    rw [this]
    simp only [hη]
    rfl
