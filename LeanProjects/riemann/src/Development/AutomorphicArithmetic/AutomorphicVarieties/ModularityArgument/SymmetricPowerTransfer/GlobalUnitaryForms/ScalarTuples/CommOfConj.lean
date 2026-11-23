import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKGlob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKTest

open Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Glob.FK

private theorem relIndex_ne {Γ X : Type} [Group Γ] (C H : Subgroup Γ) (φ : Γ → X) (s : Set X) (hs : s.Finite)
    (hmem : ∀ γ ∈ H, φ γ ∈ s) (hinj : ∀ γ δ, φ γ = φ δ → γ⁻¹ * δ ∈ C) : C.relIndex H ≠ 0 := by
  classical
  haveI : Finite s := hs.to_subtype
  let F : s → H ⧸ C.subgroupOf H := fun x =>
    if h : ∃ a : H, φ a = (x : X) then QuotientGroup.mk h.choose else QuotientGroup.mk 1
  haveI : Finite (H ⧸ C.subgroupOf H) := by
    refine Finite.of_surjective F ?_
    intro q
    refine QuotientGroup.induction_on q fun a => ?_
    have hex : ∃ b : H, φ b = ((⟨φ a, hmem a a.2⟩ : s) : X) := ⟨a, rfl⟩
    refine ⟨⟨φ a, hmem a a.2⟩, ?_⟩
    simp only [F, dif_pos hex]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hinj _ _ hex.choose_spec
  exact Subgroup.index_ne_zero_of_finite

private theorem conj_abs {A M Γ G : Type} [Ring A] [Ring M] [Group Γ] [Group G] (j : A →+* M) (R : Subring M) (ι : Γ →* G) (σ : Γ →* A)
    (ρ : G →* M) (hι : ∀ γ, ρ (ι γ) = j (σ γ)) (U : Subgroup G) (hU : ∀ u ∈ U, ∀ r ∈ R, ρ u * r * ρ u⁻¹ ∈ R)
    (hden : ∀ g, ∃ n : ℕ, n ≠ 0 ∧ (n : M) * ρ g ∈ R) (g : G) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ b ∈ R.comap j, ∀ γ ∈ (U.map (MulAut.conj g).toMonoidHom).comap ι, N • (σ γ * b * σ γ⁻¹) ∈ R.comap j := by
  obtain ⟨n1, hn1, h1⟩ := hden g
  obtain ⟨n2, hn2, h2⟩ := hden g⁻¹
  refine ⟨n1 * n2 * (n1 * n2), mul_ne_zero (mul_ne_zero hn1 hn2) (mul_ne_zero hn1 hn2), ?_⟩
  intro b hb γ hγ
  rw [Subgroup.mem_comap, Subgroup.mem_map] at hγ
  obtain ⟨u, hu, hug⟩ := hγ
  have hιγ : ι γ = g * u * g⁻¹ := by
    rw [← hug]
    simp [MulAut.conj_apply]
  have hιγ' : ι γ⁻¹ = g * u⁻¹ * g⁻¹ := by
    rw [map_inv, hιγ]
    group
  rw [Subring.mem_comap] at hb ⊢
  rw [nsmul_eq_mul, map_mul, map_mul, map_mul, map_natCast, ← hι, ← hι, hιγ, hιγ', map_mul, map_mul, map_mul, map_mul]
  have key : ((n1 * n2 * (n1 * n2) : ℕ) : M) * (ρ g * ρ u * ρ g⁻¹ * j b * (ρ g * ρ u⁻¹ * ρ g⁻¹)) =
      ((n1 : M) * ρ g) * (ρ u * (((n2 : M) * ρ g⁻¹) * j b * ((n1 : M) * ρ g)) * ρ u⁻¹) * ((n2 : M) * ρ g⁻¹) := by
    simp only [← nsmul_eq_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    ring
  rw [key]
  exact R.mul_mem (R.mul_mem h1 (hU u hu _ (R.mul_mem (R.mul_mem h2 hb) h1))) h2

private theorem comm_of_conj {A Γ : Type} [Ring A] [Group Γ] (σ : Γ →* A) (b : A) (γ δ : Γ) (h : σ γ * b * σ γ⁻¹ = σ δ * b * σ δ⁻¹) :
    σ (γ⁻¹ * δ) * b = b * σ (γ⁻¹ * δ) := by
  have e1 : σ γ⁻¹ * σ γ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have e2 : σ δ⁻¹ * σ δ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul]
  calc σ γ⁻¹ * σ δ * b = σ γ⁻¹ * (σ δ * b * σ δ⁻¹) * σ δ := by simp only [mul_assoc, e2, mul_one]
    _ = σ γ⁻¹ * (σ γ * b * σ γ⁻¹) * σ δ := by rw [h]
    _ = b * (σ γ⁻¹ * σ δ) := by simp only [← mul_assoc, e1, one_mul]

private noncomputable def sg {K : Type} [Field K] (Δ : K) : DX Δ →* Matrix (Fin 2) (Fin 2) (Lsq K Δ) where
  toFun := mt
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem stab_F {F G : Type} [Field F] [CharZero F] [Group G] {Δ : F} (hΔ : Δ ≠ 0) {M : Type} [Ring M]
    (j : Matrix (Fin 2) (Fin 2) (Lsq F Δ) →+* M) (R : Subring M) (ι : DX Δ →* G)
    (ρ : G →* M) (hι : ∀ γ, ρ (ι γ) = j (sg Δ γ)) (U : Subgroup G) (hU : ∀ u ∈ U, ∀ r ∈ R, ρ u * r * ρ u⁻¹ ∈ R)
    (hden : ∀ g, ∃ n : ℕ, n ≠ 0 ∧ (n : M) * ρ g ∈ R) (hfin : ∀ d, {y | y ∈ R.comap j ∧ y.det = d}.Finite)
    {c : F} (hc : c ≠ 0) (h1 : qm ⟨0, c⟩ 0 ∈ R.comap j) (h2 : qm 0 1 ∈ R.comap j) (g : G) :
    (ZD Δ).relIndex ((U.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0 := by
  classical
  obtain ⟨N, hN, hNmem⟩ := conj_abs j R ι (sg Δ) ρ hι U hU hden g
  have hcan : ∀ x y : Matrix (Fin 2) (Fin 2) (Lsq F Δ), N • x = N • y → x = y := by
    intro x y h
    have h' : (N : F) • x = (N : F) • y := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      exact h
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hN) h'
  have hdet : ∀ (γ : DX Δ) (b : Matrix (Fin 2) (Fin 2) (Lsq F Δ)),
      (N • (sg Δ γ * b * sg Δ γ⁻¹)).det = (N • b).det := by
    intro γ b
    have e : N • (sg Δ γ * b * sg Δ γ⁻¹) = sg Δ γ * (N • b) * sg Δ γ⁻¹ := by
      rw [mul_smul_comm, smul_mul_assoc]
    rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (sg Δ γ)), mul_assoc, ← Matrix.det_mul,
      ← map_mul, mul_inv_cancel, map_one, Matrix.det_one, mul_one]
  refine relIndex_ne (ZD Δ) ((U.map (MulAut.conj g).toMonoidHom).comap ι)
    (fun γ => (N • (sg Δ γ * qm ⟨0, c⟩ 0 * sg Δ γ⁻¹), N • (sg Δ γ * qm 0 1 * sg Δ γ⁻¹)))
    ({y | y ∈ R.comap j ∧ y.det = (N • qm (⟨0, c⟩ : Lsq F Δ) 0).det} ×ˢ
      {y | y ∈ R.comap j ∧ y.det = (N • qm (0 : Lsq F Δ) 1).det})
    ((hfin _).prod (hfin _)) ?_ ?_
  · intro γ hγ
    exact ⟨⟨hNmem _ h1 γ hγ, hdet γ _⟩, ⟨hNmem _ h2 γ hγ, hdet γ _⟩⟩
  · intro γ δ h
    obtain ⟨e1, e2⟩ := Prod.mk.inj h
    have c1 := comm_of_conj (sg Δ) _ γ δ (hcan _ _ e1)
    have c2 := comm_of_conj (sg Δ) _ γ δ (hcan _ _ e2)
    exact FK.mem_ZD hΔ hc (γ⁻¹ * δ) c1 c2

private theorem mem_box {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)
    (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := Subgroup.mem_iInf

private theorem finK_fin (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ) (hD : D.Ok) (ι : DX Δ →* DA Δ) (hι : IsIotaD ι) :
    (∃ S : Finset (DA Δ), ∀ g, ∃ γ, ∃ s ∈ S, ∃ u ∈ D.UZ, g = ι γ * s * u) ∧
    ∀ g, (ZD Δ).relIndex ((D.UZ.map (MulAut.conj g).toMonoidHom).comap ι) ≠ 0 := by
  classical
  haveI := hD.real
  have hΔ : Δ ≠ 0 := by
    intro h0
    obtain ⟨σ, -⟩ := FK.real_emb (Classical.arbitrary (F →+* ℂ))
    have h := hD.neg σ
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hιρ : ∀ γ, rho Δ (ι γ) = jj Δ (sg Δ γ) := by
    intro γ
    funext v
    rw [FK.jj_apply]
    exact hι γ v
  have hU : ∀ u ∈ D.UZ, ∀ r ∈ RR Δ, rho Δ u * r * rho Δ u⁻¹ ∈ RR Δ := by
    intro u hu r hr
    rw [FK.mem_RR] at hr ⊢
    intro v
    have huv := (mem_box _ _ u).1 hu v
    have hle : ZD ((cv v) Δ) ⊔ D.J2v v ≤ ZD ((cv v) Δ) ⊔ KD ((cv v) Δ) (Ov v) := by
      refine sup_le_sup_left ?_ _
      unfold Dat.J2v
      split_ifs with hv
      · exact (hD.sig v hv).levelTwoLeIntegral
      · exact le_rfl
    exact FK.conj_mem (Ov v) (hle huv) (hr v)
  have hfin := FK.det_fin hD.neg hΔ
  obtain ⟨c, hc0, hcint⟩ := FK.den_glob Δ
  have hq1 : qm (⟨0, (c : F)⟩ : Lsq F Δ) 0 ∈ (RR Δ).comap (jj Δ) := by
    rw [Subring.mem_comap, FK.mem_RR]
    intro v
    rw [FK.jj_apply, FK.qm_map]
    have e : (lmap (cv v) Δ) (⟨0, (c : F)⟩ : Lsq F Δ) = ⟨0, (c : Kv v)⟩ := by
      simp [lmap]
    rw [e, map_zero]
    exact FK.qm_mem (Ov v) (FK.int_om (Ov v) (FK.int_cD hcint v)) isIntegral_zero
  have hq2 : qm (0 : Lsq F Δ) 1 ∈ (RR Δ).comap (jj Δ) := by
    rw [Subring.mem_comap, FK.mem_RR]
    intro v
    rw [FK.jj_apply, FK.qm_map, map_zero, map_one]
    exact FK.qm_mem (Ov v) isIntegral_zero isIntegral_one
  refine ⟨?_, fun g => stab_F hΔ (jj Δ) (RR Δ) ι (rho Δ) hιρ D.UZ hU FK.den_rho hfin
    (Nat.cast_ne_zero.2 hc0) hq1 hq2 g⟩
  haveI := FK.lam_fg hΔ
  haveI : CharZero (Matrix (Fin 2) (Fin 2) (Lsq F Δ)) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  have hbig := cls_abs (jj Δ) (RR Δ) ι (sg Δ) (rho Δ) hιρ
    ((rpg (fun v => DX ((cv v) Δ)) fun v => KD ((cv v) Δ) (Ov v)).box fun v => KD ((cv v) Δ) (Ov v))
    (by
      intro g h1 h2
      rw [mem_box]
      intro v
      rw [FK.mem_KD]
      rw [FK.mem_RR] at h1 h2
      exact ⟨h1 v, h2 v⟩)
    (by
      intro y hy hy0
      obtain ⟨γ, hγ⟩ := FK.unit_of_shape hD.neg (FK.lam_shape hy) hy0
      exact ⟨γ, hγ⟩)
    (FK.approx_R hΔ) FK.den_rho
  refine cls_of_relIndex ι _ D.UZ ?_ hbig
  refine box_relIndex _ _ _ D.Sg (fun v hv => ?_) (fun v hv => ?_)
  · unfold Dat.J2v
    rw [if_pos hv]
    exact ne_zero_of_dvd_ne_zero (hD.sig v hv).levelTwoFiniteIndex (Subgroup.relIndex_dvd_of_le_left _ le_sup_right)
  · unfold Dat.J2v
    rw [if_neg hv]
    exact le_sup_right

theorem UpperTheory.V.Z.Sym.Glob.finK :
    UpperTheory.V.Z.Sym.Glob.FinK := by
  intro F _ _ Δ D hD V _ _ ch B hB
  refine ⟨?_, finK_test F Δ D hD V ch B hB⟩
  obtain ⟨hcls, hstab⟩ := finK_fin F Δ D hD B.ι hB.ι
  refine ⟨?_, ?_⟩
  · rw [hB.U]
    exact hcls
  · intro g
    rw [hB.U, hB.Γ₀]
    exact hstab g
