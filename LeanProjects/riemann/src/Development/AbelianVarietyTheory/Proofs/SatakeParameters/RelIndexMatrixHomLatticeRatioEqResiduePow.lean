import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgePlane
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.ThirdMomentLaw

noncomputable section

namespace GlobalTheory.HomLatIndex

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]

theorem exists_pow_mul_mem (p : ℕ) (hp : Irreducible (p : W)) (x : Qq) :
    ∃ m : ℕ, ∀ m' ≥ m, (p : Qq) ^ m' * x ∈ (algebraMap W Qq).range := by
  by_cases hx : x = 0
  · exact ⟨0, fun m' _ => ⟨0, by simp [hx]⟩⟩
  obtain ⟨n, u, rfl⟩ := exists_eq_unit_mul_zpow₂ (Qq := Qq) hp hx
  refine ⟨(-n).toNat, fun m' hm' => ?_⟩
  have hnn : 0 ≤ n + m' := by omega
  refine ⟨(u : W) * (p : W) ^ (n + m').toNat, ?_⟩
  rw [map_mul, map_pow, map_natCast, ← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_add₀ (pQ_ne hp), zpow_natCast]
  ring

theorem exists_pow_smul_integral (p : ℕ) (hp : Irreducible (p : W)) {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ Qq) : ∃ m : ℕ, ∀ m' ≥ m, ∀ i j, (p : Qq) ^ m' * M i j ∈ (algebraMap W Qq).range := by
  choose f hf using fun ij : ι × κ => exists_pow_mul_mem p hp (M ij.1 ij.2)
  exact ⟨Finset.univ.sup f, fun m' hm' i j =>
    hf (i, j) m' (le_trans (Finset.le_sup (Finset.mem_univ (i, j))) hm')⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] in

theorem mul_integral {ι κ μ : Type} [Fintype κ] {A : Matrix ι κ Qq} {B : Matrix κ μ Qq}
    (hA : ∀ i j, A i j ∈ (algebraMap W Qq).range) (hB : ∀ i j, B i j ∈ (algebraMap W Qq).range) :
    ∀ i j, (A * B) i j ∈ (algebraMap W Qq).range := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsFractionRing W Qq] in

theorem mem_movLat_iff {N N' : ℕ} (k : GL (Fin N) Qq) (k' : GL (Fin N') Qq) (y : Matrix (Fin N') (Fin N) Qq) :
    y ∈ UnitaryThetaMoves.movLat W Qq k k' ↔
      ∀ i j, (((k'⁻¹ : GL (Fin N') Qq) : Matrix (Fin N') (Fin N') Qq) * y * (k : Matrix (Fin N) (Fin N) Qq)) i j ∈
        (algebraMap W Qq).range := by
  constructor
  · rintro ⟨X, hX, rfl⟩
    have e : ((k'⁻¹ : GL (Fin N') Qq) : Matrix (Fin N') (Fin N') Qq) * UnitaryThetaMoves.movHom Qq k k' X *
        (k : Matrix (Fin N) (Fin N) Qq) = X := by
      simp only [UnitaryThetaMoves.movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_assoc]
      rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [e]
    exact hX
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [UnitaryThetaMoves.movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mul_assoc]
    rw [Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem homLat_eq_movLat {k k' : ℕ} (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq)
    (ha : IsUnit a.det) (hb : IsUnit b.det) :
    (homLat W (colSpan W a) (colSpan W b)).toAddSubgroup =
      UnitaryThetaMoves.movLat W Qq (Matrix.nonsingInvUnit a ha) (Matrix.nonsingInvUnit b hb) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, mem_homLat, mem_movLat_iff]
  change (∀ z ∈ colSpan W a, x *ᵥ z ∈ colSpan W b) ↔ ∀ i j, (b⁻¹ * x * a) i j ∈ (algebraMap W Qq).range
  constructor
  · intro hx i c
    obtain ⟨y, hy⟩ := (Formalism.MainNotions.Pf14.mem_colSpan b _).1 (hx _ (Submodule.subset_span ⟨c, rfl⟩))
    refine ⟨y i, ?_⟩
    have h1 : (b⁻¹ * x * a) *ᵥ Pi.single c 1 = b⁻¹ *ᵥ (x *ᵥ fun i => a i c) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
      rfl
    rw [hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec, Matrix.mulVec_single_one] at h1
    exact (congrFun h1 i).symm
  · intro h z hz
    obtain ⟨v, rfl⟩ := (Formalism.MainNotions.Pf14.mem_colSpan a z).1 hz
    choose X₀ hX₀ using h
    refine (Formalism.MainNotions.Pf14.mem_colSpan b _).2 ⟨(Matrix.of X₀) *ᵥ v, ?_⟩
    have hM : (Matrix.of X₀).map (algebraMap W Qq) = b⁻¹ * x * a := by
      ext i j
      exact hX₀ i j
    have e : (fun c => algebraMap W Qq (((Matrix.of X₀) *ᵥ v) c)) =
        (b⁻¹ * x * a) *ᵥ (fun c => algebraMap W Qq (v c)) := by
      funext c
      rw [RingHom.map_mulVec, hM]
      rfl
    rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hb, Matrix.one_mul]

theorem det_inv_mul_eq (p : ℕ) (hp : Irreducible (p : W)) {N : ℕ} (k₁ k₂ : GL (Fin N) Qq) :
    ∃ w : Wˣ, ((k₁⁻¹ * k₂ : GL (Fin N) Qq) : Matrix (Fin N) (Fin N) Qq).det =
      algebraMap W Qq (p : W) ^ (ordP W p (k₂ : Matrix (Fin N) (Fin N) Qq).det -
        ordP W p (k₁ : Matrix (Fin N) (Fin N) Qq).det) * algebraMap W Qq (w : W) := by
  have hne : ∀ k : GL (Fin N) Qq, (k : Matrix (Fin N) (Fin N) Qq).det ≠ 0 := fun k =>
    ((Matrix.isUnit_iff_isUnit_det _).1 k.isUnit).ne_zero
  obtain ⟨n₁, u₁, h₁⟩ := exists_eq_unit_mul_zpow₂ (Qq := Qq) hp (hne k₁)
  obtain ⟨n₂, u₂, h₂⟩ := exists_eq_unit_mul_zpow₂ (Qq := Qq) hp (hne k₂)
  have hdi : ((k₁⁻¹ : GL (Fin N) Qq) : Matrix (Fin N) (Fin N) Qq).det =
      ((k₁ : Matrix (Fin N) (Fin N) Qq).det)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  refine ⟨u₁⁻¹ * u₂, ?_⟩
  rw [Units.val_mul, Matrix.det_mul, hdi, h₁, h₂, ordP_eq hp, ordP_eq hp, map_natCast, zpow_sub₀ (pQ_ne hp),
    Units.val_mul, map_mul, map_units_inv]
  ring

theorem relIndex_movLat (p n' : ℕ) (hp : Irreducible (p : W))
    (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') {N N' : ℕ} (k₁ k₂ : GL (Fin N) Qq)
    (k₁' k₂' : GL (Fin N') Qq) (hle : UnitaryThetaMoves.movLat W Qq k₁ k₁' ≤ UnitaryThetaMoves.movLat W Qq k₂ k₂') :
    (((UnitaryThetaMoves.movLat W Qq k₁ k₁').relIndex (UnitaryThetaMoves.movLat W Qq k₂ k₂') : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) *
      ((N' : ℤ) * (ordP W p (k₂ : Matrix (Fin N) (Fin N) Qq).det - ordP W p (k₁ : Matrix (Fin N) (Fin N) Qq).det) -
        (N : ℤ) * (ordP W p (k₂' : Matrix (Fin N') (Fin N') Qq).det -
          ordP W p (k₁' : Matrix (Fin N') (Fin N') Qq).det))) := by
  set f := UnitaryThetaMoves.movHom Qq k₁⁻¹ k₁'⁻¹ with hf_def
  have hf : Function.Injective f := UnitaryThetaMoves.movHom_inv_injective k₁ k₁'
  have h1 : (UnitaryThetaMoves.movLat W Qq k₁ k₁').map f = UnitaryThetaMoves.matLat W Qq N N' := by
    rw [UnitaryThetaMoves.movLat, AddSubgroup.map_map]
    conv_rhs => rw [← AddSubgroup.map_id (UnitaryThetaMoves.matLat W Qq N N')]
    congr 1
    exact AddMonoidHom.ext fun x => UnitaryThetaMoves.movHom_inv_apply k₁ k₁' x
  have h2 : (UnitaryThetaMoves.movLat W Qq k₂ k₂').map f = UnitaryThetaMoves.movLat W Qq (k₁⁻¹ * k₂) (k₁'⁻¹ * k₂') := by
    rw [UnitaryThetaMoves.movLat, UnitaryThetaMoves.movLat, AddSubgroup.map_map]
    congr 1
    ext x : 1
    simp [hf_def, UnitaryThetaMoves.movHom, Matrix.mul_assoc, _root_.mul_inv_rev]
  have hle' : UnitaryThetaMoves.matLat W Qq N N' ≤ UnitaryThetaMoves.movLat W Qq (k₁⁻¹ * k₂) (k₁'⁻¹ * k₂') := by
    rw [← h1, ← h2]
    exact AddSubgroup.map_mono hle
  have hQ : Nat.card (IsLocalRing.ResidueField W) = p ^ n' := by
    show Nat.card (W ⧸ IsLocalRing.maximalIdeal W) = _
    rw [hp.maximalIdeal_eq]
    exact hcard
  obtain ⟨w, hw⟩ := det_inv_mul_eq p hp k₁ k₂
  obtain ⟨w', hw'⟩ := det_inv_mul_eq p hp k₁' k₂'
  obtain ⟨hnn, hidx⟩ := UnitaryThetaMoves.relIndexFormula W Qq (p : W) hp (p ^ n') hQ N N' (k₁⁻¹ * k₂) (k₁'⁻¹ * k₂') _ _ w w' hw hw'
    hle'
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf, h1, h2, hidx]
  set E : ℤ := (N' : ℤ) * (ordP W p (k₂ : Matrix (Fin N) (Fin N) Qq).det -
      ordP W p (k₁ : Matrix (Fin N) (Fin N) Qq).det) - (N : ℤ) * (ordP W p (k₂' : Matrix (Fin N') (Fin N') Qq).det -
          ordP W p (k₁' : Matrix (Fin N') (Fin N') Qq).det) with hE
  rw [Nat.cast_pow, Nat.cast_pow, ← pow_mul, ← zpow_natCast, Nat.cast_mul, Int.toNat_of_nonneg hnn]

theorem movLat_le {N N' : ℕ} (k₁ k₂ : GL (Fin N) Qq) (k₁' k₂' : GL (Fin N') Qq) (P : Matrix (Fin N') (Fin N') Qq)
    (R : Matrix (Fin N) (Fin N) Qq) (hP : ∀ i j, P i j ∈ (algebraMap W Qq).range)
    (hR : ∀ i j, R i j ∈ (algebraMap W Qq).range) (h' : (k₁' : Matrix (Fin N') (Fin N') Qq) = k₂' * P)
    (h : (k₂ : Matrix (Fin N) (Fin N) Qq) = k₁ * R) : UnitaryThetaMoves.movLat W Qq k₁ k₁' ≤ UnitaryThetaMoves.movLat W Qq k₂ k₂' := by
  rintro _ ⟨X, hX, rfl⟩
  rw [mem_movLat_iff]
  have e : ((k₂'⁻¹ : GL (Fin N') Qq) : Matrix (Fin N') (Fin N') Qq) * UnitaryThetaMoves.movHom Qq k₁ k₁' X *
      (k₂ : Matrix (Fin N) (Fin N) Qq) = P * X * R := by
    simp only [UnitaryThetaMoves.movHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [h', h]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((k₂'⁻¹ : GL (Fin N') Qq) : Matrix (Fin N') (Fin N') Qq)), Units.inv_mul, Matrix.one_mul,
      ← Matrix.mul_assoc (((k₁⁻¹ : GL (Fin N) Qq) : Matrix (Fin N) (Fin N) Qq)), Units.inv_mul, Matrix.one_mul]
  rw [e]
  exact mul_integral (mul_integral hP hX) hR

theorem relIndex_homLat_ratio : ∀ {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p n' : ℕ) (hp : Irreducible (p : W)) (hcard : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') {k k' : ℕ} (a₀ a₁ : Matrix (Fin k) (Fin k) Qq) (b₀ b₁ : Matrix (Fin k') (Fin k') Qq) (ha₀ : IsUnit a₀.det) (ha₁ : IsUnit a₁.det) (hb₀ : IsUnit b₀.det) (hb₁ : IsUnit b₁.det), (((homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup.relIndex (homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup : ℕ) : ℝ) / (((homLat W (colSpan W a₁) (colSpan W b₁)).toAddSubgroup.relIndex (homLat W (colSpan W a₀) (colSpan W b₀)).toAddSubgroup : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k : ℤ) * (ordP W p b₀.det - ordP W p b₁.det) - (k' : ℤ) * (ordP W p a₀.det - ordP W p a₁.det))) := by
  intro W Qq _ _ _ _ _ _ p n' hp hcard k k' a₀ a₁ b₀ b₁ ha₀ ha₁ hb₀ hb₁
  have hpQ : (p : Qq) ≠ 0 := pQ_ne hp
  have hp0 : (p : ℝ) ≠ 0 := by
    rintro h
    apply hp.ne_zero
    rw [Nat.cast_eq_zero.1 h, Nat.cast_zero]
  obtain ⟨m₁, hm₁⟩ := exists_pow_smul_integral p hp (b₀⁻¹ * b₁)
  obtain ⟨m₂, hm₂⟩ := exists_pow_smul_integral p hp (a₁⁻¹ * a₀)
  set c : Qq := (p : Qq) ^ (m₁ + m₂) with hc_def
  have hc : c ≠ 0 := pow_ne_zero _ hpQ
  have hcW : c ∈ (algebraMap W Qq).range := ⟨(p : W) ^ (m₁ + m₂), by rw [map_pow, map_natCast]⟩
  have hP₀ : ∀ i j, (c • (b₀⁻¹ * b₁)) i j ∈ (algebraMap W Qq).range := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hm₁ _ (Nat.le_add_right _ _) i j
  have hR₀ : ∀ i j, (c • (a₁⁻¹ * a₀)) i j ∈ (algebraMap W Qq).range := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hm₂ _ (Nat.le_add_left _ _) i j
  have hone : ∀ {n : ℕ} (i j : Fin n), (c • (1 : Matrix (Fin n) (Fin n) Qq)) i j ∈ (algebraMap W Qq).range := by
    intro n i j
    rw [Matrix.smul_apply, smul_eq_mul]
    refine Subring.mul_mem _ hcW ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have hA' : IsUnit (c⁻¹ • a₁).det := by
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 (inv_ne_zero hc))).mul ha₁
  have hB' : IsUnit (c • b₁).det := by
    rw [Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 hc)).mul hb₁
  rw [homLat_eq_movLat a₀ b₀ ha₀ hb₀, homLat_eq_movLat a₁ b₁ ha₁ hb₁]
  set T₀ := UnitaryThetaMoves.movLat W Qq (Matrix.nonsingInvUnit a₀ ha₀) (Matrix.nonsingInvUnit b₀ hb₀) with hT₀
  set T₁ := UnitaryThetaMoves.movLat W Qq (Matrix.nonsingInvUnit a₁ ha₁) (Matrix.nonsingInvUnit b₁ hb₁) with hT₁
  set S := UnitaryThetaMoves.movLat W Qq (Matrix.nonsingInvUnit _ hA') (Matrix.nonsingInvUnit _ hB') with hS
  have hS₀ : S ≤ T₀ := movLat_le _ _ _ _ _ _ hP₀ hR₀
    (show c • b₁ = b₀ * (c • (b₀⁻¹ * b₁)) by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hb₀, Matrix.one_mul])
    (show a₀ = (c⁻¹ • a₁) * (c • (a₁⁻¹ * a₀)) by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ ha₁, Matrix.one_mul])
  have hS₁ : S ≤ T₁ := movLat_le _ _ _ _ _ _ hone hone
    (show c • b₁ = b₁ * (c • (1 : Matrix (Fin k') (Fin k') Qq)) by rw [Matrix.mul_smul, Matrix.mul_one])
    (show a₁ = (c⁻¹ • a₁) * (c • (1 : Matrix (Fin k) (Fin k) Qq)) by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.mul_one])
  have i₀ : ((S.relIndex T₀ : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k' : ℤ) * (ordP W p a₀.det -
      ordP W p (c⁻¹ • a₁).det) - (k : ℤ) * (ordP W p b₀.det - ordP W p (c • b₁).det))) :=
    relIndex_movLat p n' hp hcard _ _ _ _ hS₀
  have i₁ : ((S.relIndex T₁ : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k' : ℤ) * (ordP W p a₁.det -
      ordP W p (c⁻¹ • a₁).det) - (k : ℤ) * (ordP W p b₁.det - ordP W p (c • b₁).det))) :=
    relIndex_movLat p n' hp hcard _ _ _ _ hS₁
  have m₀ := AddSubgroup.relIndex_mul_relIndex S (T₀ ⊓ T₁) T₀ (le_inf hS₀ hS₁) inf_le_left
  have m₁ := AddSubgroup.relIndex_mul_relIndex S (T₀ ⊓ T₁) T₁ (le_inf hS₀ hS₁) inf_le_right
  rw [← AddSubgroup.inf_relIndex_right T₀ T₁, ← AddSubgroup.inf_relIndex_left T₀ T₁]
  have m₀' : ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) * (((T₀ ⊓ T₁).relIndex T₀ : ℕ) : ℝ) = ((S.relIndex T₀ : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, m₀]
  have m₁' : ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) * (((T₀ ⊓ T₁).relIndex T₁ : ℕ) : ℝ) = ((S.relIndex T₁ : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, m₁]
  rw [i₀] at m₀'
  rw [i₁] at m₁'
  have hs0 : ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at m₀'
    exact zpow_ne_zero _ hp0 m₀'.symm
  have hx₀ : (((T₀ ⊓ T₁).relIndex T₀ : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k' : ℤ) * (ordP W p a₀.det -
      ordP W p (c⁻¹ • a₁).det) - (k : ℤ) * (ordP W p b₀.det - ordP W p (c • b₁).det))) /
        ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) := by
    rw [← m₀']; field_simp
  have hx₁ : (((T₀ ⊓ T₁).relIndex T₁ : ℕ) : ℝ) = (p : ℝ) ^ ((n' : ℤ) * ((k' : ℤ) * (ordP W p a₁.det -
      ordP W p (c⁻¹ • a₁).det) - (k : ℤ) * (ordP W p b₁.det - ordP W p (c • b₁).det))) /
        ((S.relIndex (T₀ ⊓ T₁) : ℕ) : ℝ) := by
    rw [← m₁']; field_simp
  rw [hx₀, hx₁, div_div_div_cancel_right₀ hs0, ← zpow_sub₀ hp0]
  congr 1
  ring

end GlobalTheory.HomLatIndex
