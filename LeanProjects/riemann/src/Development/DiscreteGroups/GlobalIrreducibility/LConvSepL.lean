import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepB

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

theorem exists_good_fix (hψ : Continuous ψ) (y z : WT (m := m) ψ) : ∃ K : Subgroup (GL (Fin m) k), Good ψ K ∧
    ∀ κ ∈ K, rhoW ψ κ y = y ∧ rhoW ψ κ z = z := by
  obtain ⟨K₁, h1o, -, h1⟩ := exists_fix y
  obtain ⟨K₂, h2o, -, h2⟩ := exists_fix z
  obtain ⟨K, hK, hsub⟩ := exists_good hψ (Filter.inter_mem (h1o.mem_nhds K₁.one_mem) (h2o.mem_nhds K₂.one_mem))
  exact ⟨K, hK, fun κ hκ => ⟨h1 κ (hsub hκ).1, h2 κ (hsub hκ).2⟩⟩

variable (ψ) in

def lamK (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ)
    (K : Subgroup (GL (Fin m) k)) (y : WT (m := m) ψ) : ℂ :=
  B y (delta ψ K) / cK ψ I K

theorem lamK_mono {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B)
    {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K) (hK' : Good ψ K') (hle : K' ≤ K) {y : WT (m := m) ψ}
    (hy : ∀ κ ∈ K, rhoW ψ κ y = y) : lamK ψ I B K' y = lamK ψ I B K y := by
  have h1 : ∀ κ ∈ K, ∀ x, B y (rhoW ψ κ x) = B y x := fun κ hκ x => by
    calc B y (rhoW ψ κ x) = B (rhoW ψ κ y) (rhoW ψ κ x) := by rw [hy κ hκ]
      _ = B y x := hB.2.2 κ y x
  have h2 : ∀ κ ∈ K, ∀ x, formI ψ I (delta ψ K) (rhoW ψ κ x) = formI ψ I (delta ψ K) x := fun κ hκ x => by
    calc formI ψ I (delta ψ K) (rhoW ψ κ x) = formI ψ I (rhoW ψ κ (delta ψ K)) (rhoW ψ κ x) := by
          rw [rhoW_delta hκ]
      _ = _ := (isInvForm_formI hI).2.2 κ _ x
  have h := delta_avg hK hK' hle (B y) (formI ψ I (delta ψ K)) h1 h2
  rw [formI_delta_le I hK hK' hle] at h
  rw [lamK, lamK, div_eq_div_iff (cK_ne_zero hI hK') (cK_ne_zero hI hK)]
  exact h

theorem lamK_eq (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B)
    {K₁ K₂ : Subgroup (GL (Fin m) k)} (h1 : Good ψ K₁) (h2 : Good ψ K₂) {y : WT (m := m) ψ}
    (hy1 : ∀ κ ∈ K₁, rhoW ψ κ y = y) (hy2 : ∀ κ ∈ K₂, rhoW ψ κ y = y) :
    lamK ψ I B K₁ y = lamK ψ I B K₂ y := by
  obtain ⟨K, hK, hsub⟩ := exists_good hψ (Filter.inter_mem (h1.1.mem_nhds K₁.one_mem) (h2.1.mem_nhds K₂.one_mem))
  rw [← lamK_mono hI hB h1 hK (fun x hx => (hsub hx).1) hy1, lamK_mono hI hB h2 hK (fun x hx => (hsub hx).2) hy2]

variable (ψ) in

def lam (hψ : Continuous ψ) (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ)
    (B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ) (y : WT (m := m) ψ) : ℂ :=
  lamK ψ I B (Classical.choose (exists_good_fix hψ y y)) y

theorem lam_eq (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B)
    {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {y : WT (m := m) ψ} (hy : ∀ κ ∈ K, rhoW ψ κ y = y) :
    lam ψ hψ I B y = lamK ψ I B K y := by
  have h := Classical.choose_spec (exists_good_fix hψ y y)
  exact lamK_eq hψ hI hB h.1 hK (fun κ hκ => (h.2 κ hκ).1) hy

theorem lam_add (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B) (y z : WT (m := m) ψ) :
    lam ψ hψ I B (y + z) = lam ψ hψ I B y + lam ψ hψ I B z := by
  obtain ⟨K, hK, hKf⟩ := exists_good_fix hψ y z
  rw [lam_eq hψ hI hB hK (fun κ hκ => by rw [map_add, (hKf κ hκ).1, (hKf κ hκ).2]),
    lam_eq hψ hI hB hK (fun κ hκ => (hKf κ hκ).1), lam_eq hψ hI hB hK (fun κ hκ => (hKf κ hκ).2)]
  simp only [lamK, map_add, LinearMap.add_apply, add_div]

theorem lam_smul (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I)
    {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ} (hB : IsInvForm (rhoW ψ) B) (a : ℂ) (y : WT (m := m) ψ) :
    lam ψ hψ I B (a • y) = (starRingEnd ℂ) a * lam ψ hψ I B y := by
  obtain ⟨K, hK, hKf⟩ := exists_good_fix hψ y y
  rw [lam_eq hψ hI hB hK (fun κ hκ => by rw [map_smul, (hKf κ hκ).1]),
    lam_eq hψ hI hB hK (fun κ hκ => (hKf κ hκ).1)]
  simp only [lamK, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

end DiscreteGroups.sglob.LConv

end
