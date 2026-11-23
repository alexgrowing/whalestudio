import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvSepL

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} (hψ : Continuous ψ) {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ}
  {B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ}

include hψ in
theorem lam_unip (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y : WT (m := m) ψ) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) :
    lam ψ hψ I B (rhoW ψ u y) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * lam ψ hψ I B y := by
  obtain ⟨K, hK, hKy⟩ := exists_good_fix hψ y y
  have hK' := good_conj hK hu
  have hfix' : ∀ κ ∈ K.map (MulAut.conj u).toMonoidHom, rhoW ψ κ (rhoW ψ u y) = rhoW ψ u y := by
    intro κ hκ
    have e : κ * u = u * (u⁻¹ * κ * u) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, (hKy _ (mem_conj.1 hκ)).1]
  rw [lam_eq hψ hI hB hK' hfix', lam_eq hψ hI hB hK (fun κ hκ => (hKy κ hκ).1)]
  have hB' : B (rhoW ψ u y) (delta ψ (K.map (MulAut.conj u).toMonoidHom)) =
      ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * B y (delta ψ K) := by
    rw [← hB.2.2 u⁻¹ (rhoW ψ u y), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, rhoW_inv_delta_conj hK hu, map_smul, smul_eq_mul]
  have hc' : cK ψ I (K.map (MulAut.conj u).toMonoidHom) = cK ψ I K := by
    rw [cK, cK, ← (isInvForm_formI hI).2.2 u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)),
      rhoW_inv_delta_conj hK hu]
    simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    linear_combination (formI ψ I (delta ψ K) (delta ψ K)) * circle_conj_mul (ψ⁻¹ (superDiag u))
  rw [lamK, lamK, hB', hc', mul_div_assoc]

include hψ in
theorem lam_eq_zero (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {z : WT (m := m) ψ} (hz : B z z = 0)
    (g : GL (Fin m) k) : lam ψ hψ I B (rhoW ψ g z) = 0 := by
  obtain ⟨K, hK, hKy⟩ := exists_good_fix hψ (rhoW ψ g z) (rhoW ψ g z)
  rw [lam_eq hψ hI hB hK (fun κ hκ => (hKy κ hκ).1), lamK,
    form_eq_zero_of_self hB.1 hB.2.1 (by rw [hB.2.2]; exact hz), zero_div]

variable (ψ) in

def Wf (hψ : Continuous ψ) (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (B : WT (m := m) ψ →ₗ⋆[ℂ] WT (m := m) ψ →ₗ[ℂ] ℂ)
    (y : WT (m := m) ψ) (g : GL (Fin m) k) : ℂ :=
  lam ψ hψ I B (rhoW ψ g y)

theorem Wf_apply (y : WT (m := m) ψ) (g : GL (Fin m) k) : Wf ψ hψ I B y g = lam ψ hψ I B (rhoW ψ g y) := rfl

theorem Wf_right (y : WT (m := m) ψ) (g x : GL (Fin m) k) : Wf ψ hψ I B y (g * x) = Wf ψ hψ I B (rhoW ψ x y) g := by
  simp only [Wf, map_mul, Module.End.mul_apply]

theorem Wf_left (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y : WT (m := m) ψ) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) (g : GL (Fin m) k) :
    Wf ψ hψ I B y (u * g) = ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * Wf ψ hψ I B y g := by
  simp only [Wf]
  rw [map_mul, Module.End.mul_apply, lam_unip hψ hI hB _ hu]

theorem Wf_add (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (y z : WT (m := m) ψ) :
    Wf ψ hψ I B (y + z) = Wf ψ hψ I B y + Wf ψ hψ I B z := by
  funext g
  simp only [Wf, map_add, Pi.add_apply]
  exact lam_add hψ hI hB _ _

theorem Wf_smul (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) (a : ℂ) (y : WT (m := m) ψ) :
    Wf ψ hψ I B (a • y) = (starRingEnd ℂ) a • Wf ψ hψ I B y := by
  funext g
  simp only [Wf, map_smul, Pi.smul_apply, smul_eq_mul]
  exact lam_smul hψ hI hB _ _

theorem Wf_eq_zero (hI : PosInt I) (hB : IsInvForm (rhoW ψ) B) {z : WT (m := m) ψ} (hz : B z z = 0) :
    Wf ψ hψ I B z = 0 :=
  funext fun g => lam_eq_zero hψ hI hB hz g

theorem isLocallyConstant_Wf (y : WT (m := m) ψ) : IsLocallyConstant (Wf ψ hψ I B y) := by
  obtain ⟨K, hKo, -, hK⟩ := exists_fix y
  refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨(fun x => g⁻¹ * x) ⁻¹' K, hKo.preimage (by fun_prop), by simp [K.one_mem], fun x hx => ?_⟩
  have e : x = g * (g⁻¹ * x) := by group
  rw [e, Wf_right, hK _ hx]

end DiscreteGroups.sglob.LConv

end
