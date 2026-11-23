import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartSelfStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem isChar_conj_eq {G : Type} [Group G] {Y : G → ℂ} (hY : IsChar ℂ ℂ Y) (g z : G) :
    Y (z * g * z⁻¹) = Y g := by
  obtain ⟨n, ρ, h⟩ := hY
  rw [h, h, Representation.char_conj]

theorem conv_op_eq {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (Y h : G → ℂ) :
    ∑ x, star (∑ y, Y y * h (y⁻¹ * x)) • ρ x =
      (∑ y, star (Y y) • ρ y) * (∑ z, star (h z) • ρ z) := by
  rw [Finset.sum_mul_sum]
  simp_rw [star_sum, star_mul', Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [map_mul, smul_mul_smul_comm, smul_smul, mul_comm]

def convL {G : Type} [Group G] [Fintype G] (Y : G → ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  ∑ g, star (Y g) • LinearMap.funLeft ℂ ℂ (fun z => g * z)

theorem convL_apply {G : Type} [Group G] [Fintype G] (Y : G → ℂ) (a : G → ℂ) (z : G) :
    convL Y a z = ∑ g, star (Y g) * a (g * z) := by
  simp [convL, LinearMap.funLeft, Finset.sum_apply]

def regKer {G : Type} [Group G] [Fintype G] (Y : G → ℂ) :
    Representation ℂ G (LinearMap.ker (convL Y)) where
  toFun g := (LinearMap.funLeft ℂ ℂ (fun z => z * g)).restrict (p := LinearMap.ker (convL Y))
      (q := LinearMap.ker (convL Y)) (by
        intro a ha
        rw [LinearMap.mem_ker] at ha ⊢
        funext z
        have := congrFun ha (z * g)
        simp only [convL_apply, Pi.zero_apply] at this ⊢
        simpa [LinearMap.funLeft, mul_assoc] using this)
  map_one' := by ext a z; simp [LinearMap.funLeft]
  map_mul' g h := by ext a z; simp [LinearMap.funLeft, mul_assoc]

theorem regKer_apply {G : Type} [Group G] [Fintype G] (Y : G → ℂ) (g : G) (a : LinearMap.ker (convL Y))
    (z : G) : ((regKer Y g a : LinearMap.ker (convL Y)) : G → ℂ) z = (a : G → ℂ) (z * g) := rfl

theorem kills_iff_conv : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y →
    (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  intro G _ _ φ Y hY
  have := Fintype.ofFinite G
  constructor
  · intro hK
    set K := LinearMap.ker (convL Y)

    have hT : ∑ g, star (Y g) • regKer Y g = 0 := by
      ext a z
      have ha := congrFun (LinearMap.mem_ker.1 a.2) z
      rw [convL_apply, Pi.zero_apply] at ha
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, regKer_apply, smul_eq_mul, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rw [← ha, ← Equiv.sum_comp (MulAut.conj z⁻¹).toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hc := isChar_conj_eq hY g z⁻¹
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv] at hc ⊢
      rw [hc]
      congr 2
      group
    have hK' := hK K (regKer Y) (by
      rw [finsum_eq_sum_of_fintype]
      have := congrArg (LinearMap.trace ℂ K) hT
      simpa [map_sum, smul_eq_mul] using this)
    rw [finsum_eq_sum_of_fintype] at hK'

    let ℓ : Module.Dual ℂ (G → ℂ) := ∑ x, star (φ x) • (LinearMap.proj x : (G → ℂ) →ₗ[ℂ] ℂ)
    have hℓ : ∀ a, ℓ a = ∑ x, star (φ x) * a x := fun a => by simp [ℓ]
    have hmem : ℓ ∈ K.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro a ha
      have := congrFun (congrArg Subtype.val (LinearMap.congr_fun hK' ⟨a, ha⟩)) 1
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, regKer_apply, smul_eq_mul, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply] at this
      have e : ∀ x, ((regKer Y x ⟨a, ha⟩ : LinearMap.ker (convL Y)) : G → ℂ) 1 = a x := fun x => by
        show a (1 * x) = a x
        rw [one_mul]
      simp only [e] at this
      rw [hℓ, this]
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
    obtain ⟨μ, hμ⟩ := hmem
    refine ⟨fun w => star (μ (Pi.single w 1)), fun x => ?_⟩
    have hδ : convL Y (Pi.single x 1) = ∑ g, star (Y g) • Pi.single (g⁻¹ * x) 1 := by
      funext z
      rw [convL_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      congr 1
      simp only [Pi.single_apply, eq_inv_mul_iff_mul_eq]
    have h1 := LinearMap.congr_fun hμ (Pi.single x 1)
    rw [LinearMap.dualMap_apply, hδ, map_sum, hℓ] at h1
    simp only [map_smul, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    rw [finsum_eq_sum_of_fintype]
    have h2 := congrArg star h1
    simp only [star_sum, star_mul', star_star] at h2
    rw [← h2]
  · rintro ⟨h, hφ⟩ V _ _ _ ρ hV
    have hY0 := GlobalTheory.T.isInCharacterIsotypicPart_self G Y hY V ρ hV
    rw [finsum_eq_sum_of_fintype] at hY0 ⊢
    simp_rw [hφ, finsum_eq_sum_of_fintype]
    rw [conv_op_eq, hY0, zero_mul]

end GlobalTheory.Shin
