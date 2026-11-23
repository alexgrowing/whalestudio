import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section
namespace Formalism.BasicNotions
namespace Rows.Data
variable {R : Ranks} (D : Rows.Data R)

def iotaQ (μ : D.Tup) : D.Qsp μ →ₗ[ℂ] D.EE := (D.iota μ).domRestrict (D.Qsp μ)

theorem iotaQ_inj (μ : D.Tup) : Function.Injective (D.iotaQ μ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hxQ : (x : D.Amb μ) ∈ D.V0 μ ⊓ (D.Usp μ)ᗮ := x.2
  have hU : (x : D.Amb μ) ∈ D.Usp μ := ⟨hxQ.1, hx⟩
  have h0 : inner ℂ (x : D.Amb μ) (x : D.Amb μ) = 0 := Submodule.inner_right_of_mem_orthogonal hU hxQ.2
  exact Subtype.ext (inner_self_eq_zero.mp h0)

def sec (μ : D.Tup) : D.EE →ₗ[ℂ] D.Amb μ :=
  (D.Qsp μ).subtype ∘ₗ (LinearEquiv.ofInjective (D.iotaQ μ) (D.iotaQ_inj μ)).symm.toLinearMap ∘ₗ
    ((LinearMap.range (D.iotaQ μ)).orthogonalProjectionOnto : D.EE →L[ℂ] LinearMap.range (D.iotaQ μ)).toLinearMap

theorem sec_iota (μ : D.Tup) (q : D.Amb μ) (hq : q ∈ D.Qsp μ) : D.sec μ (D.iota μ q) = q := by
  have hr : D.iota μ q ∈ LinearMap.range (D.iotaQ μ) := ⟨⟨q, hq⟩, rfl⟩
  have h1 : (LinearMap.range (D.iotaQ μ)).orthogonalProjectionOnto (D.iota μ q) = ⟨D.iota μ q, hr⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := LinearMap.range (D.iotaQ μ)) ⟨D.iota μ q, hr⟩
  have h2 : (LinearEquiv.ofInjective (D.iotaQ μ) (D.iotaQ_inj μ)) ⟨q, hq⟩ = ⟨D.iota μ q, hr⟩ := rfl
  simp only [sec, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, h1, ← h2, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.subtype_apply]

end Rows.Data

def Rows.BuDefQ {R : Ranks} (D : Rows.Data R) : Prop :=
  ∀ u (φ : D.Mu u) (x : D.EE), D.Bu u φ x = D.perCol u D.mu0 φ (D.sec D.mu0 x)

def Rows.PerKillsU {R : Ranks} (D : Rows.Data R) : Prop :=
  ∀ u (φ : D.Mu u), ∀ F ∈ D.Usp D.mu0, D.perCol u D.mu0 φ F = 0

def Rows.PeriodIdentityOnDegreeZero {R : Ranks} (D : Rows.Data R) : Prop :=
  ∀ u (φ : D.Mu u), ∀ F ∈ D.V0 D.mu0, D.perCol u D.mu0 φ F = D.Bu u φ (D.iota D.mu0 F)

theorem D7.perCol_add (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (F G : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (F + G) = D.what₂.perCol u D.what₂.mu0 φ F + D.what₂.perCol u D.what₂.mu0 φ G := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_add]

theorem D7.perCol_zero (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    D.what₂.perCol u D.what₂.mu0 φ 0 = 0 := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_zero]

theorem D7.periodIdentity_iff_period_kills (D : D7) (h : Rows.BuDefQ D.what₂) : Rows.PeriodIdentityOnDegreeZero D.what₂ ↔ Rows.PerKillsU D.what₂ := by
  constructor
  · intro hV u φ F hF
    have h0 : D.what₂.iota D.what₂.mu0 F = 0 := hF.2
    rw [hV u φ F hF.1, h0, h u φ 0, map_zero, D.perCol_zero]
  · intro hK u φ F hF
    set n : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection F with hn
    have hnU : n ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
    have hq : F - n ∈ D.what₂.Qsp D.what₂.mu0 :=
      ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
    have hι : D.what₂.iota D.what₂.mu0 F = D.what₂.iota D.what₂.mu0 (F - n) := by
      have : D.what₂.iota D.what₂.mu0 n = 0 := hnU.2
      rw [map_sub, this, sub_zero]
    have hF' : F = (F - n) + n := by abel
    rw [h u φ, hι, D.what₂.sec_iota _ _ hq]
    conv_lhs => rw [hF']
    rw [D.perCol_add, hK u φ n hnU, add_zero]

end Formalism.BasicNotions
end
