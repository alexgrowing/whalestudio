import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

open GlobalTheory.SplitScalar GlobalTheory.SplitHecke in

theorem om_latVac_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e, IsSplitIdem D e → ∀ g h, Formalism.L2.Theta.SuppAt e S g → Formalism.L2.Theta.SuppAt e T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  intro D ψ S T ΛS ΛT χS χT om hW hS hT e he g h hg hh hlat x y hx hy f hf hv

  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ

  obtain ⟨hdual, -, -⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hW.std hS hT
  have hdd : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1 := fun u hu u' hu' =>
    (hdual u (GlobalTheory.SplitScalar.latO_fin hu)).1 hu u' hu'
  have he' : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have hst : ∀ u ∈ Λ, cA D e • u ∈ Λ := GlobalTheory.SplitScalar.idem_smul_mem he'.1
  have hst' : ∀ u ∈ Λ, cA D (cA D e) • u ∈ Λ := by
    rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1

  have hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 :=
    fun y hy hyn => GlobalTheory.SplitScalar.exists_dual_half he hdual hst hy hyn
  have hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1 := by
    intro y hy hyn
    have hex := GlobalTheory.SplitScalar.exists_dual_half he' hdual hst' hy hyn
    rwa [GlobalTheory.DualPairCheck.cA_cA] at hex

  have hback : ∀ w, actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := fun w => by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ w
  have hmem : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ ↔ w ∈ Λ := fun w => by
    have hw := hlat (actO S T g⁻¹ h⁻¹ w)
    rwa [hback] at hw

  have hR : ∀ u ∈ ({0} : Finset (WO S T)), actO S T g⁻¹ h⁻¹ u ∈ Λ ∧ IsHalf e u := by
    intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact ⟨(hmem 0).2 (zero_mem _), GlobalTheory.SplitScalar.isHalf_zero e⟩
  have hRu : ∀ w, actO S T g⁻¹ h⁻¹ w ∈ Λ → IsHalf e w → ∃! v, v ∈ ({0} : Finset (WO S T)) ∧ w - v ∈ Λ := by
    intro w hw _
    refine ⟨0, ⟨Finset.mem_singleton_self _, by simpa using (hmem w).1 hw⟩, ?_⟩
    rintro v ⟨hv0, -⟩
    exact Finset.mem_singleton.1 hv0
  have hle : ∀ w ∈ Λ, IsHalf e w → actO S T g⁻¹ h⁻¹ w ∈ Λ := fun w hw _ => (hmem w).2 hw
  obtain ⟨r, hr, hom⟩ := GlobalTheory.SplitHecke.om_eq_smul_sum hW he hdd hd hd' hg hh hx hy hR hRu hle
  have key : om (g, h) f = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f := by
    have hk := hom f hf (fun u hu hue => hv.2 e he u hu hue) (fun u hu hue => hv.2 (cA D e) he' u hu hue)
    rwa [Finset.sum_singleton, GlobalTheory.WeilVacMove.heisO_zero] at hk

  by_cases hf0 : f = 0
  · subst hf0
    simp
  obtain ⟨htop, hlc, hsc, ht2, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI := htop
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI := hdisc
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, h1⟩, hN⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL T S) K hK hcov
  haveI := hμ
  have hper := GlobalTheory.WeilVacMove.norm_periodic hW.std hf
  obtain ⟨N, hNf⟩ := hN f hf.cont hper
  obtain ⟨-, -, hI, -⟩ := hNf μ 𝓕 hμ h𝓕
  have hu := hW.om_unit μ 𝓕 hμ h𝓕 (g, h) f hf
  rw [key] at hu
  have hpt : ∀ w, ‖(((r : ℂ) * (splitFacO χS χT x y : ℂ)) • f) w‖ₑ ^ 2 =
      ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ₑ ^ 2 * ‖f w‖ₑ ^ 2 := fun w => by
    rw [Pi.smul_apply, smul_eq_mul, enorm_mul (a := (r : ℂ) * (splitFacO χS χT x y : ℂ)), mul_pow]
  simp_rw [hpt] at hu
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top), hI, h1, one_mul] at hu
  have hN0 : (N : ENNReal) ≠ 0 := by
    intro hz
    apply hf0
    have h0 : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ = 0 := by rw [hI, hz, mul_zero]
    rw [lintegral_eq_zero_iff' (hf.cont.measurable.enorm.pow_const 2).aemeasurable] at h0
    apply GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 f hf.cont hper
    filter_upwards [h0] with w hw
    simpa using hw
  have hnorm : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hs1 : ‖(splitFacO χS χT x y : ℂ)‖ = 1 := by
      first
        | exact Circle.norm_coe _
        | exact Circle.abs_coe _
        | simp
    rw [hs1, mul_one]
  have hr1 : r = 1 := by
    have hc : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖₊ ^ 2 = 1 := by
      rw [enorm_eq_nnnorm] at hu
      have hN0' : N ≠ 0 := fun hz => hN0 (by rw [hz]; rfl)
      have h2 : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖₊ ^ 2 * N = 1 * N := by
        rw [one_mul]; exact_mod_cast hu
      exact mul_right_cancel₀ hN0' h2
    have hc' : ‖(r : ℂ) * (splitFacO χS χT x y : ℂ)‖ ^ 2 = 1 := by
      rw [← coe_nnnorm]
      exact_mod_cast hc
    rw [hnorm] at hc'
    nlinarith
  rw [key, hr1]
  simp

end GlobalTheory.VecInv
