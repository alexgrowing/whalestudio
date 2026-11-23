import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfRsmulRight
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem l2_norm_fundamental_domain (T : PT E) (s : (Fin 1 → Vsp T.dim) → ℂ) (hs : s ∈ T.Sec 1 1) {g : ℕ}
    (L : (Fin g → ℂ) ≃ₗ[ℝ] Vsp T.dim) (Λg : AddSubgroup (Fin g → ℂ)) (hΛ : ∀ γ, γ ∈ T.L ↔ L.symm γ ∈ Λg)
    (Fd : Set (Fin g → ℂ)) (hFd : IsAddFundamentalDomain Λg Fd volume) (θ : (Fin g → ℂ) → ℂ)
    (hθ : ∀ z, ‖s (fun _ => L z)‖ = ‖θ z‖) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hH : ∀ z, (hermForm Hm z z).re = ‖L z‖ ^ 2)
    (hc9 : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = 1) :
    T.l2 1 s = 1 := by
  set F : Vsp T.dim → ℂ := fun v => s (fun _ => v) with hFdef
  set G : Vsp T.dim → ℝ := (PfSupSec.toGT T).ptN2 1 F with hGdef
  have hint : ∀ z, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) = G (L z) := by
    intro z
    rw [← hθ z, hH, hGdef]
    simp [GT.ptN2, hFdef]
  simp only [hint] at hc9

  let e : (Fin g → ℂ) ≃L[ℝ] Vsp T.dim := L.toContinuousLinearEquiv
  let em : (Fin g → ℂ) ≃ᵐ Vsp T.dim := e.toHomeomorph.toMeasurableEquiv
  have hem : ∀ z, em z = L z := fun z => rfl
  set μ : Measure (Vsp T.dim) := Measure.map em volume with hμdef
  have : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map volume
  have hμ : μ = Measure.addHaarScalarFactor μ volume • volume :=
    Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  set c := Measure.addHaarScalarFactor μ volume with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  set Fd' : Set (Vsp T.dim) := em.symm ⁻¹' Fd with hFd'def
  have hpre : em ⁻¹' Fd' = Fd := by rw [hFd'def]; exact em.preimage_symm_preimage Fd
  have I1 : ∫ z in Fd, G (L z) = (c : ℝ) * ∫ v in Fd', G v := by
    have h1 := setIntegral_map_equiv em G Fd' (μ := volume)
    rw [hpre] at h1
    simp only [hem] at h1
    rw [← h1, ← hμdef, hμ, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have V1 : (volume Fd).toReal = (c : ℝ) * (volume Fd').toReal := by
    have h1 : μ Fd' = volume Fd := by rw [hμdef, MeasurableEquiv.map_apply, hpre]
    rw [← h1, hμ, Measure.smul_apply, ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul]

  let eq : ↥(lat T.b) ≃ ↥Λg :=
    { toFun := fun γ => ⟨L.symm γ, (hΛ γ).1 γ.2⟩
      invFun := fun p => ⟨L p, (hΛ (L p)).2 (by simpa using p.2)⟩
      left_inv := fun γ => by ext1; simp
      right_inv := fun p => by ext1; simp }
  have hqmp : Measure.QuasiMeasurePreserving em.symm volume volume := by
    refine ⟨em.symm.measurable, ?_⟩
    have : (Measure.map em.symm (volume : Measure (Vsp T.dim))).IsAddHaarMeasure :=
      e.symm.isAddHaarMeasure_map volume
    rw [Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.map em.symm (volume : Measure (Vsp T.dim))) volume]
    exact Measure.smul_absolutelyContinuous
  have hFd2 : IsAddFundamentalDomain ↥(lat T.b) (em.toEquiv '' Fd) volume :=
    hFd.image_of_equiv em.toEquiv hqmp eq (fun γ z => by
      show L (L.symm γ + z) = (γ : Vsp T.dim) + L z
      rw [map_add, LinearEquiv.apply_symm_apply])
  have himg : em.toEquiv '' Fd = Fd' := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      show em.symm (em z) ∈ Fd
      simpa using hz
    · intro hv
      exact ⟨em.symm v, hv, by simp⟩
  rw [himg] at hFd2
  haveI : VAddInvariantMeasure ↥(lat T.b) (Vsp T.dim) volume :=
    ⟨fun γ s _ => measure_preimage_add volume (γ : Vsp T.dim) s⟩
  have hstd : IsAddFundamentalDomain ↥(lat T.b) (ZSpan.fundamentalDomain T.b) volume :=
    ZSpan.isAddFundamentalDomain T.b volume
  have hper : ∀ (γ : ↥(lat T.b)) (v : Vsp T.dim), G (γ +ᵥ v) = G v := fun γ v =>
    ReciprocityTheory.ChartRestriction.G.I2.lemS_periodic (PfSupSec.toGT T) 1 (PfSupSec.sec_mem T hs) γ.2 v
  have hI : ∫ v in Fd', G v = ∫ v in ZSpan.fundamentalDomain T.b, G v := hFd2.setIntegral_eq hstd hper
  have hV : volume Fd' = volume (ZSpan.fundamentalDomain T.b) := hFd2.measure_eq hstd
  rw [PfSupSec.symmetricMeasure_l2Norm_eq_resolutionL2]
  show ⨍ v in ZSpan.fundamentalDomain T.b, G v = 1
  rw [setAverage_eq, measureReal_def, ← hV, ← hI]
  rw [I1, V1] at hc9
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  by_cases h0 : (volume Fd').toReal = 0
  · rw [h0, mul_zero, div_zero] at hc9; exact absurd hc9 zero_ne_one
  rw [mul_div_mul_left _ _ hc'.ne'] at hc9
  rw [smul_eq_mul, ← hc9]
  field_simp

def conjL (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) where
  toFun := star
  invFun := star
  map_add' := star_add
  map_smul' := fun r z => by ext i; simp
  left_inv := star_star
  right_inv := star_star

lemma card_idx {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (A : TorusAt X x) :
    Fintype.card (Idx A.T.dim) = X.Ψ.card * r := by
  classical
  have hcc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ := by
    intro σ
    first
      | exact star_star σ
      | exact RingHom.ext fun z => by simp [ComplexEmbedding.conjugate_coe_eq]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← Finset.sum_add_sum_compl X.Ψ]
  have h1 : ∑ τ ∈ X.Ψ, A.T.dim τ = X.Ψ.card * X.p0 := by
    rw [Finset.sum_congr rfl fun τ hτ => A.dim_pos ⟨τ, hτ⟩, Finset.sum_const, smul_eq_mul]
  have h2 : ∑ τ ∈ X.Ψᶜ, A.T.dim τ = X.Ψ.card * (r - X.p0) := by
    have h3 : ∑ τ ∈ X.Ψᶜ, A.T.dim τ = ∑ τ ∈ X.Ψ, A.T.dim (ComplexEmbedding.conjugate τ) := by
      refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
      · intro τ hτ
        rw [Finset.mem_compl] at hτ
        exact (X.cmType _).2 (by rwa [hcc])
      · intro τ hτ
        rw [Finset.mem_compl]
        exact (X.cmType τ).1 hτ
      · intro τ _; exact hcc τ
      · intro τ _; exact hcc τ
      · intro τ _; rw [hcc]
    rw [h3, Finset.sum_congr rfl fun τ hτ => A.dim_neg ⟨τ, hτ⟩, Finset.sum_const, smul_eq_mul]
  rw [h1, h2, ← mul_add, Nat.add_sub_cancel' X.p0_le]

lemma finrank_eq (D : Formalism.BasicNotions.D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f]
  have hn : D.R.n = D.R.ord := rfl
  rw [hn]
  ring

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD in
theorem torusFrame (hTM : TorusMatchSt) (hHm : UnitHmSt) : TorusFrameSt := by
  intro D T h j hj σ hσ k xf hort
  obtain ⟨W, Wu, A, L, hpins⟩ := hTM D T h j hj σ hσ k xf hort
  have hφ := hpins.1
  have hH := hpins.2.1
  have hθ := hpins.2.2.1
  simp only [LinearEquiv.coe_coe] at hφ hH hθ
  refine ⟨W, Wu, A, L.toLinearMap, hpins, ?_, ?_, ?_⟩
  · let L' : (Fin W.g → ℂ) ≃ₗ[ℝ] Vsp A.T.dim := (conjL W.g).trans (L.restrictScalars ℝ)
    have hL' : ∀ z, L' z = L (star z) := fun z => rfl
    refine l2_norm_fundamental_domain A.T A.s A.s_mem L' W.Pm.range ?_ Wu.Fd Wu.c8 Wu.θ ?_ Wu.Hm ?_ Wu.c9
    · intro γ
      rw [A.lat γ]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(W.φ k).symm ⟨v, hv⟩, ?_⟩
        have e1 : A.φ v = L' (W.Pm ((W.φ k).symm ⟨v, hv⟩)) := by
          rw [hL', ← hφ]; simp
        rw [e1, LinearEquiv.symm_apply_apply]
      · rintro ⟨a, ha⟩
        refine ⟨_, (W.φ k a).2, ?_⟩
        rw [hφ a, ← hL', ha, LinearEquiv.apply_symm_apply]
    · intro z
      rw [hL', hθ, star_star, norm_star]
    · intro z
      rw [hL']
      have h1 := ChA.re_Hf (L (star z)) (L (star z))
      rw [hH, star_star, real_inner_self_eq_norm_sq] at h1
      rw [← h1]
      simp
  · intro i
    have h1 := hHm D T h j hj σ hσ k xf hort W Wu i
    have h2 := ChA.re_Hf (L (Pi.single i 1)) (L (Pi.single i 1))
    have hs : star (Pi.single i (1 : ℂ) : Fin W.g → ℂ) = Pi.single i 1 := by
      ext j'
      by_cases hij : j' = i <;> simp [hij]
    rw [hH, hs, real_inner_self_eq_norm_sq] at h2
    have h3 : ‖L (Pi.single i 1)‖ ^ 2 ≤ 1 := by rw [← h2]; simpa using h1
    show ‖L (Pi.single i 1)‖ ≤ 1
    nlinarith [norm_nonneg (L (Pi.single i 1))]
  · rw [card_idx]
    have h2c := Formalism.L2.Pj.DatLin.two_card ((T.U j σ).X k).cmType
    rw [finrank_eq D] at h2c
    have : ((T.U j σ).X k).Ψ.card = D.R.f := by omega
    rw [this]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame
