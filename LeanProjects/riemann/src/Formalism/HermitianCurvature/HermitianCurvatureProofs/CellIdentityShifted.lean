import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmBpAtEqOfShiftR
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseCutoffIsTruncation

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section swap

variable {k r : ℕ} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']

theorem isDFrame_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ γ : B.Mat k r) :
    D.IsDFrame Ds' ν' m₀ γ ↔ D.IsDFrame Ds ν' m₀ γ := by
  simp only [D.IsDFrame, D.cofR, D.cofL, hz, hz']

theorem muR_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (_hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) :
    D.muR Ds' γ w = D.muR Ds γ w := by
  unfold D.muR D.rhoOfU
  rw [hz]

theorem inSS_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (q : B.SS k r) : Ds'.inSS q ↔ Ds.inSS q := by
  simp only [B.RealPlaceData.inSS, hz, hz']

theorem isNormCut_congr (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ) :
    D.IsNormCut Ds' γ μR θ ↔ D.IsNormCut Ds γ μR θ := by
  simp only [D.IsNormCut, inSS_swap Ds Ds' hz hz']

theorem isRelevant_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (γ : B.Mat k r) : C6.IsRelevant Ds' γ ↔ C6.IsRelevant Ds γ := by
  simp only [C6.IsRelevant, hz, hz']

theorem muSS_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hW : Ds'.μW = Ds.μW)
    (hN : Ds'.μN = Ds.μN) (hW' : Ds'.μW' = Ds.μW') : Ds'.μSS = Ds.μSS := by
  simp only [B.RealPlaceData.μSS, hW, hN, hW']

theorem orbIntegrand_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (hπ : Ds'.π = Ds.π) (A : B.Mat k r → (Wq' →L[ℂ] Wq))
    (hA : WigEquiv Ds.z Ds.z' Ds.π' Ds'.π' A) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r)
    (hγ : γ ∈ B.GV k r) (hGγ : 0 < Gf k r Ds.z Ds.z' γ) (q : B.SS k r) (hq : Ds.inSS q) :
    D.orbIntegrand Ds' γ (fun g => (f g).comp (A g)) q = (D.orbIntegrand Ds γ f q).comp (A γ) := by
  obtain ⟨h1m, n1m, h2m, n2m⟩ := hq
  have o1 : ∀ w : Fin (2 * r + k + 1) → ℂ, Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ UWset k r w := by
    intro w
    simpa using PBO.one_mem_UWset w
  have hq1 : Ds.inSS ((Matrix.of.symm (1 : B.Mat k r), q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) :=
    ⟨o1 Ds.z, n1m, o1 Ds.z', n2m⟩
  have hq0 : Ds.inSS ((q.1.1, q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) :=
    ⟨h1m, n1m, o1 Ds.z', n2m⟩
  have e1 : B.sgs ((Matrix.of.symm (1 : B.Mat k r), q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) γ
      = (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 := by
    simp [B.sgs]
  have e0 : B.sgs ((q.1.1, q.1.2), (Matrix.of.symm (1 : B.Mat k r), q.2.2)) γ
      = (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 := by
    simp [B.sgs]
  have g1GV : (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 ∈ B.GV k r :=
    Dx2.DF.mul_UH (Dx2.DF.mul_UH (WeylGroupFacts.uh_inv (B6.Nset_sub k r n1m)) hγ) (B6.Nset_sub k r n2m)
  have g0GV : (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 ∈ B.GV k r := by
    have := Dx2.DF.mul_UH (WeylGroupFacts.uh_inv (B6.UWset_sub k r Ds.z h1m)) g1GV
    simpa only [mul_assoc] using this
  have hG1 : 0 < Gf k r Ds.z Ds.z' ((Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
    rw [← e1, TBBx2.Gf_sgs Ds _ hq1]
    exact hGγ
  have hG0 : 0 < Gf k r Ds.z Ds.z' ((Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
    rw [← e0, TBBx2.Gf_sgs Ds _ hq0]
    exact hGγ
  have hAs : A (B.sgs q γ)
      = Ds.π' (Matrix.of q.2.1)⁻¹ ∘SL A γ ∘SL Ds'.π' (Matrix.of q.2.1) := by
    have s1 : B.sgs q γ
        = (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2 * Matrix.of q.2.1 := rfl
    rw [s1, hA.2.2 _ g0GV hG0 _ h2m]
    have s2 : (Matrix.of q.1.1)⁻¹ * (Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2
        = (Matrix.of q.1.1)⁻¹ * ((Matrix.of q.1.2)⁻¹ * γ * Matrix.of q.2.2) := by
      simp only [mul_assoc]
    rw [s2, hA.2.1 _ g1GV hG1 _ (WeylGroupFacts.uw_inv h1m),
      hA.1 γ hγ hGγ _ (WeylGroupFacts.mem_n_inv n1m) _ n2m]
  have h2m' : Matrix.of q.2.1 ∈ UWset k r Ds'.z' := by
    rw [hz']
    exact h2m
  have hcanc : Ds'.π' (Matrix.of q.2.1) ∘SL Ds'.π' (Matrix.of q.2.1)⁻¹ = 1 := by
    rw [← Ds'.π'_rep.2 _ h2m' _ (WeylGroupFacts.uw_inv h2m'), NFRadRedS.uw_mul_inv h2m', Ds'.π'_rep.1]
  have hxi : B.xiTau Ds' (1, 1) q = B.xiTau Ds (1, 1) q := by
    simp only [B.xiTau, hz, hz']
  simp only [D.orbIntegrand, B.rho, hxi, hπ]
  ext v
  have hv := congrArg (fun T => (T : Wq' →L[ℂ] Wq') v) hcanc
  have hv2 := congrArg (fun T => (T : Wq' →L[ℂ] Wq) ((Ds'.π' (Matrix.of q.2.1)⁻¹) v)) hAs
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at hv hv2
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [hv2, hv]

theorem orbJ_swap (Ds : B.RealPlaceData k r Wp Wq) (Ds' : B.RealPlaceData k r Wp Wq') (hz : Ds'.z = Ds.z)
    (hz' : Ds'.z' = Ds.z') (hπ : Ds'.π = Ds.π) (hW : Ds'.μW = Ds.μW) (hN : Ds'.μN = Ds.μN)
    (hW' : Ds'.μW' = Ds.μW') (A : B.Mat k r → (Wq' →L[ℂ] Wq)) (hA : WigEquiv Ds.z Ds.z' Ds.π' Ds'.π' A)
    (f : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (hγ : γ ∈ B.GV k r) (hGγ : 0 < Gf k r Ds.z Ds.z' γ)
    (μR : Measure (Mt k r)) (hrel : C6.IsRelevant Ds γ)
    (hH : B.IsHaarOn (C6.Rset γ) μR) (θ : B.SS k r → ℝ) (hθ : D.IsNormCut Ds γ μR θ)
    (hi : Integrable (fun q => θ q • D.orbIntegrand Ds γ f q) Ds.μSS) :
    D.orbJ Ds' γ μR (fun g => (f g).comp (A g)) = (D.orbJ Ds γ μR f).comp (A γ) := by
  set F' : B.Mat k r → Wq' →L[ℂ] Wp := fun g => (f g).comp (A g) with hF'
  have hθ' : D.IsNormCut Ds' γ μR θ := (isNormCut_congr Ds Ds' hz hz' γ μR θ).2 hθ
  have hrel' : C6.IsRelevant Ds' γ := (isRelevant_swap Ds Ds' hz hz' γ).2 hrel
  have hμ : Ds'.μSS = Ds.μSS := muSS_swap Ds Ds' hW hN hW'
  let L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (A γ)
  have hL : ∀ X, L X = X.comp (A γ) := fun X => rfl
  have hae : ∀ᵐ q ∂Ds.μSS,
      θ q • D.orbIntegrand Ds' γ F' q = L (θ q • D.orbIntegrand Ds γ f q) := by
    filter_upwards [TBBx2.ae_inSS Ds] with q hq
    rw [hL, ContinuousLinearMap.smul_comp, orbIntegrand_swap Ds Ds' hz hz' hπ A hA f γ hγ hGγ q hq]
  have hi' : Integrable (fun q => θ q • D.orbIntegrand Ds' γ F' q) Ds'.μSS := by
    rw [hμ]
    exact (L.integrable_comp hi).congr (hae.mono fun q hq => hq.symm)
  have hex' : ∃ θ' : B.SS k r → ℝ, D.IsNormCut Ds' γ μR θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Ds' γ F' p) Ds'.μSS := ⟨θ, hθ', hi'⟩
  have hex : ∃ θ' : B.SS k r → ℝ, D.IsNormCut Ds γ μR θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Ds γ f p) Ds.μSS := ⟨θ, hθ, hi⟩
  unfold D.orbJ
  rw [dif_pos hex', dif_pos hex]
  rw [P.orbital_integral_indep_choice k r Wp Wq' Ds' γ μR hrel' hH F' _ θ hex'.choose_spec.1 hθ'
      hex'.choose_spec.2 hi',
    P.orbital_integral_indep_choice k r Wp Wq Ds γ μR hrel hH f _ θ hex.choose_spec.1 hθ hex.choose_spec.2 hi]
  rw [hμ, integral_congr_ae hae]
  exact L.integral_comp_comm hi

end swap

theorem cell_identity_shifted : CellIdSh := by
  obtain ⟨c₃, hc⟩ := Formalism.FourierDecayAlt.P.orbital_integral_converges
  refine ⟨c₃, ?_⟩
  intro Pa Wp Wq Wq' _ _ _ _ _ _ _ _ _ u u' p q f A A₀ hT hA hA₀ hf γ hγ hG
  obtain ⟨hz, hz', hπ, hW, hN, hW', hν, hm⟩ := hT
  have hG' : 0 < D.ptG (Tz Pa.k Pa.r p.T.base.z * Tz Pa.k Pa.r p.T.base.z') Pa.r γ := hG
  have hGq : 0 < D.ptG (Tz Pa.k Pa.r q.T.base.z * Tz Pa.k Pa.r q.T.base.z') Pa.r γ := by
    rw [hz, hz']
    exact hG'
  by_cases hex : ∃ g ∈ B.GV Pa.k Pa.r, Zhat Pa.k Pa.r p.T.base.z p.T.base.z' g = D.ptMatN γ (Pa.r + 1) ∧
      D.IsDFrame p.T.base p.ν' p.m₀ g
  · have hrep : ptRep p γ = hex.choose := dif_pos hex
    obtain ⟨hgGV, hZ, hF⟩ := hex.choose_spec
    rw [hrep]
    generalize hex.choose = g at hgGV hZ hF ⊢
    obtain ⟨hw, hd⟩ := Dx2.VV.ptMatN_monoP' γ (Pa.r + 1) hγ.2 hγ.1
    have hZq : Zhat Pa.k Pa.r q.T.base.z q.T.base.z' g = D.ptMatN γ (Pa.r + 1) := by
      rw [hz, hz']
      exact hZ
    have hFq : D.IsDFrame q.T.base q.ν' q.m₀ g := by
      rw [hν, hm]
      exact (isDFrame_swap p.T.base q.T.base hz hz' p.ν' p.m₀ g).2 hF
    have hZm := hZ.trans hw
    have hGf : 0 < Gf Pa.k Pa.r p.T.base.z p.T.base.z' g := by
      rw [TBBx2.Gf_of_Zhat _ _ g γ hZ]
      exact hG'
    have hrel := Final.d_ptRelevant _ _ _ _ p.T.base γ g hγ hgGV hZ
    have hH := Formalism.FourierDecayAlt.P.radial_measure_is_haar _ _ _ _ p.T.base g _ _ hgGV hd hZm
    obtain ⟨θ, hθ, hi⟩ := hc Pa.k Pa.r Wp Wq p.T.base g _ _ A₀ f hgGV hrel hd hZm hGf hA₀ hf
    simp only [KB.Pl.V]
    rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep _ _ _ _ q.T.base q.ν' q.m₀ _ γ hγ g q.hF hGq hgGV hZq hFq,
      Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep _ _ _ _ p.T.base p.ν' p.m₀ f γ hγ g p.hF hG' hgGV hZ hF]
    convert orbJ_swap p.T.base q.T.base hz hz' hπ hW hN hW' A hA f g hgGV hGf _ hrel hH θ hθ hi using 2
    congr 1
    exact muR_swap p.T.base q.T.base hz hz' g _
  · have h1 : ¬ ∃ g ∈ B.GV Pa.k Pa.r, Zhat Pa.k Pa.r q.T.base.z q.T.base.z' g = D.ptMatN γ (Pa.r + 1) ∧
        D.IsDFrame q.T.base q.ν' q.m₀ g := by
      rintro ⟨g, hg1, hg2, hg3⟩
      apply hex
      refine ⟨g, hg1, ?_, ?_⟩
      · rw [← hz, ← hz']
        exact hg2
      · rw [hν, hm] at hg3
        exact (isDFrame_swap p.T.base q.T.base hz hz' p.ν' p.m₀ g).1 hg3
    simp only [KB.Pl.V, D.vecV]
    rw [dif_pos ⟨hγ, hGq⟩]
    conv_rhs => rw [dif_pos ⟨hγ, hG'⟩, dif_neg hex, ContinuousLinearMap.zero_comp]
    exact dif_neg h1

end

end Formalism.FourierDecayAlt.P.CutBPEq
