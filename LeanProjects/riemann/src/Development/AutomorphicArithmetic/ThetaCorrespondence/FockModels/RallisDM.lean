import Development.AutomorphicArithmetic.ThetaCorrespondence.RallisInnerProduct.GraphRelationExtendsFromFockVectorsToKFinite
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DmOfHyp

section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

open GlobalTheory.Cusp

noncomputable section

namespace UpperTheory.Lit.Rallis.RallisIPProof
open GlobalTheory

theorem rallis_of_dm : ResidueKilled.DM → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    GlobalTheory.Published.WeilThetaConvergence → GlobalTheory.Published.RallisInnerProductConvergent := by
  intro hDM hSWU hWC D A B hab hb2 hw ψ χA χB ω ωd hω hωd hTC a ha hI ν 𝓕 hcov θ C hθ hSig hCart m hm hmr mH hmH U hU hUc
    _hLow Φ₁ Φ₂ hΦ₁ hΦ₂ hK f₁ hf₁ f₂ hf₂
  have hW := GlobalTheory.weilRepresentationUnitaryPair
  have hC : GlobalTheory.Published.CuspRapidDecay := GlobalTheory.RapidDecay.cuspRapidDecay
  have ha1 : 1 ≤ A.rank := by omega
  have hw' : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by rcases hw with h | h <;> omega
  obtain ⟨hφ, hid⟩ := hTC Φ₁ Φ₂ hΦ₁ hΦ₂
  have hmem := GlobalTheory.SwSecMem.swSec_mem_degPS hW D ψ A B χB ωd hωd ν 𝓕 hcov (delta A B Φ₁ Φ₂) hφ a hK
  have hHk : IsHeckeChar D χB⁻¹ := by
    have h := hωd.hecT
    refine ⟨?_, fun x => ?_⟩
    · have : (χB⁻¹ : (AE D)ˣ →* Circle) = fun x => (χB x)⁻¹ := rfl
      rw [this]; exact h.1.inv
    · rw [MonoidHom.inv_apply, h.2 x, inv_one]
  obtain ⟨hDM1, -, hDM3⟩ := hDM D A (by omega) a ha hI χB⁻¹ B.rank hHk (resEta_inv hωd.resT) (sZero A B)
    (swSec A B ωd ν 𝓕 (delta A B Φ₁ Φ₂)) hmem
  have hA₁ : f₁ ∈ A0 θ A C := hf₁.1
  have hA₂ : f₂ ∈ A0 θ A C := hf₂.1
  have rd : ∀ u ∈ A0 θ A C, GlobalTheory.Grow.RapidDec A u := fun u hu =>
    GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (mem_cuspForms.1 hu).1.1 (mem_cuspForms.1 hu).1.2
  have rdc : ∀ u ∈ A0 θ A C, GlobalTheory.Grow.RapidDec A (fun g => conj (u g)) := fun u hu =>
    rd _ (GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 D θ A C hθ u hu)
  obtain ⟨hBI, -⟩ := hDM3 θ hθ hSig C hCart m hm f₁ hA₁ f₂ hA₂
  have hEF := hDM1.1.1
  have hZF : GlobalTheory.Eis.IsZetaFamily A χB⁻¹ m (flat A a (swSec A B ωd ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B)) f₁ f₂ :=
    ⟨hEF, fun s hs => (hBI s hs).1⟩
  have hEV := UpperTheory.Lit.Rallis.T.siegelWeil_convergent_range_kFinite_thetaFun hSWU hWC D ψ A B χB ωd hωd hab hb2 hw' a ha hI θ hθ ν 𝓕 hcov mH hmH _ hφ hK
  obtain ⟨-, hZV⟩ := GlobalTheory.Eis.zetaHolValueAt_of_eisValueAt D A χB⁻¹ hHk m hm _ hDM1.1
    (fun g => hEF.analyticOnNhd_flat g) hDM1.2 f₁ f₂ (rd _ hA₁) (rd _ hA₂) hZF (sZero A B) _ hEV

  have hKer : ∀ Φ, IsThetaFunO ψ A B Φ →
      Continuous (Function.uncurry fun g h => thetaKO ω g h Φ) ∧
      (∀ γ ∈ GQ A, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ) ∧
      (∀ g, MemL2Quotient (GQ B) mH fun h => thetaKO ω g h Φ) ∧
      (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (fun h => thetaKO ω g h Φ) fun h => thetaKO ω g h Φ) ∧
      ∀ h, GlobalTheory.Grow.ModGrowth A fun g => thetaKO ω g h Φ := by
    intro Φ hΦ
    obtain ⟨hL2, hMG⟩ := UpperTheory.Lit.Rallis.T.petersson_normSq_thetaKernel_moderateGrowth hWC D ψ A B χA χB ω ωd hω hωd hTC ha1 hw mH hmH Φ hΦ
    refine ⟨hω.om_cont Φ hΦ 0, fun γ hγ g h => ?_, hL2, hMG, fun h => ?_⟩
    · have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hΦ)
    · obtain ⟨C, N, hCN⟩ := GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ A B χA χB ω hω Φ hΦ
      refine ⟨C * GlobalTheory.Grow.height B h ^ N, N, fun g => (hCN g h).trans (le_of_eq ?_)⟩
      rw [mul_pow]; ring
  obtain ⟨i₁, i₂, l₁, l₂, hss⟩ := GlobalTheory.Core.Rk.Seesaw.seesaw_fubini D A B m mH hm hmH (fun g h => thetaKO ω g h Φ₁)
    (fun g h => thetaKO ω g h Φ₂) (fun K hK => by
      rcases hK with rfl | rfl
      exacts [hKer Φ₁ hΦ₁, hKer Φ₂ hΦ₂]) (fun g => conj (f₁ g)) (fun g => conj (f₂ g)) (rdc f₁ hA₁) (rdc f₂ hA₂)

  have key : ∀ g₁ g₂ h, thetaKO ω g₁ h Φ₁ * conj (thetaKO ω g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) * thetaKO ωd (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂) := by
    intro g₁ g₂ h
    rw [(hid g₁ g₂ h).2]
    have e : ((χB (detA A g₂) : Circle) : ℂ) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ) = 1 := by
      rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
    linear_combination (-(thetaKO ω g₁ h Φ₁ * conj (thetaKO ω g₂ h Φ₂))) * e
  have hpet : ∀ g₁ g₂, petersson B mH (fun h => thetaKO ω g₁ h Φ₁) (fun h => thetaKO ω g₂ h Φ₂) =
      ((χB (detA A g₂) : Circle) : ℂ) *
        ((((autMeasure B mH).real Set.univ : ℝ) : ℂ) * ThetaMean.thetaMean ωd mH (delta A B Φ₁ Φ₂) (io A (g₁, g₂))) := by
    intro g₁ g₂
    have e1 : petersson B mH (fun h => thetaKO ω g₁ h Φ₁) (fun h => thetaKO ω g₂ h Φ₂) =
        ((χB (detA A g₂) : Circle) : ℂ) *
          ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO ωd (io A (g₁, g₂)) h (delta A B Φ₁ Φ₂)) q
            ∂autMeasure B mH := by
      rw [← integral_const_mul]
      simp only [petersson, pet, GlobalTheory.AutomorphicL2Unitary.descend]
      congr 1
      funext q
      exact key g₁ g₂ _
    rw [e1, ← measure_smul_average, ThetaMean.thetaMean, Complex.real_smul]
  have hv : (((autMeasure B mH).real Set.univ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (volQuot_pos B mH).ne'
  have hval : (((autMeasure B mH).real Set.univ : ℝ) : ℂ)⁻¹ *
      petersson B mH (RallisIP.thetaLift ω m Φ₁ f₁) (RallisIP.thetaLift ω m Φ₂ f₂) =
      GlobalTheory.Eis.dblInt A χB⁻¹ m (ThetaMean.thetaMean ωd mH (delta A B Φ₁ Φ₂)) f₁ f₂ := by
    have hss' : petersson B mH (RallisIP.thetaLift ω m Φ₁ f₁) (RallisIP.thetaLift ω m Φ₂ f₂) = _ := hss
    rw [hss', GlobalTheory.Eis.dblInt, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun q => ?_)
    simp only [GlobalTheory.Eis.dblIntegrandQ, GlobalTheory.Eis.dblIntegrand, hpet, MonoidHom.inv_apply, Circle.coe_inv, inv_inv,
      RCLike.conj_conj]
    field_simp
  refine ⟨⟨i₁, l₁⟩, ⟨i₂, l₂⟩, hZF, ?_⟩
  rw [hval]
  exact hZV.2.valueAt

end UpperTheory.Lit.Rallis.RallisIPProof

end
end
