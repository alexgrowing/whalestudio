import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKAdd

theorem I_sub : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), G.M'.I om' (Φ - Ψ) = G.M'.I om' Φ - G.M'.I om' Ψ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ Ψ hΨ
  have hT := hM.triple
  have hPair := GlobalTheory.ThKContSmall.isPair_small hT
  have hSoΦ : Φ ∈ G.M'.So B.ψ B.τ₁ := (Submodule.mem_inf.1 hΦ).2
  have hSoΨ : Ψ ∈ G.M'.So B.ψ B.τ₁ := (Submodule.mem_inf.1 hΨ).2
  have hSΦ : Φ ∈ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ hSoΦ
  have hSΨ : Ψ ∈ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ hSoΨ
  have hv := GlobalTheory.ThKContSmall.measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
  have hpres : ∀ x, ∀ Φ₀ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ₀ ∈ schA F (Fin a' × Fin (a + a')) :=
    hT.weil'.isUSplitting.pres
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have hint : ∀ Φ₀ ∈ G.M'.So B.ψ B.τ₁, ∀ h, IntegrableOn (fun g => theta om' Φ₀ g h) G.M'.dom G.M'.μ := by
    intro Φ₀ hSo h
    have hS : Φ₀ ∈ schA F _ := GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ hSo
    have hB := (GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ₀ hS
    obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ₀ hSo 0
    refine Integrable.mono' (integrableOn_const (C := C * (ht h : ℝ) ^ k) hv.ne)
      ((hB.1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable) (ae_of_all _ fun g => ?_)
    have h1 := hC g h
    rw [pow_zero, mul_one] at h1
    exact h1
  funext h
  have e : ∀ g, theta om' (Φ - Ψ) g h = theta om' Φ g h - theta om' Ψ g h := by
    intro g
    have hA := summable_of_mem_schA F (hpres (g, h) Φ hSΦ)
    have hB' := summable_of_mem_schA F (hpres (g, h) Ψ hSΨ)
    simp only [theta, map_sub, thetaSum, Pi.sub_apply]
    exact hA.tsum_sub hB'
  simp only [Model.I, Pi.sub_apply, e]
  exact integral_sub (hint Φ hSoΦ h) (hint Ψ hSoΨ h)

end GlobalTheory.ThKAdd
