import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMatchedDescentIdentityStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKLie

theorem lie_kills : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V', ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∀ Φ₁ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (∀ x, HasDerivAt (fun t : ℝ => om' (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → G.M'.I om' Φ₁ = 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hΦ₁ hd
  have hT := hM.triple
  have hPair := GlobalTheory.ThKContSmall.isPair_small hT
  have hSo : ∀ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Ψ ∈ G.M'.So B.ψ B.τ₁ := fun Ψ hΨ => (Submodule.mem_inf.1 hΨ).2
  have hS : ∀ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Ψ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun Ψ hΨ => GlobalTheory.ThKContSmall.so_le_schA hT.geo.hM' _ (hSo Ψ hΨ)
  have hv := GlobalTheory.ThKContSmall.measure_dom_lt_top hP.siegelSetUnitary hT.base hT.geo.hV' hT.geo.hM'
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsFiniteMeasure (G.M'.μ.restrict G.M'.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hv⟩
  have hL1 := GlobalTheory.T.theta_matched_descent_identity hP F E σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ hΦ₁ hd
  funext h
  have hconst : ∀ s : ℝ, ∫ g in G.M'.dom, theta om' Φ (g * γ (Multiplicative.ofAdd s)) h ∂G.M'.μ = G.M'.I om' Φ h := by
    intro s
    rw [← congrFun (GlobalTheory.T.matched_pair_theta_lattice_sum hP F E σ B a a' G X om om' R Rf hM (γ (Multiplicative.ofAdd s)) Φ hΦ) h]
    unfold Model.I theta
    congr 1
    funext g
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ₁ (hSo _ hΦ₁) 0
  obtain ⟨C0, k0, hC0⟩ := GlobalTheory.T.schwartz_orbit_decay hP F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair Φ (hSo _ hΦ) 0
  have hB1 := ((GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ₁ (hS _ hΦ₁)).1
  have hB0 := ((GlobalTheory.T.theta_basic_properties hP.base F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hPair).1 Φ (hS _ hΦ)).1
  have hcont : ∀ (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Continuous (fun x : UA σ G.V'.J × UA σ G.W.J => theta om' Ψ x.1 x.2) →
      ∀ c : UA σ G.V'.J, Continuous fun g : UA σ G.V'.J => theta om' Ψ (g * c) h := by
    intro Ψ hΨ c
    exact hΨ.comp ((continuous_mul_right c).prodMk continuous_const)
  have hder : ∀ (g : UA σ G.V'.J) (s : ℝ), HasDerivAt (fun t : ℝ => theta om' Φ (g * γ (Multiplicative.ofAdd t)) h)
      (theta om' Φ₁ (g * γ (Multiplicative.ofAdd s)) h) s := by
    intro g s
    have h1 := HasDerivAt.comp_sub_const (x := s) (a := s) (by rw [sub_self]; exact hL1 (g * γ (Multiplicative.ofAdd s)) h)
    have e : (fun t : ℝ => theta om' Φ (g * γ (Multiplicative.ofAdd t)) h) =
        fun t => theta om' Φ (g * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (t - s))) h := by
      funext t
      rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
    rw [e]
    exact h1
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := G.M'.μ.restrict G.M'.dom)
    (F := fun (s : ℝ) (g : UA σ G.V'.J) => theta om' Φ (g * γ (Multiplicative.ofAdd s)) h)
    (F' := fun (s : ℝ) (g : UA σ G.V'.J) => theta om' Φ₁ (g * γ (Multiplicative.ofAdd s)) h)
    (x₀ := 0) (s := Set.univ) (bound := fun _ => C * (ht h : ℝ) ^ k) Filter.univ_mem
    (Eventually.of_forall fun s => (hcont Φ hB0 _).aestronglyMeasurable)
    (Integrable.mono' (integrable_const (C0 * (ht h : ℝ) ^ k0))
      (hcont Φ hB0 _).aestronglyMeasurable (ae_of_all _ fun g => by
        have e := hC0 (g * γ (Multiplicative.ofAdd 0)) h
        rw [pow_zero, mul_one] at e
        exact e))
    (hcont Φ₁ hB1 _).aestronglyMeasurable
    (ae_of_all _ fun g s _ => by
        have e := hC (g * γ (Multiplicative.ofAdd s)) h
        rw [pow_zero, mul_one] at e
        exact e)
    (integrable_const _)
    (ae_of_all _ fun g s _ => hder g s)
  have key2 := key.2
  simp only [hconst] at key2
  have e0 := key2.unique (hasDerivAt_const (0 : ℝ) (G.M'.I om' Φ h))
  simp only [ofAdd_zero, map_one, mul_one] at e0
  exact e0

end GlobalTheory.ThKLie

end
