import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralLocalDominatedStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaIntCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_le_schA {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, hSB, hvac, rfl⟩
  refine GlobalTheory.TensUniq.pure_mem_schA f φ hSB ?_
  filter_upwards [hvac, hM.std] with v h1 h2
  rw [h1, h2]

theorem isPair_of_isTriple {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) where
  base := hT.base
  herm := hT.geo.hV
  skew := hT.geo.hW
  good := hT.geo.hM
  hX := hT.chars.heckeβ
  hW := by
    refine ⟨?_, fun x => ?_⟩
    · exact hT.chars.heckeβ.1.div' hT.chars.heckeα.1
    · rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]
  resX := hT.chars.resβ
  weil := hT.weil
  resW := fun u => by
    rw [MonoidHom.div_apply, Circle.coe_div, hT.chars.resβ u, hT.chars.resα u]
    split_ifs
    · simp
    · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, pow_add]

theorem cont_inv (hdom : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ ∈ schA F (Fin a × Fin (a + a')), ∀ h₀ : UA σ G.W.J, ∃ U ∈ 𝓝 h₀, ∃ bound : UA σ G.V.J → ℝ,
      IntegrableOn bound G.M.dom G.M.μ ∧ ∀ h ∈ U, ∀ᵐ g ∂(G.M.μ.restrict G.M.dom), ‖theta om Φ g h‖ ≤ bound g) : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ ∈ PolData B G.M,
      Continuous (G.M.I om Φ) ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M.I om Φ (γ * h) = G.M.I om Φ h := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT Φ hΦ
  have hS : Φ ∈ schA F _ := polData_le_schA hT.geo.hM hΦ
  obtain ⟨hb, -⟩ := GlobalTheory.T.theta_basic_properties hKP.base F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ (isPair_of_isTriple hT)
  obtain ⟨hcont, hinv, -⟩ := hb Φ hS
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  refine ⟨?_, fun γ hγ h => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro h₀
    haveI : SecondCountableTopology (UA σ G.W.J) := (GlobalTheory.AdelicUnitaryTop.lcsc_UA F E σ (a + a') G.W.J).2.1
    haveI : FirstCountableTopology (UA σ G.W.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
    obtain ⟨U, hU, bound, hbi, hbd⟩ := hdom hKP F E σ B a a' G X om om' hT Φ hS h₀
    refine continuousAt_of_dominated ?_ ?_ hbi ?_
    · exact Eventually.of_forall fun h =>
        (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [hU] with h hh using hbd h hh
    · exact Eventually.of_forall fun g => (hcont.comp (continuous_const.prodMk continuous_id)).continuousAt
  · unfold Model.I
    congr 1
    funext g
    simpa using hinv 1 (one_mem _) γ hγ g h

theorem continuous_and_invariant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ Φ ∈ PolData B G.M,
      Continuous (G.M.I om Φ) ∧ ∀ γ ∈ ratU σ G.W.J, ∀ h, G.M.I om Φ (γ * h) = G.M.I om Φ h :=
  cont_inv GlobalTheory.T.theta_integral_local_dominated

end GlobalTheory.ThetaIntCont
