import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnipotentCosetParametrizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingIntegralCosetRepresentativesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ThK.Unfold

theorem measurable_mul_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) : Measurable (fun x : UA σ J => g * x) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  exact (continuous_const.mul continuous_id).measurable

theorem countable_ratU {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  have h1 : Countable (GL (Fin n) E) := by
    haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
    exact Function.Injective.countable (f := fun u : GL (Fin n) E => (u : Matrix (Fin n) (Fin n) E))
      (fun u v huv => Units.ext huv)
  have h2 : Countable ((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range) :=
    (Set.countable_range _).to_subtype
  refine Function.Injective.countable (f := fun x : ratU σ J =>
    (⟨x.1.1, x.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range)) ?_
  intro x y hxy
  exact Subtype.ext (Subtype.ext (Subtype.mk.inj hxy))

theorem integral_tsum_isotropic_eq : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ γ : {x : Fin (b + 2) → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → UA σ G.V.J,
      (∀ x, γ x ∈ ratU σ G.V.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x) →
    ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ →
    ∀ Φ ∈ PolData B G.M, ∀ h,
      ∫ g in G.M.dom, ∑' x, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ))) ∂G.M.μ = ∫ g in 𝓓, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ))) ∂G.M.μ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ γ hγ 𝓓 h𝓓 Φ hΦ h
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI := hT.geo.hM.haar
  have hx0 : form σ G.V.J H.x H.x = 0 := hC.hH.xx
  have hx0ne : H.x ≠ 0 := by
    intro h0
    have := hC.hH.xy
    rw [h0] at this
    simp [form] at this
  exact GlobalTheory.T.unfolding_integral_coset_representatives G.M.μ (measurable_mul_left σ G.V.J) (ratU σ G.V.J) _ (countable_ratU σ G.V.J) inf_le_left G.M.dom 𝓓
    hT.geo.hM.dom h𝓓 γ (fun x => (hγ x).1) (GlobalTheory.T.rational_unipotent_coset_parametrization F E σ G.V.J H.x hx0 hx0ne γ hγ) _
    (GlobalTheory.T.doubling_eigen_intertwiner_triple_first hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h)
    (GlobalTheory.T.doubling_eigen_intertwiner_triple_second hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ 𝓓 h𝓓 Φ hΦ h)

end GlobalTheory.ThK.Unfold
