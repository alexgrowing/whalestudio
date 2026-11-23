import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleSplitCharactersExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePolynomialLocalFunctionalsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThetaAtGood

set_option maxHeartbeats 2000000 in

theorem thetaIntegral_eq_sum_intertw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ B₀ : GL (Fin (a + a')) (Fv F B.v₁), ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = a + a') (χ : Fin 2 → (Fv F B.v₁)ˣ →* ℂˣ),
      ((b 0 = a ∧ b 1 = a') ∨ (b 0 = a' ∧ b 1 = a)) ∧ (∀ j, IsUnram (χ j)) ∧ (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) ∧
      ∃ (m : ℕ) (T : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ))
        (x : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ))),
        (∀ j, IsIntertw σ (c • G.W.J.map σ) B.τ₁ B₀ (pairInd (Fv F B.v₁) b hb χ) (T j)) ∧
        (fun y => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm y)) = ∑ j, T j (x j) := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hK hT c hc hσc Φ hΦ B₀
  obtain ⟨b, hb, χ, hbl, hun, hu, P, honto, hker, heq⟩ := GlobalTheory.T.triple_split_characters_exist F E σ hσ B a a' G X om om' hK hT c hc hσc
  obtain ⟨m, L, φ, hφ, hkill, hequiv, hsum⟩ := GlobalTheory.T.triple_polynomial_local_functionals F E σ hσ B a a' G X om om' hK hT c hc hσc Φ hΦ
  let K := Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁)
  generalize hπ : pairInd (Fv F B.v₁) b hb χ = π at heq ⊢
  let P' := P.domRestrict K
  have hsurj : Function.Surjective P' := by
    intro ξ
    obtain ⟨φ₀, h₀, rfl⟩ := honto ξ
    exact ⟨⟨φ₀, Submodule.subset_span h₀⟩, rfl⟩
  have hle : ∀ j, LinearMap.ker P' ≤ LinearMap.ker ((L j).comp K.subtype) := by
    intro j z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have hz' := hker z.1 z.2 hz
    have : Submodule.span ℂ {z | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁,
            ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om' (g, 1)) φ₀ φ₁ ∧ z = φ₁ - φ₀}
          ≤ LinearMap.ker (L j) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, hg, φ₀, h₀, φ₁, h₁, hA, rfl⟩
      simp [hkill j g hg φ₀ h₀ φ₁ h₁ hA]
    exact this hz'
  let e := P'.quotKerEquivOfSurjective hsurj
  let T1 : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ) :=
    fun j => ((LinearMap.ker P').liftQ ((L j).comp K.subtype) (hle j)).comp e.symm.toLinearMap
  have hT1 : ∀ j, ∀ φ₀ (h₀ : φ₀ ∈ K), T1 j (P φ₀) = L j φ₀ := by
    intro j φ₀ h₀
    have : P φ₀ = e (Submodule.Quotient.mk ⟨φ₀, h₀⟩) := by
      rw [LinearMap.quotKerEquivOfSurjective_apply_mk]; rfl
    simp only [T1, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearEquiv.symm_apply_apply,
      Submodule.liftQ_apply, Submodule.coe_subtype]
  refine ⟨b, hb, χ, hbl, hun, hu, m, fun j => (T1 j).comp (π B₀), fun j => π B₀⁻¹ (P (φ j)), ?_, ?_⟩
  · intro j g x hx w y
    simp only [LinearMap.comp_apply, hπ]
    have hx' : IsCompAt σ (c • G.W.J.map σ) B.τ₁ 1 (B₀ * g * B₀⁻¹) x := by
      unfold IsCompAt at hx ⊢
      rw [hx]; simp
    obtain ⟨φ₀, h₀, hφ₀⟩ := honto (π B₀ w)
    have hh := heq (B₀ * g * B₀⁻¹) x hx' φ₀ h₀
    obtain ⟨φ₁, hh⟩ := hh
    obtain ⟨h₁, hh⟩ := hh
    obtain ⟨hA, hP⟩ := hh
    have hgg : B₀ * g * B₀⁻¹ * B₀ = B₀ * g := by group
    have e1 : π B₀ (π g w) = π (B₀ * g * B₀⁻¹) (π B₀ w) := by
      calc π B₀ (π g w) = (π B₀ * π g) w := (Module.End.mul_apply _ _ _).symm
        _ = π (B₀ * g) w := by rw [← map_mul]
        _ = (π (B₀ * g * B₀⁻¹) * π B₀) w := by rw [← map_mul π, hgg]
        _ = π (B₀ * g * B₀⁻¹) (π B₀ w) := Module.End.mul_apply _ _ _
    have hS : φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) := h₁.1
    have k1 := hT1 j φ₁ (Submodule.subset_span h₁)
    have k2 := hT1 j φ₀ (Submodule.subset_span h₀)
    have k3 := hequiv j x φ₀ h₀ φ₁ hS hA
    rw [e1, ← hφ₀, ← hP, k1, k2, k3]
  · refine hsum.trans (Finset.sum_congr rfl fun j _ => ?_)
    have h3 : π B₀ (π B₀⁻¹ (P (φ j))) = P (φ j) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    show L j (φ j) = T1 j (π B₀ (π B₀⁻¹ (P (φ j))))
    rw [h3, hT1 j _ (Submodule.subset_span (hφ j))]

end GlobalTheory.ThetaAtGood
