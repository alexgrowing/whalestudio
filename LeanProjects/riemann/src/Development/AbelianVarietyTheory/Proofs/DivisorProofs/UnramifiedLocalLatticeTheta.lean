import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGoodPlaceIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentInvariantFunctionalInducedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentInvariantFunctionalTwoDimStatement

noncomputable section

namespace GlobalTheory.JacBlock₂

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem jacquet_position_coeff : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ Λ : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ z ∈ augAt om' v, Λ z = 0) → (∀ n ∈ unip σ G.W H', n ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, n)) φ φ₁ → Λ φ₁ = Λ φ) → ∀ ψ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ p q : ℂ, ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → ∀ ψ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, m)) ψ ψ₁ → Λ ψ₁ = p * ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) + q * ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' v hv w hw Λ hΛaug hΛN ψ hψ
  obtain ⟨ι, ν₀, e, hsm, hun, hbij, hrank, hV', hN, hLevi, hchar⟩ := GlobalTheory.T.triple_local_good_place_intertwiner hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' v hv w hw

  set S := SB (Fin a' × Fin (a + a') → Fv F v)
  set Sm := SB (Matrix (Fin a') (Fin (a + a')) (Fv F v))
  let ιR : S →ₗ[ℂ] Sm := (ι.domRestrict S).codRestrict Sm (fun φ => hbij.mapsTo φ.2)
  have hιR : Function.Bijective ιR := by
    refine ⟨fun φ φ' h => Subtype.ext (hbij.injOn φ.2 φ'.2 (congrArg Subtype.val h)), fun Ψ => ?_⟩
    obtain ⟨φ, hφ, hφΨ⟩ := hbij.surjOn Ψ.2
    exact ⟨⟨φ, hφ⟩, Subtype.ext hφΨ⟩
  let eR := LinearEquiv.ofBijective ιR hιR
  obtain ⟨Λ₀, hΛ₀⟩ := LinearMap.exists_extend ((Λ.comp S.subtype).comp eR.symm.toLinearMap)
  have key : ∀ φ ∈ S, Λ₀ (ι φ) = Λ φ := by
    intro φ hφ
    have h1 := congrArg (fun f => f (ιR ⟨φ, hφ⟩)) hΛ₀
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    have h2 : eR.symm (ιR ⟨φ, hφ⟩) = ⟨φ, hφ⟩ := eR.symm_apply_apply ⟨φ, hφ⟩
    rw [show (ιR ⟨φ, hφ⟩ : Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ) = ι φ from rfl] at h1
    rw [h1]
    simp only [LinearEquiv.coe_coe, h2]
  have hlt : a' < a := hT.geo.lt
  have ha' : 1 ≤ a' := by have := hT.geo.aBig; omega
  have hB := GlobalTheory.T.unipotent_invariant_functional_two_dim GlobalTheory.T.unipotent_invariant_functional_induced hKP (Fv F v) a' (a + a') ν₀ ha' (by omega) hsm hun Λ₀
    (by
      intro g₀ Ψ hΨ
      obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ
      obtain ⟨g, hg, hgact⟩ := hV' g₀
      obtain ⟨φ₁, hφ₁, hact, heq⟩ := hgact φ hφ
      rw [← heq, map_sub, key φ₁ hφ₁, key φ hφ, ← map_sub]
      exact hΛaug _ (Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hact, rfl⟩))
    (by
      intro u hu Ψ hΨ
      obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ
      obtain ⟨n, hn, hnU, hnact⟩ := hN u hu
      obtain ⟨φ₁, hφ₁, hact, heq⟩ := hnact φ hφ
      rw [← heq, key φ₁ hφ₁, key φ hφ]
      exact hΛN n hn hnU φ hφ φ₁ hφ₁ hact)
    hrank
  obtain ⟨p, q, hpq⟩ := hB (ι ψ) (hbij.mapsTo hψ)
  refine ⟨p, q, fun x m hm ψ₁ hψ₁ hact => ?_⟩
  rw [← key ψ₁ hψ₁, hLevi x m hm ψ hψ ψ₁ hψ₁ hact, map_smul, hpq (e x), smul_eq_mul, ← hchar x]
  ring

end GlobalTheory.JacBlock₂
