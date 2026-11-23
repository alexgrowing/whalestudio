import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_extScalars : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (A : Type) [CommRing A] (Y : Obj F 𝔠 (Sp A)), Nonempty Y.DetGen →
    (∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] A))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R₀ ⊗[ℤ] A).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A)) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ) →
    IsUnit ((6 : ℕ) : A) → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : A →+* B) (Y' : Obj F 𝔠 (Sp B)) (φ : Y'.A.left ⟶ Y.A.left),
    Y'.IsPullBy Y (spMap σ) φ → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y'.DetGen), s.val B Y' h δ = t.val B Y' h δ) := by
  intro F _ _ 𝔠 R₀ _ k s t A _ Y ⟨δ₀⟩ hst h6 B _ _ σ Y' φ hY' h δ
  let inr : A →ₐ[ℤ] R₀ ⊗[ℤ] A := Algebra.TensorProduct.includeRight
  let τ : R₀ ⊗[ℤ] A →ₐ[R₀] B :=
    Algebra.TensorProduct.lift (Algebra.ofId R₀ B) σ.toIntAlgHom fun _ _ ↦ Commute.all _ _
  have hτinr : (τ : R₀ ⊗[ℤ] A →+* B).comp inr.toRingHom = σ := by
    ext a
    simp [τ, inr]
  have hsp : spMap σ = spMap (τ : R₀ ⊗[ℤ] A →+* B) ≫ spMap inr.toRingHom := by
    rw [← hτinr]
    simp [spMap, Spec.map_comp]
  have h6C : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A) := by
    have := h6.map inr
    rwa [map_natCast] at this
  obtain ⟨YC, ψ, hYC⟩ := Obj.exists_isPullBy Y (spMap inr.toRingHom)
  obtain ⟨ψ', hψ', -⟩ := Obj.IsPullBy.cancel (hsp ▸ hY') hYC
  obtain ⟨δC, hδC, -⟩ := hYC.existsUnique_detGen inr.toRingHom δ₀
  obtain ⟨δB, hδB, -⟩ := hψ'.existsUnique_detGen (τ : R₀ ⊗[ℤ] A →+* B) δC
  have e1 := s.baseChange _ B τ YC h6C Y' h ψ' δC δB hψ' hδB
  have e2 := t.baseChange _ B τ YC h6C Y' h ψ' δC δB hψ' hδB
  have e3 := hst YC ψ hYC h6C δC
  have hB : s.val B Y' h δB = t.val B Y' h δB := by rw [e1, e2, e3]
  obtain ⟨c, hc⟩ : ∃ c : B, δB.1 = c • δ.1 := by
    have : δB.1 ∈ Submodule.span B {δ.1} := by rw [δ.2]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨c, hc.symm⟩
  rw [← s.homog B Y' h δ δB c hc, ← t.homog B Y' h δ δB c hc, hB]

end GlobalTheory.RealMult
