import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_restrictions_zero_of_minimalPrimes_over :
    ∀ (M : Scheme.{0}) (V W : M.Opens) (hW : IsAffineOpen W) (K : Type) [Field K],
    IsReduced (Γ(M, W) ⊗[ℤ] K) →
    (∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
      hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V) →
    ∀ (h : Γ(M, W) ⊗[ℤ] K),
    (∀ (W' : M.Opens), IsAffineOpen W' → ∀ hW' : W' ≤ W ⊓ V,
      LinearMap.rTensor K (M.presheaf.map (homOfLE (hW'.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap h = 0) →
    h = 0 := by
  intro M V W hW K _ hred hV h hh
  have key : ∀ q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K), h ∈ q := by
    intro q hq
    haveI : q.IsPrime := hq.1.1
    set p : PrimeSpectrum Γ(M, W) := PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom
      (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩ with hp
    have hxW : hW.fromSpec p ∈ W := by
      have h1 : hW.fromSpec p ∈ Set.range hW.fromSpec := ⟨p, rfl⟩
      rwa [hW.range_fromSpec] at h1
    have hxV : hW.fromSpec p ∈ V := hV q hq
    obtain ⟨f, hfle, hxf⟩ := hW.exists_basicOpen_le (V := W ⊓ V) ⟨hW.fromSpec p, hxW, hxV⟩ hxW
    have hfp : f ⊗ₜ[ℤ] (1 : K) ∉ q := by
      have h1 : p ∈ hW.fromSpec ⁻¹ᵁ M.basicOpen f := hxf
      rw [hW.fromSpec_preimage_basicOpen] at h1
      exact h1
    have h0 := hh (M.basicOpen f) (hW.basicOpen f) hfle
    let φ : Γ(M, W) →+* Γ(M, M.basicOpen f) :=
      (M.presheaf.map (homOfLE (hfle.trans inf_le_left)).op).hom
    letI : Algebra Γ(M, W) Γ(M, M.basicOpen f) := φ.toAlgebra
    haveI : IsLocalization.Away f Γ(M, M.basicOpen f) := hW.isLocalization_basicOpen f
    let g0 : Γ(M, W) →+* Localization.AtPrime q :=
      (algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q)).comp
        Algebra.TensorProduct.includeLeftRingHom
    have hu : IsUnit (g0 f) :=
      IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q) ⟨f ⊗ₜ[ℤ] (1 : K), hfp⟩
    let g1 : Γ(M, M.basicOpen f) →+* Localization.AtPrime q := IsLocalization.Away.lift f hu
    let g2 : K →+* Localization.AtPrime q :=
      (algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q)).comp
        Algebra.TensorProduct.includeRight.toRingHom
    let G : Γ(M, M.basicOpen f) ⊗[ℤ] K →ₐ[ℤ] Localization.AtPrime q :=
      Algebra.TensorProduct.lift (⟨g1, fun n => by simp⟩ : Γ(M, M.basicOpen f) →ₐ[ℤ] Localization.AtPrime q)
        (⟨g2, fun n => by simp⟩ : K →ₐ[ℤ] Localization.AtPrime q) (fun _ _ => Commute.all _ _)
    have hG : ∀ z : Γ(M, W) ⊗[ℤ] K,
        G (LinearMap.rTensor K φ.toAddMonoidHom.toIntLinearMap z) =
          algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a k =>
        rw [LinearMap.rTensor_tmul]
        have e1 : g1 (φ a) = g0 a := IsLocalization.Away.lift_eq f hu a
        change g1 (φ a) * g2 k = _
        rw [e1]
        simp only [g0, g2, RingHom.comp_apply, ← map_mul]
        congr 1
        simp
      | add x y hx hy => simp only [map_add, hx, hy]
    have hz : algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q) h = 0 := by
      rw [← hG h]
      change G (LinearMap.rTensor K φ.toAddMonoidHom.toIntLinearMap h) = 0
      rw [h0, map_zero]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ h).1 hz
    have hmq : (m : Γ(M, W) ⊗[ℤ] K) * h ∈ q := by rw [hm]; exact q.zero_mem
    exact (‹q.IsPrime›.mem_or_mem hmq).resolve_left m.2
  have hrad : h ∈ (⊥ : Ideal (Γ(M, W) ⊗[ℤ] K)).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr key
  obtain ⟨n, hn⟩ := hrad
  exact IsNilpotent.eq_zero ⟨n, Ideal.mem_bot.mp hn⟩

end GlobalTheory
