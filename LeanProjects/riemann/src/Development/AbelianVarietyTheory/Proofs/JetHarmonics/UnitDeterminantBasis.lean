import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs

open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.UnitDeterminantBasis

theorem det_ne_zero {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O]
    [Algebra k O] [IsDomain O] {n : ℕ} {e : A}
    (b : Module.Basis (Fin n) k (LinearMap.range (LinearMap.mulLeft k e)))
    (T : Fin n → (A →ₐ[k] O)) (hT : Function.Injective T) (hTe : ∀ j, T j e = 1) :
    (Matrix.of fun i j => T j (b i : A)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hc0
  have hli := (linearIndependent_algHom_toLinearMap k A O).comp T hT
  rw [Fintype.linearIndependent_iff] at hli
  funext j
  refine hli c ?_ j
  have h1 : (∑ j, c j • (T j).toLinearMap) ∘ₗ
      (LinearMap.range (LinearMap.mulLeft k e)).subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simpa [LinearMap.sum_apply, mul_comm] using this
  ext a
  have h2 := LinearMap.congr_fun h1 ⟨e * a, a, rfl⟩
  simpa [LinearMap.sum_apply, hTe] using h2

theorem exists_basis_isUnit_det : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R], v.Integers R → (∀ σ σ' : OE →+* R, (∀ a : OE, v (algebraMap R C (σ a - σ' a)) < 1) → σ = σ') → ∀ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE) (t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e), ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)), IsUnit (Matrix.det (Matrix.of fun i j => ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e) : OE →+* R) (b i : TensorProduct ℤ ℤ_[p] OE))) := by
  intro p _ OE _ _ _ C _ v R _ _ _ hv hsep w t
  let b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) :=
    Module.finBasisOfFinrankEq _ _ rfl
  refine ⟨b, ?_⟩
  by_contra hx
  obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits hx
  have hMp : M.IsPrime := hM.isPrime
  let T : Fin w.n → (TensorProduct ℤ ℤ_[p] OE →ₐ[ℤ_[p]] R ⧸ M) := fun j =>
    (Ideal.Quotient.mkₐ ℤ_[p] M).comp (AvDefs.tauExt ((t j : AvDefs.Emb (O := R) w.e) : OE →+* R))
  refine det_ne_zero b T ?_ ?_ ?_
  · intro j j' h
    apply t.injective
    apply Subtype.ext
    refine hsep _ _ fun a => ?_
    have h1 := DFunLike.congr_fun h (1 ⊗ₜ a)
    have h2 : ((t j : AvDefs.Emb (O := R) w.e) : OE →+* R) a -
        ((t j' : AvDefs.Emb (O := R) w.e) : OE →+* R) a ∈ M := by
      rw [← Ideal.Quotient.eq]
      simpa [T, AvDefs.tauExt] using h1
    refine lt_of_le_of_ne (hv.map_le_one _) fun h3 => ?_
    exact hM.ne_top (M.eq_top_of_isUnit_mem h2 (hv.isUnit_iff_valuation_eq_one.2 h3))
  · intro j
    have h1 : AvDefs.tauExt ((t j : AvDefs.Emb (O := R) w.e) : OE →+* R) w.e = 1 := (t j).2
    simp only [T, AlgHom.comp_apply, h1, map_one]
  · have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hxM
    rw [RingHom.map_det] at h1
    exact h1

end GlobalTheory.UnitDeterminantBasis
