import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

namespace GlobalTheory.HTLat.Point

theorem smul_latTQuot_le_latT : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C) {n : ℕ} (r : Fin n → O) (a : Fin n → 𝓞 E), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then d else 0) → ∀ {w : P.V}, w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ → d • w ∈ P.latT := by
  intro p _ C _ _ _ _ O _ _ _ _ _ E _ _ _ P φ d n r a hsum w hw
  obtain ⟨y, hy, rfl⟩ := hw
  have hact : ∀ (b : 𝓞 E) (x : P.V), x ∈ P.latT → P.actV b x ∈ P.latT := by
    intro b x hx
    obtain ⟨s, rfl⟩ := hx
    induction s using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | tmul c t => exact ⟨c ⊗ₜ P.actT b t, by rw [P.inclT_tmul, P.inclT_tmul]; rfl⟩
  have e : d • idem (isSplitting_embO P.integers) φ =
      ∑ k, algebraMap O C (r k) ⊗ₜ[ℤ] a k := (isSplitting_embO P.integers).1 (by
    ext ψ
    rw [map_smul, splitMap_idem, map_sum, Finset.sum_apply]
    simp only [splitMap_tmul, RingHom.comp_apply, algebraMap_embO, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul]
    rw [hsum ψ]
    split_ifs <;> simp)
  change d • proj (isSplitting_embO P.integers) P.actV φ y ∈ P.latT
  rw [proj, ← LinearMap.smul_apply, ← map_smul, e, map_sum, LinearMap.sum_apply]
  refine P.latT.sum_mem fun k _ => ?_
  rw [tensorAction_tmul, algebraMap_smul]
  exact P.latT.smul_mem _ (hact _ _ hy)

end GlobalTheory.HTLat.Point
