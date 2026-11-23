import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmitsurCohomologyH1

noncomputable def d0 (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] :
    D' →ₗ[D] D' ⊗[D] D' :=
  TensorProduct.mk D D' D' 1 - (TensorProduct.mk D D' D').flip 1

theorem amitsur_d0_apply (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D'] (a : D') :
    d0 D D' a = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  simp [d0]

theorem cocycle_is_coboundary : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (c : D' ⊗[D] D'),
    (∀ (E : Type) [CommRing E] [Algebra D E] (f₁ f₂ f₃ : D' →ₐ[D] E),
      Algebra.TensorProduct.lift f₁ f₃ (fun _ _ ↦ Commute.all _ _) c =
        Algebra.TensorProduct.lift f₁ f₂ (fun _ _ ↦ Commute.all _ _) c +
          Algebra.TensorProduct.lift f₂ f₃ (fun _ _ ↦ Commute.all _ _) c) →
    ∃ a : D', c = (1 : D') ⊗ₜ[D] a - a ⊗ₜ[D] (1 : D') := by
  intro D D' _ _ _ _ c hc
  let i1 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') := Algebra.TensorProduct.includeLeft
  let i2 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeLeft
  let i3 : D' →ₐ[D] D' ⊗[D] (D' ⊗[D] D') :=
    (Algebra.TensorProduct.includeRight).comp Algebra.TensorProduct.includeRight
  have h := hc (D' ⊗[D] (D' ⊗[D] D')) i1 i2 i3
  have k1 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i1 i3 (fun _ _ ↦ Commute.all _ _) x -
        Algebra.TensorProduct.lift i1 i2 (fun _ _ ↦ Commute.all _ _) x =
        LinearMap.lTensor D' (d0 D D') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i1, i2, i3, amitsur_d0_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, ← hx, ← hy]; abel
  have k2 : ∀ x : D' ⊗[D] D',
      Algebra.TensorProduct.lift i2 i3 (fun _ _ ↦ Commute.all _ _) x = (1 : D') ⊗ₜ[D] x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      rw [map_add, hx, hy, TensorProduct.tmul_add]
  have key : (1 : D') ⊗ₜ[D] c = LinearMap.lTensor D' (d0 D D') c := by
    rw [← k1, ← k2, h]; abel
  let q := (LinearMap.range (d0 D D')).mkQ
  have hq : (1 : D') ⊗ₜ[D] q c = 0 := by
    have : (1 : D') ⊗ₜ[D] q c = LinearMap.lTensor D' q ((1 : D') ⊗ₜ[D] c) := by simp
    rw [this, key, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have hz : q ∘ₗ d0 D D' = 0 := by
      ext a; simp [q]
    rw [hz]; simp
  have hq0 : q c = 0 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff D _ (A := D') _).1 hq
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hq0
  exact ⟨a, by rw [← ha, amitsur_d0_apply]⟩

end GlobalTheory.AmitsurCohomologyH1
