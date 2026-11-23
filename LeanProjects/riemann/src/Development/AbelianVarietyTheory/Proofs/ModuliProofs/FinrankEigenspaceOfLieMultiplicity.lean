import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.UnifEigenRank

theorem finrank_of_existsUnique {k V : Type} [Field k] [AddCommGroup V] [Module k V] (E : Submodule k V) {n : ℕ}
    (W : Fin n → V) (hW : ∀ i, W i ∈ E) (h : ∀ z ∈ E, ∃! c : Fin n → k, z = ∑ i, c i • W i) :
    Module.finrank k E = n := by
  let W' : Fin n → E := fun i => ⟨W i, hW i⟩
  have hc : ∀ c : Fin n → k, ((Fintype.linearCombination k W' c : E) : V) = ∑ i, c i • W i := fun c => by
    simp [Fintype.linearCombination_apply, W']
  have hb : Function.Bijective (Fintype.linearCombination k W') := by
    refine (Function.bijective_iff_existsUnique _).2 fun z => ?_
    refine (existsUnique_congr fun c => ?_).1 (h z z.2)
    rw [Subtype.ext_iff, hc, eq_comm]
  rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_fin_fun]

end GlobalTheory.UnifEigenRank

open GlobalTheory.UnifLieBasis in
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD isTan_iff isLieComb_iff isTan_scale) in

theorem GlobalTheory.UnifEigenRank.finrank_eigenspace_of_lieMult : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : Type) [CommRing O] (act : OAct O P₀.A) (F : O → Module.End ℂ (Fin P₀.g → ℂ)), (∀ a z, u.ex (F a z) = u.ex z ≫ act.act a) → ∀ (τ : O →+* ℂ) (n : ℕ), LieMult act (𝟙 _) τ n → Module.finrank ℂ ↥(⨅ a, Module.End.eigenspace (F a) (τ a)) = n := by
  intro P₀ u Hm χ hu O _ act F hF τ n hn
  have := act.hom
  let j : epsPt (𝟙 (Sp ℂ)) ≅ epsR ℂ := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp ℂ)) ⟶ P₀.A) ≃* (epsR ℂ ⟶ P₀.A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl P₀.A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have one : (1 : Over.mk (𝟙 (Sp ℂ)) ⟶ P₀.A).left = η[P₀.A].left := Category.id_comp _
  obtain ⟨v, hv, hb⟩ := LiePull.basis_transport e (P := IsLieEigen act (𝟙 _) τ)
    (R := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R' := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (Q := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he, one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he]
      rfl))
    (fun c u v => by rw [he, he]; rfl) n hn
  have key : ∀ (z : Fin P₀.g → ℂ) (w : epsR ℂ ⟶ P₀.A), IsTangent w → u.IsDiff z w →
      ((∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w) ↔
        z ∈ ⨅ a, Module.End.eigenspace (F a) (τ a)) := by
    intro z w hw hd
    rw [Submodule.mem_iInf]
    refine forall_congr' fun a => ?_
    rw [Module.End.mem_eigenspace_iff]
    have h1 : u.IsDiff (F a z) (w ≫ act.act a) :=
      isDiff_comp u (act.act a) (LinearMap.toContinuousLinearMap (F a)) (hF a) hw hd
    have h2 := isDiff_smul u ((isTan_iff _).2 hw) hd (τ a)
    have t1 := isTangent_comp (act.act a) hw
    have t2 := (isTan_iff _).1 (isTan_scale (τ a) ((isTan_iff _).2 hw))
    constructor
    · intro h
      exact (hu.tan₁ _ t1).unique h1 (by rw [h]; exact h2)
    · intro h
      rw [h] at h1
      exact (hu.tan₂ _).unique ⟨t1, h1⟩ ⟨t2, h2⟩
  choose W hW using fun i => (hu.tan₁ (v i) (hv i).1).exists
  have ht : ∀ i, Chart.IsTan (R := ℂ) (G := P₀.A) (v i) := fun i => (isTan_iff _).2 (hv i).1
  have hp : ∀ c : Fin n → ℂ, IsTangent (prodPts (R := ℂ) (G := P₀.A) c v) ∧
      u.IsDiff (∑ i, c i • W i) (prodPts (R := ℂ) (G := P₀.A) c v) := by
    intro c
    obtain ⟨a, b⟩ := isDiff_list_prod u (fun i => c i • W i) _
      (fun i => isTan_scale (c i) (ht i)) (fun i => isDiff_smul u (ht i) (hW i) (c i))
    exact ⟨(isTan_iff _).1 a, b⟩
  refine UnifEigenRank.finrank_of_existsUnique _ W (fun i => (key _ _ (hv i).1 (hW i)).1 (hv i).2) fun z hz => ?_
  obtain ⟨w, hw, hd⟩ := (hu.tan₂ z).exists
  refine (existsUnique_congr fun c => ?_).1 (hb w ⟨hw, (key _ _ hw hd).2 hz⟩)
  refine Iff.trans (isLieComb_iff c v w) ⟨fun h => ?_, fun h => ?_⟩
  · exact (hu.tan₁ _ hw).unique hd (by rw [h]; exact (hp c).2)
  · rw [h] at hd
    exact (hu.tan₂ _).unique ⟨hw, hd⟩ (hp c)
