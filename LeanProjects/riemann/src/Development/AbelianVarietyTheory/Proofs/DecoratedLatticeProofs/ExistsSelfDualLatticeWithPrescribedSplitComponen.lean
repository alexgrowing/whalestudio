import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

namespace GlobalTheory.FrameGlob

open Matrix

theorem exists_gl_of_lattices {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] (Λ₁ Λ₂ : Submodule 𝒪[k] (n → k)) (h₁ : Λ₁.IsLattice k)
    (h₂ : Λ₂.IsLattice k) : ∃ g : GL n k, ∀ z, z ∈ Λ₁ ↔ g.val *ᵥ z ∈ Λ₂ := by
  have key : ∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsLattice k →
      ∃ e : (Fin (Fintype.card n) → k) ≃ₗ[k] (n → k), ∀ y, e y ∈ Λ ↔ ∀ i, y i ∈ 𝒪[k] := by
    intro Λ hΛ
    let b := Module.finBasisOfFinrankEq 𝒪[k] Λ (Submodule.IsLattice.finrank_of_pi k Λ)
    let b' := b.extendOfIsLattice k
    have hkey : ∀ c : Fin (Fintype.card n) → 𝒪[k],
        b'.equivFun.symm (fun i => (c i : k)) = ((∑ i, c i • b i : Λ) : n → k) := by
      intro c
      rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Module.Basis.extendOfIsLattice_apply]
      rfl
    refine ⟨b'.equivFun.symm, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
    · have h1 := hkey (b.repr ⟨_, h⟩)
      rw [b.sum_repr] at h1
      rw [← b'.equivFun.symm.injective h1]
      exact fun i => (b.repr ⟨_, h⟩ i).2
    · have h1 := hkey fun i => ⟨y i, h i⟩
      have h2 : b'.equivFun.symm y = _ := h1
      rw [h2]
      exact Subtype.property _
  obtain ⟨e₁, he₁⟩ := key Λ₁ h₁
  obtain ⟨e₂, he₂⟩ := key Λ₂ h₂
  let φ : (n → k) ≃ₗ[k] (n → k) := e₁.symm.trans e₂
  refine ⟨⟨LinearMap.toMatrix' φ.toLinearMap, LinearMap.toMatrix' φ.symm.toLinearMap, ?_, ?_⟩, fun z => ?_⟩
  · rw [← LinearMap.toMatrix'_mul]
    have : φ.toLinearMap * φ.symm.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_mul]
    have : φ.symm.toLinearMap * φ.toLinearMap = LinearMap.id := by ext; simp
    rw [this, LinearMap.toMatrix'_id]
  · show z ∈ Λ₁ ↔ LinearMap.toMatrix' φ.toLinearMap *ᵥ z ∈ Λ₂
    rw [LinearMap.toMatrix'_mulVec]
    have h := he₁ (e₁.symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.coe_coe, ← he₂]
    rfl

end GlobalTheory.FrameGlob

namespace GlobalTheory.FrameGlob

open Matrix

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  obtain ⟨hee, hec, -⟩ := p.split
  refine ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1 p.e).2 ?_
  rw [← hsum, add_mul, hee, mul_comm (cA D p.e), hec, add_zero]

theorem sec_eq_mul (p : SplitPt D k) (a : k) : p.sec a = p.e * p.sec a := by
  have h := p.sec_pr (p.sec a)
  rwa [p.pr_sec] at h

theorem sec_mem_idAt (p : SplitPt D k) (a : k) : p.sec a ∈ idAt D (· = p.v) := by
  rw [sec_eq_mul]
  exact Ideal.mul_mem_right _ _ (e_mem_idAt p)

variable {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem mt_gl_vec {p : SplitPt D k} (β : Frame p S n) (g : GL n k) (z : n → k) :
    mt S (β.gl g) *ᵥ (fun i => p.sec ((β.b *ᵥ z) i)) = fun i => p.sec ((β.b *ᵥ (g.val *ᵥ z)) i) := by
  funext i
  set m := mt S (β.gl g)
  set y : Fin S.rank → AE D := fun i => p.sec ((β.b *ᵥ z) i)
  have he : (m *ᵥ y) i = p.e * (m *ᵥ y) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show m i j * p.sec _ = p.e * (m i j * p.sec _)
    conv_lhs => rw [sec_eq_mul]
    ring
  have hpr : p.pr ((m *ᵥ y) i) = ((m.map p.pr) *ᵥ (β.b *ᵥ z)) i := by
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, y, p.pr_sec]
  rw [he, ← p.sec_pr, hpr, β.gl_mat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_assoc, β.b'b, Matrix.mul_one]

theorem mt_gl_off {p : SplitPt D k} (β : Frame p S n) (g : GL n k) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D (· ≠ p.v)) : mt S (β.gl g) *ᵥ y = y := by
  obtain ⟨ε, hε, hsum⟩ := p.above
  have h0 : (mt S (β.gl g) - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← β.gl_supp g i j, hsum]
    calc algebraMap (AF D.host.F) (AE D) ε * (mt S (β.gl g) - 1) i j * y j
        = (mt S (β.gl g) - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring
      _ = 0 := by rw [(GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).2 _ (hy j), mul_zero]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (L : Lat S)
    (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S L → Λ.IsLattice k →
    ∃ M : Lat S, IsSelfDualC S M ∧ β.IsLat M Λ ∧ latV S M (· ≠ p.v) = latV S L (· ≠ p.v) := by
  intro D k _ _ _ _ p S n _ _ β L Λ hL hΛ
  obtain ⟨Λ₁, hΛ₁, hLat₁, -⟩ := GlobalTheory.T.selfDual_splitComponent_isLattice_stabilizer_eq D k p S n β L hL
  obtain ⟨g, hg⟩ := exists_gl_of_lattices Λ₁ Λ hΛ₁ hΛ
  obtain ⟨M, hM, hMv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D S L hL).1 (β.gl g)
  have supp : ∀ (N : Lat S), IsSelfDualC S N → ∀ y, y ∈ latV S N (· ≠ p.v) → ∀ i, y i ∈ idAt D (· ≠ p.v) :=
    fun N hN y hy => (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ p.v)).2 S).2.2.2 N y hN.1 |>.1 hy).1
  refine ⟨M, hM, fun x => ?_, ?_⟩
  · have hx : x = g.val *ᵥ ((g⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [hx, ← hg, hLat₁, hMv (· = p.v) _ (fun i => sec_mem_idAt p _), mt_gl_vec]
  · ext y
    constructor
    · intro hy
      have hs := supp M hM y hy
      rw [← mt_gl_off β g y hs] at hy
      exact (hMv (· ≠ p.v) y hs).2 hy
    · intro hy
      have hs := supp L hL y hy
      have h := (hMv (· ≠ p.v) y hs).1 hy
      rwa [mt_gl_off β g y hs] at h

end GlobalTheory.FrameGlob
