import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsLowInv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

section Mat

variable {R : Type} [CommRing R] {m : ℕ}

theorem IsLowInv.of_mul_eq_one {N L : Matrix (Fin m) (Fin m) R} (hL : IsLowInv L) (hN : ∀ i j, i < j → N i j = 0)
    (h : N * L = 1) : IsLowInv N := by
  refine ⟨hN, fun i => ?_⟩
  have e : (N * L) i i = N i i * L i i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [hL.1 k i h', mul_zero]
    · rw [hN i k h', zero_mul]
  rw [h, Matrix.one_apply_eq] at e
  exact ⟨⟨N i i, L i i, e.symm, by rw [mul_comm]; exact e.symm⟩, rfl⟩

theorem InCell.exists_lowInv {A A' : Matrix (Fin m) (Fin m) R} {w : Equiv.Perm (Fin m)} {a : Above m → R}
    (h : InCell A w a) (h' : InCell A' w a) : ∃ M, IsLowInv M ∧ A' = M * A := by
  obtain ⟨L, hL, e⟩ := h
  obtain ⟨L', hL', e'⟩ := h'
  have hd := isUnit_det_of_isLowInv hL
  haveI := Matrix.invertibleOfIsUnitDet L hd
  have hinv : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hd
  have hlow : ∀ i j, i < j → L⁻¹ i j = 0 := fun i j hij =>
    Matrix.blockTriangular_inv_of_blockTriangular hL.blockTriangular (OrderDual.toDual_lt_toDual.2 hij)
  refine ⟨L' * L⁻¹, hL'.mul (IsLowInv.of_mul_eq_one hL hlow hinv), ?_⟩
  have hs : ∀ X : Matrix (Fin m) (Fin m) R, (X * A).submatrix id w = X * A.submatrix id w := fun X => by
    ext i j
    simp [Matrix.mul_apply]
  have key : A'.submatrix id w = (L' * L⁻¹ * A).submatrix id w := by
    rw [hs, e, e', Matrix.mul_assoc, ← Matrix.mul_assoc L⁻¹, hinv, Matrix.one_mul]
  ext i j
  simpa using congrFun (congrFun key i) (w.symm j)

end Mat

section Pt

theorem frameIn_tri : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}, ∀ {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) {R R' : Type} [CommRing R] [CommRing R'] (ν : R →+* R') (ψ : Γ(gen Z, V) →+* R) {x : Sp R ⟶ gen Z} (hx : spMap ψ ≫ hV.fromSpec = x) {x' : Sp R' ⟶ gen Z} (hx' : spMap (ν.comp ψ) ≫ hV.fromSpec = x') (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)) (g' : EigFrame Z ((ν.comp ψ).comp φV) (x' ≫ genι Z)) (a : Cell.Coord Dw → R), Cell.FrameIn hV f₀ w ψ hx g a → Cell.FrameIn hV f₀ w (ν.comp ψ) hx' g' (ν ∘ a) → ∃ t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ, g.Tri ν g' t := by
  intro E _ _ _ H Dw l Xo c O _ β Z V hV φV f₀ w R R' _ _ ν ψ x hx x' hx' g g' a hg hg'
  obtain ⟨A, hA, hAc⟩ := hg
  obtain ⟨A', hA', hAc'⟩ := hg'
  have hxx : x' = spMap ν ≫ x := by
    rw [← hx', ← hx, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  have hxg : spMap ν ≫ (x ≫ genι Z) = x' ≫ genι Z := by rw [hxx, Category.assoc]
  have hφ : (ν.comp ψ).comp φV = ν.comp (ψ.comp φV) := RingHom.comp_assoc _ _ _
  obtain ⟨g₁, hg₁⟩ := g.exists_isMap (x' := x' ≫ genι Z) ν hφ (by rw [hxx, Category.assoc])
  have hv₁ : ∀ τ j, g₁.vec τ j = GlobalTheory.LieLocFrame.res ν hxg (g.vec τ j) := fun τ j =>
    GlobalTheory.LieMet.tan_ext (hg₁ τ j)
  have h0 : spMap ψ ≫ hV.fromSpec ≫ genι Z = x ≫ genι Z := by rw [← hx, Category.assoc]
  have h1 : spMap (ν.comp ψ) ≫ hV.fromSpec ≫ genι Z = x' ≫ genι Z := by rw [← hx', Category.assoc]
  have hr : ∀ τ k, GlobalTheory.LieLocFrame.res ν hxg (GlobalTheory.LieLocFrame.res ψ h0 (f₀.vec τ k)) =
      GlobalTheory.LieLocFrame.res (ν.comp ψ) h1 (f₀.vec τ k) := fun τ k =>
    GlobalTheory.LieLocFrame.res_res ψ h0 ν hxg rfl h1 _
  choose M hM hMA using fun τ => InCell.exists_lowInv ((hAc τ).map ν) (hAc' τ)
  have hvec : ∀ τ i, g'.vec τ i = ∑ j, M τ i j • g₁.vec τ j := by
    intro τ i
    simp only [hv₁, hA, GlobalTheory.LieLocFrame.res_sum, hr, hA', hMA τ, Matrix.mul_apply, Matrix.map_apply, Finset.smul_sum,
      smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hco : ∀ τ, g₁.co g' τ = (M τ).transpose := fun τ =>
    EigFrame.co_eq fun i => (GlobalTheory.LieMet.isComb_iff (g₁.vec τ) _ (g'.vec τ i)).2 (hvec τ i)
  refine ⟨fun τ i => ((hM τ).2 i).unit, ?_, hφ, fun τ i =>
    ⟨fun k => g₁.co g' τ k i, ?_, fun k hk => ?_, ?_⟩⟩
  · rw [hxx, Category.assoc]
  · rw [hco]; exact ((hM τ).2 i).unit_spec.symm
  · rw [hco]; exact (hM τ).1 i k hk
  · rw [← funext (hg₁ τ)]
    exact g₁.co_spec g' τ i

end Pt

end GlobalTheory.ShFam.Cell
