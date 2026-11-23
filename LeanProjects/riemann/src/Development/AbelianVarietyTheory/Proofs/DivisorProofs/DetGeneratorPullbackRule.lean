import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem tensorEval_includeRight_comp {R₀ A B : Type} [CommRing R₀] [CommRing A] [CommRing B] (ρ : A →+* B)
    (d : R₀ ⊗[ℤ] A) :
    tensorEval ((Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := B)).toRingHom.comp ρ) d =
      TensorProduct.comm ℤ B R₀
        (LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap (TensorProduct.comm ℤ R₀ A d)) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    simp [tensorEval_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isChartFun_unique : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {N : ℕ} {M : Scheme.{0}}
    {s : M ⟶ Sp (Localization.Away (N : ℤ))} {U : Obj F 𝔠 M} {α : U.Level N} {V : M.Opens},
    IsDPModel N s U α V → ∀ {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k)
    {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left}, Y.IsPullBy U hW.fromSpec φY →
    ∀ {δY : Y.DetGen} {h h' : R₀ ⊗[ℤ] Γ(M, W)}, IsChartFun r₀ Y δY h → IsChartFun r₀ Y δY h' → h = h' := by
  intro F _ _ 𝔠 N M s U α V hDP R₀ _ k r₀ W hW Y φY hY δY h h' hh hh'
  obtain ⟨-, -, hflat, hV, hnorm, hcod⟩ := hDP
  rw [← sub_eq_zero]
  have key := rTensor_eq_zero_of_restrict_affine_inf N M s V hflat hnorm hcod W hW R₀
    (TensorProduct.comm ℤ R₀ Γ(M, W) (h - h')) ?_
  · exact (TensorProduct.comm ℤ R₀ Γ(M, W)).map_eq_zero_iff.1 key
  intro W' hW' hle
  let ρ : Γ(M, W) →+* Γ(M, W') := (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom
  let ψ : Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W') :=
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom.comp ρ
  obtain ⟨X, φ, hX⟩ := Obj.exists_isPullBy Y (spMap ψ)
  obtain ⟨δ, hδ, -⟩ := hX.existsUnique_detGen ψ δY

  have hmap : spMap ψ ≫ hW.fromSpec =
      spMap (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom ≫ hW'.fromSpec := by
    rw [← hW.map_fromSpec hW' (homOfLE (hle.trans inf_le_left)).op]
    simp [ψ, ρ, spMap, Spec.map_comp]
  have hXr : X.IsRapoport := by
    rw [Obj.isRapoport_iff]
    refine Set.eq_univ_of_forall fun x K _ t hx Z χ hZ ↦ ?_
    have hZU : Z.IsPullBy U (t ≫ spMap ψ ≫ hW.fromSpec) (χ ≫ φ ≫ φY) := hZ.comp (hX.comp hY)
    obtain ⟨z, rfl⟩ := hx
    have hmem : (t ≫ spMap ψ ≫ hW.fromSpec) z ∈ (V : Set M) := by
      rw [hmap]
      have : (hW'.fromSpec) ((t ≫ spMap (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom) z) ∈ (W' : Set M) := by
        rw [← hW'.range_fromSpec]; exact ⟨_, rfl⟩
      exact (hle.trans inf_le_right) (by simpa using this)
    rw [hV] at hmem
    exact hmem K _ ⟨z, rfl⟩ Z _ hZU
  have e1 := hh _ ψ X φ hXr δ hX hδ
  have e2 := hh' _ ψ X φ hXr δ hX hδ
  have e : tensorEval ψ (h - h') = 0 := by rw [map_sub, ← e1, ← e2, sub_self]
  rw [tensorEval_includeRight_comp, LinearEquiv.map_eq_zero_iff] at e
  exact e

end GlobalTheory.RealMult
