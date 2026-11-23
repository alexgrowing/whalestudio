import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPolFormIsNabla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionTensor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTRealise

theorem pairing_eps_eq_zero {k : Type} [Field k] {M : Type*} [AddCommGroup M] [Module (DualNumber k) M]
    (χ : M →ₗ[DualNumber k] M →ₗ[DualNumber k] DualNumber k) {X Z X' Z' : M} {a b c e : k}
    (h₁ : χ X X' = algebraMap k (DualNumber k) a) (h₂ : χ X Z' = algebraMap k (DualNumber k) b)
    (h₃ : χ Z X' = algebraMap k (DualNumber k) c) (h₄ : χ Z Z' = algebraMap k (DualNumber k) e)
    (ha : a = 0) (hbc : b + c = 0) :
    χ (X + (DualNumber.eps : DualNumber k) • Z) (X' + (DualNumber.eps : DualNumber k) • Z') = 0 := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h₁, h₂, h₃, h₄, smul_eq_mul]
  subst ha
  ext
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
    linear_combination hbc

set_option maxHeartbeats 1000000 in

theorem graphFil_isotropic : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (P : LB (A₀ ⊗ A₀).left), P.IsLB → ∀ (φ : LinearMap.BilinForm k (HdR A₀)),
    GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) A₀ A₀ P φ → ∀ f : HdR A₀ →ₗ[k] HdR A₀,
    (∀ x ∈ Fil A₀, ∀ y ∈ Fil A₀, φ (f x) y + φ x (f y) = 0) →
    ∀ φ' : Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ →ₗ[DualNumber k] Crys (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ →ₗ[DualNumber k] DualNumber k,
    GlobalTheory.AbDual.IsCorrForm (epsDP k) (GlobalTheory.DeRham.epsRed k) A₀ A₀ P φ' →
    ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, ∀ d' ∈ GlobalTheory.HTRealise.graphFil A₀ f, φ' d d' = 0 := by
  intro k _ A₀ _ hA P hP φ hφ f hf φ' hφ' d hd d' hd'
  have := hA.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.SerreDim.exists_dim_of_grpObj A₀
  have iso := GlobalTheory.PrincipalPolPairing.isotropic GlobalTheory.abelianDeRham hA hg hP hφ
  have C := GlobalTheory.PolFormNabla.cupSquare_eps (AbelianSchemeGerms.isAbelianScheme_tensor A₀ A₀ hA hA)
    (GlobalTheory.AbDual.smooth_prod hg hg)
  have e : LBIso (P.pull (𝟙 _)) P :=
    (CechPic.cls_eq_iff (pull_isLB hP _) hP).1 (by rw [CechPic.cls_pull hP, CechPic.pull_id])
  obtain ⟨χ, hχ, hk⟩ := hφ.pull hP (constMor A₀) (constMor A₀) (h := 𝟙 _) (by simp) (by simp) hP e
  obtain rfl := hχ.unique C hP hφ'
  have hm := isBC_constMor hA
  obtain ⟨x, hx, y, hy, ed⟩ := mem_graphFil.1 hd
  obtain ⟨x', hx', y', hy', ed'⟩ := mem_graphFil.1 hd'
  obtain ⟨X, hX⟩ := hm.exists x
  obtain ⟨Z, hZ⟩ := hm.exists (f x + y)
  obtain ⟨X', hX'⟩ := hm.exists x'
  obtain ⟨Z', hZ'⟩ := hm.exists (f x' + y')
  have dE : d = X + (DualNumber.eps : DualNumber k) • Z := crys_ext hA fun c => by
    rw [ed c, LinearMap.add_apply, LinearMap.smul_apply, hX c, hZ c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have dE' : d' = X' + (DualNumber.eps : DualNumber k) • Z' := crys_ext hA fun c => by
    rw [ed' c, LinearMap.add_apply, LinearMap.smul_apply, hX' c, hZ' c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have h₁ : φ x x' = 0 := iso x hx x' hx'
  have h₂ : φ x (f x' + y') + φ (f x + y) x' = 0 := by
    rw [map_add, map_add, LinearMap.add_apply, iso x hx y' hy', iso y hy x' hx', add_zero, add_zero, add_comm]
    exact hf x hx x' hx'
  rw [dE, dE']
  exact pairing_eps_eq_zero χ (hk _ _ _ _ hX hX') (hk _ _ _ _ hX hZ') (hk _ _ _ _ hZ hX') (hk _ _ _ _ hZ hZ') h₁ h₂

end GlobalTheory.HTRealise
