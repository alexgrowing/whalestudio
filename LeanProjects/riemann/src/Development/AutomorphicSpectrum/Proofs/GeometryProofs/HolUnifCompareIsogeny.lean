import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertDataEqOfLbIsoPowPull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeUniq

open GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A']

theorem isDiff_comp {M : LB A.left} {M' : LB A'.left} {g g' : ℕ} (u : HolUnif A M g) (u' : HolUnif A' M' g')
    (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) (f : A' ⟶ A) (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u.ex (F z) = u'.ex z ≫ f) {a' : Fin g' → ℂ} {x' : epsR ℂ ⟶ A'} (ht : IsTangent x')
    (hd : u'.IsDiff a' x') : u.IsDiff (F a') (x' ≫ f) := by
  obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F a')
  have a1 := isDerivAt0_comp_linMap (isHolTo_ex u) F (isDerivAt0_of_isDiff u h₁ h₂)
  have a2 := GlobalTheory.FibreDeriv.isDerivAt0_comp (isDerivAt0_of_isDiff u' ht hd) f.left
  rw [show (fun z => (u.ex (F z)).left) = fun z => (u'.ex z).left ≫ f.left from
    funext fun z => by rw [hF, Over.comp_left]] at a1
  have e : t = x' ≫ f := Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique a1 a2)
  exact e ▸ h₂

theorem tangent_of_iso (e : A' ≅ A) [IsMonHom e.hom] {x : epsR ℂ ⟶ A} {x' : epsR ℂ ⟶ A'} (hx : IsTangent x)
    (h : x' ≫ e.hom = x) : IsTangent x' := by
  have h' : x' = x ≫ e.inv := by rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have h₁ : η[A'] ≫ e.hom = η[A] := IsMonHom.one_hom e.hom
  have h₂ : η[A] ≫ e.inv = η[A'] := by rw [← h₁, Category.assoc, e.hom_inv_id, Category.comp_id]
  unfold IsTangent at hx ⊢
  rw [h', Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, h₂]

theorem hermForm_eq_of_pullbacks : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G.left) (g g' : ℕ) (u : HolUnif A (L.pull φ) g) (u' : HolUnif A' (L.pull φ') g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), L.IsLB → IsAbelianScheme A → IsGrpPullback A G z φ → IsGrpPullback A' G z φ' → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (x y : epsR ℂ ⟶ A) (x' y' : epsR ℂ ⟶ A') (a b : Fin g → ℂ) (a' b' : Fin g' → ℂ), IsTangent x → IsTangent y → x'.left ≫ φ' = x.left ≫ φ → y'.left ≫ φ' = y.left ≫ φ → u.IsDiff a x → u.IsDiff b y → u'.IsDiff a' x' → u'.IsDiff b' y' → hermForm Hm' a' b' = hermForm Hm a b := by
  intro X G _ L z A A' _ _ φ φ' g g' u u' Hm Hm' χ χ' hL hAb hp hp' d₁ d₂ hAH hAH' x y x' y' a b a' b' hx hy hxx hyy
    da db da' db'
  obtain ⟨e, hmon, he⟩ := grpPullback_iso hp' hp
  haveI := hmon
  have hol : IsHolTo (Set.univ : Set (Fin g' → ℂ)) (fun w => (u'.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u') e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hAb (L.pull φ) g g' u d₁ d₂
    (fun w => u'.ex w ≫ e.hom) (fun p q => by rw [u'.ex_add, MonObj.mul_comp]) hol
  have hΛ : ∀ l ∈ u'.Λ, F l ∈ u.Λ := fun l hl => (u.ker _).1 (by
    rw [hF, (u'.ker l).2 hl, MonObj.one_comp])
  have iso : LBIso (lbPow (L.pull φ') 1) (lbPow ((L.pull φ).pull e.hom.left) 1) :=
    GlobalTheory.lbIso_lbPow (GlobalTheory.GenSpread.lbIso_pull_pull hL e.hom.left he.symm) 1
  have hH := (GlobalTheory.appellHumbert_data_eq_of_lbIso_pow_pull A' A (L.pull φ') (L.pull φ) g' g u' u Hm' Hm χ' χ e.hom F hΛ 1
    one_pos (pull_isLB hL φ') (pull_isLB hL φ) hAH' hAH hF iso).1
  have coord : ∀ (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A') (c : Fin g → ℂ) (c' : Fin g' → ℂ), IsTangent v →
      v'.left ≫ φ' = v.left ≫ φ → u.IsDiff c v → u'.IsDiff c' v' → F c' = c := fun v v' c c' hv hvv dc dc' => by
    have h : v' ≫ e.hom = v := Over.OverMorphism.ext (hp.1.hom_ext
      (by rw [Over.comp_left, Category.assoc, he, hvv]) (by rw [Over.w, Over.w]))
    have ht := tangent_of_iso e hv h
    exact (d₁ v hv).unique (h ▸ isDiff_comp u u' d₂ e.hom F hF ht dc') dc
  rw [hH, coord x x' a a' hx hxx da da', coord y y' b b' hy hyy db db']

end GlobalTheory.CompanionTheory.Ar.HodgeUniq
