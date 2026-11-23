import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionsGenerateIdealProjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

theorem val_res_pullO_g (φ : X ⟶ PSpace R N) (e : ℕ) (i j : (pullO φ e).ι)
    {V : X.Opens} (h : V ≤ (pullO φ e).U i ⊓ (pullO φ e).U j) :
    ((res h ((pullO φ e).g i j) : Γ(X, V)ˣ) : Γ(X, V)) = pullRatio φ V i (h.trans inf_le_left) j ^ e := by
  have : (((pullO φ e).g i j : Γ(X, (pullO φ e).U i ⊓ (pullO φ e).U j)ˣ) :
      Γ(X, (pullO φ e).U i ⊓ (pullO φ e).U j)) = pullRatio φ _ i inf_le_left j ^ e :=
    Units.val_pow_eq_pow_val _ _
  rw [res, Units.coe_map, MonoidHom.coe_coe, this]
  exact (map_pow _ _ e).trans (congrArg (· ^ e) (resG_pullRatio h))

theorem isLB_pullO (φ : X ⟶ PSpace R N) (e : ℕ) : (pullO φ e).IsLB where
  cover := (isCoordFamily_pullRatio φ).cover
  g_self i := by
    ext
    rw [val_res_pullO_g, Units.val_one]
    exact (congrArg (· ^ e) pullRatio_self).trans (one_pow e)
  cocycle i j k := by
    ext
    rw [Units.val_mul, val_res_pullO_g, val_res_pullO_g, val_res_pullO_g]
    exact (mul_pow _ _ e).symm.trans (congrArg (· ^ e) pullRatio_mul_pullRatio)

theorem exists_generates_isLB (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (J : X.IdealSheafData) (hs : IsProjOver s) :
    ∃ (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), L₀.IsLB ∧ Generates J σ := by
  classical
  obtain ⟨N, φ, _, -⟩ := hs
  have fg : ∀ a, (J.ideal (affChart φ a)).FG := fun a => by
    have : IsNoetherianRing Γ(PSpace R N, chart R N a) :=
      isNoetherianRing_of_ringEquiv _ (chartAlgEquiv R N a).toRingEquiv
    have : IsNoetherianRing Γ(X, (affChart φ a).1) :=
      isNoetherianRing_of_surjective _ _ _ (φ.app_surjective _ (isAffineOpen_chart R N a))
    exact IsNoetherian.noetherian _
  choose S hS using fg
  choose e₀ he₀ using fun p : Σ a, S a =>
    exists_form_of_mem φ J p.1 p.2.1 (hS p.1 ▸ Ideal.subset_span p.2.2)
  choose F hF hFa hFb using fun p => he₀ p (Finset.univ.sup e₀) (Finset.le_sup (Finset.mem_univ p))
  let q := (Fintype.equivFinOfCardEq (Fintype.card_option (α := Σ a, S a))).symm
  let τ : Option (Σ a, S a) → (pullO φ (Finset.univ.sup e₀)).Sec := fun o =>
    o.elim (pullFormSec φ 0 (isHomogeneous_zero _ R _)) fun p => pullFormSec φ (F p) (hF p)
  refine ⟨_, _, fun j => τ (q j), isLB_pullO φ _, (isCoordFamily_pullRatio φ).cover, fun k V h => ?_⟩
  have key : J.ideal (affChart φ k) = Ideal.span (Set.range fun j => (τ (q j)).f k) := by
    refine le_antisymm ?_ (Ideal.span_le.2 ?_)
    · rw [← hS k]
      refine Ideal.span_mono fun g hg => ⟨q.symm (some ⟨k, g, hg⟩), ?_⟩
      simp only [q.apply_symm_apply]
      exact hFa ⟨k, g, hg⟩
    · rintro _ ⟨j, rfl⟩
      dsimp only
      cases q j with
      | none =>
        exact (congrArg (· ∈ J.ideal (affChart φ k)) (pullForm_zero (φ := φ) (hi := le_rfl))).mpr (zero_mem _)
      | some p => exact hFb p k
  rw [← J.map_ideal (V := affChart φ k) h, key]
  erw [Ideal.map_span, ← Set.range_comp]
  rfl

end GlobalTheory.ProjBlowup
