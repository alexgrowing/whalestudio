import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

theorem exists_formOn_eq (a : Fin (N + 1)) (s : Γ(PSpace R N, chart R N a)) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d),
      formOn (chart R N a) a le_rfl d F hF = s := by
  obtain ⟨p, rfl⟩ := (chartAlgEquiv R N a).surjective s
  obtain ⟨x, rfl⟩ := (polyEquivAway R N a).symm.surjective p
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N a) x
  refine ⟨n, f, by simpa using hf, ?_⟩
  rw [← chartAlgEquiv_dehom, ← awayToPoly_mk R N a n f hf]
  rfl

def pullForm (φ : X ⟶ PSpace R N) (W : X.Opens) (i : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ chart R N i)
    (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous d) : Γ(X, W) :=
  (φ.appLE (chart R N i) W hi).hom (formOn (chart R N i) i le_rfl d F hF)

section

variable {φ : X ⟶ PSpace R N} {W V : X.Opens} {i j : Fin (N + 1)} {hi : W ≤ φ ⁻¹ᵁ chart R N i}
  {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R}

theorem resG_pullForm (h : V ≤ W) (hF : F.IsHomogeneous d) :
    resG X h (pullForm φ W i hi d F hF) = pullForm φ V i (h.trans hi) d F hF :=
  resG_appLE φ hi h _

theorem pullForm_zero : pullForm φ W i hi d 0 (isHomogeneous_zero _ R d) = 0 := by
  rw [pullForm, formOn_zero, map_zero]

theorem pullForm_eq_pow_mul (hj : W ≤ φ ⁻¹ᵁ chart R N j) (hF : F.IsHomogeneous d) :
    pullForm φ W i hi d F hF = pullRatio φ W i hi j ^ d * pullForm φ W j hj d F hF := by
  have hW : W ≤ φ ⁻¹ᵁ (chart R N i ⊓ chart R N j) := le_inf hi hj
  have := congrArg (φ.appLE _ W hW).hom
    (formOn_eq_ratioOn_pow_mul (U := chart R N i ⊓ chart R N j) (hi := inf_le_left) inf_le_right hF)
  rw [map_mul, map_pow, appLE_ratioOn, ← resG_formOn (hi := le_rfl) inf_le_left,
    ← resG_formOn (hi := le_rfl) inf_le_right, appLE_resG, appLE_resG] at this
  exact this

theorem pullForm_X_pow_mul (n : ℕ) (hF : F.IsHomogeneous d) {e : ℕ}
    (hG : (MvPolynomial.X j ^ n * F).IsHomogeneous e) :
    pullForm φ W i hi e _ hG = pullRatio φ W i hi j ^ n * pullForm φ W i hi d F hF := by
  rw [pullForm, pullForm, pullRatio, formOn_eq_aeval, formOn_eq_aeval, map_mul, map_pow, aeval_X, map_mul,
    map_pow]

end

def pullO (φ : X ⟶ PSpace R N) (e : ℕ) : LB X where
  ι := Fin (N + 1)
  U i := φ ⁻¹ᵁ chart R N i
  g i j := (Units.mkOfMulEqOne (pullRatio φ _ i inf_le_left j) (pullRatio φ _ j inf_le_right i)
    (pullRatio_mul_pullRatio.trans pullRatio_self)) ^ e

def pullFormSec (φ : X ⟶ PSpace R N) {e : ℕ} (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e) :
    (pullO φ e).Sec where
  f i := pullForm φ _ i le_rfl e F hF
  compat i j := by
    refine (resG_pullForm inf_le_left hF).trans ((pullForm_eq_pow_mul (j := j) inf_le_right hF).trans ?_)
    exact congrArg₂ (· * ·) (Units.val_pow_eq_pow_val (Units.mkOfMulEqOne _ _ _) e).symm
      (resG_pullForm inf_le_right hF).symm

abbrev affChart (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (i : Fin (N + 1)) : X.affineOpens :=
  ⟨φ ⁻¹ᵁ chart R N i, (isAffineOpen_chart R N i).preimage φ⟩

theorem exists_pow_mul_pullForm_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    {a : Fin (N + 1)} {d : ℕ} {F : MvPolynomial (Fin (N + 1)) R} (hF : F.IsHomogeneous d)
    (h : pullForm φ _ a le_rfl d F hF ∈ J.ideal (affChart φ a)) (b : Fin (N + 1)) :
    ∃ n, pullRatio φ _ b le_rfl a ^ n * pullForm φ _ b le_rfl d F hF ∈ J.ideal (affChart φ b) := by
  let r : Γ(X, (affChart φ b).1) := pullRatio φ _ b le_rfl a
  have ha : X.basicOpen r ≤ φ ⁻¹ᵁ chart R N a := basicOpen_pullRatio.le.trans inf_le_right
  have h1 : resG X ha (pullForm φ _ a le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) :=
    J.ideal_le_comap_ideal (U := X.affineBasicOpen r) (V := affChart φ a) ha h
  have h2 : resG X (X.basicOpen_le r) (pullForm φ _ b le_rfl d F hF) ∈ J.ideal (X.affineBasicOpen r) := by
    rw [resG_pullForm] at h1 ⊢
    rw [pullForm_eq_pow_mul (j := a) ha]
    exact Ideal.mul_mem_left _ _ h1
  rw [← J.map_ideal_basicOpen] at h2
  have inst := (affChart φ b).2.isLocalization_basicOpen r
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (.powers r)
    Γ(X, X.basicOpen r) _ _).1 h2
  exact ⟨n, hn⟩

theorem exists_form_of_mem (φ : X ⟶ PSpace R N) [IsClosedImmersion φ] (J : X.IdealSheafData)
    (a : Fin (N + 1)) (g : Γ(X, (affChart φ a).1)) (hg : g ∈ J.ideal (affChart φ a)) :
    ∃ e₀, ∀ e, e₀ ≤ e → ∃ (F : MvPolynomial (Fin (N + 1)) R) (hF : F.IsHomogeneous e),
      pullForm φ _ a le_rfl e F hF = g ∧ ∀ b, pullForm φ _ b le_rfl e F hF ∈ J.ideal (affChart φ b) := by
  obtain ⟨s, rfl⟩ := φ.app_surjective _ (isAffineOpen_chart R N a) g
  obtain ⟨d, F, hF, rfl⟩ := exists_formOn_eq a s
  have e₁ : pullForm φ _ a le_rfl d F hF = (φ.app (chart R N a)).hom (formOn (chart R N a) a le_rfl d F hF) := by
    rw [pullForm, Scheme.Hom.app_eq_appLE]
  choose n hn using exists_pow_mul_pullForm_mem φ J hF (e₁ ▸ hg)
  refine ⟨Finset.univ.sup n + d, fun e he => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_of_add_le_right he)
  refine ⟨MvPolynomial.X a ^ k * F, (isHomogeneous_X_pow a k).mul hF, ?_, fun b => ?_⟩
  · rw [pullForm_X_pow_mul k hF, pullRatio_self, one_pow, one_mul]
    exact e₁
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le'
      ((Finset.le_sup (f := n) (Finset.mem_univ b)).trans (Nat.le_of_add_le_add_right he))
    rw [pullForm_X_pow_mul _ hF, pow_add, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hn b)

theorem exists_generates (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) :
    ∃ (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec), Generates J σ := by
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
  refine ⟨_, _, fun j => τ (q j), (isCoordFamily_pullRatio φ).cover, fun k V h => ?_⟩
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
