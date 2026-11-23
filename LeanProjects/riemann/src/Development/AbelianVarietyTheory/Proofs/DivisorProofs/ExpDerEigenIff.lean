import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDerivAt0CompLinearIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)}

def expDer (he : IsExp y e) (w : Fin g → ℂ) : epsPt y ⟶ G := (he.2.2.2.1 w).exists.choose

variable (he : IsExp y e)
include he

theorem expDer_spec (w : Fin g → ℂ) : IsDerivAt0 (fun z => (e z).left) w (expDer he w).left :=
  (he.2.2.2.1 w).exists.choose_spec

theorem exp_zero : e 0 = 1 := by
  have h := he.1 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_eq_iff (w : Fin g → ℂ) (v : epsPt y ⟶ G) :
    IsDerivAt0 (fun z => (e z).left) w v.left ↔ expDer he w = v :=
  ⟨fun hv => Over.OverMorphism.ext
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he w) hv), fun hv => hv ▸ expDer_spec he w⟩

theorem expDer_base (w : Fin g → ℂ) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (1 : Over.mk y ⟶ G).left := by
  rw [(expDer_spec he w).1]; show (e 0).left = _; rw [exp_zero he]

theorem expDer_injective : Function.Injective (expDer he) := by
  intro w w' h
  have h1 := expDer_spec he w
  have h2 := expDer_spec he w'
  rw [← h] at h2
  have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (expDer he w).left = (e 0).left := h1.1
  exact (he.2.2.2.2 _ hb).unique h1 h2

theorem expDer_surj (v : epsPt y ⟶ G)
    (hv : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left) :
    ∃ w, expDer he w = v := by
  obtain ⟨w, hw, -⟩ := he.2.2.2.2 v (by rw [hv, exp_zero he])
  exact ⟨w, (expDer_eq_iff he w v).1 hw⟩

theorem expDer_add (w w' : Fin g → ℂ) : expDer he (w + w') = expDer he w * expDer he w' :=
  (expDer_eq_iff he _ _).1 (GlobalTheory.UnifCompare.isDerivAt0_mul (by rw [exp_zero he]) (expDer_spec he w)
    (expDer_spec he w'))

theorem expDer_zero : expDer he 0 = 1 := by
  have h := expDer_add he 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

theorem expDer_smul (c : ℂ) (w : Fin g → ℂ) :
    (expDer he (c • w)).left = spMap (epsScale c) ≫ (expDer he w).left :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique (expDer_spec he _)
    (GlobalTheory.UnifCompare.isDerivAt0_smul (expDer_spec he w) c)

theorem expDer_prod {n : ℕ} (f : Fin n → Fin g → ℂ) :
    (List.ofFn fun j => expDer he (f j)).prod = expDer he (∑ j, f j) := by
  induction n with
  | zero => simp [expDer_zero he]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => f j.succ), Fin.sum_univ_succ, expDer_add he]

theorem expDer_mulVec (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (w : Fin g → ℂ) : expDer he (M *ᵥ w) = expDer he w ≫ φ := by
  have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_comp_hom (expDer_spec he w) φ.left
  have h2 : (fun z => (e z).left ≫ φ.left) = fun z => (e (Matrix.mulVecLin M z)).left := by
    funext z; rw [Matrix.mulVecLin_apply, hM z, Over.comp_left]
  rw [h2, GlobalTheory.ThetaWitness.isDerivAt0_comp_linear_iff (fun z => (e z).left) he.2.2.1] at h1
  exact (expDer_eq_iff he _ _).1 h1

theorem expDer_eigen_iff (M : Matrix (Fin g) (Fin g) ℂ) (φ : G ⟶ G) (hM : ∀ z, e (M *ᵥ z) = e z ≫ φ)
    (c : ℂ) (w : Fin g → ℂ) :
    (expDer he w ≫ φ).left = spMap (epsScale c) ≫ (expDer he w).left ↔ M *ᵥ w = c • w := by
  rw [← expDer_mulVec he M φ hM, ← expDer_smul he]
  constructor
  · intro h
    exact expDer_injective he (Over.OverMorphism.ext h)
  · intro h
    rw [h]

end GlobalTheory.UPel.HT.LieType
