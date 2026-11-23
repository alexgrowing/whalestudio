import Mathlib
import Formalism.PeriodIntegrals.SupportParts
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocProdFormula

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocStep : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D), Agree δ M p →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)), kind w = kind w' →
  ∀ c : Option ((M p).Cls D.R.rS), BBtop M δ T T' p w c ≠ 0 → BBtop M δ T T' p w' c ≠ 0 →
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) =
        (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
      (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS))

def TopNe : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1)), Dmin w (D.R.rS + 1) ≠ 0

theorem ne_zero_of_finprod_ne_zero {α : Type*} (f : α → ℂ) (hf : (Function.mulSupport f).Finite)
    (h : ∏ᶠ a, f a ≠ 0) (a : α) : f a ≠ 0 := by
  intro ha
  apply h
  rw [finprod_eq_prod f hf]
  apply Finset.prod_eq_zero (i := a)
  · rw [Set.Finite.mem_toFinset]
    simp [Function.mem_mulSupport, ha]
  · exact ha

theorem norm_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) :
    Algebra.norm ℚ (D.conjF x) = Algebra.norm ℚ x := by
  let σ : D.host.E →ₐ[ℚ] D.host.E := D.conjF.restrictScalars ℚ
  have hb : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  exact Algebra.norm_eq_of_algEquiv (AlgEquiv.ofBijective σ hb) x

theorem absNorm_eq_of_modK (D : Formalism.BasicNotions.D7)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hM : ∀ p, (M p).OK)
    (x x' : D.host.E) (hx : x ≠ 0) (hx' : x' ≠ 0)
    (h : ∀ p, (M p).modK ((D.s.atP p).ιE x) = (M p).modK ((D.s.atP p).ιE x')) :
    |Algebra.norm ℚ x| = |Algebra.norm ℚ x'| := by
  have e := local_product_formula D.host.F D.host.E D.sp.cm.deg2 D.conjF D.s.atP M hM
  have h1 := e x hx
  have h2 := e x' hx'
  simp only [h] at h1
  have h3 := h1.symm.trans h2
  have h4 := inv_injective h3
  exact_mod_cast h4

theorem supportVec_of (hL : LocStep) (hT : TopNe) (D : Formalism.BasicNotions.D7) : PI.SupportParts.SupportVec D := by
  intro δ M hA T T' w w' κ th hf hf' hB hB'
  have hk : kind w = κ := by
    by_contra hne
    exact hB (by simp [BBG, hne])
  have hk' : kind w' = κ := by
    by_contra hne
    exact hB' (by simp [BBG, hne])
  have hp : ∏ᶠ p, BBtop M δ T T' p w (th p) ≠ 0 := by
    intro h0
    exact hB (by simp [BBG, hk, h0])
  have hp' : ∏ᶠ p, BBtop M δ T T' p w' (th p) ≠ 0 := by
    intro h0
    exact hB' (by simp [BBG, hk', h0])
  have hkk : kind w = kind w' := hk.trans hk'.symm
  have hloc := fun p => hL D δ M p (hA p) T T' w w' hkk (th p)
    (ne_zero_of_finprod_ne_zero _ hf hp p) (ne_zero_of_finprod_ne_zero _ hf' hp' p)
  have hOK : ∀ p, (M p).OK := fun p => (hA p).1
  unfold PI.SupportParts.normG Gpt
  rcases hcase : kind w with _ | ζ
  · have h0 : Dmin w D.R.rS = 0 := by
      unfold kind at hcase
      by_contra hne
      simp [hne] at hcase
    have hcase' : kind w' = none := hkk ▸ hcase
    have h0' : Dmin w' D.R.rS = 0 := by
      unfold kind at hcase'
      by_contra hne
      simp [hne] at hcase'
    rw [h0, h0']
    have hn := absNorm_eq_of_modK D M hOK _ _ (hT D w) (hT D w') (fun p => (hloc p).1)
    simp only [mul_zero, map_zero, sub_zero, map_mul, abs_mul, norm_conjF, hn]
  · have hcase' : kind w' = some ζ := hkk ▸ hcase
    have hr : Dmin w D.R.rS ≠ 0 := by
      unfold kind at hcase
      by_contra hne
      simp [hne] at hcase
    have hr' : Dmin w' D.R.rS ≠ 0 := by
      unfold kind at hcase'
      by_contra hne
      simp [hne] at hcase'
    have hz : zetaOf w = ζ := by
      unfold kind at hcase
      simpa [hr] using hcase
    have hz' : zetaOf w' = ζ := by
      unfold kind at hcase'
      simpa [hr'] using hcase'
    have e1 : Dmin w (D.R.rS + 1) = ζ * Dmin w D.R.rS := by
      rw [← hz, zetaOf, div_mul_cancel₀ _ hr]
    have e1' : Dmin w' (D.R.rS + 1) = ζ * Dmin w' D.R.rS := by
      rw [← hz', zetaOf, div_mul_cancel₀ _ hr']
    have hn := absNorm_eq_of_modK D M hOK _ _ hr hr' (fun p => (hloc p).2)
    have g1 : ∀ x : D.host.E, ζ * x * D.conjF (ζ * x) - (T : D.host.E) * T' * (x * D.conjF x) =
        x * D.conjF x * (ζ * D.conjF ζ - (T : D.host.E) * T') := by
      intro x
      rw [map_mul]
      ring
    rw [e1, e1', g1, g1]
    simp only [map_mul, abs_mul, norm_conjF, hn]

theorem supportVecAll_of (hL : LocStep) (hT : TopNe) : PI.SupportParts.SupportVecAll :=
  fun D => supportVec_of hL hT D

end PI.SupportDatumW
