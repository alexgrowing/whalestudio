import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverRestrictEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorLiftAlongEtaleMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackNeZeroOfEtaleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem kltAt_iff_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n m : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens) (D₀ : CartierDiv W) (D₁ : CartierDiv M), Etale (U.ι ≫ f) → 0 < m → (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) → ∀ y ∈ U, (GlobalTheory.Discrepancy.KltAt (f ≫ p) n (GlobalTheory.Discrepancy.qWeil D₁ m) y ↔ GlobalTheory.Discrepancy.KltAt p n (GlobalTheory.Discrepancy.qWeil D₀ m) (f y)) := by
  intro M W _ _ _ _ p f _ n m _ _ U D₀ D₁ hU hm hD y hy
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme M := ModifSections.isNormalScheme_of_smooth (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := ModifSections.isNormalScheme_of_smooth p
  have hnM := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
  have hnW := NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hne : ∀ η : RatForms p n, η ≠ 0 → ratPull p f n η ≠ 0 := GlobalTheory.T.rationalTopFormPullback_ne_zero_of_etale M W p f n U hU ⟨y, hy⟩
  have hlog : ∀ (η : RatForms p n) (m' : ℕ) (g : W.functionFieldˣ), η ≠ 0 →
      IsLogEqn p (qWeil D₀ m) η (f y) m' g →
      IsLogEqn (f ≫ p) (qWeil D₁ m) (ratPull p f n η) y m'
        (Units.map (functionFieldMap f).toMonoidHom g) := by
    intro η m' g hη h z hz E' hE'
    have hzU : z ∈ U := hz.mem_open U.isOpen hy
    obtain ⟨E, hE, hord, hform⟩ := GlobalTheory.T.exists_primeDivisor_etalePullback_orders M W p f n U hU z hzU E' hE'
    have key := h (f z) (hz.map f.continuous) E hE
    obtain ⟨d, hd⟩ := D₀.exists_isEqn (f z)
    have hd' := hD z d hd
    have hmult : D₁.mult z = D₀.mult (f z) := by
      rw [hd'.mult_eq, hd.mult_eq, ← hE'.ord_eq, ← hE.ord_eq, hord]
    rw [hform η hη, hord, ← key]
    simp [qWeil, hmult]
  constructor
  · intro hk
    obtain ⟨η, hη, hG⟩ := isLogCanonicalMultiple_canonical (p := p) (n := n) hnW D₀ hm
    obtain ⟨g, hg⟩ := (m • canonical p n + D₀).exists_isEqn (f y)
    have h1 := hG (f y) g hg
    refine (h1.kltAt_iff hnW hη hm).2 fun E hE => ?_
    obtain ⟨E', hE', hord, hform⟩ := GlobalTheory.T.primeDivisor_lift_along_etale_map M W p f n U hU y hy E hE
    have h2 := ((hlog η m g hη h1).kltAt_iff hnM (hne η hη) hm).1 hk E' hE'
    rw [discrep, hord, hform η hη] at h2
    exact h2
  · rintro ⟨η, m', g, hη, hm', h1, h2⟩
    refine ⟨ratPull p f n η, m', _, hne η hη, hm', hlog η m' g hη h1, fun E' hE' => ?_⟩
    obtain ⟨E, hE, hord, hform⟩ := GlobalTheory.T.primeDivisorOver_restrict_etale M W p f n U hU y hy E' hE'
    have h3 := h2 E hE
    rw [discrep] at h3 ⊢
    rw [hord, hform η hη]
    exact h3
end GlobalTheory.EtaleKlt
