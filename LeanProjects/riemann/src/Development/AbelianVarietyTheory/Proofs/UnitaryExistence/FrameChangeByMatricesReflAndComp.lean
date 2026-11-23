import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculusStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frChg_refl_and_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), FrChg (fun _ => 1) 1 y y ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y' y'' → FrChg (fun τ => g' τ * g τ) (a' * a) y y'' := by
  intro E _ _ _ H Dw l Xo c S _ _ y y' y''
  have hid : y.x = spMap (RingHom.id S) ≫ y.x := by
    have : spMap (RingHom.id S) = 𝟙 (Sp S) := Spec.map_id _
    rw [this, Category.id_comp]
  obtain ⟨-, h2, -, h4⟩ := GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x hid hid
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S y.x
  have hb : ∀ τ i, ∃ m, v m = y.u τ i := fun τ i => (htan _).1 (y.tan τ i)
  choose b hb using hb
  have hu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  refine ⟨⟨rfl, fun τ i => ?_, ?_⟩, ?_⟩
  · rw [hu τ, hcomb]
    simp [Matrix.one_apply]
  · rw [h2]
    intro i
    rw [(h4 1 1 i).2.2, _root_.one_mul]
  · rintro g g' a a' ⟨hx, hc, hs⟩ ⟨hx', hc', hs'⟩
    obtain ⟨x', xo', u', t', e', b', s', gen'⟩ := y'
    obtain ⟨x'', xo'', u'', t'', e'', b'', s'', gen''⟩ := y''
    dsimp only at hx hx' hc hc' hs hs'
    subst hx'
    subst hx
    refine ⟨rfl, fun τ i => ?_, ?_⟩
    · have h1 : u' τ = fun j => v (∑ k, g τ j k • b τ k) := by
        funext j
        have := hc τ j
        rw [hu τ, hcomb] at this
        exact this
      have h3 := hc' τ i
      rw [h1, hcomb] at h3
      dsimp only
      rw [hu τ, hcomb, h3]
      congr 1
      simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    · dsimp only
      rw [h2] at hs hs' ⊢
      intro i
      rw [hs' i, hs i, (h4 a' a i).1, _root_.mul_assoc]

end GlobalTheory.Frames
