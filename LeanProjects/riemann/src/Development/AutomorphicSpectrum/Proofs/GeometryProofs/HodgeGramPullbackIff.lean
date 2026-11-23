import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lbIso_pull_gram {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (chartPullPull M j j rfl) (chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem hodgeGram_iff_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (k : ℕ) (v' : Fin k → (epsAt x' ⟶ t'.G)) (v : Fin k → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x = x' ≫ f → (∀ a, (v' a).left ≫ m.φ = (v a).left) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  intro E _ _ _ H S S' t t' f m x' x k v' v Γ hx hv
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := m.lin.imp fun _ h => h.1
  constructor
  · rintro ⟨Q, ψ, w, u, Hm, χ, W, hp, hl, hu, hw, hΓ⟩
    refine ⟨Q, ψ ≫ m.φ, w, u, Hm, χ, W, hp.comp m.cart, ?_, hu, fun i => ⟨?_, (hw i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) Q.isLB (lbIso_pull_gram hL ψ rfl).symm hl
    · rw [← Category.assoc, (hw i).1, hv]
  · rintro ⟨Q, ψ, w, u, Hm, χ, W, hp, hl, hu, hw, hΓ⟩
    have sq : ψ ≫ t.G.hom = (Q.A.hom ≫ x') ≫ f := by
      rw [Category.assoc]; exact hp.1.w
    let ψ' : Q.A.left ⟶ t'.G.left := m.cart.1.lift ψ (Q.A.hom ≫ x') sq
    have h1 : ψ' ≫ m.φ = ψ := m.cart.1.lift_fst _ _ sq
    have h2 : ψ' ≫ t'.G.hom = Q.A.hom ≫ x' := m.cart.1.lift_snd _ _ sq
    have hp' : IsGrpPullback Q.A t'.G x' ψ' := m.cart.cancel (hp.congr rfl h1.symm) h2
    refine ⟨Q, ψ', w, u, Hm, χ, W, hp', ?_, hu, fun i => ⟨?_, (hw i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t'.PP.isLB _) (pull_isLB t.PP.isLB _) Q.isLB (lbIso_pull_gram hL ψ' h1.symm) hl
    · apply m.cart.1.hom_ext
      · rw [Category.assoc, h1, (hw i).1, hv]
      · rw [Category.assoc, h2, ← Category.assoc, Over.w (w i), Over.w (v' i)]
        rfl

end GlobalTheory.CompanionTheory.Ar.Flat
