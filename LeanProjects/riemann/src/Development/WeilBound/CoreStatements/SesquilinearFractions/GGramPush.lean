import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder CategoryTheory.Obj

namespace PositivityTheory.Xgf.ChartPullbackComposition

variable {X X' X'' : Scheme.{0}}

def chartPullComp (L : LB X) (φ : X' ⟶ X) (ψ : X'' ⟶ X') : ChartPull (L.pull (ψ ≫ φ)) (L.pull φ) ψ where
  idx J := J
  le J y hy := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hy)
  g y J J' hj hj' := by
    have h1 : ψ y ∈ (L.pull φ).U J := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hj)
    have h2 : ψ y ∈ (L.pull φ).U J' := (mem_pull (F := φ)).2 ((mem_pull (F := ψ ≫ φ)).1 hj')
    refine (gm_pull_g L (ψ ≫ φ) (𝟙 _) y J J' hj hj').trans ?_
    refine Eq.trans ?_ (gm_pull_g L φ ψ y J J' h1 h2).symm
    rw [Category.id_comp]

end PositivityTheory.Xgf.ChartPullbackComposition

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.ChartPullbackComposition in
theorem hodge_gram_invariant_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (x' : Sp ℂ ⟶ S') (x : Sp ℂ ⟶ S) (n : ℕ) (v' : Fin n → (epsAt x' ⟶ t'.G)) (v : Fin n → (epsAt x ⟶ t.G)) (Γ : Matrix (Fin n) (Fin n) ℂ), x = x' ≫ f → (∀ k, (v k).left = (v' k).left ≫ m.φ) → (IsHodgeGram t'.G t'.PP.L x' v' Γ ↔ IsHodgeGram t.G t.PP.L x v Γ) := by
  intro E _ _ _ H S S' t t' f m x' x n v' v Γ hx hv
  obtain ⟨w₀, hw₀, -⟩ := m.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := ⟨w₀, hw₀⟩

  have hpull : ∀ {Z : Scheme.{0}} (ψ' : Z ⟶ t'.G.left), LBIso (t'.PP.L.pull ψ') (t.PP.L.pull (ψ' ≫ m.φ)) :=
    fun ψ' => LBIso.chartPull (chartPullPull t'.PP.L ψ' ψ' rfl) (chartPullComp t.PP.L m.φ ψ') hL
  constructor
  · rintro ⟨Q, ψ', v₁, u, Hm, χ, W, hPB, hLB, hAH, hv₁, hΓ⟩
    refine ⟨Q, ψ' ≫ m.φ, v₁, u, Hm, χ, W, (hPB.comp m.cart).congr hx.symm rfl, ?_, hAH, fun i => ⟨?_, (hv₁ i).2⟩, hΓ⟩
    · exact LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB t'.PP.isLB _) Q.isLB (LBIso.symm (hpull ψ')) hLB
    · rw [← Category.assoc, (hv₁ i).1, hv i]
  · rintro ⟨Q, ψ, v₁, u, Hm, χ, W, hPB, hLB, hAH, hv₁, hΓ⟩
    have hP := ((isGrpPullback_pullback t'.G x').comp m.cart).congr hx.symm rfl
    obtain ⟨e, he, heψ⟩ := grpPullback_iso hPB hP
    have hψ' : IsGrpPullback Q.A t'.G x' (e.hom.left ≫ pullback.fst t'.G.hom x') :=
      ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback t'.G x')).congr (Category.id_comp x') rfl
    have hcomp : (e.hom.left ≫ pullback.fst t'.G.hom x') ≫ m.φ = ψ := by
      rw [Category.assoc]; exact heψ
    refine ⟨Q, e.hom.left ≫ pullback.fst t'.G.hom x', v₁, u, Hm, χ, W, hψ', ?_, hAH, fun i => ⟨?_, (hv₁ i).2⟩, hΓ⟩
    · refine LBIso.trans (pull_isLB t'.PP.isLB _) (pull_isLB t.PP.isLB _) Q.isLB (hpull _) ?_
      rw [hcomp]
      exact hLB
    · apply m.cart.1.hom_ext
      · rw [Category.assoc, hcomp, (hv₁ i).1, hv i]
      · rw [Category.assoc, hψ'.1.w, ← Category.assoc, Over.w, Over.w]
        rfl

end PositivityTheory.Xgf
