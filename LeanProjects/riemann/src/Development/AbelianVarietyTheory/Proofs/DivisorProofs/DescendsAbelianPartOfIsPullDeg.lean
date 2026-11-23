import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

def chartPullCompOf {X Y Y' : Scheme.{0}} (L : LB X) (g : Y ⟶ X) (h : Y' ⟶ Y) (k : Y' ⟶ X) (e : h ≫ g = k) :
    ChartPull (L.pull k) (L.pull g) h where
  idx J := J
  le J y hy := by
    subst e
    exact mem_pull.2 (by simpa using mem_pull.1 hy)
  g y J J' hj hj' := by
    subst e
    have hj₁ : h y ∈ (L.pull g).U J := mem_pull.2 (by simpa using mem_pull.1 hj)
    have hj₁' : h y ∈ (L.pull g).U J' := mem_pull.2 (by simpa using mem_pull.1 hj')
    refine (gm_pull_g L (h ≫ g) (𝟙 _) y J J' hj hj').trans ?_
    refine Eq.trans ?_ (gm_pull_g L g h y J J' hj₁ hj₁').symm
    rw [Category.id_comp]

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem descAt_of_isPullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁)
    (Q : DegPre V) (D : DegPre V₁), IsPullDeg ρ Q D → D.P.g = Q.P.g ∧ ∀ (K : Type) [Field K] (ev : V₁ →+* K)
    (k₀ : Subfield K), DescAt D ev k₀ → DescAt Q (ev.comp ρ) k₀ := by
  intro V V₁ _ _ _ _ ρ Q D p
  have gp := pull_grp p
  refine ⟨H1.dim_unique _ D.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback gp.1 Q.P.smoothDim)
    (eSec D.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V₁)), ?_⟩
  intro K _ ev k₀ hd
  obtain ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hab, hM, h₁, h₀, hw, hc⟩ := hd
  have hL : LBIso (Q.P.L.pull (π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)))) (M₀.pull π₀) :=
    LBIso.trans (pull_isLB Q.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB hM _)
      (LBIso.chartPull (chartPullCompOf Q.P.L _ π₁ _ rfl) (chartPullPull D.P.L π₁)
        (LBIso.symm ⟨p.w, p.w_gen⟩)) ⟨w, hw⟩
  obtain ⟨w', hw'⟩ := hL
  refine ⟨B₀, i₁, i₂, M₀, fun a => c₀ (p.xe.symm a), B', i₃, π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)),
    π₀, w', fun a => c' (p.xe.symm a), hab, hM, ?_, h₀, hw', fun a => ⟨(hc _).1, ?_, (hc _).2.2⟩⟩
  · exact (h₁.comp gp).congr (spMap_comp_ringHom ρ ev).symm rfl
  · have e₁ := (hc (p.xe.symm a)).2.1
    have e₂ := p.c_pr (p.xe.symm a)
    rw [AddEquiv.apply_symm_apply] at e₂
    rw [← Category.assoc, e₁, Category.assoc, e₂, ← Category.assoc, spMap_comp_ringHom]

end GlobalTheory.USep
