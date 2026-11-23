import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Twist

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (b : R →+* R') (a : R' →+* R'') :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  rw [← Spec.map_comp]; rfl

theorem twist_fibre_iso : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (L : LB X.left), L.IsLB →
  ∀ (K : Type) [Field K]
  (ev : V₁ →+* K) (σ : K ≃+* K) (K₀ : Type) [Field K₀] (e : K₀ →+* K), σ.toRingHom.comp e = e →
  ∀ (Z : Over (Sp K)) [GrpObj Z] (LZ : LB Z.left), LZ.IsLB → ∀ (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  LBIso (L.pull (pullback.fst X.hom (spMap ev))) (LZ.pull ψ) →
  ∀ (Y : Over (Sp K₀)) [GrpObj Y] (L₀ : LB Y.left), L₀.IsLB → ∀ (φ : Z.left ⟶ Y.left), IsGrpPullback Z Y (spMap e) φ →
  LBIso LZ (L₀.pull φ) →
  ∃ f : ((Over.pullback (spMap ev)).obj X).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X).left,
    IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) (𝟙 _) f ∧
    LBIso (L.pull (pullback.fst X.hom (spMap ev))) (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) ∧
    ∀ (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left) (y₀ : Sp K₀ ⟶ Y.left), q ≫ ψ ≫ φ = spMap e ≫ y₀ →
      q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
      q ≫ f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst X.hom (spMap ev) := by
  intro V₁ _ X _ L hL K _ ev σ K₀ _ e hσe Z _ LZ hLZ ψ hψ H1 Y _ L₀ hL₀ φ hφ H2
  have hs : spMap σ.toRingHom ≫ spMap e = spMap e := by rw [spMap_comp_spMap, hσe]
  have hev : spMap σ.toRingHom ≫ spMap ev = spMap (σ.toRingHom.comp ev) := spMap_comp_spMap _ _
  have hX := isGrpPullback_pullback X (spMap ev)
  have hXσ := isGrpPullback_pullback X (spMap (σ.toRingHom.comp ev))
  have hχ := hψ.comp hφ
  obtain ⟨ρ, hρ1, hρ2⟩ : ∃ ρ : pullback X.hom (spMap (σ.toRingHom.comp ev)) ⟶ pullback X.hom (spMap ev),
      ρ ≫ pullback.fst X.hom (spMap ev) = pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) ∧
      ρ ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) ≫ spMap σ.toRingHom :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap σ.toRingHom)
      (by rw [pullback.condition, Category.assoc, hev]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hρ : IsGrpPullback ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X) ((Over.pullback (spMap ev)).obj X)
      (spMap σ.toRingHom) ρ := hX.cancel (hXσ.congr hev.symm hρ1.symm) hρ2
  have hσχ := hρ.comp hχ
  obtain ⟨f, hf1, hf2⟩ : ∃ f : pullback X.hom (spMap ev) ⟶ pullback X.hom (spMap (σ.toRingHom.comp ev)),
      f ≫ ρ ≫ ψ ≫ φ = ψ ≫ φ ∧
      f ≫ pullback.snd X.hom (spMap (σ.toRingHom.comp ev)) = pullback.snd X.hom (spMap ev) :=
    ⟨hσχ.1.lift (ψ ≫ φ) (pullback.snd X.hom (spMap ev))
      (by rw [hχ.1.w]; simp only [Category.id_comp, hs]; try rfl), hσχ.1.lift_fst _ _ _, hσχ.1.lift_snd _ _ _⟩
  have hfg : IsGrpPullback ((Over.pullback (spMap ev)).obj X) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj X)
      (𝟙 _) f :=
    hσχ.cancel (hχ.congr (by simp only [Category.id_comp, hs]) hf1.symm)
      (by rw [Category.comp_id]; exact hf2)
  have hτ1 : f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)) = (f ≫ ρ) ≫ pullback.fst X.hom (spMap ev) := by
    rw [Category.assoc, hρ1]
  have hτχ : (f ≫ ρ) ≫ ψ ≫ φ = ψ ≫ φ := by rw [Category.assoc, hf1]
  have hτ2 : (f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = pullback.snd X.hom (spMap ev) ≫ spMap σ.toRingHom := by
    rw [Category.assoc, hρ2, ← Category.assoc, hf2]
  refine ⟨f, hfg, ?_, ?_⟩
  · have K1 : LBIso (LZ.pull ψ) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull LZ ψ ψ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => φ) _ ψ fun _ => rfl) H2
    have hA := pull_isLB hL (pullback.fst X.hom (spMap ev))
    have hC := pull_isLB hL₀ (ψ ≫ φ)
    have AC := LBIso.trans hA (pull_isLB hLZ ψ) hC H1 K1
    have D : LBIso (L.pull (f ≫ pullback.fst X.hom (spMap (σ.toRingHom.comp ev)))) (L₀.pull (ψ ≫ φ)) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => pullback.fst X.hom (spMap ev)) _ (f ≫ ρ) fun _ => hτ1)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L₀ _ (fun _ => ψ ≫ φ) _ (f ≫ ρ) fun _ => hτχ.symm) AC
    exact LBIso.trans hA hC (pull_isLB hL _) AC D.symm
  · intro q y₀ hq hq'
    have hqτ : q ≫ f ≫ ρ = spMap σ.toRingHom ≫ q := by
      apply hχ.1.hom_ext
      · rw [Category.assoc, hτχ, hq, Category.assoc, hq, ← Category.assoc, hs]
      · show (q ≫ f ≫ ρ) ≫ pullback.snd X.hom (spMap ev) = (spMap σ.toRingHom ≫ q) ≫ pullback.snd X.hom (spMap ev)
        rw [Category.assoc, hτ2, ← Category.assoc, hq', Category.assoc, hq', Category.id_comp, Category.comp_id]
    rw [hτ1, ← Category.assoc, hqτ, Category.assoc]

end GlobalTheory.Poinc.Sep.Twist
