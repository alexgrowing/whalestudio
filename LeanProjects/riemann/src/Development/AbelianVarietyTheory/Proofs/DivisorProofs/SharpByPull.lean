import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEighthPowerGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreUniformisedModelPointGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePolarisationEqEighthPowerPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullAlong

theorem sharpBy_pull {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (t : T' ⟶ T) (v : T' ⟶ F.X) (hv : t ≫ u = v)
    (c : SiegPre g n ζ (u ≫ F.s)) (pr : Fin 8 → (P.A ⟶ c.A)) (φA : P'.A.left ⟶ P.A.left)
    (hS : SharpBy F W P u c pr) (hA : IsGrpPullback P'.A P.A t φA) (hL : LBIso P'.L (P.L.pull φA)) :
    ∃ (c' : SiegPre g n ζ (v ≫ F.s)) (pr' : Fin 8 → (P'.A ⟶ c'.A)) (χ : c'.A.left ⟶ c.A.left),
      SharpBy F W P' v c' pr' ∧ IsGrpPullback c'.A c.A t χ ∧ ∀ a, (pr' a).left ≫ χ = φA ≫ (pr a).left := by
  subst hv
  obtain ⟨hpb, hmon, huniv, hLc⟩ := hS
  have hid : spMap (RingHom.id o) = 𝟙 (Sp o) := Spec.map_id _
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n o o ζ ζ (RingHom.id o) T T' (u ≫ F.s)
    ((t ≫ u) ≫ F.s) t rfl (by rw [hid, Category.comp_id, Category.assoc])).1 c
  have hcomp := GlobalTheory.SiegelPullComp.pb_comp hpb hc'
  obtain ⟨χ, χ₂, hχ, hsq, hP, -⟩ := hc'
  obtain ⟨pr', hpr', hmon', huniv'⟩ := GlobalTheory.T.eighthPowerProjections_groupPullback pr hA hχ hmon huniv
  exact ⟨c', pr', χ, ⟨hcomp, hmon', huniv', GlobalTheory.T.lineBundleIso_eighthPower_groupPullback c.P c'.P P.L P'.L pr pr' W c.isLB c'.isLB P.isLB P'.isLB hsq hP hpr' hL hLc⟩,
    hχ, hpr'⟩

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ FinalForm.u₀ ≫ u) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  intro g n o _ ζ F W o' Ω _ _ _ S ρ u c pr hS M U₀ EE FinalForm R _ _ _ _ G' _ _ _ D' A' U' ξ gm hgm hLB ξ₀ hξ₀
  obtain ⟨ψ, hψφ, hψs, hψpb⟩ := GlobalTheory.T.genericFibre_uniformisedModelPoint_groupPullback FinalForm U' ξ gm hgm ξ₀ hξ₀
  have hL := GlobalTheory.T.genericFibre_polarisation_eq_eighthPower_pullback FinalForm U' gm ψ hψφ hLB
  obtain ⟨c', pr', χ, hS', hχ, hpr'⟩ := sharpBy_pull F W ρ.P A' u (ξ₀ ≫ FinalForm.u₀) (ξ₀ ≫ FinalForm.u₀ ≫ u)
    (Category.assoc _ _ _) c pr (ψ ≫ pullback.fst _ _) hS hψpb hL
  refine ⟨c', pr', hS', fun a b f f' hf hff' => ?_⟩
  obtain ⟨-, f₁, hf₁, hf₁φ⟩ := hf
  refine ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom, ?_, by simp⟩
  refine GlobalTheory.T.elementaryMatrixEndomorphism_groupPullback_transport pr pr' a b f₁ _ hψpb hχ hpr' ?_ hf₁
  have hgi : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have hmapf : ((Over.pullback (jK R)).map f').left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ f'.left :=
    pullback.lift_fst _ _ _
  have hmapf₁ : ((Over.pullback FinalForm.u₀).map f₁).left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f₁.left :=
    pullback.lift_fst _ _ _
  have key : (U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom).left ≫ ψ = ψ ≫ ((Over.pullback FinalForm.u₀).map f₁).left := by
    apply FinalForm.cart.1.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [hψφ, reassoc_of% hgi, reassoc_of% hmapf, hff', hf₁φ, reassoc_of% hψφ]
    · have w1 : ((Over.pullback FinalForm.u₀).map f₁).left ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom =
          ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom := Over.w _
      have w2 : ψ ≫ ((Over.pullback FinalForm.u₀).obj ρ.P.A).hom = A'.A.hom ≫ ξ₀ := hψs
      simp only [Category.assoc, w1, w2]
      rw [← Category.assoc, Over.w]
  rw [← Category.assoc, key, Category.assoc, hmapf₁, Category.assoc]

end GlobalTheory.Poinc.Eq8.PullAlong

end
