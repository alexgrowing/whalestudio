import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeronNeutralComponentFiniteLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianFieldPointEqEighthPowerUniversalPullbStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.SharpOnV

theorem lAb : ∀ {X : Scheme.{0}} (G : Over X) (V : X.Opens), (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ V.toScheme), IsProper (pullback.snd G.hom (t ≫ V.ι))) → (V : Set X) ⊆ abLocus G := by
  intro X G V h s hs K _ _ t ⟨p, hp⟩
  have hr : Set.range t.base ⊆ (V : Set X) := by
    rintro _ ⟨q, rfl⟩
    have : q = p := Subsingleton.elim _ _
    subst this
    rw [hp]; exact hs
  let t' := IsOpenImmersion.lift V.ι t (by rwa [Scheme.Opens.range_ι])
  have ht : t' ≫ V.ι = t := IsOpenImmersion.lift_fac _ _ _
  have := h K t'
  rwa [ht] at this

theorem lGen : ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ X) (gm : G'.left ⟶ G.left), IsGrpPullback G' G ξ gm → IsGrpPullback A'.A G (jK R ≫ ξ) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) := by
  intro X G _ R _ _ _ G' _ _ D' A' U' ξ gm hgm
  exact ((GlobalTheory.NeutralLevel.isGrpPullback_of_iso_inv (jK R) G' U'.gen U'.gen_hom).comp hgm).congr rfl (Category.assoc _ _ _)

theorem lLB : ∀ {X : Scheme.{0}} (L : LB X) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))} (U' : Unif (maximalIdeal R) D' A' G') (gm : G'.left ⟶ X), L.IsLB → LBIso U'.LG.L (L.pull gm) → LBIso A'.L (L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm)) := by
  intro X L R _ _ _ G' _ _ D' A' U' gm hL hLB
  have hA := A'.isLB
  have ext : LBIso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK R))) := U'.ext
  have H1 := GlobalTheory.ThetaAffineGlue.lbIso_comp (pull_isLB hA _) U'.LG.isLB hL ext hLB
  have H2 := GlobalTheory.ThetaAffineGlue.lbIso_pull H1 U'.gen.inv.left
  have hP : (A'.L.pull U'.gen.hom.left).IsLB := pull_isLB hA _
  have refl : LBIso (A'.L.pull U'.gen.hom.left) (A'.L.pull U'.gen.hom.left) :=
    LBIso.trans hP (pull_isLB hP _) hP (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP) (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP))
  have H4 := GlobalTheory.ThetaAffineGlue.lbIso_pull refl U'.gen.inv.left
  have e : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  rw [e] at H4
  have H3 : LBIso A'.L ((A'.L.pull U'.gen.hom.left).pull U'.gen.inv.left) :=
    LBIso.trans hA (pull_isLB hA _) (pull_isLB hP _) (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hA) (LBIso.symm H4)
  exact LBIso.trans hA (pull_isLB hP _) (pull_isLB hL _) H3 H2

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → (V : Set M.Z) ⊆ abLocus FinalForm.G ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (ξ : Sp R ⟶ M.Z) (gm : G'.left ⟶ FinalForm.G.left), IsGrpPullback G' FinalForm.G ξ gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → ∀ ξ₀ : Sp (FractionRing R) ⟶ V.toScheme, ξ₀ ≫ V.ι = jK R ≫ ξ → ∃ c' pr', SharpBy F W A' (ξ₀ ≫ v) c' pr' ∧ ∀ (a b : Fin 8) (f : FinalForm.G ⟶ FinalForm.G) (f' : G' ⟶ G'), MatOn FinalForm pr a b f → f'.left ≫ gm = gm ≫ f.left → ∃ f₁ : A'.A ⟶ A'.A, MatEnd pr' a b f₁ ∧ (Over.pullback (jK R)).map f' ≫ U'.gen.hom = U'.gen.hom ≫ f₁ := by
  intro g n o _ ζ F W o' Ω _ _ _ _ S ρ u c pr hS M U₀ EE FinalForm hO V v hv
  have hK := GlobalTheory.T.semiAbelian_fieldPoint_eq_eighthPower_universal_pullback g n o ζ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm hO V v hv
  refine ⟨lAb FinalForm.G V fun K _ _ t => ?_, ?_⟩
  · obtain ⟨c', pr', -, -, huniv, -, -⟩ := hK K t ((Over.pullback (t ≫ V.ι)).obj FinalForm.G) (pullback.fst _ _)
      (isGrpPullback_pullback _ _)
    exact GlobalTheory.T.isProper_eighth_fibre_power_over pr' huniv c'.ab.proper
  · intro R _ _ _ hB G' _ _ hsemi D' A' U' ξ gm hgm hLB ξ₀ hξ₀
    have hpb : IsGrpPullback A'.A FinalForm.G (ξ₀ ≫ V.ι) (U'.gen.inv.left ≫ pullback.fst G'.hom (jK R) ≫ gm) :=
      (lGen U' ξ gm hgm).congr hξ₀.symm rfl
    have hL := lLB FinalForm.L.L U' gm FinalForm.L.isLB hLB
    obtain ⟨c', pr', hSP, hmon, huniv, hlb, hmat⟩ := hK (FractionRing R) ξ₀ A'.A _ hpb
    refine ⟨c', pr', ⟨hSP, hmon, huniv, hlb A'.L A'.isLB hL⟩, fun a b f f' hf hff' => ?_⟩
    have hgi : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    have hmapf : ((Over.pullback (jK R)).map f').left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ f'.left :=
      pullback.lift_fst _ _ _
    refine ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map f' ≫ U'.gen.hom, hmat a b f _ hf ?_, by simp⟩
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hgi, reassoc_of% hmapf, hff']

end GlobalTheory.Poinc.Eq8.SharpOnV

end
