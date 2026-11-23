import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

variable {R : Type} [CommRing R] [IsDomain R]

theorem famMapTw_trPt (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {b b' : TF (R := R) (Kb R) ⟶ D.P.A}
    (hb : twF ρ ≫ b = b') : famMapTw D ρ ≫ DegPre.trPt D (Kb R) b = DegPre.trPt D (Kb R) b' ≫ famMapTw D ρ := by
  subst hb
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trPt]
  · simp [DegPre.trPt, padd, comp_lift_assoc]

theorem zF_famMapTw (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) :
    DegPre.zF D (Kb R) ≫ famMapTw D ρ = twF ρ ≫ DegPre.zF D (Kb R) := by
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem famMapTw_famφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) (β : D.X) (i : Fin 4) :
    (famMapTw D ρ).left ≫ DegPre.famφ D (Kb R) β i = DegPre.famφ D (Kb R) β i :=
  (famφ_famMap D (Kb R) (TwF ρ) β i).symm

theorem famMapTw_phiφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {y y₀ : D.X} (α : D.X)
    {b b₀ : TF (R := R) (Kb R) ⟶ D.P.A} (hy : y₀ = y) (hb : twF ρ ≫ b₀ = b) :
    (fun k => (famMapTw D ρ).left ≫ DegPre.phiφ D (Kb R) y₀ α b₀ k) = DegPre.phiφ D (Kb R) y α b := by
  subst hy
  funext k
  rcases k with i | i
  · exact famMapTw_famφ D ρ _ i
  · show (famMapTw D ρ).left ≫ (DegPre.trPt D (Kb R) b₀).left ≫ DegPre.famφ D (Kb R) α i =
      (DegPre.trPt D (Kb R) b).left ≫ DegPre.famφ D (Kb R) α i
    rw [← Category.assoc, ← Over.comp_left, famMapTw_trPt D ρ hb, Over.comp_left, Category.assoc,
      famMapTw_famφ]

theorem twF_left (ρ : Kb R →ₐ[FractionRing R] Kb R) : (twF ρ).left = spMap ρ.toRingHom := rfl

end GlobalTheory.Mum.Conj.PhiTw

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

theorem phiRel_famTw : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N),
    PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  intro R _ _ D N τ p p₀ h w s s' H α u hu hu0
  have hL := D.P.isLB
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  let σ : Kb R →ₐ[FractionRing R] Kb R := (e.symm : Kb R →ₐ[FractionRing R] Kb R)
  have hστ : ∀ x, σ (τ x) = x := fun x => e.symm_apply_apply x
  have hτσ : ∀ x, τ (σ x) = x := fun x => e.apply_symm_apply x
  have hb₀ : twF τ ≫ p.g.b = p₀.g.b := Over.OverMorphism.ext (by
    rw [Over.comp_left, twF_left]; exact h.2.1.symm)
  have hb : twF σ ≫ p₀.g.b = p.g.b := by
    rw [← hb₀, ← Category.assoc, twF_comp_eq_id hστ, Category.id_comp]
  have hφ := famMapTw_phiφ D σ α h.1 hb
  let u' := genCast hφ (LB.pullGen D.P.L _ _ u (famMapTw D σ).left)
  have hu' : u'.IsGen := genCast_isGen _ (DVR.pullGen_isGen _ _ _ u hu _)
  have hid : (twF σ).left ≫ spMap τ.toRingHom = 𝟙 _ := by
    rw [← twF_left, ← Over.comp_left, twF_comp_eq_id hστ]; rfl
  have hz : (DegPre.zF D (Kb R)).left ≫ (famMapTw D σ).left = (twF σ).left ≫ (DegPre.zF D (Kb R)).left := by
    rw [← Over.comp_left, zF_famMapTw, Over.comp_left]
  have hu'0 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (DegPre.zF D (Kb R)).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) := corr_of_val hL fun y J hJ => by
    rw [val_pull hJ, val_genCast, val_pull hJ, Category.id_comp, hz, ← val_pull hJ, val_corr hJ hu0,
      val_mul hJ, val_mul hJ, val_corr hJ (h.2.2 α), val_pull hJ, frTw, val_genCast, val_pull hJ, hid]
  have H1 := (secRel_iff hL _ _ _ _ _ _ _ _ _ u').1 (H α u' hu' hu'0)
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e1 := H1 _ (famMapTw D τ).left y J hJ
  have hTT : (famMapTw D τ).left ≫ (famMapTw D σ).left = 𝟙 _ := by
    rw [← Over.comp_left, famMapTw_comp_eq_id D hτσ]; rfl
  rw [val_genCast, val_pull hJ, hTT] at e1
  rw [← h.1] at e1
  have hc : (famMapTw D τ).left ≫ (DegPre.trPt D (Kb R) p.g.b).left =
      (DegPre.trPt D (Kb R) p₀.g.b).left ≫ (famMapTw D τ).left := by
    rw [← Over.comp_left, famMapTw_trPt D τ hb₀, Over.comp_left]
  rw [sval_famTw _ _ _ _ _ _ hJ, sval_famTw _ _ _ _ _ _ hJ]
  simp only [Category.id_comp]
  rw [e1, hc]

end GlobalTheory.Mum.Conj.PhiTw
