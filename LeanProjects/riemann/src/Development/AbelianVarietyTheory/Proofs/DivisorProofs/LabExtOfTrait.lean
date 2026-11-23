import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsFinExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}

theorem Trait.exists_lift {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W)
    (F : Type) [Field F] [Algebra (FractionRing W) F] (z : Sp F ⟶ C.G.left)
    (hz : z ≫ C.G.hom = jFK (R := W) F ≫ jK W ≫ T.ξ) :
    ∃ x : TFK (R := W) F ⟶ T.A.A, x.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z := by
  have w₁ : z ≫ C.G.hom = (jFK (R := W) F ≫ jK W) ≫ T.ξ := by rw [hz, Category.assoc]
  have w₂ : T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁ ≫ T.G.hom = jFK (R := W) F ≫ jK W :=
    T.cart.1.lift_snd _ _ _
  let g₂ : Sp F ⟶ pullback T.G.hom (jK W) := pullback.lift (T.cart.1.lift z (jFK (R := W) F ≫ jK W) w₁) (jFK (R := W) F) w₂
  have hs : T.U.gen.hom.left ≫ T.A.A.hom = pullback.snd T.G.hom (jK W) := Over.w T.U.gen.hom
  have hgi : T.U.gen.hom.left ≫ T.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  refine ⟨Over.homMk (g₂ ≫ T.U.gen.hom.left) (by
    show (g₂ ≫ T.U.gen.hom.left) ≫ T.A.A.hom = jFK (R := W) F
    rw [Category.assoc, hs]; exact pullback.lift_snd _ _ _), ?_⟩
  show (g₂ ≫ T.U.gen.hom.left) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = z
  rw [Category.assoc, reassoc_of% hgi, pullback.lift_fst_assoc]
  exact T.cart.1.lift_fst _ _ _

end GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.LabTrans GlobalTheory.ArcPull

theorem labExt_of_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], Nonempty (Trait C W) →
    ∀ σ : Kb R →ₐ[FractionRing R] Kb R, LabExt σ (C.lab j) (C.lab j) := by
  intro R _ _ _ hR D C j W _ _ _ ⟨T⟩ σ p q hpq
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  have hGF := hL.globalFns
  have := hR.2
  have hB := D.tau_bimult
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  letI : Algebra (FractionRing R) (Kb W) := ((algebraMap (FractionRing W) (Kb W)).comp (fracMap T.inj)).toAlgebra
  have cF : Compat T.φ (Kb W) := fun r => congrArg (algebraMap (FractionRing W) (Kb W)) (fracMap_algebraMap T.inj r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) (Kb W)
  obtain ⟨r, hr⟩ := exists_ext hB em q
  have hr' : QkExt (em.comp σ).toRingHom p r := qkExt_trans hpq hr
  have hr₁ := isPullGtF_pullGt T.hD hGF cF r.g

  have hgp : jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ = jFK (R := R) (Kb W) ≫ C.gp := by
    let ρ : R →+* Kb W := (algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp T.φ)
    have hρ : Function.Injective ρ :=
      (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
    have hy : (jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ) ≫ C.π = spMap ρ := by
      rw [Category.assoc, Category.assoc, T.ξ_π, spMap_comp, spMap_comp]
    obtain ⟨ga, hga, e⟩ := Modif.factor_gp R C.toModif (Kb W) ρ _ hρ hy
    have hga' : ga = algebraMap (FractionRing R) (Kb W) :=
      IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun s => (hga s).trans (cF s).symm)
    rw [e, hga']
  have hz : ∀ (τ : Kb R →ₐ[FractionRing R] Kb W) (x : TFK (R := R) (Kb R) ⟶ C.A.A),
      (spMap τ.toRingHom ≫ x.left ≫ C.α) ≫ C.G.hom = jFK (R := W) (Kb W) ≫ jK W ≫ T.ξ := by
    intro τ x
    rw [hgp, Category.assoc, Category.assoc, C.α_cart.1.w, ← Category.assoc x.left, Over.w x, ← Category.assoc]
    show (spMap τ.toRingHom ≫ spMap (algebraMap (FractionRing R) (Kb R))) ≫ C.gp = _
    rw [← spMap_comp]; exact congrArg (fun f => spMap f ≫ C.gp) τ.comp_algebraMap
  obtain ⟨x₁, hx₁⟩ := T.exists_lift (Kb W) _ (hz em (C.lab j q))
  obtain ⟨x₂, hx₂⟩ := T.exists_lift (Kb W) _ (hz (em.comp σ) (C.lab j p))
  have t₁ := T.lab (Kb W) em cF j q r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₁ hr rfl hr₁ hx₁
  have t₂ := T.lab (Kb W) (em.comp σ) cF j p r (pullQk T.hD hGF cF hB T.D'.tau_bimult r) x₂ hr' rfl hr₁ hx₂
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause W _ bW T.D' T.A T.G hGs T.U (Kb W) (C.n ^ j) hk
  have e : x₁ = x₂ := ((hf.1 _ _).1 t₁).trans ((hf.1 _ _).1 t₂).symm
  subst e
  have e' := hx₁.symm.trans hx₂
  haveI : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (spMap em.toRingHom)).1 (C.α_cart.1.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, e', Category.assoc, ← Category.assoc (spMap em.toRingHom), ← spMap_comp]
    rfl
  · rw [Category.assoc, Over.w (C.lab j q), Category.assoc, Category.assoc, Over.w (C.lab j p)]
    exact congrArg (spMap em.toRingHom ≫ ·) ((spMap_comp _ _).symm.trans (congrArg spMap σ.comp_algebraMap)).symm

end GlobalTheory.Mum
