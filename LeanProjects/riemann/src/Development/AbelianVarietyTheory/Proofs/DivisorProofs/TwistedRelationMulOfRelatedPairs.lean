import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGeneratStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianParStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.ProdRel

variable {R : Type} [CommRing R] [IsDomain R]

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem comp_tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) {T : Over (Spec (CommRingCat.of R))} (r : T ⟶ D.P.A) (k : Fin 5) :
    r.left ≫ tφ D a β k = ((![r, r * cP D T β, cP D T β, 1, r ≫ a] : Fin 5 → (T ⟶ D.P.A)) k).left := by
  fin_cases k
  · show r.left ≫ 𝟙 _ = r.left; simp
  · show r.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c β)).left = (r * cP D T β).left
    rw [← Over.comp_left, padd, ← Hom.mul_def, MonObj.comp_mul, Category.comp_id]
    congr 2
    exact comp_cP D r β
  · show r.left ≫ (toUnit D.P.A ≫ D.c β).left = (cP D T β).left
    rw [← Over.comp_left]; exact congrArg _ (comp_cP D r β)
  · show r.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (1 : T ⟶ D.P.A).left
    rw [← Over.comp_left, Hom.one_def, ← Category.assoc, toUnit_unique (r ≫ toUnit _) (toUnit T)]
  · show r.left ≫ a.left = (r ≫ a).left; rw [Over.comp_left]

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem formEq (D : DegPre R) (a : D.P.A ⟶ D.P.A) (mu β β' β₁ β₁' : D.X) (n j n' j' : ℤ) :
    FormEq (Sum.elim (Sum.elim (Sum.elim (dφ D a mu β β₁) (dφ D a mu β' β₁'))
        (fun k => (lift (cP D (DegPre.BF D (FractionRing R)) β₁) (lift (cP D (DegPre.BF D (FractionRing R)) β₁')
          (DegPre.prB D (FractionRing R)))).left ≫ thφ D.P.A (x3 D.P.A) k))
        (fun k => (lift (cP D (DegPre.BF D (FractionRing R)) β) (lift (cP D (DegPre.BF D (FractionRing R)) β')
          (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)))).left ≫ thφ D.P.A (x3 D.P.A) k))
      (Sum.elim (Sum.elim (Sum.elim (dε n j) (dε n' j')) thε) (fun k => - thε k))
      (dφ D a mu (β + β') (β₁ + β₁')) (dε (n + n') (j + j')) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [prod_cub, prod_cub]
  simp only [dφ, dε, Sum.elim_inl, Sum.elim_inr]
  simp only [← Category.assoc, ← Over.comp_left]
  simp only [comp_tφ]
  simp only [Fin.prod_univ_five, tε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, zpow_one, neg_neg]
  have htr : DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
      DegPre.prB D (FractionRing R) * cP D (DegPre.BF D (FractionRing R)) mu := by
    simp only [DegPre.trF, DegPre.prB, lift_snd, padd, ← Hom.mul_def]; rfl
  rw [htr, cPoint_add, cPoint_add]
  generalize DegPre.prB D (FractionRing R) = Y
  generalize cP D (DegPre.BF D (FractionRing R)) mu = Cm
  generalize cP D (DegPre.BF D (FractionRing R)) β = Cb
  generalize cP D (DegPre.BF D (FractionRing R)) β' = Cb'
  generalize cP D (DegPre.BF D (FractionRing R)) β₁ = Cc
  generalize cP D (DegPre.BF D (FractionRing R)) β₁' = Cc'
  rw [mul_comm Cc Y, mul_comm Cc' Y, mul_comm Cb (Y * Cm), mul_comm Cb' (Y * Cm), mul_comm (Cc * Cc') Y,
    mul_comm (Cb * Cb') (Y * Cm)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem trF_prB (D : DegPre R) (mu : D.X) : DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R) =
    DegPre.prB D (FractionRing R) * cP D (DegPre.BF D (FractionRing R)) mu := by
  simp only [DegPre.trF, DegPre.prB, lift_snd, padd, ← Hom.mul_def]; rfl

theorem zF_prB (D : DegPre R) : DegPre.zF D (FractionRing R) ≫ DegPre.prB D (FractionRing R) = 1 := by
  simp only [DegPre.zF, DegPre.prB, lift_snd, Hom.one_def]

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_prodFac (D : DegPre R) (hB : D.TauBimult) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) (n j n' j' : ℤ)
    (mu β β' β₁ β₁' : D.X) (uf : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β₁) (dε n j)))
    (ug : LB.Gen (LB.LinComb D.P.L (dφ D a mu β' β₁') (dε n' j')))
    (hf : IsFac D a h n j mu β β₁ uf) (hg : IsFac D a h n' j' mu β' β₁' ug) :
    ∃ w : LB.Gen (LB.LinComb D.P.L (dφ D a mu (β + β') (β₁ + β₁')) (dε (n + n') (j + j'))),
      IsFac D a h (n + n') (j + j') mu (β + β') (β₁ + β₁') w ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
        val w x z J = val uf x z J * val ug x z J *
          val D.cub.t (x ≫ (lift (cP D (DegPre.BF D (FractionRing R)) β₁) (lift (cP D (DegPre.BF D (FractionRing R)) β₁')
            (DegPre.prB D (FractionRing R)))).left) z J *
          (val D.cub.t (x ≫ (lift (cP D (DegPre.BF D (FractionRing R)) β) (lift (cP D (DegPre.BF D (FractionRing R)) β')
            (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)))).left) z J)⁻¹ := by
  let c1 := LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    (lift (cP D (DegPre.BF D (FractionRing R)) β₁) (lift (cP D (DegPre.BF D (FractionRing R)) β₁')
      (DegPre.prB D (FractionRing R)))).left
  let c2 := LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    (lift (cP D (DegPre.BF D (FractionRing R)) β) (lift (cP D (DegPre.BF D (FractionRing R)) β')
      (DegPre.trF D (FractionRing R) mu ≫ DegPre.prB D (FractionRing R)))).left
  let w0 := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ uf ug) c1)
    (LB.invGen D.P.L _ _ c2)
  have hw0 : w0.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hf.1 hg.1)
    (pullGen_isGen _ _ _ _ D.cub.isGen _)) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))
  obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (formEq D a mu β β' β₁ β₁' n j n' j') w0 hw0
  have ev : ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
      val w x z J = val uf x z J * val ug x z J * val c1 x z J * (val c2 x z J)⁻¹ := fun Z x z J hJ => by
    exact (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) (val_inv _ _)))
  refine ⟨w, ⟨hw, fun z J hJ => ?_⟩, fun Z x z J hJ => ?_⟩
  · rw [ev _ _ z J hJ, hf.2 z J hJ, hg.2 z J hJ, val_cub D.cub (DegPre.zF D (FractionRing R)) hJ,
      val_cub D.cub (DegPre.zF D (FractionRing R)) hJ, comp_cP, comp_cP, comp_cP, comp_cP, zF_prB,
      trF_prB, MonObj.comp_mul, zF_prB, comp_cP, _root_.one_mul, (isCub_cubV D.cub hJ).face₃]
    have t := tau_mul (𝟙 (TF (R := R) (FractionRing R))) hJ hB β β' mu
    rw [tau_symm (𝟙 (TF (R := R) (FractionRing R))) hJ (β + β'), tau_symm (𝟙 (TF (R := R) (FractionRing R))) hJ β,
      tau_symm (𝟙 (TF (R := R) (FractionRing R))) hJ β'] at t
    simp only [Over.id_left, Category.id_comp] at t
    have t' := congrArg Additive.ofMul t
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv, ofMul_one] at t' ⊢
    linear_combination (norm := module) -t'
  · exact (ev _ _ z J hJ).trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))
      (congrArg (·⁻¹) (val_pull hJ _ _ _)))

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem comp_cub (D : DegPre R) (β β' : D.X) {T : Over (Spec (CommRingCat.of R))} (r : T ⟶ D.P.A) :
    r.left ≫ (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left =
      (lift (cP D T β) (lift (cP D T β') r) : T ⟶ G3 D.P.A).left := by
  rw [← Over.comp_left, comp_lift, comp_lift, Category.comp_id, ← comp_cP D r β, ← comp_cP D r β']
  rfl

theorem trel_prod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (mu β β' β₁ β₁' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β') (p : SecT D.toPre a n'' j'' (β + β')) (f₁ : SecT D.toPre a n j β₁) (g₁ : SecT D.toPre a n' j' β₁') (p₁ : SecT D.toPre a n'' j'' (β₁ + β₁')), β₁ = β + shift h h' n j mu → β₁' = β' + shift h h' n' j' mu → IsProdT f g p → IsProdT f₁ g₁ p₁ → TRel h mu f f₁ → TRel h mu g g₁ → TRel h mu p p₁ := by
  intro R _ _ _ hA D a a' h h' hE n j n' j' n'' j'' hn hj mu β β' β₁ β₁' f g p f₁ g₁ p₁ e e' hp hp₁ hf hg
  subst hn hj
  obtain ⟨v, hv⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hA D a a' h h' hE n j mu β β₁ e
  obtain ⟨v', hv'⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hA D a a' h h' hE n' j' mu β' β₁' e'
  obtain ⟨v'', hv''⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hA D a a' h h' hE (n + n') (j + j') mu (β + β') (β₁ + β₁') (by
    rw [e, e']; simp only [shift, add_smul]; abel)
  obtain ⟨uf, huf⟩ := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hA D a h hE.1 hE.2.2.2.1 n j mu β β₁ v hv).1
  obtain ⟨ug, hug⟩ := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hA D a h hE.1 hE.2.2.2.1 n' j' mu β' β₁' v' hv').1
  obtain ⟨w, hw, ew⟩ := exists_prodFac D.toPre D.tau_bimult a h n j n' j' mu β β' β₁ β₁' uf ug huf hug
  intro u hu Z x z J hJ
  have e₁ := hp₁ Z (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J hJ
  have e₂ := hp Z (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J hJ
  rw [Category.assoc, comp_cub] at e₁
  rw [Category.assoc, show ((DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.prB D.toPre (FractionRing R)).left) ≫ _ = _
    from comp_cub D.toPre β β' (DegPre.trF D.toPre (FractionRing R) mu ≫ DegPre.prB D.toPre (FractionRing R))] at e₂
  rw [e₁, e₂, hf uf huf Z x z J hJ, hg ug hug Z x z J hJ,
    (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hA D a h hE.1 hE.2.2.2.1 _ _ mu _ _ v'' hv'').2.1 u w hu hw Z x z J hJ, ew Z x z J hJ]
  have key : ∀ {S : Type} [CommRing S] (s t : S) (c₁ c₂ b₁ b₂ : Sˣ),
      s * b₁.val * (t * b₂.val) * c₁.val = s * t * c₂.val * (b₁ * b₂ * c₁ * c₂⁻¹).val := by
    intro S _ s t c₁ c₂ b₁ b₂
    simp only [Units.val_mul]
    linear_combination (-(s * t * b₁.val * b₂.val * c₁.val)) * c₂.mul_inv
  exact key _ _ _ _ _ _

end GlobalTheory.TwFam.ProdRel
