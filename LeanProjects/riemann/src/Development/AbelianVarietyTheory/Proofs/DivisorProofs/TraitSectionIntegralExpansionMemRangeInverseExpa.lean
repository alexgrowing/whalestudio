import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Mum.TraitValue

theorem value_of_expands {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Sp (FractionRing W))} {G : Over (Sp W)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (F : Type) [Field F] [Algebra (FractionRing W) F] {k : ℕ} (hk : 1 ≤ k)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK W))))
    (t : SecK A.L (snd (TFK (R := W) F) A.A).left k) (s : Fam D.toPre F k) (h : U.ExpandsF F k w t s)
    (σ : H0 U.LG.L k) (f : ∀ x, D.toPre.SecB k x) (hσ : ∀ e, U.ExpandsAt e k σ f)
    (hs : ∀ x, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F x) (DegPre.famε k) (s.s x) (D.toPre.famφB x)
      (DegPre.famε k) (f x) (DegPre.prB D.toPre F).left 1)
    (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ A.A).left) (z : Z) JG Jt (hG : Good U.LG.L z JG) (ht : Good A.L z Jt) :
    sval σ (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W)) z JG =
      (gw w (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left) z
        (JG (q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W)))
        (fun _ => Jt (q ≫ (snd (TFK (R := W) F) A.A).left)) ^ k).val * sval t q z Jt := by
  obtain ⟨σ', h₁, h₂⟩ := h
  have h₃ : U.ExpandsG F k (extendSec U.toUnifPre F k (genericSec U.toUnifPre k σ)) s := by
    refine (expandsG_iff U.toUnifPre F k _ s).2 ⟨1, fun _ => 1, fun _ => (σ, f), fun _ => hσ, ?_, fun α => ?_⟩
    · rw [Fin.sum_univ_one, one_smul]
    · rw [Fin.sum_univ_one, one_smul]
      refine sec_ext' D.toPre.P.isLB fun y J hJ => ?_
      have a := (secScal_iff_val D.toPre.P.isLB _ _ _ _).1 (hs α) y J hJ
      rw [gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul] at a
      exact a.symm.trans ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing W) F))))))).symm
  obtain rfl : σ' = _ :=
    ((expandsG_bijective U.toUnifPre F GlobalTheory.allSixLaws.1.globalFns hk (U.expand k hk)).2 s).unique h₂ h₃
  let n : TFK (R := W) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have e₁ : (q ≫ n.left) ≫ (U.genF F).left = q := by
    rw [Category.assoc, ← Over.comp_left, hn, Over.id_left, Category.comp_id]
  have e₂ : (q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left =
      q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left := by
    rw [Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left]
  have e₃ : (q ≫ n.left) ≫ UnifPre.gFK (G := G) F =
      q ≫ (snd (TFK (R := W) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK W) := by
    rw [← Category.assoc, e₂, Category.assoc, Category.assoc]
  have e₄ : ((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left =
      q ≫ (snd (TFK (R := W) F) A.A).left := by
    rw [e₂, Category.assoc, Category.assoc, ← Over.comp_left _ _ _ U.gen.inv, Iso.inv_hom_id, Over.id_left,
      Category.comp_id]
  have key := (isoRelM_iff w _ k _ h₁.1 _ h₁.2.1 _ _).1 h₁ Z (q ≫ n.left) z
    (JG ((q ≫ n.left) ≫ UnifPre.gFK (G := G) F))
    (Jt (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left))
    (hG ((q ≫ n.left) ≫ UnifPre.gFK (G := G) F))
    (ht (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫ U.gen.hom.left))
  rw [Category.comp_id, e₁, e₄, zpow_natCast] at key
  have v : sval (extendSec U.toUnifPre F k (genericSec U.toUnifPre k σ)) (q ≫ n.left) z JG =
      sval σ (((q ≫ n.left) ≫ (snd (TFK (R := W) F) ((Over.pullback (jK W)).obj G)).left) ≫
        pullback.fst G.hom (jK W)) z JG :=
    (sval_pullOver _ _ _ _ hG).trans (sval_pullOver _ _ _ _ hG)
  have key' := v.symm.trans key
  rw [e₂, e₃, Category.assoc, Category.assoc] at key'
  exact key'

theorem value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W)))), w₀.IsGen → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ s', T.U.ExpandsF F (C.n ^ j) w₀ (E' s') s') → ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s' : Fam T.D'.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((s').s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1) → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JG Jt, Good C.P.L.L z JP → Good T.U.LG.L z JG → Good T.A.L z Jt → sval σ p z JP = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' s') q z Jt := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ w₀ _ E' hE F₀ s' σ hs ⟨σ'', f'', hc, hp, he⟩ Z p q h₁ h₂ z JP JG Jt gP gG gt
  have hk : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have ep : p = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) := by
    refine T.cart.1.hom_ext (by rw [h₁]; simp only [Category.assoc]) ?_
    have a₁ : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have a₂ : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom =
        (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have a₃ : spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) = jFK (R := W) F ≫ jK W :=
      Spec.map_comp (CommRingCat.ofHom (algebraMap W (FractionRing W))) (CommRingCat.ofHom (algebraMap (FractionRing W) F))
    rw [h₂, a₃, Category.assoc, Category.assoc, Category.assoc, pullback.condition, reassoc_of% a₁, reassoc_of% a₂]
  have c := hc Z p z JP JG gP gG
  have h1 : Out.scal T.G.hom (1 : W) = 1 := by unfold Out.scal; rw [map_one, map_one]
  rw [h1, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul] at c
  have v := value_of_expands T.U F hk w₀ (E' s') s' (hE s') σ'' f'' he (hs f'' hp) Z q z JG Jt gG gt
  rw [c, _root_.mul_assoc, ← v, ← ep]

end GlobalTheory.Mum.TraitValue
