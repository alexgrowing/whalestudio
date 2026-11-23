import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefAtPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem gm_spMap_unitOn_top {A B : Type} [CommRing A] [CommRing B] (m : A →+* B) (z : Sp B) (k : Aˣ) :
    gm (spMap m) z ⊤ (unitOn k) = gm (𝟙 (Sp B)) z ⊤ (unitOn (Units.map m.toMonoidHom k)) := by
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  have nat := congrArg (fun q => q.hom k.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom m))
  exact congrArg ((Sp B).presheaf.germ ⊤ z trivial).hom nat.symm

theorem from_pull : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D), Function.Injective f → From T ω s ε n D₀.toPre e β ββ w → ∃ ββ' w', From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ Jd D₀ ω s e β ββ w f D hD hf hF
  obtain ⟨pb, sq, gen, hc, hτ⟩ := hF
  have hR : ∃ (β₂₁ : (G2 D.P.A).left ⟶ (G2 D₀.toPre.P.A).left)
      (w₁ : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ D₀.toPre.P.A D₀.toPre.P.L).pull β₂₁)),
      IsGrpPullback D.P.A D₀.toPre.P.A (spMap f) (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ∧
      IsSquare (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) β₂₁ ∧ w₁.IsGen ∧
      (∀ a, (D.c a).left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) =
        spMap f ≫ (D₀.toPre.c (hD.xe a)).left) ∧
      ∀ κ : (TK V).left ⟶ (TK R).left, κ ≫ jK R = jK V ≫ spMap f → ∀ a b z J J', Good D₀.toPre.P.L z J →
        Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
          lamVal w₁ (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left z J J' *
            val (D₀.toPre.tau (hD.xe a) (hD.xe b)) κ z J := by
    obtain ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, tau₁⟩ := GlobalTheory.MumFam.refAt_pull R V f hf Jd D₀ D hD
    exact ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, fun κ hκ a b z J J' hJ hJ' => (tau₁ κ hκ a b z J J' hJ hJ').trans
      (congrArg _ ((Wit.exists_tau D₀.toPre (hD.xe a) (hD.xe b)).choose_spec.2 _ κ z J hJ))⟩
  obtain ⟨β₂₁, w₁, pb₁, sq₁, gen₁, c₁, tau₁⟩ := hR
  have hΛT : (abelian₂ T.B T.M.L).IsLB := DVR.linComb_isLB _ T.M.isLB _ _
  have hΛ₀ : (abelian₂ D₀.toPre.P.A D₀.toPre.P.L).IsLB := DVR.linComb_isLB _ D₀.toPre.P.isLB _ _
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  obtain ⟨w', T3⟩ := exists_comp hΛ₀ w w₁ ((isGen_iff _).1 gen) ((isGen_iff _).1 gen₁) hΛT hΛ
  refine ⟨β₂₁ ≫ ββ, w', (IsGrpPullback.comp pb₁ pb).congr (GlobalTheory.HalfBC.spMap_comp_spMap' ω f) rfl, ⟨?_, ?_⟩,
    (isGen_iff _).2 (T3.pgen_comp hΛ₀ ((isGen_iff _).1 gen) ((isGen_iff _).1 gen₁)), fun a => ?_, fun a b => ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (β₂₁ ≫ ·) sq.1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) sq₁.1).trans (Category.assoc _ _ _))))
  · exact (Category.assoc _ _ _).trans ((congrArg (β₂₁ ≫ ·) sq.2).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ β) sq₁.2).trans (Category.assoc _ _ _))))
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ β) (c₁ a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (spMap f ≫ ·) (hc (hD.xe a))).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (GlobalTheory.HalfBC.spMap_comp_spMap' ω f))))))
  · obtain ⟨k₀, hk₀, hv₀⟩ := hτ (hD.xe a) (hD.xe b)
    let m : FractionRing R →+* FractionRing V := IsLocalization.map (FractionRing V) f (M := nonZeroDivisors R)
      (T := nonZeroDivisors V) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)
    have hm : ∀ r, m (algebraMap R (FractionRing R) r) = algebraMap V (FractionRing V) (f r) := fun r =>
      IsLocalization.map_eq _ _
    refine ⟨Units.map m.toMonoidHom k₀, ?_, fun z Jt J' hJt hJ' => ?_⟩
    · show m k₀ = _
      rw [hk₀, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, hm]
      rfl
    · let κ : (TK V).left ⟶ (TK R).left := spMap m
      have hκ : κ ≫ jK R = jK V ≫ spMap f := by
        show spMap m ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap V (FractionRing V)) ≫ spMap f
        rw [GlobalTheory.HalfBC.spMap_comp_spMap', GlobalTheory.HalfBC.spMap_comp_spMap']
        congr 1
        exact RingHom.ext hm
      choose J₁ hJ₀ using fun χ : (TK V).left ⟶ D₀.toPre.P.A.left => exists_chart D₀.toPre.P.isLB (χ z)
      have hJ₁ : Good D₀.toPre.P.L z J₁ := hJ₀
      have t₁ := tau₁ κ hκ a b z J₁ J' hJ₁ hJ'
      have n₁ : val (D₀.toPre.tau (hD.xe a) (hD.xe b)) (κ ≫ 𝟙 _) z J₁ = Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (D₀.toPre.tau (hD.xe a) (hD.xe b)) (𝟙 _) (κ z) (fun ψ => J₁ (κ ≫ ψ))) :=
        Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) κ z J₁ hJ₁).2.2.1 _)
      rw [Category.comp_id] at n₁
      have h₀ := hv₀ (κ z) (fun ψ => Jt (κ ≫ ψ)) (fun ψ => J₁ (κ ≫ ψ)) (fun ψ => hJt (κ ≫ ψ)) (fun ψ => hJ₁ (κ ≫ ψ))
      have h₁ := (congrArg (Units.map (κ.stalkMap z).hom.toMonoidHom) h₀).trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_mul _ _ _)))
      have g₁ : Units.map (κ.stalkMap z).hom.toMonoidHom (gm (𝟙 (TK R).left) (κ z) ⊤ (unitOn k₀)) =
          gm (𝟙 (TK V).left) z ⊤ (unitOn (Units.map m.toMonoidHom k₀)) := by
        rw [← GlobalTheory.ConstFam.gm_comp_stalkMap κ (𝟙 _) z ⊤ trivial, Category.comp_id]
        exact gm_spMap_unitOn_top m z k₀
      have g₂ := (GlobalTheory.HalfBC.lamVal_comp w κ
        (lift (toUnit (TK R) ≫ D₀.toPre.c (hD.xe a)) (toUnit (TK R) ≫ D₀.toPre.c (hD.xe b))).left z Jt J₁ hJt hJ₁).symm
      have g₃ : Units.map (κ.stalkMap z).hom.toMonoidHom (val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b)))
          ((TK R).hom ≫ spMap ω) (κ z) (fun ψ => Jt (κ ≫ ψ))) =
          val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b))) (κ ≫ (TK R).hom ≫ spMap ω) z Jt :=
        (Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ _ κ z Jt hJt).2.2.1 _)).symm
      have hb : κ ≫ (TK R).hom ≫ spMap ω = (TK V).hom ≫ spMap (f.comp ω) := by
        show κ ≫ jK R ≫ spMap ω = jK V ≫ spMap (f.comp ω)
        rw [← Category.assoc, hκ, Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
      have hx : ∀ χ, (toUnit (TK V) ≫ D.c χ).left ≫ (hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) =
          κ ≫ (toUnit (TK R) ≫ D₀.toPre.c (hD.xe χ)).left := fun χ => by
        show (jK V ≫ (D.c χ).left) ≫ _ = κ ≫ jK R ≫ (D₀.toPre.c (hD.xe χ)).left
        rw [Category.assoc, c₁ χ, ← Category.assoc, ← Category.assoc, hκ]
      have hP : κ ≫ (lift (toUnit (TK R) ≫ D₀.toPre.c (hD.xe a)) (toUnit (TK R) ≫ D₀.toPre.c (hD.xe b))).left =
          (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β₂₁ := by
        refine Eq.symm ?_
        apply pullback.hom_ext
        · show _ ≫ (fst D₀.toPre.P.A D₀.toPre.P.A).left = _ ≫ (fst D₀.toPre.P.A D₀.toPre.P.A).left
          rw [Category.assoc, sq₁.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
            lift_fst]
          exact hx a
        · show _ ≫ (snd D₀.toPre.P.A D₀.toPre.P.A).left = _ ≫ (snd D₀.toPre.P.A D₀.toPre.P.A).left
          rw [Category.assoc, sq₁.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
            lift_snd]
          exact hx b
      have key : ∀ p : (TK V).left ⟶ (G2 D.P.A).left,
          lamVal w' p z Jt J' = lamVal w (p ≫ β₂₁) z Jt J₁ * lamVal w₁ p z J₁ J' := by
        intro p
        have t := T3 _ p z (fun I => Jt (p ≫ (β₂₁ ≫ ββ) ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
          (fun I => J₁ ((p ≫ β₂₁) ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
          (fun I => J' (p ≫ GlobalTheory.PrimCocycle.lamφ D.P.A I))
          (Set.mem_iInter.2 fun I => hJt _) (Set.mem_iInter.2 fun I => hJ₁ _) (Set.mem_iInter.2 fun I => hJ' _)
        refine t.trans (congrArg₂ (· * ·) ?_ ?_)
        · show _ = gw w (p ≫ β₂₁) z (fun I => Jt ((p ≫ β₂₁) ≫ ββ ≫ GlobalTheory.PrimCocycle.lamφ T.B I))
            (fun I => J₁ ((p ≫ β₂₁) ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
          simp only [Category.assoc]
        · show _ = gw w₁ p z (fun I => J₁ (p ≫ β₂₁ ≫ GlobalTheory.PrimCocycle.lamφ D₀.toPre.P.A I))
            (fun I => J' (p ≫ GlobalTheory.PrimCocycle.lamφ D.P.A I))
          simp only [Category.assoc]
      show _ = _ * (_ * val (T.τ₀ ((n : ℤ) • e (hD.xe a)) ((n : ℤ) • e (hD.xe b))) _ z Jt)
      rw [t₁, n₁, h₁, g₁, g₂, g₃, hP, hb, key]
      ac_rfl

end GlobalTheory.TInj
