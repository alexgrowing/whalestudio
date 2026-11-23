import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDefectDegenerationDataBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.PsiRing GlobalTheory.PrimCocycle

noncomputable section

namespace GlobalTheory.TInj.FromRefine

theorem from_of_refines : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (ρ : R →+* V) (ω : W →+* R) (s : I → R) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (D : DegPre V) (e' : D.X ≃+ Q.X), Function.Injective ρ → DataFrom T ω s ε n Q e → Refines Q ρ D e' → ∃ β ββ w, From T (ρ.comp ω) (fun i => ρ (s i)) ε n D (e'.trans e) β ββ w := by
  intro o W _ _ _ T I _ ε n R _ _ V _ _ ρ ω s Q e D e' hρ hDF hR
  obtain ⟨βQ, β₂Q, wQ, pbQ, sqQ, genQ, cQ, τQ⟩ := hDF
  obtain ⟨βR, β₂R, wR, pbR, sqR, genR, cR, τR⟩ := hR
  have hΛT : (abelian₂ T.B T.M.L).IsLB := DVR.linComb_isLB _ T.M.isLB _ _
  have hΛQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hΛD : (abelian₂ D.P.A D.P.L).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  obtain ⟨w'', hT⟩ := exists_comp hΛQ wQ wR ((isGen_iff _).1 genQ) ((isGen_iff _).1 genR) hΛT hΛD
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D.P.A).left) (z : Z) J JQ J', Good T.M.L z J → Good Q.M.L z JQ →
      Good D.P.L z J' → lamVal w'' p z J J' = lamVal wQ (p ≫ β₂R) z J JQ * lamVal wR p z JQ J' := by
    intro Z p z J JQ J' hJ hJQ hJ'
    have t := hT Z p z (fun I => J (p ≫ (β₂R ≫ β₂Q) ≫ lamφ T.B I))
      (fun I => JQ ((p ≫ β₂R) ≫ lamφ Q.B I)) (fun I => J' (p ≫ lamφ D.P.A I))
      (Set.mem_iInter.2 fun I => hJ (p ≫ (β₂R ≫ β₂Q) ≫ lamφ T.B I))
      (Set.mem_iInter.2 fun I => hJQ ((p ≫ β₂R) ≫ lamφ Q.B I))
      (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ D.P.A I))
    refine t.trans (congrArg₂ (· * ·) ?_ ?_)
    · show _ = gw wQ (p ≫ β₂R) z (fun I => J ((p ≫ β₂R) ≫ β₂Q ≫ lamφ T.B I))
        (fun I => JQ ((p ≫ β₂R) ≫ lamφ Q.B I))
      simp only [Category.assoc]
    · show _ = gw wR p z (fun I => JQ (p ≫ β₂R ≫ lamφ Q.B I)) (fun I => J' (p ≫ lamφ D.P.A I))
      simp only [Category.assoc]
  refine ⟨βR ≫ βQ, β₂R ≫ β₂Q, w'', ?_, isSquare_comp sqR sqQ,
    (isGen_iff _).2 (hT.pgen_comp hΛQ ((isGen_iff _).1 genQ) ((isGen_iff _).1 genR)), ?_, ?_⟩
  · exact (IsGrpPullback.comp pbR pbQ).congr (GlobalTheory.HalfBC.spMap_comp_spMap' ω ρ) rfl
  · intro a
    show (D.c a).left ≫ βR ≫ βQ = spMap (ρ.comp ω) ≫ (T.c₀ ((n : ℤ) • e (e' a))).left
    rw [← Category.assoc, cR, Category.assoc, cQ, ← Category.assoc, GlobalTheory.HalfBC.spMap_comp_spMap']
  · intro a b
    obtain ⟨k, hk, hv⟩ := τQ (e' a) (e' b)
    let m : FractionRing R →+* FractionRing V := IsLocalization.map (FractionRing V) ρ (M := nonZeroDivisors R)
      (T := nonZeroDivisors V) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ hρ)
    have hm : ∀ r, m (algebraMap R _ r) = algebraMap V _ (ρ r) := fun r => IsLocalization.map_eq _ _
    let κ : (TK V).left ⟶ (TK R).left := spMap m
    have hκ : κ ≫ jK R = jK V ≫ spMap ρ := GlobalTheory.HalfBC.gam_comm ρ m hm
    refine ⟨Units.map m.toMonoidHom k, ?_, fun z J J' hJ hJ' => ?_⟩
    · rw [Units.coe_map]
      show m (k : FractionRing R) = _
      rw [hk, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow₀, hm]
      rfl
    · choose JQ hJQ0 using fun χ : (TK V).left ⟶ Q.B.left => exists_chart Q.M.isLB (χ z)
      have hJQ : Good Q.M.L z JQ := hJQ0
      have r1 := τR κ hκ a b z JQ J' hJQ hJ'
      have nQ : val (Q.tau (e' a) (e' b)) (κ ≫ 𝟙 _) z JQ = Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (Q.tau (e' a) (e' b)) (𝟙 _) (κ z) (fun ψ => JQ (κ ≫ ψ))) :=
        Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) κ z JQ hJQ).2.2.1 _)
      rw [Category.comp_id] at nQ
      have r2 := hv (κ z) (fun ψ => J (κ ≫ ψ)) (fun ψ => JQ (κ ≫ ψ)) (fun ψ => hJ (κ ≫ ψ)) (fun ψ => hJQ (κ ≫ ψ))
      rw [r2, map_mul, map_mul] at nQ
      have g1 : Units.map (κ.stalkMap z).hom.toMonoidHom (gm (𝟙 _) (κ z) ⊤ (unitOn k)) =
          gm (𝟙 _) z ⊤ (unitOn (Units.map m.toMonoidHom k)) := by
        rw [← GlobalTheory.ConstFam.gm_comp_stalkMap κ (𝟙 _) z ⊤ trivial, Category.comp_id]
        exact GlobalTheory.PolDeg.gm_spMap_unitOn m k z
      have g2 := (GlobalTheory.HalfBC.lamVal_comp wQ κ
        (lift (toUnit (TK R) ≫ Q.c (e' a)) (toUnit (TK R) ≫ Q.c (e' b))).left z J JQ hJ hJQ).symm
      have g3 : Units.map (κ.stalkMap z).hom.toMonoidHom
          (val (T.τ₀ ((n : ℤ) • e (e' a)) ((n : ℤ) • e (e' b))) ((TK R).hom ≫ spMap ω) (κ z) (fun ψ => J (κ ≫ ψ))) =
          val (T.τ₀ ((n : ℤ) • e (e' a)) ((n : ℤ) • e (e' b))) (κ ≫ (TK R).hom ≫ spMap ω) z J :=
        (Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ ((TK R).hom ≫ spMap ω) κ z J hJ).2.2.1 _)).symm
      have hx : ∀ χ, (toUnit (TK V) ≫ D.c χ).left ≫ βR = κ ≫ (toUnit (TK R) ≫ Q.c (e' χ)).left := fun χ => by
        show (jK V ≫ (D.c χ).left) ≫ βR = κ ≫ jK R ≫ (Q.c (e' χ)).left
        rw [Category.assoc, cR, ← Category.assoc, ← hκ, Category.assoc]
      have hP : (lift (toUnit (TK V) ≫ D.c a) (toUnit (TK V) ≫ D.c b)).left ≫ β₂R =
          κ ≫ (lift (toUnit (TK R) ≫ Q.c (e' a)) (toUnit (TK R) ≫ Q.c (e' b))).left := by
        apply pullback.hom_ext
        · show _ ≫ (fst Q.B Q.B).left = _ ≫ (fst Q.B Q.B).left
          rw [Category.assoc, sqR.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
            ← Over.comp_left, lift_fst]
          exact hx a
        · show _ ≫ (snd Q.B Q.B).left = _ ≫ (snd Q.B Q.B).left
          rw [Category.assoc, sqR.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
            ← Over.comp_left, lift_snd]
          exact hx b
      have hb : κ ≫ (TK R).hom ≫ spMap ω = (TK V).hom ≫ spMap (ρ.comp ω) := by
        rw [← GlobalTheory.HalfBC.spMap_comp_spMap', ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ spMap ω) hκ
      rw [g1, g2, g3, ← hP, hb] at nQ
      rw [r1, nQ, key _ _ z J JQ J' hJ hJQ hJ']
      ac_rfl

end GlobalTheory.TInj.FromRefine
