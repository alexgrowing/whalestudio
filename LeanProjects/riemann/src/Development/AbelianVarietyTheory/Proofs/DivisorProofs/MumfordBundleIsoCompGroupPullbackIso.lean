import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LamPullComp

section Iso

variable {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {B' : Over S₁} [GrpObj B']
  {G' : Over S₂} [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} {β₂ : (G2 B').left ⟶ (G2 G).left}
  {sq : (G2 G').left ⟶ (G2 B').left} {L : LB G.left} {L' : LB G'.left}

theorem pt_eq (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (I : ULift.{0} (Finset (Fin 2))) (x : (G2 G').left) :
    lamφ G I (β₂ (sq x)) = φ (lamφ G' I x) :=
  congrArg (fun g => g x) (h I)

theorem iso_le (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ)
    (p : (((abelian₂ G L).pull β₂).pull sq).ι × (abelian₂ G' L').ι) (I : ULift.{0} (Finset (Fin 2))) :
    (((abelian₂ G L).pull β₂).pull sq).U p.1 ⊓ (abelian₂ G' L').U p.2 ≤
      lamφ G' I ⁻¹ᵁ ((L.pull φ).U (fun _ => p.1 PUnit.unit PUnit.unit I) ⊓ L'.U (p.2 I)) := fun x hx =>
  ⟨mem_pull.2 (by
    have := Set.mem_iInter.1 (mem_pull.1 (mem_pull.1 hx.1)) I
    show φ (lamφ G' I x) ∈ _
    rw [← pt_eq h I x]; exact this), Set.mem_iInter.1 hx.2 I⟩

def iso2 (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) :
    LB.Iso (abelian₂ G' L') (((abelian₂ G L).pull β₂).pull sq) :=
  ⟨fun p => ∏ I, (res (iso_le h p I)
    (pullU (lamφ G' I) _ (v.s (fun _ => p.1 PUnit.unit PUnit.unit I, p.2 I)))) ^ lamε I⟩

theorem mumfordBundle_pullback_composite_germ_iso (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) {Y : Scheme.{0}}
    (r : Y ⟶ (G2 G').left) (y : Y) (j : PUnit → ULift.{0} (Finset (Fin 2)) → L.ι)
    (k : ULift.{0} (Finset (Fin 2)) → L'.ι)
    (hj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I)) (hk : ∀ I, lamφ G' I (r y) ∈ L'.U (k I)) :
    gw (iso2 h v) r y j k = ∏ I, gw v (r ≫ lamφ G' I) y (j PUnit.unit I) (k I) ^ lamε I := by
  have hm : r y ∈ (((abelian₂ G L).pull β₂).pull sq).U (fun _ => j) ⊓ (abelian₂ G' L').U k :=
    ⟨mem_pull.2 (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (sq (r y))) ∈ L.U (j PUnit.unit I)
      rw [pt_eq h]; exact hj I)), Set.mem_iInter.2 hk⟩
  unfold gw
  dsimp only [iso2]
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => (map_zpow _ _ _).trans (congrArg (· ^ lamε I) ?_))
  exact (gm_res r y _ hm _).trans (gm_pull r (lamφ G' I) y ((L.pull φ).U (fun _ => j PUnit.unit I) ⊓ L'.U (k I))
    ⟨mem_pull.2 (hj I), hk I⟩ _)

theorem mumfordBundle_pullback_composite_isGen (h : ∀ I, sq ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ) (v : LB.Iso L' (L.pull φ)) (hv : PGen v) :
    PGen (iso2 h v) := by
  intro Y r y j j' k k' hj hj' hk hk'
  have bj := mem_pull.1 hj
  have bj' := mem_pull.1 hj'
  have aj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj I
  have aj' : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j' PUnit.unit I) := fun I => by
    rw [← pt_eq h I]; exact Set.mem_iInter.1 bj' I
  have ak : ∀ I, lamφ G' I (r y) ∈ L'.U (k I) := fun I => Set.mem_iInter.1 hk I
  have ak' : ∀ I, lamφ G' I (r y) ∈ L'.U (k' I) := fun I => Set.mem_iInter.1 hk' I
  rw [mumfordBundle_pullback_composite_germ_iso h v r y j k aj ak, mumfordBundle_pullback_composite_germ_iso h v r y j' k' aj' ak']
  have e₀ := gm_pull_g (abelian₂ G L) β₂ (r ≫ sq) y j j' hj hj'
  have e₁ := gm_linComb L (lamφ G) lamε ((r ≫ sq) ≫ β₂) y (j PUnit.unit) (j' PUnit.unit) bj bj'
  have e₂ := gm_linComb L' (lamφ G') lamε r y k k' hk hk'
  erw [e₀, e₁, e₂]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [hv Y (r ≫ lamφ G' I) y (j PUnit.unit I) (j' PUnit.unit I) (k I) (k' I) (aj I) (aj' I) (ak I) (ak' I),
    Category.assoc, Category.assoc, Category.assoc, h, mul_zpow, mul_zpow, inv_zpow]

end Iso

theorem lamIso_comp_pull : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S₁ S₂ S₀ G _ _ B' _ G' _ _ T _ _ f₁ f₂ β' Φ φ β₂ β₂' L L' M gp' gΦ hsq hΦ hL hL' hM v w₁ hv hw₁
  have gp : IsGrpPullback G' G (f₂ ≫ f₁) φ := (IsGrpPullback.comp gΦ gp').congr rfl hΦ
  have e1 : GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ = GlobalTheory.HalfBC.sqOf gp := by
    apply pullback.hom_ext
    · show _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, hsq.1, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      show ((fst G' G').left ≫ Φ) ≫ β' = (fst G' G').left ≫ φ
      rw [Category.assoc, hΦ]
    · show _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, hsq.2, ← Category.assoc]
      unfold GlobalTheory.HalfBC.sqOf
      rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
      show ((snd G' G').left ≫ Φ) ≫ β' = (snd G' G').left ≫ φ
      rw [Category.assoc, hΦ]
  have h : ∀ I, GlobalTheory.HalfBC.sqOf gΦ ≫ β₂ ≫ lamφ G I = lamφ G' I ≫ φ := fun I => by
    rw [← Category.assoc, e1, GlobalTheory.HalfBC.sqOf_lamφ]
  have hΛT : (abelian₂ T M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛG : ((abelian₂ G L).pull β₂).IsLB := LB.isLB_pull (DVR.linComb_isLB _ hL _ _) _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w, Tw⟩ := exists_comp hΛG w₁ (iso2 h v) ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv)) hΛT hΛ'
  refine ⟨w, (isGen_iff _).2 (Tw.pgen_comp hΛG ((isGen_iff _).1 hw₁) (mumfordBundle_pullback_composite_isGen h v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := Tw Z p z (fun I => J (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (fun _ I => J₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ lamφ T I))
    (mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (β₂ (GlobalTheory.HalfBC.sqOf gΦ (p z))) ∈ L.U (J₁ ((p ≫ lamφ G' I) ≫ φ))
      rw [pt_eq h]; exact hJ₁ ((p ≫ lamφ G' I) ≫ φ)))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z (fun I => J ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂' ≫ lamφ T I))
      (fun _ I => J₁ ((p ≫ GlobalTheory.HalfBC.sqOf gΦ) ≫ β₂ ≫ lamφ G I))
    simp only [Category.assoc, h]
  · exact mumfordBundle_pullback_composite_germ_iso h v p z _ _ (fun I => hJ₁ ((p ≫ lamφ G' I) ≫ φ)) (fun I => hJ' (p ≫ lamφ G' I))

end GlobalTheory.LamPullComp

end
