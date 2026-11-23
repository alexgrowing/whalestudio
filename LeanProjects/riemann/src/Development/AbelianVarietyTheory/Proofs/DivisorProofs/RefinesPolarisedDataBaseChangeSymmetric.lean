import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TauBimultOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrimitiveCocycle
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.StalkMapInjectiveOfFlat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PsiRing GlobalTheory.PrimCocycle

noncomputable section

namespace GlobalTheory.HalfBC

section abelian₂

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def sqOf (h : IsGrpPullback G' G f φ) : (G2 G').left ⟶ (G2 G).left :=
  (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left

theorem sqOf_lamφ (h : IsGrpPullback G' G f φ) (I : ULift.{0} (Finset (Fin 2))) :
    sqOf h ≫ lamφ G I = lamφ G' I ≫ φ :=
  (psum_push h _ _ (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')))
    (fun i => by fin_cases i <;> simp [x2]) I.down).symm

theorem isSquare_sqOf (h : IsGrpPullback G' G f φ) : IsSquare φ (sqOf h) :=
  ⟨congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')))⟩

theorem pt_sqOf (h : IsGrpPullback G' G f φ) (I : ULift.{0} (Finset (Fin 2))) (x : (G2 G').left) :
    lamφ G I (sqOf h x) = φ (lamφ G' I x) :=
  congrArg (fun g => g x) (sqOf_lamφ h I)

variable {L : LB G.left} {L' : LB G'.left}

theorem lamIso_le (h : IsGrpPullback G' G f φ) (p : ((abelian₂ G L).pull (sqOf h)).ι × (abelian₂ G' L').ι)
    (I : ULift.{0} (Finset (Fin 2))) :
    ((abelian₂ G L).pull (sqOf h)).U p.1 ⊓ (abelian₂ G' L').U p.2 ≤
      lamφ G' I ⁻¹ᵁ ((L.pull φ).U (fun _ => p.1 PUnit.unit I) ⊓ L'.U (p.2 I)) := fun x hx =>
  ⟨mem_pull.2 (by
    have := Set.mem_iInter.1 (mem_pull.1 hx.1) I
    show φ (lamφ G' I x) ∈ _
    rw [← pt_sqOf h I x]; exact this), Set.mem_iInter.1 hx.2 I⟩

def lamIso (h : IsGrpPullback G' G f φ) (v : LB.Iso L' (L.pull φ)) : LB.Iso (abelian₂ G' L') ((abelian₂ G L).pull (sqOf h)) :=
  ⟨fun p => ∏ I, (res (lamIso_le h p I) (pullU (lamφ G' I) _ (v.s (fun _ => p.1 PUnit.unit I, p.2 I)))) ^ lamε I⟩

theorem gw_lamIso (h : IsGrpPullback G' G f φ) (v : LB.Iso L' (L.pull φ)) {Y : Scheme.{0}} (r : Y ⟶ (G2 G').left)
    (y : Y) (j : ULift.{0} (Finset (Fin 2)) → L.ι) (k : ULift.{0} (Finset (Fin 2)) → L'.ι)
    (hj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j I)) (hk : ∀ I, lamφ G' I (r y) ∈ L'.U (k I)) :
    gw (lamIso h v) r y j k = ∏ I, gw v (r ≫ lamφ G' I) y (j I) (k I) ^ lamε I := by
  have hm : r y ∈ ((abelian₂ G L).pull (sqOf h)).U (fun _ => j) ⊓ (abelian₂ G' L').U k :=
    ⟨mem_pull.2 (Set.mem_iInter.2 fun I => by
      show lamφ G I (sqOf h (r y)) ∈ L.U (j I)
      rw [pt_sqOf]; exact hj I), Set.mem_iInter.2 hk⟩
  unfold gw
  dsimp only [lamIso]
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => (map_zpow _ _ _).trans (congrArg (· ^ lamε I) ?_))
  exact (gm_res r y _ hm _).trans (gm_pull r (lamφ G' I) y ((L.pull φ).U (fun _ => j I) ⊓ L'.U (k I)) ⟨mem_pull.2 (hj I), hk I⟩ _)

theorem pgen_lamIso (h : IsGrpPullback G' G f φ) (v : LB.Iso L' (L.pull φ)) (hv : PGen v) :
    PGen (lamIso h v) := by
  intro Y r y j j' k k' hj hj' hk hk'
  have aj : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j I) := fun I => by
    rw [← pt_sqOf h I]; exact Set.mem_iInter.1 hj I
  have aj' : ∀ I, φ (lamφ G' I (r y)) ∈ L.U (j' I) := fun I => by
    rw [← pt_sqOf h I]; exact Set.mem_iInter.1 hj' I
  have ak : ∀ I, lamφ G' I (r y) ∈ L'.U (k I) := fun I => Set.mem_iInter.1 hk I
  have ak' : ∀ I, lamφ G' I (r y) ∈ L'.U (k' I) := fun I => Set.mem_iInter.1 hk' I
  rw [gw_lamIso h v r y j k aj ak, gw_lamIso h v r y j' k' aj' ak']
  have e₁ := gm_linComb L (lamφ G) lamε (r ≫ sqOf h) y j j' hj hj'
  have e₂ := gm_linComb L' (lamφ G') lamε r y k k' hk hk'
  erw [e₁, e₂]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [hv Y (r ≫ lamφ G' I) y (j I) (j' I) (k I) (k' I) (aj I) (aj' I) (ak I) (ak' I), Category.assoc,
    Category.assoc, sqOf_lamφ, mul_zpow, mul_zpow, inv_zpow]

theorem isGen_lamIso (h : IsGrpPullback G' G f φ) (v : LB.Iso L' (L.pull φ)) (hv : v.IsGen) :
    (lamIso h v).IsGen :=
  (isGen_iff _).2 (pgen_lamIso h v ((isGen_iff v).1 hv))

end abelian₂

section Kappa

variable {R R₁ R₂ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂]

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem gam_comm (σ : R₁ →+* R₂) (gam : FractionRing R₁ →+* FractionRing R₂)
    (hg : ∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) : spMap gam ≫ jK R₁ = jK R₂ ≫ spMap σ := by
  have e₁ : jK R₁ = spMap (algebraMap R₁ (FractionRing R₁)) := rfl
  have e₂ : jK R₂ = spMap (algebraMap R₂ (FractionRing R₂)) := rfl
  rw [e₁, e₂, spMap_comp_spMap', spMap_comp_spMap']
  congr 1
  exact RingHom.ext hg

theorem exists_kappa (ρ : R →+* R₁) (σ : R₁ →+* R₂) (gam : FractionRing R₁ →+* FractionRing R₂)
    (hg : ∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) (hρ : Function.Injective ρ) :
    ∃ κ₁ : (TK R₁).left ⟶ (TK R).left, κ₁ ≫ jK R = jK R₁ ≫ spMap ρ ∧
      ∀ κ : (TK R₂).left ⟶ (TK R).left, κ ≫ jK R = jK R₂ ≫ spMap (σ.comp ρ) → κ = spMap gam ≫ κ₁ := by
  let m : FractionRing R →+* FractionRing R₁ := IsLocalization.map (FractionRing R₁) ρ
    (M := nonZeroDivisors R) (T := nonZeroDivisors R₁) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ hρ)
  have hm : m.comp (algebraMap R (FractionRing R)) = (algebraMap R₁ (FractionRing R₁)).comp ρ :=
    IsLocalization.map_comp _
  have e : ∀ A : Type, ∀ [CommRing A] [IsDomain A], jK A = spMap (algebraMap A (FractionRing A)) := fun _ => rfl
  refine ⟨spMap m, ?_, fun κ hκ => ?_⟩
  · rw [e, e, spMap_comp_spMap', spMap_comp_spMap', hm]
  · obtain ⟨κ', rfl⟩ : ∃ κ', Spec.map κ' = κ := ⟨Spec.preimage κ, Spec.map_preimage κ⟩
    rw [e, e, spMap_comp_spMap'] at hκ
    rw [spMap_comp_spMap']
    have h₁ : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ κ') =
        Spec.map (CommRingCat.ofHom ((algebraMap R₂ (FractionRing R₂)).comp (σ.comp ρ))) := by
      rw [Spec.map_comp]; exact hκ
    have h₂ := Spec.map_injective h₁
    show Spec.map κ' = Spec.map (CommRingCat.ofHom _)
    congr 1
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) ?_
    ext r
    have h₃ := congrArg (fun q => q.hom r) h₂
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h₃
    simp only [RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [h₃, show m (algebraMap R _ r) = algebraMap R₁ _ (ρ r) from IsLocalization.map_eq _ _, hg]

end Kappa

section Main

theorem lamVal_comp {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)) {Z Z' : Scheme.{0}} (σ : Z' ⟶ Z) (p : Z ⟶ (G2 B').left) (z : Z')
    (J : (Z' ⟶ B.left) → M.ι) (J' : (Z' ⟶ B'.left) → M'.ι) (hJ : Good M z J) (hJ' : Good M' z J') :
    lamVal w (σ ≫ p) z J J' =
      Units.map (σ.stalkMap z).hom.toMonoidHom (lamVal w p (σ z) (fun ψ => J (σ ≫ ψ)) (fun ψ => J' (σ ≫ ψ))) := by
  show gw w (σ ≫ p) z (fun I => J ((σ ≫ p) ≫ β₂ ≫ lamφ B I)) (fun I => J' ((σ ≫ p) ≫ lamφ B' I)) = _
  simp only [Category.assoc]
  exact GlobalTheory.ConstFam.gm_comp_stalkMap σ p z
    (((abelian₂ B M).pull β₂).U (fun _ I => J (σ ≫ p ≫ β₂ ≫ lamφ B I)) ⊓ (abelian₂ B' M').U (fun I => J' (σ ≫ p ≫ lamφ B' I)))
    ⟨mem_pull.2 (Set.mem_iInter.2 fun I => hJ (σ ≫ p ≫ β₂ ≫ lamφ B I)),
      Set.mem_iInter.2 fun I => hJ' (σ ≫ p ≫ lamφ B' I)⟩ _

theorem lift_sqOf {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'}
    (x y : T ⟶ G') : (lift x y).left ≫ sqOf h = (lift (pushPt h.1.w x) (pushPt h.1.w y)).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst G G).left = _ ≫ (fst G G).left
    rw [Category.assoc, (isSquare_sqOf h).1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
    rfl
  · show _ ≫ (snd G G).left = _ ≫ (snd G G).left
    rw [Category.assoc, (isSquare_sqOf h).2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
    rfl

theorem half_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : Data R) (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ (ρ : R →+* R₁) (e : D₁.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D₁ e (fun _ _ => 1) → Half Q (σ.comp ρ) D₂ (xe.trans e) (fun _ _ => 1) := by
  intro R _ _ Q R₁ _ _ R₂ _ _ σ D₁ D₂ β v xe gam hgam gp hv hc hrig hψ ρ e hρ H
  obtain ⟨β₁, β₂₁, w₁, pb₁, sq₁, gen₁, norm₁, c₁, tau₁⟩ := H
  have hΛQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hΛ₁ : (abelian₂ D₁.P.A D₁.P.L).IsLB := DVR.linComb_isLB _ D₁.P.isLB _ _
  have hΛ₂ : (abelian₂ D₂.P.A D₂.P.L).IsLB := DVR.linComb_isLB _ D₂.P.isLB _ _
  obtain ⟨w', T⟩ := exists_comp hΛ₁ w₁ (lamIso gp v) ((isGen_iff _).1 gen₁)
    (pgen_lamIso gp v ((isGen_iff v).1 hv)) hΛQ hΛ₂
  have sgam := gam_comm σ gam hgam
  obtain ⟨κ₁, hκ₁, hκu⟩ := exists_kappa ρ σ gam hgam hρ
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D₂.P.A).left) (z : Z) J J₁ J', Good Q.M.L z J → Good D₁.P.L z J₁ →
      Good D₂.P.L z J' → lamVal w' p z J J' = lamVal w₁ (p ≫ sqOf gp) z J J₁ *
        ∏ I, gw v (p ≫ lamφ D₂.P.A I) z (J₁ ((p ≫ lamφ D₂.P.A I) ≫ β)) (J' (p ≫ lamφ D₂.P.A I)) ^ lamε I := by
    intro Z p z J J₁ J' hJ hJ₁ hJ'
    have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂₁) ≫ lamφ Q.B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₁.P.A I)) (fun I => J' (p ≫ lamφ D₂.P.A I))
      (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂₁) ≫ lamφ Q.B I))
      (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₁.P.A I))
      (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ D₂.P.A I))
    refine t.trans (congrArg₂ (· * ·) ?_ ?_)
    · show _ = gw w₁ (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂₁ ≫ lamφ Q.B I))
        (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₁.P.A I))
      simp only [Category.assoc]
    · rw [gw_lamIso gp v p z _ _ (fun I => by
        have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₁.P.A I)
        rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
        exact this) (fun I => hJ' (p ≫ lamφ D₂.P.A I))]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc]
  refine ⟨β ≫ β₁, sqOf gp ≫ β₂₁, w', ?_, ⟨?_, ?_⟩, (isGen_iff _).2 (T.pgen_comp hΛ₁ ((isGen_iff _).1 gen₁)
    (pgen_lamIso gp v ((isGen_iff v).1 hv))), ?_, ?_, ?_⟩
  · exact (IsGrpPullback.comp gp pb₁).congr (spMap_comp_spMap' ρ σ) rfl
  · rw [Category.assoc, sq₁.1, ← Category.assoc, (isSquare_sqOf gp).1, Category.assoc]
  · rw [Category.assoc, sq₁.2, ← Category.assoc, (isSquare_sqOf gp).2, Category.assoc]
  · intro T z J J' hJ hJ'
    choose J₁ hJ₁ using fun χ : T.left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (χ z)
    have o : pushPt gp.1.w (1 : T ⟶ D₂.P.A) = 1 := map_one (pushHom gp T)
    rw [key _ _ z J J₁ J' hJ hJ₁ hJ', lift_sqOf gp, o]
    rw [norm₁ (Over.mk (T.hom ≫ spMap σ)) z J J₁ hJ hJ₁, _root_.one_mul]
    rw [prod_lam (1 : T ⟶ D₂.P.A) 1 (fun q => gw v q z (J₁ (q ≫ β)) (J' q)), _root_.mul_one]
    simp only [mul_inv_cancel, _root_.one_mul, inv_mul_cancel]
  · intro a
    show (D₂.c a).left ≫ β ≫ β₁ = spMap (σ.comp ρ) ≫ (Q.c (e (xe a))).left
    rw [← Category.assoc, hc, Category.assoc, c₁, ← Category.assoc, spMap_comp_spMap']
  · intro κ hκ a b z J J' hJ hJ'
    obtain rfl := hκu κ hκ
    rw [show unitOn (1 : (FractionRing R₂)ˣ) = 1 from map_one _, map_one, _root_.mul_one]
    choose J₁ hJ₀ using fun χ : (TK R₂).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (χ z)
    have hJ₁ : Good D₁.P.L z J₁ := hJ₀
    let g₀ : (TK R₂).left ⟶ (TK R₁).left := spMap gam
    have hx : ∀ χ, D₂.xK χ ≫ β = g₀ ≫ D₁.xK (xe χ) := fun χ => by
      show (jK R₂ ≫ (D₂.c χ).left) ≫ β = spMap gam ≫ jK R₁ ≫ (D₁.c (xe χ)).left
      rw [Category.assoc, hc, ← Category.assoc, ← sgam, Category.assoc]
    have hP : (lift (toUnit (TK R₂) ≫ D₂.c a) (toUnit (TK R₂) ≫ D₂.c b)).left ≫ sqOf gp =
        g₀ ≫ (lift (toUnit (TK R₁) ≫ D₁.c (xe a)) (toUnit (TK R₁) ≫ D₁.c (xe b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst D₁.P.A D₁.P.A).left = _ ≫ (fst D₁.P.A D₁.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact hx a
      · show _ ≫ (snd D₁.P.A D₁.P.A).left = _ ≫ (snd D₁.P.A D₁.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact hx b
    have t₁ := tau₁ κ₁ hκ₁ (xe a) (xe b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ)) (fun ψ => hJ (g₀ ≫ ψ))
      (fun ψ => hJ₁ (g₀ ≫ ψ))
    rw [show unitOn (1 : (FractionRing R₁)ˣ) = 1 from map_one _, map_one, _root_.mul_one] at t₁
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (D₁.tau (xe a) (xe b)) (g₀ ≫ 𝟙 _) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D₁.tau (xe a) (xe b)) (𝟙 _) (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J₁ hJ₁).2.2.1 _)
    have nQ : val (Q.tau (e (xe a)) (e (xe b))) (g₀ ≫ κ₁) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (e (xe a)) (e (xe b))) κ₁ (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κ₁ g₀ z J hJ).2.2.1 _)
    rw [Category.comp_id] at n₁
    have A := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp w₁ g₀ _ z J J₁ hJ hJ₁).symm nQ.symm))
    let h : ((TK R₂).left ⟶ D₂.P.A.left) → ((TK R₂).left.presheaf.stalk z)ˣ :=
      fun q => gw v q z (J₁ (q ≫ β)) (J' q)
    have vψ : ∀ χ, val (D₁.psi (xe χ)) g₀ z J₁ = (h (DVR.cP D₂ _ χ).left)⁻¹ * val (D₂.psi χ) (𝟙 _) z J' := fun χ => by
      have e := CubTransport.val_pmaps (fun _ => hx χ) (hψ χ) (𝟙 _) hJ₁ hJ'
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at e
      exact e
    have vρ : val D₁.rigK g₀ z J₁ = h (1 : TK R₂ ⟶ D₂.P.A).left * val D₂.rigK (𝟙 _) z J' := by
      have h₁ : eSec D₂.P.A ≫ β = spMap σ ≫ eSec D₁.P.A := (cubeMapOf gp).e_comm
      have e := CubTransport.val_pmaps (fun _ => h₁) hrig (TK R₂).hom hJ₁ hJ'
      rw [Fintype.prod_unique, zpow_one] at e
      have b₁ : g₀ ≫ (toUnit (TK R₁)).left = (TK R₂).hom ≫ spMap σ := sgam
      have b₂ : 𝟙 _ ≫ (toUnit (TK R₂)).left = (TK R₂).hom := Category.id_comp _
      refine (val_pull hJ₁ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
      rw [b₁, b₂]
      exact e
    have K := (key _ (lift (toUnit (TK R₂) ≫ D₂.c a) (toUnit (TK R₂) ≫ D₂.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
      (congrArg₂ (· * ·) (congrArg (fun q => lamVal w₁ q z J J₁) hP)
        (prod_lam (DVR.cP D₂ (TK R₂) a) (DVR.cP D₂ (TK R₂) b) h))
    rw [TauPull.val_tau _ hJ₁, ← map_add, vψ, vψ, vψ, vρ, DVR.cPoint_add] at A
    refine Eq.trans ?_ (congrArg₂ (· * ·) K.symm rfl)
    rw [TauPull.val_tau _ hJ']
    refine Eq.trans ?_ (mul_right_comm _ _ _)
    refine Eq.trans ?_ (congrArg₂ (· * ·) A rfl)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end Main

end GlobalTheory.HalfBC

end
