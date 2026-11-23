import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroupsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedOfTwoIdempotentFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHomStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FactorPol

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend GlobalTheory.Mum.Two GlobalTheory.UT

theorem lbIso_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin a
  obtain ⟨hno, -, hic, -⟩ := hR
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  have ha := oG.hom a
  have hsa := oG.hom (star a)
  have hgen := U.gen_hom
  have hL := U.LG.isLB
  have hA := A.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance
  have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩

  have eA : cubeCls A.A ![fst A.A A.A ≫ oA.act a, snd A.A A.A] (cls A.L hA) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] (cls A.L hA) :=
    (cls_cubeLB A.A _ hA).symm.trans (((cls_eq_iff (LB.isLB_linComb hA _ _) (LB.isLB_linComb hA _ _)).2
      (GlobalTheory.FullPoint.lbIso_of_rosatiAdj hA (oA.rosati a))).trans (cls_cubeLB A.A _ hA))
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
      CechPic.pull U.gen.hom.left (cls A.L hA) := by
    obtain ⟨w, hw⟩ := U.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm

  have hgK : cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act a),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) =
      cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act (star a))]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) := by
    rw [hc']
    let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
      (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
    have hu : u.left ≫ (A.A ⊗ A.A).hom = ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e₁ := hlin.ext a
    have e₂ := hlin.ext (star a)
    rw [← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A ≫ oA.act a, snd A.A A.A] u.left hu (fun i => ?_),
      ← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] u.left hu
        (fun i => ?_), eA]
    · fin_cases i
      · show (fst _ _ ≫ U.gen.hom).left = (u ≫ fst A.A A.A).left
        congr 1; simp [u]
      · show ((snd _ _ ≫ (Over.pullback (jK R)).map (oG.act (star a))) ≫ U.gen.hom).left = (u ≫ snd A.A A.A ≫ oA.act (star a)).left
        congr 1; simp [u, e₂]
    · fin_cases i
      · show ((fst _ _ ≫ (Over.pullback (jK R)).map (oG.act a)) ≫ U.gen.hom).left = (u ≫ fst A.A A.A ≫ oA.act a).left
        congr 1; simp [u, e₁]
      · show (snd _ _ ≫ U.gen.hom).left = (u ≫ snd A.A A.A).left
        congr 1; simp [u]
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  refine pic_ext (jK R) hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
  · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
      (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
    fin_cases i <;> simp
  · have hGp := isGrpPullback_pullback G (jK R)
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    let δ := lift ((Over.pullback (jK R)).map (fst G G)) ((Over.pullback (jK R)).map (snd G G))
    have e := congrArg (CechPic.pull δ.left) hgK
    have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hGp (T' := (Over.pullback (jK R)).obj (G ⊗ G)) (T := G ⊗ G)
      (fun i => (Over.pullback (jK R)).map (x i)) x (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    rw [pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G ≫ oG.act a, snd G G] i)) δ
        (fun i => by fin_cases i <;> simp [δ]),
      pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G, snd G G ≫ oG.act (star a)] i)) δ
        (fun i => by fin_cases i <;> simp [δ])] at e
    exact (e' _).trans (e.trans (e' _).symm)

section Comp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D₃ : DegData R I}
  {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
  {U₃ : UnifPre I D₃ A₃ G₃} {a : G₁ ⟶ G₂} {a' : G₂ ⟶ G₃}

theorem over_comp {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {b' : D₂.toPre.P.A ⟶ D₃.toPre.P.A} (h : Over₀ U₁ U₂ a b)
    (h' : Over₀ U₂ U₃ a' b') : Over₀ U₁ U₃ (a ≫ a') (b ≫ b') := fun e => by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, h' e, ← Category.assoc, h e, Category.assoc]

theorem over_id : Over₀ U₁ U₁ (𝟙 _) (𝟙 _) := fun e => by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

theorem onTorus_comp {h : D₂.toPre.X → D₁.toPre.X} {h' : D₃.toPre.X → D₂.toPre.X} (H : OnTorus U₁ U₂ a h)
    (H' : OnTorus U₂ U₃ a' h') : OnTorus U₁ U₃ (a ≫ a') (h ∘ h') := fun e => by
  obtain ⟨t, ht, et⟩ := H e
  obtain ⟨t', ht', et'⟩ := H' e
  refine ⟨t ≫ t', fun χ => unit_ext fun z _ => ?_, by
    rw [Functor.map_comp, ← Category.assoc, et, Category.assoc, et', Category.assoc]⟩
  have e₁ := congrArg (gm (𝟙 _) z ⊤) (ht (h' χ))
  have e₂ := congrArg (gm (𝟙 _ ≫ t.left) z ⊤) (ht' χ)
  refine Eq.trans ?_ e₁
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) (t ≫ t').left z ⊤ trivial _)).trans
    (Eq.trans ?_ ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)).symm)
  refine Eq.trans ?_ e₂
  refine Eq.trans ?_ ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _ ≫ t.left) t'.left z ⊤ trivial _)).symm
  rw [Over.comp_left, Category.assoc]

theorem onTorus_id : OnTorus U₁ U₁ (𝟙 _) id := fun e =>
  ⟨𝟙 _, fun χ => unit_ext fun z _ => ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans
    (gm_pull (𝟙 _) (𝟙 _) z ⊤ trivial _)).trans (by rw [Category.comp_id]; rfl), by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩

end Comp

theorem lbIso_proj {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (inc : G ⟶ G') (pr : G' ⟶ G) (f g g' : G' ⟶ G')
    (hg : pr ≫ inc ≫ f = g)
    (H : LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ f) : G2 G ⟶ G2 G').left))
    (adj : LBIso (cubeLB G' ![fst G' G' ≫ g', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ g] L')) :
    LBIso (cubeLB G ![fst G' G' ≫ pr, snd G' G' ≫ pr] L)
      (cubeLB G' ![fst G' G' ≫ (pr ≫ inc) ≫ g', snd G' G' ≫ 𝟙 G'] L') := by
  have hΛ' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  have e₁ : cubeCls G (x2 G) (cls L hL) = CechPic.pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ f) : G2 G ⟶ G2 G').left
      (cubeCls G' (x2 G') (cls L' hL')) :=
    (cls_cubeLB G _ hL).symm.trans (((cls_eq_iff _ (pull_isLB hΛ' _)).2 H).trans
      ((cls_pull hΛ' _ _).trans (congrArg _ (cls_cubeLB G' _ hL'))))
  have e₂ := (cls_cubeLB G' _ hL').symm.trans (((cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL' _ _)).2 adj).trans
    (cls_cubeLB G' _ hL'))
  rw [pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ f] _ (fun i => by fin_cases i <;> simp [x2])] at e₁
  have e₃ := congrArg (CechPic.pull (lift (fst G' G' ≫ pr) (snd G' G' ≫ pr) : G' ⊗ G' ⟶ G ⊗ G).left) e₁
  have e₄ := congrArg (CechPic.pull (lift (fst G' G' ≫ pr ≫ inc) (snd G' G') : G' ⊗ G' ⟶ G' ⊗ G').left) e₂
  rw [pull_cubeCls G _ ![fst G' G' ≫ pr, snd G' G' ≫ pr] _ (fun i => by fin_cases i <;> simp [x2]),
    pull_cubeCls G' _ ![fst G' G' ≫ pr ≫ inc, snd G' G' ≫ g] _ (fun i => by fin_cases i <;> simp [← hg])] at e₃
  rw [pull_cubeCls G' _ ![fst G' G' ≫ (pr ≫ inc) ≫ g', snd G' G' ≫ 𝟙 G'] _ (fun i => by fin_cases i <;> simp),
    pull_cubeCls G' _ ![fst G' G' ≫ pr ≫ inc, snd G' G' ≫ g] _ (fun i => by fin_cases i <;> simp)] at e₄
  exact (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL' _ _)).1
    ((cls_cubeLB G _ hL).trans (e₃.trans (e₄.symm.trans (cls_cubeLB G' _ hL').symm)))

set_option maxHeartbeats 1000000 in

theorem samePol_of_unif_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (D₀ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D₀ A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → SamePol D.toPre D₀.toPre := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG lin G _ _ hG inc pr hinc hpr ip pi D₀ A U H
  have := hR.2
  have hA := hR.1
  have := U.gen_hom
  have := U'.gen_hom
  obtain ⟨prB, hprB, qpr⟩ := GlobalTheory.T.exists_abelianPart_hom_uniformisedGroups R _ hA D' D₀ A' A G' G U'.toUnifPre U.toUnifPre pr hpr
  obtain ⟨incB, hincB, qinc⟩ := GlobalTheory.T.exists_abelianPart_hom_uniformisedGroups R _ hA D₀ D' A A' G G' U.toUnifPre U'.toUnifPre inc hinc
  obtain ⟨h, th⟩ := GlobalTheory.T.uniformisedGroupHom_characterMap_constant R _ hA D' D₀ A' A G' G U'.toUnifPre U.toUnifPre pr hpr
  obtain ⟨k, tk⟩ := GlobalTheory.T.uniformisedGroupHom_characterMap_constant R _ hA D₀ D' A A' G G' U.toUnifPre U'.toUnifPre inc hinc
  have un := GlobalTheory.T.uniformisedGroupHom_induced_maps_unique R _ hA D₀ D₀ A A G G U.toUnifPre U.toUnifPre
  have un' := GlobalTheory.T.uniformisedGroupHom_induced_maps_unique R _ hA D' D' A' A' G' G' U'.toUnifPre U'.toUnifPre
  have ql : ∀ x, Over₀ U'.toUnifPre U'.toUnifPre (oG.act x) (F.o.onB.act x) := fun x e => lin.q_lin e x
  have il : ∀ x, OnTorus U'.toUnifPre U'.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin.i_lin e x
  have ipB : incB ≫ prB = 𝟙 _ := (un _).1 _ _ (ip ▸ over_comp qinc qpr) over_id
  have piB : prB ≫ incB = F.o.onB.act F.e := (un' _).1 _ _ (pi ▸ over_comp qpr qinc) (ql _)
  have kh : ∀ χ, k (h χ) = χ := congrFun ((un _).2 _ _ (ip ▸ onTorus_comp tk th) onTorus_id)
  have hk : ∀ χ, h (k χ) = star F.e • χ := congrFun ((un' _).2 _ _ (pi ▸ onTorus_comp th tk) (il _))
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  have L : Lin U'.toUnifPre U.toUnifPre pr prB h := ⟨hpr, hprB, qpr, th⟩
  have C := GlobalTheory.T.torusCoordinates_compare_normalisedGenerators R _ hA D' D₀ A' A G' G U'.toUnifPre U.toUnifPre pr prB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A'.A ⟶ A.A, IsMonHom c ∧ Gen₀ U'.toUnifPre U.toUnifPre pr c :=
    ⟨U'.gen.inv ≫ (Over.pullback (jK R)).map pr ≫ U.gen.hom, inferInstance, by simp [Gen₀]⟩
  have adj := lbIso_star R hA D' A' G' hG' U' F.O F.o oA oG lin
  have ex := fun x => (functorial_of_unif R _ hA D' A' G' hG' U').1 (oG.act x) (oA.act x) (oG.hom x) (oA.hom x) (lin.ext x)
  obtain ⟨E, eG, eA⟩ := ex (star (F.f * F.e) * F.e)
  obtain ⟨E', eG', -⟩ := ex (star (star (F.f * F.e) * F.e))
  have eh : ∀ y, E.h y = star F.e • F.f • F.e • y := fun y =>
    (congrFun ((un' _).2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) (il _)) y).trans (by
      rw [star_mul, star_star, mul_smul, mul_smul])
  have H₁ := lbIso_proj U.LG.isLB U'.LG.isLB inc pr (oG.act F.f) (oG.act (star (star (F.f * F.e))))
    (oG.act (star (F.f * F.e))) (by rw [star_star, oG.map_mul, ← pi, Category.assoc]) H (adj _)
  rw [pi, ← oG.map_mul, ← eG] at H₁
  have H₂ := GlobalTheory.T.cubeBundleIso_uniformisedGroup_genericFibre R _ D' D₀ A' A G' G U'.toUnifPre U.toUnifPre pr pr E.aG (𝟙 _) c c E.aA (𝟙 _) gc gc E.ext
    (by simp [Gen₀]) H₁
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.T.exists_algClosedField_torsionMaps_commute_hom R _ hA D' D₀ A' A G' G hG' hG U' U pr c prB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.T.semiAbelianHom_torsionCompatible_periods_lattices R _ hA D' D₀ A' A G' G hG' hG U' U pr c prB h hc gc L C E E'
    (by rw [eG, eG']; exact adj _) H₂ Ω K
  have := oG.hom F.f
  have := F.o.onB.hom F.f
  have H₃ := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hA D₀ D' A A' G G' hG hG' U U' inc (inc ≫ oG.act F.f) incB (incB ≫ F.o.onB.act F.f) hinc
    inferInstance hincB inferInstance qinc (over_comp qinc (ql _)) H
  have hφ' : ∀ y, h (φ y) = star F.e • F.f • F.e • y := fun y => (hhφ y).trans (eh y)
  obtain ⟨cφ, w, hw, ht⟩ := GlobalTheory.T.factor_periods_projection_period_points R D₀.toPre D'.toPre D'.tau_bimult F.O F.o F.e F.f incB prB h φ hincB hprB piB
    (fun χ => (C χ).imp fun _ => And.left) H₃ Ω hφ hφ'
  have ex : ∀ y, F.e • F.xi y = F.xi y := fun y => by rw [← F.xi_xp, F.xp_xi]
  let ε : D.toPre.X ≃+ D₀.toPre.X := AddEquiv.ofBijective (φ.comp F.xi) ⟨fun y y' e => F.inj (by
      have := congrArg h e
      simpa only [AddMonoidHom.comp_apply, hφ', ex] using this), fun χ => by
    obtain ⟨y, hy⟩ := F.onto (h χ)
    exact ⟨y, hinj (by rw [AddMonoidHom.comp_apply, hφ', ex, ← hy, ← hk, kh])⟩⟩
  have hε : ∀ χ, φ (F.xi (ε.symm χ)) = χ := ε.apply_symm_apply
  let F₀ : Factor D₀.toPre D'.toPre :=
    { O := F.O, o := F.o, e := F.e, f := F.f, inc := incB, pr := prB, xi := F.xi.comp ε.symm.toAddMonoidHom, xp := φ, w := w
      idem := F.idem, inc_hom := hincB, pr_hom := hprB, inc_pr := ipB, pr_inc := piB, xp_xi := hε
      xi_xp := fun z => by
        have : φ z = ε (F.xp z) := hinj (by
          show _ = h (φ (F.xi (F.xp z)))
          rw [hφ', hφ', F.xi_xp, ← mul_smul F.e F.e, F.idem])
        show F.xi (ε.symm (φ z)) = _
        rw [this, ε.symm_apply_apply, F.xi_xp]
      c_xi := fun χ => by
        show D'.toPre.c (F.xi (ε.symm χ)) = _
        conv_rhs => rw [← hε χ, cφ, Category.assoc, piB, ← F.o.c_lin, ex]
      inj := F.inj.comp ε.symm.injective
      onto := fun z => (F.onto z).elim fun y hy => ⟨ε y, by
        show _ = star F.e • F.f • F.xi (ε.symm (ε y))
        rw [ε.symm_apply_apply, hy]⟩
      w_gen := hw
      tau := fun a b z J J' hJ hJ' => by
        have := ht (F.xi (ε.symm a)) (F.xi (ε.symm b)) z J J' hJ hJ'
        rw [hε, hε, ex, ex] at this
        exact this }
  exact GlobalTheory.T.samePolarised_of_two_idempotentFactors R D.toPre D₀.toPre D'.toPre D.tau_bimult F F₀ rfl rfl (fun _ => rfl) (fun _ => rfl)

end GlobalTheory.Mum.FactorPol
