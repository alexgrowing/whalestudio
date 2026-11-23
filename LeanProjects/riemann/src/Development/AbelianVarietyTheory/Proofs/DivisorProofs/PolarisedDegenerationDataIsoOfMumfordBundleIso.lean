import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctorialOfUnif
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartHomUniformisedGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomCharacterMapConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinatesCompareNormalisedGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleIsoUniformisedGroupGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.SameLam

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

set_option maxHeartbeats 1000000 in

theorem iso_of_lbIso_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ [Module O D'.toPre.X] (o' : D'.toPre.OAct O) (oA' : A'.OAct O), U'.toUnifPre.OLinear O o' oA' oG → LBIso (abelian₂ G U'.LG.L) (abelian₂ G U.LG.L) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom ∧ Over₀ U'.toUnifPre U.toUnifPre (𝟙 G) Φ.hom ∧ OnTorus U'.toUnifPre U.toUnifPre (𝟙 G) xe.symm ∧ (∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG lin D' A' U' _ o' oA' lin' H
  have := hR.2
  have hA := hR.1
  have := U.gen_hom
  have := U'.gen_hom
  obtain ⟨prB, hprB, qpr⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨incB, hincB, qinc⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨h, th⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨k, tk⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (𝟙 G)
    inferInstance
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre (𝟙 G)
  have un' := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D' D' A' A' G G U'.toUnifPre U'.toUnifPre (𝟙 G)
  have ipB : incB ≫ prB = 𝟙 _ := un'.1 _ _ (by have := over_comp qinc qpr; rwa [Category.comp_id] at this) over_id
  have piB : prB ≫ incB = 𝟙 _ := un.1 _ _ (by have := over_comp qpr qinc; rwa [Category.comp_id] at this) over_id
  have kh : ∀ χ, k (h χ) = χ := congrFun (un'.2 _ _ (by have := onTorus_comp tk th; rwa [Category.comp_id] at this)
    onTorus_id)
  have hk : ∀ χ, h (k χ) = χ := congrFun (un.2 _ _ (by have := onTorus_comp th tk; rwa [Category.comp_id] at this)
    onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  let xe : D'.toPre.X ≃+ D.toPre.X :=
    { toFun := h, invFun := k, left_inv := kh, right_inv := hk, map_add' := h.map_add }

  have ql : ∀ x, Over₀ U.toUnifPre U.toUnifPre (oG.act x) (o.onB.act x) := fun x e => lin.q_lin e x
  have ql' : ∀ x, Over₀ U'.toUnifPre U'.toUnifPre (oG.act x) (o'.onB.act x) := fun x e => lin'.q_lin e x
  have il : ∀ x, OnTorus U.toUnifPre U.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin.i_lin e x
  have il' : ∀ x, OnTorus U'.toUnifPre U'.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin'.i_lin e x
  have linB : ∀ a, o'.onB.act a ≫ incB = incB ≫ o.onB.act a := fun a =>
    (GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (oG.act a)).1 _ _
      (by have := over_comp (ql' a) qinc; rwa [Category.comp_id] at this)
      (by have := over_comp qinc (ql a); rwa [Category.id_comp] at this)
  have linS : ∀ (b : O) χ, star b • h χ = h (star b • χ) := fun b => congrFun
    ((GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (oG.act b)).2 _ _
      (by have := onTorus_comp (il b) th; rwa [Category.comp_id] at this)
      (by have := onTorus_comp th (il' b); rwa [Category.id_comp] at this))
  have linX : ∀ (a : O) x, h (a • x) = a • h x := fun a x => by
    have := linS (star a) x
    rw [star_star] at this
    exact this.symm

  have L : Lin U.toUnifPre U'.toUnifPre (𝟙 G) prB h := ⟨inferInstance, hprB, qpr, th⟩
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G) prB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A'.A, IsMonHom c ∧ Gen₀ U.toUnifPre U'.toUnifPre (𝟙 G) c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map (𝟙 G) ≫ U'.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨E, eG, -⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (𝟙 G) (𝟙 A.A) inferInstance inferInstance
    (by simp)
  have eh : ∀ y, E.h y = y := fun y =>
    congrFun (un.2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) onTorus_id) y
  have adj : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) := by
    rw [eG]
    simp only [Category.comp_id]
    exact GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_linComb U.LG.isLB _ _)
  have H₂ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G) (𝟙 G) E.aG (𝟙 G) c c
    E.aA (𝟙 _) gc gc E.ext (by simp [Gen₀]) (by rw [eG]; simp only [Category.comp_id]; exact H)
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D' A A' G G hG hG U U' (𝟙 G) c prB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D' A A' G G hG hG U U' (𝟙 G) c prB h hc gc L C E E
    adj H₂ Ω K
  have H' : LBIso (abelian₂ G U'.LG.L) ((abelian₂ G U.LG.L).pull (lift (fst G G ≫ 𝟙 G) (snd G G ≫ 𝟙 G) : G2 G ⟶ G2 G).left) := by
    simp only [Category.comp_id, lift_fst_snd, Over.id_left]
    exact LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) H
  have H₃ := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hA D' D A' A G G hG hG U' U (𝟙 G) (𝟙 G) incB incB inferInstance inferInstance hincB hincB
    qinc qinc H'
  have key := GlobalTheory.Mum.Two.Fac.periods_of_factor R D'.toPre D.toPre D.tau_bimult O o 1 1 incB prB h φ hincB hprB
    (by rw [piB, o.onB.map_one]) (fun χ => (C χ).imp fun _ => And.left)
    (by rw [o.onB.map_one, Category.comp_id]; exact H₃) Ω hφ
    (fun y => by rw [hhφ, eh, star_one, one_smul, one_smul, one_smul])
  rw [o.onB.map_one, Category.comp_id] at key
  obtain ⟨cφ, w, hw, ht⟩ := key
  have φh : ∀ x, φ (h x) = x := fun x => hinj ((hhφ (h x)).trans (eh _))
  refine ⟨⟨incB, prB, ipB, piB⟩, xe, hincB, qinc, tk, linB, linX, fun x => ?_, w, hw, fun a b z J J' hJ hJ' => ?_⟩
  · show D'.toPre.c x ≫ incB = D.toPre.c (h x)
    have := cφ (h x)
    rw [φh] at this
    rw [this, Category.assoc, piB, Category.comp_id]
  · have := ht (h a) (h b) z J J' hJ hJ'
    rw [φh, φh, one_smul, one_smul, one_smul] at this
    exact this

end GlobalTheory.Mum.SameLam
