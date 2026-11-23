import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqOfSecConst
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalOfNormalised
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.SettingConsistentExample

theorem exists_even_one {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] (P : CP G)
    (i : H ⟶ G) (hi : i = 1) : ∃ σ : CubTriv P.c i, σ.Even := by
  subst hi
  obtain ⟨t, ht, hv⟩ := exists_gen P.L.isLB (φ := (PEmpty.elim : PEmpty → (H.left ⟶ G.left))) (ε := PEmpty.elim)
    (K' := Fin 2) (φ' := ![(1 : H ⟶ G).left, (1 : H ⟶ G).left]) (ε' := ![1, -1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen P.L.L) (LB.isGen_oneGen _)
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ H.left) (z : Z) (J), Good P.L.L z J → val t r z J = 1 :=
    fun Z r z J hJ => (hv Z r z J hJ).trans (val_one _)
  refine ⟨⟨t, ht, fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · simp only [v _ _ z J hJ, MonObj.comp_one, (isCub_cubV P.c hJ).face, _root_.mul_one]
  · show val t _ z J = _ * val t _ z J
    rw [v _ _ z J hJ, v _ _ z J hJ, MonObj.comp_one, P.val_sym_one hJ, _root_.mul_one]

section Generic
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']

theorem isCPPullback_cancel {P : CP G} {P' : CP G'} {P'' : CP G''} {f : S' ⟶ S} {g : S'' ⟶ S'} {f₀ : S'' ⟶ S}
    {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left} {F₀ : G''.left ⟶ G.left} (h : IsCPPullback P' P f F)
    (n : IsCPPullback P'' P f₀ F₀) (e₁ : g ≫ f = f₀) (e₂ : F' ≫ F = F₀) (w : F' ≫ G'.hom = G''.hom ≫ g) :
    IsCPPullback P'' P' g F' := by
  subst e₁ e₂
  obtain ⟨h, v, hv⟩ := h
  obtain ⟨n, u, hu⟩ := n
  have hg := h.cancel n w
  obtain ⟨w', h', -⟩ := (isCPMap_comp_cancel _ _ _ f g G G' G'' P P' P'' F _ v F' w n.1.w hv).2
    (fun T x y => Over.OverMorphism.ext (hg.2 T x y _ _ rfl rfl).symm) u hu
  exact ⟨hg, w', h'⟩

variable (hG : IsAbelianScheme G) (hG' : IsAbelianScheme G') (X : Type) [AddCommGroup X] [Subsingleton X]

omit [IsCommMonObj G] [IsCommMonObj G'] in

def abMap (F : G'.left ⟶ G.left) : (TQ.abelian G' hG' X).B.left ⟶ (TQ.abelian G hG X).B.left := F

omit [IsCommMonObj G'] in

def abMap' {Y : Scheme.{0}} (F : G'.left ⟶ Y) : (TQ.abelian G' hG' X).B.left ⟶ Y := F

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem abMap_q (F : G'.left ⟶ G.left) :
    (TQ.abelian G' hG' X).q.left ≫ abMap hG hG' X F = F ≫ (TQ.abelian G hG X).q.left :=
  (Category.id_comp _).trans (Category.comp_id _).symm

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem abMap_comp {Y : Scheme.{0}} {F : G'.left ⟶ G.left} {F₁ : G.left ⟶ Y} {F₀ : G'.left ⟶ Y} (h : F ≫ F₁ = F₀) :
    abMap hG hG' X F ≫ abMap' hG X F₁ = abMap' hG' X F₀ := h

theorem abMap_pb {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsCPPullback P' P f F) :
    IsCPPullback (TQ.Desc.abelian (X := X) hG' P').M (TQ.Desc.abelian (X := X) hG P).M f (abMap hG hG' X F) := h

theorem abMap'_pb {P : CP G} {P' : CP G'} {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsCPPullback P' P f F) :
    IsCPPullback (TQ.Desc.abelian (X := X) hG' P').M P f (abMap' hG' X F) := h

omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem ab_tor {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f F) :
    TorusCompat f F (TQ.abelian G' hG' X).i (TQ.abelian G hG X).i := by
  obtain ⟨i', hi', -⟩ := existsUnique_torusCompat hg.1 (TQ.abelian G hG X).i
  have := (TQ.abelian G hG X).i_hom
  have := hi'.isMonHom hg
  have : i' = (TQ.abelian G' hG' X).i := by
    have h1 : 𝟙 (splitTorus S' X) = 1 := point_eq_of_subsingleton _ _
    rw [← Category.id_comp i', h1, MonObj.one_comp]
    exact Hom.one_def
  exact this ▸ hi'

omit hG' in
theorem ab_even (P : CP G) : ∃ σ : CubTriv P.c (TQ.abelian G hG X).i, σ.Even :=
  exists_even_one _ _ (Hom.one_def).symm

end Generic

section Thick
variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

omit [IsDomain R] [GrpObj G] in
theorem thickMap_fst : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [IsDomain R] [GrpObj G] in
theorem thickMap_snd : thickMap R I e G ≫ (thickObj R I (e + 1) G).hom = (thickObj R I e G).hom ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

omit [IsDomain R] in

theorem isGrpPullback_thickMap :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm (thickMap_fst I e G).symm)
    (thickMap_snd I e G)

theorem isCPPullback_level [IsCommMonObj G] {P : CP G} {P₀ : CP (thickObj R I e G)} (h₀ : IsLevelCP I e P₀ P) :
    IsCPPullback P₀ P (thick R I e) (pullback.fst G.hom (thick R I e)) :=
  ⟨isGrpPullback_pullback G _, h₀⟩

theorem isCPPullback_levels [IsCommMonObj G] {P : CP G} {P₀ : CP (thickObj R I e G)} {P₁ : CP (thickObj R I (e + 1) G)}
    (h₀ : IsLevelCP I e P₀ P) (h₁ : IsLevelCP I (e + 1) P₁ P) :
    IsCPPullback P₀ P₁ (thickTrans R I e) (thickMap R I e G) :=
  isCPPullback_cancel (isCPPullback_level I (e + 1) G h₁) (isCPPullback_level I e G h₀) (thickTrans_comp R I e)
    (thickMap_fst I e G) (thickMap_snd I e G)

theorem nonempty_lev_torus (X : Type) [AddCommGroup X] :
    Nonempty (Lev I (CP.triv (splitTorus (Spec (CommRingCat.of R)) X)) X e) := by
  obtain ⟨Q, -⟩ := exists_tq_baseChange _ _ (thick R I e) X _ _ _ (isGrpPullback_pullback _ _) (TQ.torus _ X)
  exact ⟨⟨Q, CP.triv _, isLevelCP_triv I e _, TQ.Desc.triv Q⟩⟩

end Thick

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

def good (hV : CDVR V) (hG : IsAbelianScheme G) (gen : (Over.pullback (jK V)).obj G ≅ A.A) (hgen : IsMonHom gen.hom)
    (P : CP G) (w : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK V)))) (hw : w.IsGen) :
    HidaSetting V A G where
  cdvr := hV
  semi := isSemiAbelian_of_isAbelianScheme G hG
  gen := gen
  gen_hom := hgen
  P := P
  wA := w
  wA_gen := hw
  X := PUnit
  Q₀ := TQ.abelian _ (isAbelianScheme_pullback_obj _ G hG) PUnit
  P₀ := (exists_isLevelCP _ 0 P).choose
  lev₀ := (exists_isLevelCP _ 0 P).choose_spec
  even₀ := ab_even _ _ _

def goodLev (s : HidaSetting V A G) (hG : IsAbelianScheme G) [Subsingleton s.X] (e : ℕ) :
    Lev (IsLocalRing.maximalIdeal V) s.P s.X e where
  Q := TQ.abelian _ (isAbelianScheme_pullback_obj _ G hG) s.X
  Pe := (exists_isLevelCP _ e s.P).choose
  lev := (exists_isLevelCP _ e s.P).choose_spec
  D := TQ.Desc.abelian _ _

def goodTower (s : HidaSetting V A G) (hG : IsAbelianScheme G) [Subsingleton s.X] : Tower s where
  l := goodLev s hG
  tor e := ab_tor (isAbelianScheme_pullback_obj _ G hG) (isAbelianScheme_pullback_obj _ G hG) s.X
    (isGrpPullback_thickMap (IsLocalRing.maximalIdeal V) e G)
  β e := abMap (isAbelianScheme_pullback_obj _ G hG) (isAbelianScheme_pullback_obj _ G hG) s.X (thickMap V _ e G)
  β_pb e := abMap_pb _ _ s.X (isCPPullback_levels _ e G (goodLev s hG e).lev (goodLev s hG (e + 1)).lev)
  β_q e := abMap_q _ _ s.X _

def goodAlg (s : HidaSetting V A G) (hG : IsAbelianScheme G) [Subsingleton s.X] (ha : RelAmple G s.P.L.L) :
    (goodTower s hG).Alg where
  B := G
  isAb := hG
  M := s.P
  ample := ha
  b e := abMap' (isAbelianScheme_pullback_obj _ G hG) s.X (pullback.fst G.hom (thick V _ e))
  b_pb e := abMap'_pb _ s.X (isCPPullback_level _ e G (goodLev s hG e).lev)
  b_β e := abMap_comp _ _ s.X (thickMap_fst _ e G)

theorem good_of_degPre (hB : PolBaseChangeSt) (hV : CDVR V) (D : DegPre V) :
    ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (s : HidaSetting V A D.P.A) (t : Tower s), Nonempty t.Alg := by
  obtain ⟨A, eA, hA, w, hw⟩ := GoodReductionUnif.exists_baseChange hB (jK V) D.P
  let s : HidaSetting V A D.P.A := good hV D.P.isAb eA hA (CP.ofDegPre SemiRigid.globalFns D) w hw
  have : Subsingleton s.X := inferInstanceAs (Subsingleton PUnit)
  exact ⟨A, s, goodTower s D.P.isAb, ⟨goodAlg s D.P.isAb D.P.ample⟩⟩

theorem good_of_polAV (hL : Laws) (hV : CDVR V) (P : PolAV (Spec (CommRingCat.of V))) :
    ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (s : HidaSetting V A P.A) (t : Tower s), Nonempty t.Alg := by
  have hV' := hV
  obtain ⟨h₁, h₂, -⟩ := hV'
  have : IsNoetherianRing V := inferInstance
  obtain ⟨A, eA, hA, w, hw⟩ := GoodReductionUnif.exists_baseChange hL.polBaseChange (jK V) P
  obtain ⟨D, rfl, -, -⟩ := exists_unif_abelianScheme hL.globalFns hL.secBaseChange hL.cube V
    (IsLocalRing.maximalIdeal V) P A eA hA ⟨w, hw⟩
  exact good_of_degPre hL.polBaseChange hV D.toPre

theorem zero_padic (p : ℕ) [Fact p.Prime] :
    ∃ (s : HidaSetting ℤ_[p] (Inh.zeroPolAV _) (𝟙_ (Over (Spec (CommRingCat.of ℤ_[p]))))) (t : Tower s),
      Nonempty t.Alg := by
  let s : HidaSetting ℤ_[p] (Inh.zeroPolAV _) (𝟙_ (Over (Spec (CommRingCat.of ℤ_[p])))) :=
    good ⟨inferInstance, inferInstance, inferInstance⟩ (isAbelianScheme_unit _)
      ((UnifZero.isTerminalPullback (jK ℤ_[p])).uniqueUpToIso isTerminalTensorUnit)
      ⟨toUnit_unique _ _, toUnit_unique _ _⟩ (CP.triv _) _ (UnifZero.one_isGen_div _ _ _ _)
  have : Subsingleton s.X := inferInstanceAs (Subsingleton PUnit)
  exact ⟨s, goodTower s (isAbelianScheme_unit _), ⟨goodAlg s _ (Inh.zeroPolAV _).ample⟩⟩

theorem not_allSet_false : ¬ AllSet fun _ => False := fun h =>
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (zero_padic 2).elim fun s _ => h _ _ _ s

theorem repWt_one {s : HidaSetting V A G} {t : Tower s} (a : t.Alg) (e : ℕ) : a.RepWt 1 0 e := by
  obtain ⟨u, hu, -⟩ := exists_gen a.M.L.isLB (φ := (PEmpty.elim : PEmpty → (a.B.left ⟶ a.B.left))) (ε := PEmpty.elim)
    (K' := Fin 2) (φ' := ![((toUnit a.B ≫ (1 : 𝟙_ _ ⟶ a.B)) * 𝟙 a.B).left, 𝟙 a.B.left]) (ε' := ![-1, 1])
    (fun U _ h => by simp [Fin.prod_univ_two]) (LB.oneGen a.M.L.L) (LB.isGen_oneGen _)
  refine ⟨LB.genPull _ u _, LB.isGen_genPull _ u hu _, fun j => ?_⟩
  exact TorusQuotientLift.isWt_appLE_of_invariant ((t.l e).Q.q.left ≫ a.b e) (fun Z τ g => by
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, TorusQuotientLift.act_comp_q, Over.comp_left]) _
    (LB.wchart_le _ (K := PUnit) (fun _ => (t.l e).Q.q.left ≫ a.b e) j PUnit.unit) (u.s (j PUnit.unit)).val

theorem cubeSt' : CubeSt :=
  GlobalTheory.AbLaw.Cube.cube_of_gen GlobalTheory.laws_without_cohomology.1 (GlobalTheory.AbLaw.exists_gen_theta
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy
    (GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1)
    GlobalTheory.AbLaw.isProjBy_tensor GlobalTheory.TrivLocus.isClosed_trivLocus
    (GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.Seesaw.seesaw
      (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.laws_without_cohomology.1
        GlobalTheory.KuennethOne.kuenneth_injective)))

theorem exists_hidaSetting_tower_of_cdvr (hV : CDVR V) (P : PolAV (Spec (CommRingCat.of V))) :
    ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (s : HidaSetting V A P.A) (t : Tower s) (a : t.Alg),
      a.B = P.A ∧ s.P.L.L = P.L := by
  have hV' := hV
  obtain ⟨h₁, h₂, -⟩ := hV'
  have : IsNoetherianRing V := inferInstance
  obtain ⟨A, eA, hA, w, hw⟩ := GoodReductionUnif.exists_baseChange GlobalTheory.polBaseChange_holds (jK V) P
  obtain ⟨D, rfl, -⟩ := SelfUnif.exists_degData cubeSt' (IsLocalRing.maximalIdeal V) P
  let s : HidaSetting V A D.toPre.P.A := good hV D.toPre.P.isAb eA hA (CP.ofDegPre SemiRigid.globalFns D.toPre) w hw
  have : Subsingleton s.X := inferInstanceAs (Subsingleton PUnit)
  exact ⟨A, s, goodTower s D.toPre.P.isAb, goodAlg s D.toPre.P.isAb D.toPre.P.ample, rfl, rfl⟩

def curveTwoAdic : WeierstrassCurve ℤ_[2] := ⟨0, 0, 1, 0, 0⟩

instance isElliptic_curveTwoAdic : curveTwoAdic.IsElliptic := ⟨by
  have h : curveTwoAdic.Δ = -(3 : ℤ_[2]) ^ 3 := by
    simp only [curveTwoAdic, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    ring
  have h3 : IsUnit (3 : ℤ_[2]) := by
    have : ‖((3 : ℕ) : ℤ_[2])‖ = 1 := PadicInt.norm_natCast_eq_one_iff.2 (by norm_num)
    exact PadicInt.isUnit_iff.2 (by simpa using this)
  rw [h]
  exact (h3.pow 3).neg⟩

theorem elliptic_two_adic :
    ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing ℤ_[2]))))
      (s : HidaSetting ℤ_[2] A (GlobalTheory.WeierstrassCurve.ellPolAV curveTwoAdic).A) (t : Tower s) (a : t.Alg),
      a.B = (GlobalTheory.WeierstrassCurve.ellPolAV curveTwoAdic).A ∧ ∀ u : s.P.L.L.Gen, ¬ u.IsGen := by
  obtain ⟨A, s, t, a, h, h'⟩ := exists_hidaSetting_tower_of_cdvr (V := ℤ_[2]) ⟨inferInstance, inferInstance, inferInstance⟩
    (GlobalTheory.WeierstrassCurve.ellPolAV curveTwoAdic)
  refine ⟨A, s, t, a, h, ?_⟩
  rw [h']
  exact GlobalTheory.WeierstrassCurve.not_isGen_ellPolAV curveTwoAdic

end GlobalTheory.UU.SettingConsistentExample
end
