import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackExtendDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionSquareOfAxesTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActExtendsSemiAbelianDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeGeometricPointsOfGenericDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationKernelKilledOverDvrOfGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemeDvrSectionsMulEquivGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvrStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NotWeilIsGrpPullbackNoncomm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTObjExt

variable {p : ℕ} [Fact p.Prime]

theorem sp_point {R W R' : Type} [CommRing R] [CommRing W] [CommRing R'] (gm : R →+* W) (β : R →+* R')
    (x : Sp R' ⟶ Sp W) (hx : x ≫ spMap gm = spMap β) : ∃ β₀ : W →+* R', spMap β₀ = x ∧ β₀.comp gm = β := by
  refine ⟨(Spec.preimage x).hom, by simp [spMap], ?_⟩
  have e : spMap ((Spec.preimage x).hom.comp gm) = spMap β := by
    rw [spMap_comp, ← hx]; congr 1; simp [spMap]
  have e2 := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom e2

theorem lift_match₂ {S S' : Scheme.{0}} {A : Over S'} {G : Over S} {φ : A.left ⟶ G.left}
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (hsq : IsSquare φ φ₂) (u v : A ⊗ A ⟶ A) (U V : G ⊗ G ⟶ G)
    (hu : u.left ≫ φ = φ₂ ≫ U.left) (hv : v.left ≫ φ = φ₂ ≫ V.left) :
    (lift u v).left ≫ φ₂ = φ₂ ≫ (lift U V).left := by
  have pG : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  apply pG.hom_ext
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hu, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hv, Category.assoc,
      ← Over.comp_left, lift_snd]

theorem isTanScal_push {O : Type} [Ring O] {S S' : Scheme.{0}} {G : Over S} {A : Over S'} [GrpObj G] [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (act : OActN O A) (act' : OActN O G)
    (hact : ∀ c, (act.act c).left ≫ φ = φ ≫ (act'.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S') :
    ∃ e : (epsPtR x ⟶ A) ≃* (epsPtR (x ≫ f) ⟶ G), ∀ (b : O) (c : R') (v : epsPtR x ⟶ A),
      IsTanScal act x b c v ↔ IsTanScal act' (x ≫ f) b c (e v) := by
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  refine ⟨e, fun b c v => ?_⟩
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ A).left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have E : e (v ≫ act.act b) = e v ≫ act'.act b := Over.OverMorphism.ext (by
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A)).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · rw [← E, he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ act.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem tate_push {D : Datum p} {S S' : Scheme.{0}} {G : Over S} {A : Over S'} [GrpObj G] [GrpObj A]
    [IsCommMonObj A] {f : S' ⟶ S} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ)
    {φ₂ : (G2 A).left ⟶ (G2 G).left} (hsq : IsSquare φ φ₂) (act : OActN D.O A) (act' : OActN D.O G)
    (hact : ∀ c, (act.act c).left ≫ φ = φ ≫ (act'.act c).left) (P : LB (G2 A).left) (P' : LB (G2 G).left)
    (hP : P.IsLB) (hP' : P'.IsLB) (iP : LBIso P (P'.pull φ₂)) (N : ℕ) (lv : D.La → (𝟙_ (Over S') ⟶ A))
    (lv' : D.La → (𝟙_ (Over S) ⟶ G)) (hlv : ∀ y, (lv y).left ≫ φ = f ≫ (lv' y).left)
    (k : Type) [Field k] (x : Sp k ⟶ S')
    (H : ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ lv y = I.ev N y) :
    ∃ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ G) (fun c g => g ≫ act'.act c)
        (fun n g g' z => Out.WeilIs G (P'.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ lv' y = I.ev N y := by
  obtain ⟨I, hI⟩ := H
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have hd : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 G) (𝟙 G)).left :=
    GlobalTheory.AxisTrivExt.lift_match hsq.1 hsq.2 (𝟙 A) (𝟙 A) (𝟙 G) (𝟙 G) (by simp) (by simp)
  have a3 : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P'.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GenSpread.lbIso_pullback iP _
  have b1 : LBIso (P'.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) ((P'.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GenSpread.lbIso_pull_pull hP' _ hd.symm
  have b2 : LBIso (P'.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) ((P'.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
    GenSpread.lbIso_pull_pull hP' φ rfl
  have iD : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P'.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
    LBIso.trans (pull_isLB hP _) (pull_isLB hP' _) (pull_isLB (pull_isLB hP' _) _)
      (LBIso.trans (pull_isLB hP _) (pull_isLB (pull_isLB hP' _) _) (pull_isLB hP' _) a3 b1.symm) b2
  have W' := fun (n : ℤ) (g g' : Over.mk x ⟶ A) (z : kˣ) =>
    weilIs_baseChange_of_comm S S' G A f φ h (P'.pull (lift (𝟙 G) (𝟙 G)).left) (P.pull (lift (𝟙 A) (𝟙 A)).left)
      (pull_isLB hP' _) (pull_isLB hP _) iD k x n g g' (e g) (e g') z (he g) (he g')
  have lin : ∀ (c : D.O) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ act'.act c := fun c g =>
    Over.OverMorphism.ext (by rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
  refine ⟨{ ζ := I.ζ
            ζ_prim := I.ζ_prim
            ζ_pow := I.ζ_pow
            ev := fun n y => e (I.ev n y)
            add := fun n y y' => by simp only [I.add, map_mul]
            lin := fun n c y => by simp only [I.lin, lin]
            ker := fun n hn hp y => by
              rw [← I.ker n hn hp y]
              exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
            onto := fun n hn hp q => by
              obtain ⟨q, rfl⟩ := e.surjective q
              rw [← map_pow]
              refine Iff.trans ?_ ((I.onto n hn hp q).trans ?_)
              · exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
              · exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩, fun ⟨y, hy⟩ => ⟨y, e.injective hy⟩⟩
            tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp y]
            isom := fun n hn hp y y' => (W' n _ _ _).1 (I.isom n hn hp y y') }, fun y => ?_⟩
  show toUnit _ ≫ lv' y = e (I.ev N y)
  rw [← hI y]
  have e₁ : (toUnit (Over.mk x)).left = x := by simpa using Over.w (toUnit (Over.mk x))
  have e₂ : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := by simpa using Over.w (toUnit (Over.mk (x ≫ f)))
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, Category.assoc, hlv, e₁, e₂, Category.assoc]

theorem extends_obj : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (o : Obj b N (spMap ((algebraMap W L).comp gm))) (G : Over (Sp W)) [GrpObj G] (φ : o.A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback o.A G (spMap (algebraMap W L)) φ → ∃ o' : Obj b N (spMap gm), Nonempty (ObjMap o o' (spMap (algebraMap W L))) := by
  intro p _ D R _ b N W L _ _ _ _ _ _ gm o G _ φ hG hA
  haveI : IsCommMonObj G := hG.comm
  have pG : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  let φ₂ : (G2 o.A).left ⟶ (G2 G).left := pG.lift ((fst o.A o.A).left ≫ φ) ((snd o.A o.A).left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hA.1.w, ← Category.assoc, ← Category.assoc, Over.w (fst o.A o.A),
      Over.w (snd o.A o.A)])
  have hsq : IsSquare φ φ₂ := ⟨pG.lift_fst _ _ _, pG.lift_snd _ _ _⟩

  obtain ⟨act', ⟨h1, h2, h3, h4⟩, hact⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G o.A φ (isSemiAbelian_of_isAbelianScheme G hG) hA
    D.Oᵐᵒᵖ (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a c => by simp [o.act.mul]) (fun a c => by simp [o.act.add])
  let actG : OActN D.O G :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => h1 _
      one := by simpa using h2
      mul := fun c d => by rw [MulOpposite.op_mul]; exact h3 _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact h4 _ _ }
  have hactG : ∀ c, (o.act.act c).left ≫ φ = φ ≫ (actG.act c).left := fun c => hact (MulOpposite.op c)

  obtain ⟨P', hP', r1, r2, iP⟩ := GlobalTheory.AxisTrivExt.exists_extension_square_of_axes_trivial W L G o.A φ φ₂ hG hA hsq
    o.P o.isLB o.rig₁ o.rig₂
  have hP := o.isLB
  have symm' : LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) := by
    have i0 : LBIso (o.P.pull (𝟙 (G2 o.A).left)) (o.P.pull (lift (snd o.A o.A) (fst o.A o.A)).left) :=
      LBIso.trans (pull_isLB hP _) hP (pull_isLB hP _) (lbIso_pull_id hP) o.symm
    have i1 := GlobalTheory.T.lineBundleIso_pullback_extend_DVR W L G o.A φ φ₂ hG hA hsq o.P P' hP hP' iP (𝟙 _) (lift (snd o.A o.A) (fst o.A o.A))
      (𝟙 _) (lift (snd G G) (fst G G)) (by simp)
      (lift_match₂ hsq _ _ _ _ hsq.2.symm hsq.1.symm) i0
    exact LBIso.trans hP' (pull_isLB hP' _) (pull_isLB hP' _) (lbIso_pull_id hP').symm i1
  have rosati' : ∀ c : D.O, LBIso (P'.pull (lift (fst G G ≫ actG.act c) (snd G G)).left)
      (P'.pull (lift (fst G G) (snd G G ≫ actG.act (D.star c).unop)).left) := fun c =>
    GlobalTheory.T.lineBundleIso_pullback_extend_DVR W L G o.A φ φ₂ hG hA hsq o.P P' hP hP' iP _ _ _ _
      (lift_match₂ hsq _ _ _ _ (by rw [Over.comp_left, Category.assoc, hactG, ← Category.assoc, ← hsq.1,
        Category.assoc, Over.comp_left]) hsq.2.symm)
      (lift_match₂ hsq _ _ _ _ hsq.1.symm (by rw [Over.comp_left, Category.assoc, hactG, ← Category.assoc,
        ← hsq.2, Category.assoc, Over.comp_left])) (o.rosati c)
  have ample' := GlobalTheory.T.relAmple_diagonal_extendedBundle_of_generic W L G o.A φ φ₂ hG hA hsq o.P P' hP hP' iP o.ample
  have kerP' : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp W)) (x : T ⟶ G),
      (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, hk⟩ := o.kerP
    exact ⟨e, he, GlobalTheory.T.polarisation_kernel_killed_over_dvr_of_generic W L G o.A φ φ₂ hG hA hsq o.P P' hP hP' iP r1 r2 symm' ample' e hk⟩

  obtain ⟨eL, heL⟩ := GlobalTheory.T.properGroupScheme_dvr_sections_mulEquiv_generic W L G o.A φ hG.proper hA
  have inj : ∀ s₁ s₂ : 𝟙_ (Over (Sp L)) ⟶ o.A, s₁.left ≫ φ = s₂.left ≫ φ → s₁ = s₂ := fun s₁ s₂ e =>
    Over.OverMorphism.ext (hA.1.hom_ext e (by rw [Over.w, Over.w]))
  have key : ∀ s t, s.left ≫ φ = spMap (algebraMap W L) ≫ t.left → eL s = t := fun s t e => by
    have e' := heL (eL.symm t)
    rw [MulEquiv.apply_symm_apply] at e'
    rw [inj s (eL.symm t) (e.trans e'.symm), MulEquiv.apply_symm_apply]
  let eta' : D.La → (𝟙_ (Over (Sp W)) ⟶ G) := fun y => eL (o.eta y)
  have eta_add' : ∀ x y, eta' (x + y) = eta' x * eta' y := fun x y => by
    simp only [eta', o.eta_add, map_mul]
  have hlv : ∀ y, (o.eta y).left ≫ φ = spMap (algebraMap W L) ≫ (eta' y).left := fun y => heL _

  have disc : IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) := by
    have hc : (Int.natAbs (D.tr ^ 2 - 4 * D.nm)).Coprime p := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 fun hd => D.disc_p ?_)
      exact Int.ofNat_dvd_left.2 hd
    have hu := (b.unit _ hc).map gm
    rw [map_natCast] at hu
    rcases Int.natAbs_eq (D.tr ^ 2 - 4 * D.nm) with e | e
    · rw [e, Int.cast_natCast]; exact hu
    · rw [e, Int.cast_neg, Int.cast_natCast]; exact hu.neg
  have comax' : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => (gm.comp (b.t i)) x - (gm.comp (b.t j)) x) = ⊤ :=
    fun i j hij => by
      have e := congrArg (Ideal.map gm) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at e
      simpa [Function.comp_def, map_sub] using e
  have hx : ∀ (R' : Type) [CommRing R'] (β : L →+* R'),
      spMap β ≫ spMap ((algebraMap W L).comp gm) = spMap (β.comp ((algebraMap W L).comp gm)) :=
    fun R' _ β => (spMap_comp _ _).symm
  have lieGen : ∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G,
      IsTanScal actG (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L (gm b.ρ))) v →
      ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G),
        (∀ i, ∀ c : 𝓞 D.F, IsTanScal actG (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c)
          (β (algebraMap W L ((gm.comp (b.t i)) c))) (w i)) ∧ v = (List.ofFn w).prod := by
    intro R' _ β
    rw [spMap_comp]
    intro v hv
    obtain ⟨e, he⟩ := isTanScal_push hA o.act actG hactG (spMap β)
    have hu := (he _ _ (e.symm v)).2 (by rw [MulEquiv.apply_symm_apply]; exact hv)
    obtain ⟨w, hw, hwv⟩ := o.lie R' (β.comp ((algebraMap W L).comp gm)) (spMap β) (hx R' β) _ hu
    refine ⟨fun i => e (w i), fun i c => (he _ _ _).1 (hw i c), ?_⟩
    rw [← e.apply_symm_apply v, hwv, map_list_prod, List.map_ofFn]
    rfl
  have rankGen : ∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i,
      LieMult (actG.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (gm.comp (b.t i))) D.m := by
    intro k _ _ β i
    rw [spMap_comp]
    exact (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) (Sp W) (Sp L) G o.A (spMap (algebraMap W L)) φ (actG.toF D)
      (o.act.toF D) hA (fun c => hactG _) k (spMap β) _ D.m).1 (o.lieRank k (spMap β) _ (hx k β) i)
  obtain ⟨lieG, rankG⟩ := GlobalTheory.T.harrisTaylor_lie_condition_extends_abelianScheme_dvr p D W L G hG actG (gm b.ρ) (fun i => gm.comp (b.t i))
    (fun i => by simp [b.t_ω]) (by simpa using congrArg gm b.ρ_root) comax' disc lieGen rankGen

  have geomGen : ∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k),
      ∃ I : TateIsoO D k (Over.mk (spMap (β.comp (algebraMap W L))) ⟶ G) (fun c g => g ≫ actG.act c)
        (fun n g g' z => Out.WeilIs G (P'.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)),
      ∀ x, toUnit _ ≫ eta' x = I.ev N x := by
    intro k _ _ β
    rw [spMap_comp]
    exact tate_push hA hsq o.act actG hactG o.P P' hP hP' iP N o.eta eta' hlv k (spMap β)
      (o.geom k (spMap β) _ (hx k β))
  have geomG := GlobalTheory.T.tateSimilitude_geometric_points_of_generic_dvr p D R b N W L gm G hG actG P' hP' eta' eta_add' geomGen
  have lie' : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp W), x ≫ spMap gm = spMap β →
      ∀ v : epsPtR x ⟶ G, IsTanScal actG x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v →
        ∃ w : Fin D.a → (epsPtR x ⟶ G),
          (∀ i, ∀ c : 𝓞 D.F, IsTanScal actG x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧
          v = (List.ofFn w).prod := by
    intro R' _ β x hx' v hv
    obtain ⟨β₀, rfl, rfl⟩ := sp_point gm β x hx'
    exact lieG R' β₀ v hv
  have rank' : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W) (β : R →+* k), x ≫ spMap gm = spMap β →
      ∀ i, LieMult (actG.toF D) x (β.comp (b.t i)) D.m := by
    intro k _ _ x β hx' i
    obtain ⟨β₀, rfl, rfl⟩ := sp_point gm β x hx'
    exact rankG k β₀ i
  have lin' : ∀ (c : D.O) x, eta' (c • x) = eta' x ≫ actG.act c := by
    intro c x
    show eL (o.eta (c • x)) = eL (o.eta x) ≫ actG.act c
    rw [o.eta_lin]
    refine key _ _ ?_
    rw [Over.comp_left, Category.assoc, hactG, ← Category.assoc, hlv, Category.assoc, Over.comp_left]
  have ker' : ∀ x, eta' (N • x) = 1 := by
    intro x
    show eL (o.eta (N • x)) = 1
    rw [o.eta_ker, map_one]
  have geom' : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W) (β : R →+* k), x ≫ spMap gm = spMap β →
      ∃ I : TateIsoO D k (Over.mk x ⟶ G) (fun c g => g ≫ actG.act c)
        (fun n g g' z => Out.WeilIs G (P'.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ eta' y = I.ev N y := by
    intro k _ _ x β hx'
    obtain ⟨β₀, rfl, rfl⟩ := sp_point gm β x hx'
    exact geomG k β₀
  exact ⟨Obj.mk G hG actG P' hP' r1 r2 symm' ample' kerP' rosati' lie' rank' eta' eta_add' lin' ker' geom',
    ⟨ObjMap.mk φ φ₂ hA hsq hactG iP hlv⟩⟩
end GlobalTheory.HTObjExt
