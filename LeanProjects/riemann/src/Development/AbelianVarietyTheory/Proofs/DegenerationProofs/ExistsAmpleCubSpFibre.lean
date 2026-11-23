import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSabExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNonzeroLocusEqOfIsAffineOpen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.SS.AmpCub

open GlobalTheory.CechPic GlobalTheory.TripleExt GlobalTheory.EndOnTorsion GlobalTheory.AmpleStabFinite GlobalTheory.AbLaw

theorem pic_eq_zero {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {H : Scheme.{0}} (p : H ⟶ Sp V) (e : Sp V ⟶ H) (hs : Smooth p)
    (hi : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (c : CechPic.Pic H)
    (h₁ : CechPic.pull (pullback.fst p (etaK V K)) c = 0) : c = 0 := by
  have h₂ := pull_spec_local e c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  let eK : Sp K ⟶ pullback p (etaK V K) := pullback.lift (etaK V K ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.id_comp]; exact Category.comp_id _)
  have heK : eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e := pullback.lift_fst _ _ _
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hM (pullback.fst p (etaK V K) ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₁])
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hM (e ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₂])
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hM _ _ t ht (pullback.snd p (etaK V K)) eK
    (pullback.lift_snd _ _ _) _ _ (LB.pullGen M _ _ ρ (etaK V K)) (DVR.pullGen_isGen _ _ _ _ hρ _) (by
      congr 1
      funext k
      rw [← Category.assoc, heK, Category.assoc])
  obtain ⟨s, ⟨hs₁, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V K H H p e hs hi he eK heK M hM
    PUnit (fun _ => 𝟙 H) (fun _ => 1) u ρ hu hρ cu
  have := (cls_eq_zero_iff (pull_isLB hM (𝟙 H))).2 ⟨s, hs₁⟩
  rwa [cls_pull hM, pull_id] at this

section Cube

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem cube_pts {c : CechPic.Pic G.left} (h : cubeCls (x3 G) c = 0) {T : Over S} (x : Fin 3 → (T ⟶ G)) :
    cubeCls x c = 0 := by
  have h₁ := congrArg (CechPic.pull (lift (x 0) (lift (x 1) (x 2))).left) h
  rw [pull_cubeCls_pre, map_zero] at h₁
  refine Eq.trans ?_ h₁
  congr 1
  funext i
  fin_cases i <;> simp [x3]

theorem cube_pull {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {c : CechPic.Pic G.left}
    (hc : cubeCls (x3 G) c = 0) : cubeCls (x3 G') (CechPic.pull φ c) = 0 :=
  (pull_cubeCls_push h (x3 G') (fun i => pushPt h.1.w (x3 G' i)) (𝟙 _) (fun _ => (Category.id_comp _).symm) c).symm.trans
    (by rw [cube_pts hc, map_zero])

theorem sum_three {T : Over S} (x y z : T ⟶ G) {A : Type*} [AddCommGroup A] (h : (T ⟶ G) → A) :
    ∑ I : ULift.{0} (Finset (Fin 3)), ((-1 : ℤ) ^ (3 - I.down.card)) • h (psum G ![x, y, z] I.down) =
      h (x * y * z) - h (x * y) - h (x * z) - h (y * z) + h x + h y + h z - h 1 := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 3)) ≃ Finset (Fin 3)) _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • h (psum G ![x, y, z] I)) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have p₀ : psum G ![x, y, z] ∅ = 1 := rfl
  have p₁ : psum G ![x, y, z] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y, z] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y, z] {2} = z := _root_.mul_one z
  have p₄ : psum G ![x, y, z] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₅ : psum G ![x, y, z] {0, 2} = x * z := congrArg (x * ·) (_root_.mul_one z)
  have p₆ : psum G ![x, y, z] {1, 2} = y * z := congrArg (y * ·) (_root_.mul_one z)
  have p₇ : psum G ![x, y, z] {0, 1, 2} = x * y * z :=
    (congrArg (fun w => x * (y * w)) (_root_.mul_one z)).trans (_root_.mul_assoc x y z).symm
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇]
  have c₁ : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c₂ : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₃ : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₄ : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  simp only [c₁, c₂, c₃, c₄, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

theorem cubeCls_three {T : Over S} (x y z : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y, z] c = CechPic.pull (x * y * z).left c - CechPic.pull (x * y).left c - CechPic.pull (x * z).left c -
      CechPic.pull (y * z).left c + CechPic.pull x.left c + CechPic.pull y.left c + CechPic.pull z.left c -
      CechPic.pull (1 : T ⟶ G).left c :=
  sum_three x y z fun w => CechPic.pull w.left c

theorem pull_inv {T : Over S} (x : T ⟶ G) (c : CechPic.Pic G.left) :
    CechPic.pull x.left (CechPic.pull (ι[G]).left c) = CechPic.pull (x⁻¹).left c := by
  rw [← pull_comp, ← Over.comp_left]; rfl

theorem cube_symm {c : CechPic.Pic G.left} (hc : cubeCls (x3 G) c = 0) :
    cubeCls (x3 G) (c + CechPic.pull (ι[G]).left c) = 0 := by
  have e : x3 G = ![x3 G 0, x3 G 1, x3 G 2] := rfl
  have h₁ := cube_pts hc ![x3 G 0, x3 G 1, x3 G 2]
  have h₂ := cube_pts hc ![(x3 G 0)⁻¹, (x3 G 1)⁻¹, (x3 G 2)⁻¹]
  rw [cubeCls_three] at h₁ h₂
  rw [e, cubeCls_three]
  simp only [map_add, pull_inv, mul_inv, inv_one]
  rw [← add_zero (0 : CechPic.Pic _)]
  refine Eq.trans ?_ (congrArg₂ (· + ·) h₁ h₂)
  abel

end Cube

section Field

variable {k : Type} [Field k] {H : Over (Sp k)} [GrpObj H] [IsCommMonObj H]

theorem square {c : CechPic.Pic H.left} (hc : cubeCls (x3 H) c = 0) (a : 𝟙_ (Over (Sp k)) ⟶ H) :
    CechPic.pull (transl a).hom.left c + CechPic.pull (transl a⁻¹).hom.left c = (2 : ℤ) • c := by
  have z : ∀ b : 𝟙_ (Over (Sp k)) ⟶ H, CechPic.pull (toUnit H ≫ b).left c = 0 := fun b => by
    rw [Over.comp_left, pull_comp]
    exact (congrArg _ (pull_spec_local (K := k) b.left c)).trans (map_zero _)
  have h := cube_pts hc ![toUnit H ≫ a, toUnit H ≫ a⁻¹, 𝟙 H]
  have e : (toUnit H ≫ a) * (toUnit H ≫ a⁻¹) = 1 := by
    rw [← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one]
  have o : CechPic.pull (1 : H ⟶ H).left c = 0 := z η[H]
  rw [cubeCls_three, e, _root_.one_mul, z, z, o, Over.id_left, pull_id] at h
  change CechPic.pull ((toUnit H ≫ a) * 𝟙 H).left c + CechPic.pull ((toUnit H ≫ a⁻¹) * 𝟙 H).left c = _
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  abel

theorem pt_transl (x a : 𝟙_ (Over (Sp k)) ⟶ H) : x ≫ (transl a).hom = a * x := by
  simp [transl, MonObj.comp_mul, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (𝟙 _)]

theorem nonempty_preimage {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] {W : Y.Opens} (hW : (W : Set Y).Nonempty) :
    ((f ⁻¹ᵁ W : X.Opens) : Set X).Nonempty := by
  obtain ⟨w, hw⟩ := hW
  obtain ⟨x, rfl⟩ := f.surjective w
  exact ⟨x, hw⟩

theorem ample [IsAlgClosed k] [LocallyOfFiniteType H.hom] [IsIntegral H.left] [H.left.IsSeparated] {L : LB H.left}
    (hL : L.IsLB) (hc : cubeCls (x3 H) (cls L hL) = 0) {W : H.left.Opens} (hW : IsLocus (cls L hL) W)
    (ha : IsAffineOpen W) (hne : (W : Set H.left).Nonempty) (x : H.left) :
    ∃ s : LB.Sec (pw L (2 : ℕ)), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s) := by
  have iso : ∀ f : H ≅ H, IsIso f.hom.left := fun f => inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  have isoι : IsIso (ι[H]).left := inferInstanceAs (IsIso ((Over.forget _).map ι[H]))
  have pl : ∀ f : H.left ⟶ H.left, IsLocus (CechPic.pull f (cls L hL)) (f ⁻¹ᵁ W) := fun f => by
    obtain ⟨s, rfl⟩ := hW.exists_sec hL
    exact ⟨_, pull_isLB hL _, secPull s f, rfl, nonzeroLocus_secPull _ _⟩
  have key : ∀ (y : 𝟙_ (Over (Sp k)) ⟶ H) (p : Sp k), ∃ s : LB.Sec (pw L (2 : ℕ)),
      y.left p ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s) := by
    intro y p
    have := iso (transl y)
    obtain ⟨σ, hσ, hm⟩ := NoBasePoint.exists_section_mem H.hom
      ((transl y).hom.left ⁻¹ᵁ W ⊓ ((ι[H]).left ≫ (transl y).hom.left) ⁻¹ᵁ W)
      (nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _) (TopologicalSpace.Opens.isOpen _)
        (nonempty_preimage _ hne) (nonempty_preimage _ hne))
    let a : 𝟙_ (Over (Sp k)) ⟶ H := Over.homMk σ hσ
    have hl := (pl (transl a).hom.left).add (pl (transl a⁻¹).hom.left)
    rw [square hc a, ← cls_pw hL] at hl
    obtain ⟨s, hs⟩ := hl.exists_sec
    have := iso (transl a)
    have := iso (transl a⁻¹)
    refine ⟨s, hs.ge ⟨?_, ?_⟩, ?_⟩
    · have e : y ≫ (transl a).hom = a ≫ (transl y).hom := by rw [pt_transl, pt_transl, _root_.mul_comm]
      exact (congrArg (fun q => q.left p ∈ W) e).mpr (hm p).1
    · have e : y ≫ (transl a⁻¹).hom = a ≫ ι[H] ≫ (transl y).hom := by
        rw [← Category.assoc, pt_transl, pt_transl, _root_.mul_comm]; rfl
      exact (congrArg (fun q => q.left p ∈ W) e).mpr (hm p).2
    · exact (congrArg IsAffineOpen hs).mpr ((ha.preimage _).inf (ha.preimage _))
  have : JacobsonSpace H.left := LocallyOfFiniteType.jacobsonSpace H.hom
  obtain ⟨z, hz, hcl⟩ := nonempty_inter_closedPoints (Z := closure {x}) ⟨x, subset_closure rfl⟩
    isClosed_closure.isLocallyClosed
  obtain ⟨s, hs, hs'⟩ := key (Over.homMk (pointOfClosedPoint H.hom z hcl) (pointOfClosedPoint_comp H.hom z hcl))
    (IsLocalRing.closedPoint k)
  have hs₁ : z ∈ Out.nonzeroLocus s := (congrArg (· ∈ Out.nonzeroLocus s) (pointOfClosedPoint_apply H.hom z hcl _)).mp hs
  exact ⟨s, (specializes_iff_mem_closure.2 hz).mem_open (TopologicalSpace.Opens.isOpen _) hs₁, hs'⟩

theorem exists_ampleCub [IsAlgClosed k] [LocallyOfFiniteType H.hom] [IsIntegral H.left] [H.left.IsSeparated]
    {c : CechPic.Pic H.left} (hc : cubeCls (x3 H) c = 0) {W : H.left.Opens} (hW : IsLocus c W)
    (ha : IsAffineOpen W) (hne : (W : Set H.left).Nonempty) : ∃ L : LB H.left, AmpleCub H L := by
  have isoι : IsIso (ι[H]).left := inferInstanceAs (IsIso ((Over.forget _).map ι[H]))
  have hW' : IsLocus (CechPic.pull (ι[H]).left c) ((ι[H]).left ⁻¹ᵁ W) := by
    obtain ⟨M, hM, s, rfl, rfl⟩ := hW
    exact ⟨_, pull_isLB hM _, secPull s _, rfl, nonzeroLocus_secPull _ _⟩
  obtain ⟨L, hL, e⟩ := cls_surj (c + CechPic.pull (ι[H]).left c)
  have hc' := cube_symm hc
  have hW'' := hW.add hW'
  rw [← e] at hc' hW''
  refine ⟨L, hL, (cls_eq_zero_iff (isLB_cube _ hL)).1 ((cls_cube _ hL).trans hc'),
    (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_, 2, one_le_two,
    ample hL hc' hW'' (ha.inf (ha.preimage _)) (nonempty_preirreducible_inter W.isOpen
      (TopologicalSpace.Opens.isOpen _) hne (nonempty_preimage _ hne))⟩
  rw [cls_linComb hL, Fin.sum_univ_two]
  show (1 : ℤ) • CechPic.pull (ι[H]).left (cls L hL) + (-1 : ℤ) • CechPic.pull (𝟙 H.left) (cls L hL) = 0
  rw [pull_id, e, map_add, ← pull_comp, ← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left, pull_id]
  abel

end Field

theorem cube_model {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (P : Out.PolAV (Sp K)) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    [GeometricallyConnected G.hom] {φ : P.A.left ⟶ G.left} (h : IsGrpPullback P.A G (etaK R K) φ)
    (c : CechPic.Pic G.left) : cubeCls (x3 G) c = 0 := by
  have := P.isAb.comm
  have hsm₂ : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc₂ : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  have hsm : Smooth (G3 G).hom := by
    show Smooth (pullback.fst G.hom (G ⊗ G).hom ≫ G.hom)
    infer_instance
  have hgc : GeometricallyConnected (G3 G).hom := by
    show GeometricallyConnected (pullback.fst G.hom (G ⊗ G).hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  let T' : Over (Sp K) := Over.mk (pullback.snd (G3 G).hom (etaK R K))
  let u : Over.mk (T'.hom ≫ etaK R K) ⟶ G3 G := Over.homMk (pullback.fst (G3 G).hom (etaK R K)) pullback.condition
  have hy : ∀ y : G3 G ⟶ G, ∃ y' : T' ⟶ P.A, pushPt h.1.w y' = u ≫ y := fun y =>
    ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  choose y hy using hy
  let e : 𝟙_ (Over (Sp R)) ⟶ G3 G := lift η[G] (lift η[G] η[G])
  refine pic_eq_zero (K := K) (G3 G).hom e.left hsm (geometricallyIntegral_of_smooth _) (Over.w e) _ ?_
  refine (pull_cubeCls_push h (fun i => y (x3 G i)) (x3 G) u (fun i => hy _) c).trans (cube_pts ?_ _)
  obtain ⟨M, hM, eM⟩ := cls_surj (CechPic.pull φ c)
  rw [← eM, ← cls_cube _ hM]
  exact (cls_eq_zero_iff _).2 (GlobalTheory.T.cube_theorem_and_sections_finite_growth_abelianVariety.1 _ P M hM)

end GlobalTheory.SS.AmpCub

namespace GlobalTheory.SS

open AmpCub GlobalTheory.CechPic GlobalTheory.EndOnTorsion

theorem exists_ampleCub_spFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (P : Out.PolAV (Sp K)) (G : Over (Sp R)) [GrpObj G], SmConn G → ∀ e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ P.A, IsMonHom e.hom → ∃ L : LB (spFibre G).left, AmpleCub (spFibre G) L := by
  intro R K _ _ _ _ _ ⟨hD, _, hk, hK⟩ P G _ ⟨hc, hs, hsep, hq, hg⟩ e he
  have hV : IsRegularRing R := ExtendRig.isRegularRing_of_isDiscreteValuationRing R
  have : GeometricallyIntegral G.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R G.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  have hp := isGrpPullback_pullback G (spMap (IsLocalRing.residue R))
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hA : IsGrpPullback P.A G (etaK R K) (e.inv.left ≫ pullback.fst G.hom (spMap (algebraMap R K))) :=
    ((isGrpPullback_of_iso e.symm).comp (isGrpPullback_pullback G (spMap (algebraMap R K)))).congr
      (Category.id_comp _) rfl
  have : IsIntegral (spFibre G).left :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom (spMap (IsLocalRing.residue R)))
  have : IsAffineHom (pullback.fst G.hom (spMap (IsLocalRing.residue R))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsSeparated (spFibre G).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : LocallyOfFiniteType (spFibre G).hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : (spFibre G).left.IsSeparated := ⟨by rw [← terminal.comp_from (spFibre G).hom]; infer_instance⟩
  obtain ⟨y⟩ : Nonempty (spFibre G).left := inferInstance
  obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := pullback.fst G.hom (spMap (IsLocalRing.residue R)) y) trivial
  obtain ⟨L, s, hL, rfl⟩ := exists_nonzeroLocus_eq_of_isAffineOpen G.left hst W hW ⟨_, hy⟩
  exact exists_ampleCub (cube_pull hp (cube_model P G hA (cls L hL)))
    ⟨_, pull_isLB hL _, secPull s _, rfl, nonzeroLocus_secPull _ _⟩ (hW.preimage _) ⟨y, hy⟩

end GlobalTheory.SS
