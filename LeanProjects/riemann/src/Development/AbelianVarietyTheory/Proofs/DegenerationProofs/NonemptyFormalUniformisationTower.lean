import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyBiTrivOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BiTrivLiftOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapCompCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDescendThrough
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenPull

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.FormalTower

theorem exists_tq_lift {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] (φ : A →+* A')
    (hφ : Function.Surjective φ) (hn : IsNilpotent (RingHom.ker φ)) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Sp A')) [GrpObj G₀]
    (F : G₀.left ⟶ G.left) (hF : IsGrpPullback G₀ G (spMap φ) F) (Q₀ : TQ G₀ X) :
    ∃ Q : TQ G X, TorusCompat (spMap φ) F Q₀.i Q.i := by
  let e := RingHom.quotientKerEquivOfSurjective hφ
  let r : Sp (A ⧸ RingHom.ker φ) ⟶ Sp A' := spMap e.symm.toRingHom
  let s : Sp A' ⟶ Sp (A ⧸ RingHom.ker φ) := spMap e.toRingHom
  have hr : r ≫ spMap φ = red (RingHom.ker φ) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact e.symm_apply_eq.2 rfl
  have hs : s ≫ r = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact e.apply_symm_apply a
  have h₁ := isGrpPullback_pullback G₀ r
  obtain ⟨Q₁, c₁⟩ := exists_tq_baseChange _ _ _ X _ _ _ h₁ Q₀
  obtain ⟨Q, c⟩ := TorusQuotLift.main A _ hn X G _ _ ((h₁.comp hF).congr hr rfl) Q₁
  refine ⟨Q, ?_⟩
  rw [torusCompat_iff] at c c₁ ⊢
  rw [← hr, bcMap_comp, ← Category.assoc, ← c₁, Category.assoc, Category.assoc] at c
  have c' := congrArg (SplitTorus.bcMap s X ≫ ·) c
  simp only [← Category.assoc, ← bcMap_comp, hs, bcMap_id, Category.id_comp] at c'
  exact c'

theorem isCPPullback_of_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G]
    [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] {P : CP G} {P' : CP G'}
    {P'' : CP G''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {f'' : S'' ⟶ S} {F : G'.left ⟶ G.left} {F' : G''.left ⟶ G'.left}
    {F'' : G''.left ⟶ G.left} (h : IsCPPullback P' P f F) (h'' : IsCPPullback P'' P f'' F'')
    (hF : IsGrpPullback G'' G' f' F') (e : f' ≫ f = f'') (e' : F' ≫ F = F'') : IsCPPullback P'' P' f' F' := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨_, _, h''⟩ := h''
  exact ⟨hF, TowerEx.exists_cancel h h'' hF e e'⟩

theorem exists_isCPPullback_desc {S S' : Scheme.{0}} [ConnectedSpace S'] {f : S' ⟶ S} {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    [ConnectedSpace G'.left] {F : G'.left ⟶ G.left} {P : CP G} {P' : CP G'} (hP : IsCPPullback P' P f F)
    {Q : TQ G X} {Q' : TQ G' X} (h : TorusCompat f F Q'.i Q.i) (D : Q.Desc P) (D' : Q'.Desc P') :
    ∃ β : Q'.B.left ⟶ Q.B.left, IsCPPullback D'.M D.M f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left := by
  obtain ⟨hF, _, hP⟩ := hP
  exact TowerEx.exists_transition hF hP h D D'

section Level

variable {R : Type} [CommRing R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]

theorem isGrpPullback_thickMap (e : ℕ) :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem isNilpotent_of_le_map (n : ℕ) (J : Ideal (R ⧸ I ^ n)) (hJ : J ≤ I.map (Ideal.Quotient.mk (I ^ n))) :
    IsNilpotent J := by
  refine ⟨n, le_bot_iff.1 ((Ideal.pow_right_mono hJ n).trans ?_)⟩
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

variable {I}

theorem pow_succ_ne_top (hI : I ≠ ⊤) (e : ℕ) : I ^ (e + 1) ≠ ⊤ := fun h =>
  hI (top_le_iff.1 (h.symm.le.trans (Ideal.pow_le_self (Nat.succ_ne_zero e))))

theorem isLocalRing_quot [IsLocalRing R] (hI : I ≠ ⊤) (e : ℕ) : IsLocalRing (R ⧸ I ^ (e + 1)) :=
  have := Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top hI e)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

theorem connectedSpace_sp (A : Type) [CommRing A] [IsLocalRing A] : ConnectedSpace (Sp A) :=
  SplitTorus.connectedSpace_of_isLocalRing A

theorem exists_tq_succ [IsLocalRing R] [IsCommMonObj G] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (e : ℕ) (Q₀ : TQ (thickObj R I e G) X) :
    ∃ Q : TQ (thickObj R I (e + 1) G) X, TorusCompat (thickTrans R I e) (thickMap R I e G) Q₀.i Q.i := by
  have := isLocalRing_quot hI (e + 1)
  have := (IsSemiAbelian.pullback (thick R I (e + 1)) G hG).smooth
  refine exists_tq_lift _ (Ideal.Quotient.factor_surjective _) (isNilpotent_of_le_map I _ _ fun x hx => ?_) _ _ _
    (isGrpPullback_thickMap I G e) Q₀
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.mem_map_of_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero e) (Ideal.Quotient.eq_zero_iff_mem.1 hx))

theorem nonempty_biTriv (h₁ : Laws) (h₂ : Laws2) [IsLocalRing R] [IsNoetherianRing R] [IsCommMonObj G] [I.IsPrime]
    [IsIntegrallyClosed (R ⧸ I)] (hG : IsSemiAbelian G) {X : Type} [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (e : ℕ) (Q : TQ (thickObj R I e G) X) (P : CP (thickObj R I e G)) :
    Nonempty (BiTriv P.c Q.i) := by
  let J := I.map (Ideal.Quotient.mk (I ^ (e + 1)))
  let ε : ((R ⧸ I ^ (e + 1)) ⧸ J) ≃+* R ⧸ I :=
    DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self (Nat.succ_ne_zero e))
  have : IsDomain ((R ⧸ I ^ (e + 1)) ⧸ J) := ε.toMulEquiv.isDomain _
  have : IsIntegrallyClosed ((R ⧸ I ^ (e + 1)) ⧸ J) := IsIntegrallyClosed.of_equiv ε.symm
  have h₀ := IsSemiAbelian.pullback (red J) _ (IsSemiAbelian.pullback (thick R I e) G hG)
  have := h₀.smooth
  have := h₀.geomConnected
  have := h₀.comm
  have : ConnectedSpace (Sp ((R ⧸ I ^ (e + 1)) ⧸ J)) := inferInstance
  have := (GroupConn.connectedSpace_group _ ((Over.pullback (red J)).obj (thickObj R I e G))).1
  have hp := isGrpPullback_pullback (thickObj R I e G) (red J)
  obtain ⟨Q₀, c⟩ := exists_tq_baseChange _ _ _ X _ _ _ hp Q
  obtain ⟨P₀, w, hw⟩ := exists_pull P (TowerEx.toBase_mul hp hp.1.w)
  exact biTriv_lift_of_isNilpotent _ J (isNilpotent_of_le_map I _ _ le_rfl) X _ _ _ _ hp P P₀ w hw _ _ Q.i_hom Q₀.i_hom c
    (BiextTriv.nonempty_biTriv_normal h₁ h₂ _ X _ _ _ _ Q₀.i_hom)

theorem exists_even (h₁ : Laws) (h₂ : Laws2) [IsDomain R] [IsCommMonObj G]
    (P : CP G) (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) (hW : HypW G P.L.L)
    {X : Type} [AddCommGroup X] (e : ℕ) (Q : TQ (thickObj R I e G) X) (P' : CP (thickObj R I e G))
    (h : IsLevelCP I e P' P) (b : Nonempty (BiTriv P'.c Q.i)) : ∃ σ : CubTriv P'.c Q.i, σ.Even := by
  obtain ⟨w, -, hw, -, -, hL, -⟩ := hW
  obtain ⟨v, hv⟩ := h
  exact EvenTriv.exists_even_cubTriv h₁ h₂ R G hG hp P w hw hL _ _ X Q P' _ _
    (isGrpPullback_pullback G (thick R I e)).1 v hv b

theorem connectedSpace_thickObj [IsLocalRing R] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (e : ℕ) :
    ConnectedSpace (thickObj R I e G).left := by
  have := isLocalRing_quot hI e
  have := connectedSpace_sp (R ⧸ I ^ (e + 1))
  have h₀ := IsSemiAbelian.pullback (thick R I e) G hG
  have := h₀.smooth
  have := h₀.geomConnected
  exact (GroupConn.connectedSpace_group _ (thickObj R I e G)).1

omit [GrpObj G] in

theorem thickMap_fst (e : ℕ) :
    thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem isCPPullback_thick [IsDomain R] [IsCommMonObj G] {P : CP G} {e : ℕ} {P' : CP (thickObj R I e G)}
    (h : IsLevelCP I e P' P) : IsCPPullback P' P (thick R I e) (pullback.fst G.hom (thick R I e)) :=
  ⟨isGrpPullback_pullback G _, h⟩

theorem isCPPullback_thickMap [IsDomain R] [IsCommMonObj G] {P : CP G} {e : ℕ} {P' : CP (thickObj R I e G)}
    {P'' : CP (thickObj R I (e + 1) G)} (h' : IsLevelCP I e P' P) (h'' : IsLevelCP I (e + 1) P'' P) :
    IsCPPullback P' P'' (thickTrans R I e) (thickMap R I e G) :=
  isCPPullback_of_comp (isCPPullback_thick G h'') (isCPPullback_thick G h') (isGrpPullback_thickMap I G e)
    (thickTrans_comp R I e) (thickMap_fst G e)

theorem exists_isCPPullback [IsDomain R] [IsLocalRing R] [IsCommMonObj G] (hI : I ≠ ⊤) (hG : IsSemiAbelian G) {P : CP G}
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] {e : ℕ} (l : Lev I P X e) (l' : Lev I P X (e + 1))
    (c : TorusCompat (thickTrans R I e) (thickMap R I e G) l.Q.i l'.Q.i) :
    ∃ β : l.Q.B.left ⟶ l'.Q.B.left, IsCPPullback l.D.M l'.D.M (thickTrans R I e) β ∧
      l.Q.q.left ≫ β = thickMap R I e G ≫ l'.Q.q.left :=
  have := isLocalRing_quot hI e
  have := connectedSpace_sp (R ⧸ I ^ (e + 1))
  have := connectedSpace_thickObj G hI hG e
  exists_isCPPullback_desc (isCPPullback_thickMap G l.lev l'.lev) c l'.D l.D

end Level

theorem nonempty_towerR : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → IsProper (pullback.snd G.hom (jK R)) → SplitOver G I → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), Nonempty (TowerR I P X) := by
  intro h₁ h₂ R _ _ _ I ⟨⟨hN, _⟩, _, _, hI, hC⟩ G _ _ P hG hW hp ⟨E, ⟨d⟩⟩
  have hI' := hI.ne_top
  have := E.free
  have := E.finite
  refine ⟨E.X, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨Q₁, -⟩ := exists_tq_of_gtDatum _ E _ d
  let r : Sp (R ⧸ I ^ (0 + 1)) ⟶ Sp (R ⧸ I) := spMap (Ideal.Quotient.factor (show I ≤ I ^ (0 + 1) by simp))
  have hr : r ≫ spMap (Ideal.Quotient.mk I) = thick R I 0 := by
    rw [← Spec.map_comp]
    rfl
  let F : (thickObj R I 0 G).left ⟶ ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by rw [Category.assoc, hr]; exact pullback.condition)
  obtain ⟨Q₀, -⟩ := exists_tq_baseChange _ _ r E.X _ _ F ((isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (thick R I 0)).congr hr.symm (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)) Q₁
  choose nx hnx using fun e => exists_tq_succ (I := I) (X := E.X) G hI' hG e
  let Q : ∀ e, TQ (thickObj R I e G) E.X := fun e => Nat.rec Q₀ nx e
  have hQ : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (Q e).i (Q (e + 1)).i := fun e => hnx e (Q e)
  choose Pe hPe using fun e => exists_isLevelCP I e P
  have hD : ∀ e, Nonempty ((Q e).Desc (Pe e)) := fun e => by
    have := isLocalRing_quot hI' e
    have := connectedSpace_sp (R ⧸ I ^ (e + 1))
    have := connectedSpace_thickObj G hI' hG e
    have b := nonempty_biTriv G h₁ h₂ hG e (Q e) (Pe e)
    exact nonempty_desc _ E.X _ (Q e) (Pe e) b
      (exists_even G h₁ h₂ P hG hp hW e (Q e) (Pe e) (hPe e) b)
  let l : ∀ e, Lev I P E.X e := fun e => ⟨Q e, Pe e, hPe e, (hD e).some⟩
  choose β hβ hq using fun e => exists_isCPPullback G hI' hG (l e) (l (e + 1)) (hQ e)
  exact ⟨⟨l, hQ, β, hβ, hq⟩⟩

end GlobalTheory.FormalTower

end
