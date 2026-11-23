import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByWeightZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LePreimageOpenPartIffTestCoordinatesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FibreImm

theorem le_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] {U V : X.Opens}
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  intro z hz
  by_contra hV
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set X) ∩ (V : Set X)ᶜ) ⟨z, hz, hV⟩
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)
  have e := pointOfClosedPoint_apply π y hc (IsLocalRing.closedPoint k)
  have h1 := (CrdCalc.top_le_iff _ _).1 (h _ (pointOfClosedPoint_comp π y hc)
    ((CrdCalc.top_le_iff _ _).2 (e.symm ▸ hy)))
  exact hy' (e ▸ h1)

theorem eq_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] {U : X.Opens} {f g : Γ(X, U)}
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = GlobalTheory.ZH.valR x U g) : f = g := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  refine le_of_points π fun x hx hb => ?_
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le _))
  refine absurd ?_ ((CrdCalc.isUnit_valR_iff _ U hU _).2 hb).ne_zero
  rw [CrdCalc.valR_eq x U hU, map_sub, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, h x hx hU, sub_self]

theorem isClosedImmersion_of_surjective {V U : Scheme.{0}} [IsAffine V] [U.IsSeparated] (f : V ⟶ U)
    (hf : Function.Surjective f.appTop) : IsClosedImmersion f := by
  have : IsClosedImmersion (f ≫ U.toSpecΓ) := by
    refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2
  exact IsClosedImmersion.of_comp f U.toSpecΓ

theorem isClosedImmersion_of_crd {k : Type} [Field k] [IsAlgClosed k] {X T : Scheme.{0}} [IsReduced X]
    (pX : X ⟶ Sp k) (pT : T ⟶ Sp k) [LocallyOfFiniteType pX] [IsSeparated pT] (h : X ⟶ T) (hp : h ≫ pT = pX)
    {HX : LB X} {HT : LB T} (hX : HX.IsLB) (hT : HT.IsLB) {J : Type} (F : J → HX.Sec) (s : J → HT.Sec)
    (J₀ : Set J) (imm : ImmBy pX HX F J₀) (cov : ⨆ i : J₀, Out.nonzeroLocus (s i) = ⊤)
    (crd : ∀ (x : Sp k ⟶ X) (v : J → k), x ≫ pX = 𝟙 _ → Crd HX F x v → Crd HT s (x ≫ h) v) :
    IsClosedImmersion h := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _ cov fun i => ?_
  obtain ⟨haff, r, hr, hgen⟩ := imm.2 i i.2
  have hV : h ⁻¹ᵁ Out.nonzeroLocus (s i) = Out.nonzeroLocus (F i) := by
    refine le_antisymm (le_of_points pX fun x hx hU => ?_) (le_of_points pX fun x hx hU => ?_)
    · obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      exact (CrdCalc.crd_isUnit_iff _ hv).1 ((CrdCalc.crd_isUnit_iff _ (crd x v hx hv)).2 hU)
    · obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      exact (CrdCalc.crd_isUnit_iff _ (crd x v hx hv)).1 ((CrdCalc.crd_isUnit_iff _ hv).2 hU)
  have hsurj : Function.Surjective (h.appLE _ _ hV.ge).hom := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨constFn pT _ a, eq_of_points pX fun x hx hU => ?_⟩
      rw [GlobalTheory.Points.valR_appLE x h hV.ge hU, GlobalTheory.Points.valR_constFn_of_section pX x hx _ hU,
        GlobalTheory.Points.valR_constFn_of_section pT (x ≫ h) (by rw [Category.assoc, hp, hx])
          (Out.nonzeroLocus (s i)) (hU.trans (x.preimage_mono hV.ge))]
    · obtain ⟨r', hr', -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hT (s j) (s i) _ le_rfl
      refine ⟨r', eq_of_points pX fun x hx hU => ?_⟩
      obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      have h1 := CrdCalc.crd_ratio hv (hr j) hU
      have h2 := CrdCalc.crd_ratio (crd x v hx hv) hr' (hU.trans (x.preimage_mono hV.ge))
      rw [GlobalTheory.Points.valR_appLE x h hV.ge hU]
      exact ((CrdCalc.crd_isUnit_iff _ hv).2 hU).mul_right_cancel (h2.symm.trans h1)
  have hsurj' : Function.Surjective (h.app (Out.nonzeroLocus (s i))).hom := by
    revert hsurj
    generalize Out.nonzeroLocus (F i) = V at hV
    subst hV
    rw [Scheme.Hom.appLE_eq_app]
    exact id
  have : IsAffine (h ⁻¹ᵁ Out.nonzeroLocus (s i)).toScheme := by rw [hV]; exact haff
  have : T.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from pT]; infer_instance
  have : (Out.nonzeroLocus (s i)).toScheme.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (Out.nonzeroLocus (s i)).ι]; infer_instance
  refine isClosedImmersion_of_surjective _ ?_
  rw [morphismRestrict_appTop]
  have h₁ : Function.Surjective (h.app ((Out.nonzeroLocus (s i)).ι ''ᵁ ⊤)).hom := by
    rw [Scheme.Opens.ι_image_top]
    exact hsurj'
  exact (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom _).op)).2.comp h₁

abbrev pullLB {X Y : Scheme.{0}} (f : Y ⟶ X) (L : LB X) : LB Y :=
  ⟨L.ι, fun l => f ⁻¹ᵁ L.U l, fun l l' => pullU f (L.U l ⊓ L.U l') (L.g l l')⟩

def pullSection {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} (s : L.Sec) : (pullLB f L).Sec where
  f l := (f.app (L.U l)).hom (s.f l)
  compat i j := by
    have e := congrArg (f.app (L.U i ⊓ L.U j)).hom (s.compat i j)
    rw [map_mul] at e
    have e₁ := congrArg (fun φ => φ.hom (s.f i)) (f.naturality (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op)
    have e₂ := congrArg (fun φ => φ.hom (s.f j)) (f.naturality (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op)
    exact e₁.symm.trans (e.trans (congrArg (_ * ·) e₂))

theorem crd_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} {J : Type} (s : J → L.Sec) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y) (v : J → R) : Crd (pullLB f L) (fun j => pullSection f (s j)) x v ↔ Crd L s (x ≫ f) v := by
  refine exists_congr fun l => exists_congr fun c => and_congr Iff.rfl (forall_congr' fun j => ?_)
  rw [GlobalTheory.Points.valR_comp x f]
  rfl

theorem crd_lin {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X} {I J : Type} [Fintype J]
    {s : J → H.Sec} {s' : I → H.Sec} {n : Matrix I J k} (hn : ∀ i, IsLin p s (n i) (s' i)) {x : Sp k ⟶ X}
    (hx : x ≫ p = 𝟙 _) {v : J → k} (hv : Crd H s x v) : Crd H s' x (n.mulVec v) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  refine ⟨l, c, hl, fun i => ?_⟩
  rw [hn i l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, GlobalTheory.Points.valR_constFn_of_section p x hx _ hl, hv,
    mul_left_comm]

theorem isClosedImmersion_special_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (f' : t.u.G.left ⟶ Q.G.toScheme), f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι → ∀ h : pullback t.u.G.hom (rPt p ≫ spMap t.u.j) ⟶ pullback (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y), h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f' → h ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion h := by
  intro L o Ω _ _ _ _ S ρ M U₀ EE hbf Q p _ y y₀ t c tm hBig f' hf' h h1 h2
  have : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(utest_dim_and_split L o Ω S ρ p y₀ t.u).2.2.2.1, hBig.1, hBig.2.1⟩
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hs : Smooth t.u.G.hom := t.mod.smooth.smooth
  have : Smooth t.mod.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  have : IsReduced t.mod.Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced t.mod.Φ.G.hom
  have := Q.proper
  suffices IsClosedImmersion (pb.isoPullback.hom ≫ h) from
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).1 this
  have hrange : Set.range (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι) ⊆
      Set.range (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι ≫ Q.P.hom) z =
        (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ rPt p ≫ y) z := by rw [pullback.condition]
    have e₂ : rPt p (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) z) = cPt p := by
      rw [Subsingleton.elim (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) z) (IsLocalRing.closedPoint (kb p))]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    change (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι ≫ Q.P.hom) z ∈ Q.W tm.l
    rw [e]
    exact (congrArg (fun w => y w ∈ Q.W tm.l) e₂).mpr tm.mem
  let e := IsOpenImmersion.lift (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι _ hrange
  have he : e ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ Q.G.ι := IsOpenImmersion.lift_fac _ _ _
  let ψ : t.u.V →+* kb p := (IsLocalRing.residue (OO p)).comp t.u.j
  have hψ : rPt p ≫ spMap t.u.j = spMap ψ := (Spec.map_comp _ _).symm
  have hm : IsUnit (tm.m.map ψ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact tm.unit.map ψ
  have hH : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := DVR.linComb_isLB _ Q.isLB _ _
  have hT := pullChart_isLB e hH
  choose s hs using fun i => (GlobalTheory.SecRatio.existsUnique_isLin (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y))
    (fun j => pullSection e (Q.σ tm.l j)) ((tm.m.map ψ)⁻¹ i)).exists
  have hsnd : (pb.isoPullback.hom ≫ h) ≫ pullback.snd _ _ = t.mod.Φ.G.hom := by
    rw [Category.assoc, h2, IsPullback.isoPullback_hom_snd]
  have hhe : (pb.isoPullback.hom ≫ h) ≫ e = t.mod.r ≫ tm.f := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι, Category.assoc, he, Category.assoc, Category.assoc,
      reassoc_of% h1, hf', IsPullback.isoPullback_hom_fst_assoc]
  refine isClosedImmersion_of_crd t.mod.Φ.G.hom (pullback.snd _ _) _ hsnd (t.mod.Φ.H_isLB 1) hT t.mod.F s _
    (GlobalTheory.T.immBy_weight_zero' L.1 L.2.1 (kb p) t.mod.Φ S.g S.N _ _ S.J _ t.mod.F t.mod.pol hB t.mod.good t.mod.dim) ?_ ?_
  · refine top_le_iff.1 (le_of_points (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y)) fun x hx _ => ?_)
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists hH (Q.σ tm.l) (x ≫ e)
    have hw := crd_lin hs hx ((crd_pull e _ x v).2 hv)
    have hv' : v = (tm.m.map ψ).mulVec ((tm.m.map ψ)⁻¹.mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm, Matrix.one_mulVec]
    rw [hv'] at hv
    obtain ⟨i, hi, hne⟩ := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hbf Q p y y₀ t c tm hBig (x ≫ e) _ (by
      rw [Category.assoc, reassoc_of% he, pullback.condition, reassoc_of% hx]) hv).1 (by
      rw [Category.assoc, he, ← Category.assoc, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
      exact le_rfl)
    exact ((CrdCalc.crd_isUnit_iff i hw).1 hne.isUnit).trans (x.preimage_mono
      (le_iSup (fun i : {i | t.mod.xe.symm (t.cls i) = 0} => Out.nonzeroLocus (s i))
        ⟨i, t.mod.xe.symm.map_eq_zero_iff.2 hi⟩))
  · intro x v hx hv
    have h₁ := t.mod.red (Over.homMk x hx) v hv
    have h₂ := tm.crd (kb p) ψ (x ≫ t.mod.r) v (by rw [Category.assoc, pb.w, reassoc_of% hx, hψ]) h₁
    rw [Category.assoc, ← hhe, ← Category.assoc] at h₂
    have h₃ := crd_lin hs (by rw [Category.assoc, hsnd, hx]) ((crd_pull e _ _ _).2 h₂)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec] at h₃

end GlobalTheory.ZH.FibreImm
end
