import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CommGroupCommonFactorQuotientCancel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqTopOfClosedFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WtTower

theorem gm_linCombIso {X Y Z : Scheme.{0}} {L M : LB X} (w : LB.Iso L M) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (p : (LB.LinComb M φ ε).ι × (LB.LinComb L φ ε).ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ (LB.div (LB.LinComb M φ ε) (LB.LinComb L φ ε)).U p) :
    gm r z _ ((LB.linCombIso w φ ε).s p) =
      ∏ a, gm (r ≫ φ a) z ((LB.div M L).U (p.1 a, p.2 a)) (w.s (p.1 a, p.2 a)) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ M.U (p.1 a) ⊓ L.U (p.2 a) :=
    ⟨LB.wchart_le M φ p.1 a hz.1, LB.wchart_le L φ p.2 a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z ((LB.div M L).U (p.1 a, p.2 a)) hm _)

theorem exists_gen_of_iso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen)
    (t : LB.Gen A) (ht : t.IsGen) : ∃ t' : LB.Gen B, t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : B.ι) (i : A.ι),
      r z ∈ B.U j → r z ∈ A.U i →
      gm r z (B.U j) (t'.s j) = gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := by
  have tr : ∀ (y : Y) (j j' : B.ι) (i i' : A.ι), y ∈ B.U j → y ∈ B.U j' → y ∈ A.U i → y ∈ A.U i' →
      gm (𝟙 Y) y (B.U j ⊓ A.U i) (w.s (j, i)) * gm (𝟙 Y) y (A.U i) (t.s i) =
        gm (𝟙 Y) y _ (B.g j j') * (gm (𝟙 Y) y (B.U j' ⊓ A.U i') (w.s (j', i')) * gm (𝟙 Y) y (A.U i') (t.s i')) := by
    intro y j j' i i' hj hj' hi hi'
    have hm : (𝟙 Y : Y ⟶ Y) y ∈ B.U j ⊓ A.U i ⊓ (B.U j' ⊓ A.U i') := ⟨⟨hj, hi⟩, hj', hi'⟩
    have hn : (𝟙 Y : Y ⟶ Y) y ∈ A.U i ⊓ A.U i' := ⟨hi, hi'⟩
    have e := (gm_res _ y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hw (j, i) (j', i'))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 Y) y (j, i) (j', i') hm) (gm_res _ y _ hm _))))
    have e' := (gm_res _ y _ hn _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ht i i')).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res _ y _ hn _))))
    refine (congrArg₂ (· * ·) e e').trans ?_
    rw [_root_.mul_mul_mul_comm, inv_mul_cancel_right]
    rfl
  have glue : ∀ j : B.ι, ∃ s : Γ(Y, B.U j)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : A.ι),
      r z ∈ B.U j → r z ∈ A.U i →
      gm r z (B.U j) s = gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := by
    intro j
    have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : A.ι), r z ∈ B.U j ⊓ A.U i →
        gm r z (B.U j ⊓ A.U i) (@id (Γ(Y, B.U j ⊓ A.U i)ˣ) (w.s (j, i)) * res inf_le_right (t.s i)) =
          gm r z (B.U j ⊓ A.U i) (w.s (j, i)) * gm r z (A.U i) (t.s i) := fun Z r z i h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res r z _ h _))
    obtain ⟨s, hs⟩ := glue_unit (B.U j) (fun i => B.U j ⊓ A.U i) (fun _ => inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hA x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hx, hi⟩)
      (fun i => @id (Γ(Y, B.U j ⊓ A.U i)ˣ) (w.s (j, i)) * res inf_le_right (t.s i)) (fun i i' x hx => by
        rw [v _ _ x i hx.1, v _ _ x i' hx.2, tr x j j i i' hx.1.1 hx.1.1 hx.1.2 hx.2.2, gm_self hB _ x hx.1.1,
          _root_.one_mul])
    refine ⟨s, fun Z r z i hj hi => ?_⟩
    have hm : r z ∈ B.U j ⊓ A.U i := ⟨hj, hi⟩
    exact (gm_res r z inf_le_left hm s).symm.trans ((congrArg (gm r z _) (hs i)).trans (v Z r z i hm))
  choose s hs using glue
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z j i => hs j Z r z i⟩
  obtain ⟨i, hi⟩ := exists_chart hA y
  rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
  exact (hs j _ _ y i hy.1 hi).trans ((tr y j j' i i hy.1 hy.2 hi hi).trans (congrArg _ (hs j' _ _ y i hy.2 hi).symm))

theorem triv_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) (t : Triv A) :
    Triv B := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, ht⟩ := t
  obtain ⟨t', ht', -⟩ := exists_gen_of_iso hA hB w hw t ht
  exact ⟨t', ht'⟩

variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_genWt_of_lbIso {G : Over S} [GrpObj G] (Q : TQ G X) {N N' : LB Q.B.left} (hN : N.IsLB) (hN' : N'.IsLB)
    (h : LBIso N N') {u : LB.Gen (N.pull Q.q.left)} {χ : X} (hu : Q.GenWt N u χ) :
    ∃ u' : LB.Gen (N'.pull Q.q.left), Q.GenWt N' u' χ := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨u', hu', hv⟩ := exists_gen_of_iso (pull_isLB hN _) (pull_isLB hN' _)
    (LB.linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1)) (DVR.linCombIso_isGen w hw _ _) u hu.1
  refine ⟨u', hu', fun J => isWt_of_gm _ _ fun Z t g z hz => ?_⟩
  have e : ((t ≫ Q.i) * g).left ≫ Q.q.left = g.left ≫ Q.q.left := congrArg (·.left) (WtBundle.act_comp Q t g)
  have m : ∀ (M : LB Q.B.left) (I : PUnit → M.ι), g.left z ∈ (M.pull Q.q.left).U I →
      ((t ≫ Q.i) * g).left z ∈ (M.pull Q.q.left).U I := fun M I h =>
    (mem_pull (F := Q.q.left)).2 ((congrArg (fun a : Z.left ⟶ Q.B.left => a z ∈ M.U (I PUnit.unit)) e).mpr
      ((mem_pull (F := Q.q.left)).1 h))
  obtain ⟨I, hI⟩ := exists_chart (pull_isLB hN Q.q.left) (g.left z)
  have a₁ := gm_linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) (J, I) g.left z ⟨hz, hI⟩
  have a₂ := gm_linCombIso w (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) (J, I) ((t ≫ Q.i) * g).left z
    ⟨m _ _ hz, m _ _ hI⟩
  rw [e, ← a₁] at a₂
  rw [hv _ _ z J I (m _ _ hz) (m _ _ hI), hv _ _ z J I hz hI, WtBundle.gm_of_isWt (hu.2 I) t g z (m _ _ hI) hI,
    gm_charUnit, mul_left_comm]
  exact congrArg (fun x => _ * (x * _)) a₂

theorem exists_genWt_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (Q : TQ G X) (Q' : TQ G' X) {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) (hi : TorusCompat f F Q'.i Q.i) {β : Q'.B.left ⟶ Q.B.left}
    (hβ : Q'.q.left ≫ β = F ≫ Q.q.left) {N : LB Q.B.left} {u : LB.Gen (N.pull Q.q.left)} {χ : X}
    (hu : Q.GenWt N u χ) : ∃ u' : LB.Gen ((N.pull β).pull Q'.q.left), Q'.GenWt (N.pull β) u' χ :=
  let c := chartPullLinComb N β (K := PUnit) (fun _ => Q'.q.left) (fun _ => Q.q.left) (fun _ => 1) F fun _ => hβ
  ⟨GtBaseChange.genPull c u, GtBaseChange.genPull_isGen c hu.1, fun J => (hu.2 (c.idx J)).pull hF hi (c.le J)⟩

theorem exists_gen_comp {G : Over S} [GrpObj G] (Q : TQ G X) {Y : Scheme.{0}} (b : Q.B.left ⟶ Y) {O : LB Y}
    {u : LB.Gen ((O.pull b).pull Q.q.left)} {χ : X} (hu : Q.GenWt (O.pull b) u χ) :
    ∃ u' : LB.Gen (O.pull (Q.q.left ≫ b)), u'.IsGen ∧ ∀ j, IsWt Q.i _ (u'.s j).val χ :=
  let c := chartPullIn O (K := PUnit) (fun _ => b) (fun _ => 1) Q.q.left
  ⟨GtBaseChange.genPull c u, GtBaseChange.genPull_isGen c hu.1, fun J => (hu.2 (c.idx J)).res (c.le J)⟩

theorem psum_eq_lift {B T : Over S} [GrpObj B] [IsCommMonObj B] (x : Fin 2 → (T ⟶ B)) (I : Finset (Fin 2)) :
    (psum B x I).left = (lift (x 0) (x 1)).left ≫ (psum B (x2 B) I).left := by
  have e : (fun i => preHom (lift (x 0) (x 1)) (x2 B i)) = x := funext fun i => by
    fin_cases i
    exacts [lift_fst (x 0) (x 1), lift_snd (x 0) (x 1)]
  have := psum_hom (preHom (lift (x 0) (x 1))) (x2 B) I
  rw [e] at this
  exact congrArg (·.left) this.symm

theorem triv_lam_pull {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {f : S' ⟶ S} {b : B'.left ⟶ B.left} (hb : IsGrpPullback B' B f b) {O : LB B.left} {N : LB B'.left} (hO : O.IsLB)
    (hN : N.IsLB) (h : LBIso N (O.pull b)) (ht : Triv (abelian₂ B' N)) {T : Over S'} (U : Over.mk (T.hom ≫ f) ⟶ B ⊗ B) :
    Triv ((abelian₂ B O).pull U.left) := by
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → (T ⟶ B'), ∀ i, pushPt hb.1.w (x i) = U ≫ x2 B i :=
    ⟨fun i => Over.homMk (hb.1.lift (U ≫ x2 B i).left T.hom (Over.w (U ≫ x2 B i))) (hb.1.lift_snd _ _ _),
      fun i => Over.OverMorphism.ext (hb.1.lift_fst _ _ _)⟩
  obtain ⟨w, hw⟩ := h
  obtain ⟨t, ht⟩ := ht
  have t₁ : Triv (cubeLB B' x N) :=
    gen_chartPull (chartPullSame N (fun I : ULift (Finset (Fin 2)) => (psum B' x I.down).left)
      (fun I => (psum B' (x2 B') I.down).left) (fun I => (-1) ^ (2 - I.down.card)) (lift (x 0) (x 1)).left
      fun I => psum_eq_lift x I.down) t ht
  have l₁ : (cubeLB B' x N).IsLB := LB.isLB_linComb hN _ _
  have l₂ : (cubeLB B' x (O.pull b)).IsLB := LB.isLB_linComb (pull_isLB hO b) _ _
  have l₃ : (abelian₂ B O).IsLB := LB.isLB_linComb hO _ _
  have t₂ : Triv (cubeLB B' x (O.pull b)) := triv_of_lbIso l₁ l₂ ⟨_, DVR.linCombIso_isGen w hw _ _⟩ t₁
  have c : ChartPull (cubeLB B' x (O.pull b)) (abelian₂ B O) U.left :=
    chartPullLinComb O b (fun I : ULift (Finset (Fin 2)) => (psum B' x I.down).left)
      (fun I => (psum B (x2 B) I.down).left) (fun I => (-1) ^ (2 - I.down.card)) U.left
      fun I => psum_push hb x (x2 B) U hx I.down
  exact triv_of_lbIso l₂ (pull_isLB l₃ _)
    (LBIso.chartPull c (chartPullPull (abelian₂ B O) U.left U.left rfl) (GtBaseChange.lbIso_refl l₃)) t₂

theorem isGrpPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (e : ℕ) : IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

theorem isLocalRing_quotient_pow (V : Type) [CommRing V] [IsLocalRing V] (e : ℕ) :
    IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) :=
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal V).ne_top (Ideal.pow_le_self (Nat.succ_ne_zero e)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isProjBy_of_relAmple {R : Type} [CommRing R] (B : Over (Spec (CommRingCat.of R))) {L : LB B.left}
    (hL : L.IsLB) (h : RelAmple B L) : IsProjBy B.hom := by
  obtain ⟨d, -, n, σ, hσ⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 h
  exact ⟨_, isLB_pw hL _, n, σ, hσ⟩

theorem triv_lam_of_levels (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {O : LB B.left} (hO : O.IsLB)
    (h : ∀ e, Triv ((abelian₂ B O).pull (fstG (IsLocalRing.maximalIdeal V) e (B ⊗ B)).left)) : Triv (abelian₂ B O) :=
  AbTriv.triv_of_forall_thick hG V (B ⊗ B) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hB hB)
    (isProjBy_tensor V _ _ hp hp) _ (LB.isLB_linComb hO _ _) h

end GlobalTheory.WtTower
