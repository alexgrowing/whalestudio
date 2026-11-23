import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsGtPtGenRelRField

noncomputable section

namespace GlobalTheory.ArcQBC

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Bundles

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
  {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}

theorem pmaps_unique (hL : L.IsLB) {a a' : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (H' : PMaps w φ' φ ε a' t h) : a = a' := by
  obtain ⟨s⟩ := a
  obtain ⟨s'⟩ := a'
  refine congrArg _ (funext fun q => unit_ext fun y hy => ?_)
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  exact mul_left_cancel ((H _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)).symm.trans
    (H' _ (𝟙 _) y p q hp (Set.mem_iInter.1 hy)))

theorem pmaps_of_val (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (ht : t.IsGen)
    (H : ∀ (y : Y') J J', Good L y J → Good L' y J' → val t (𝟙 _ ≫ h) y J =
      (∏ k, ConstFam.wVal w y J J' (𝟙 _ ≫ φ' k) ^ ε k) * val a (𝟙 _) y J') : PMaps w φ' φ ε a t h := by
  obtain ⟨a', ha', H'⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw) hL hL' h hψ t ht
  obtain rfl : a = a' := by
    obtain ⟨s⟩ := a
    obtain ⟨s'⟩ := a'
    refine congrArg _ (funext fun q => unit_ext fun y hy => ?_)
    obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' hL' y
    have e := mul_left_cancel ((H y J J' hJ hJ').symm.trans (ConstFam.pmaps_val hψ H' (𝟙 _) hJ hJ'))
    exact (gen_trans ha (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).trans ((congrArg _ e).trans
      (gen_trans ha' (𝟙 _) y hy (hJ'.mem _ (𝟙 _))).symm)
  exact H'

theorem exists_pullSec (F : X' ⟶ X) (s : LB.Sec L) : ∃ θ : LB.Sec (L.pull F), PullSec F s θ := by
  have le : ∀ j, (L.pull F).U j ≤ F ⁻¹ᵁ L.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  refine ⟨⟨fun j => (F.appLE _ _ (le j)).hom (s.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => ?_⟩, fun j h => rfl⟩
  refine ((gs_res _ y _ hy _).trans ((gs_appLE F _ _ (le j) (𝟙 _) y hy.1 _).trans
    (gs_compat s (𝟙 _ ≫ F) y (le j hy.1) (le j' hy.2)))).trans (Eq.symm ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 _) y j j' hy.1 hy.2)))
        ((gs_res _ y _ hy _).trans (gs_appLE F _ _ (le j') (𝟙 _) y hy.2 _)))))

theorem through_iff (s : LB.Sec L) (s' : LB.Sec L') :
    (∃ θ : LB.Sec (L.pull F), PullSec F s θ ∧ IsoMaps w s' θ) ↔
      ∀ (y : X') j k, F y ∈ L.U j → y ∈ L'.U k →
        gs (𝟙 _ ≫ F) y _ (s.f j) = (gw w (𝟙 _) y j k).val * gs (𝟙 _) y _ (s'.f k) := by
  have le : ∀ j, (L.pull F).U j ≤ F ⁻¹ᵁ L.U (j PUnit.unit) := fun j y hy => mem_pull.1 hy
  have key : ∀ θ : LB.Sec (L.pull F), PullSec F s θ → ∀ (y : X') (j : PUnit → L.ι), y ∈ (L.pull F).U j →
      gs (𝟙 _) y _ (θ.f j) = gs (𝟙 _ ≫ F) y _ (s.f (j PUnit.unit)) := fun θ hθ y j hy => by
    rw [hθ j (le j)]
    exact gs_appLE F _ _ (le j) (𝟙 _) y hy _
  constructor
  · rintro ⟨θ, hθ, hm⟩ y j k hj hk
    have hy : (𝟙 X' : X' ⟶ X') y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    refine (key θ hθ y (fun _ => j) hy.1).symm.trans ((gs_res _ y _ hy _).symm.trans
      ((congrArg (gs (𝟙 _) y _) (hm (fun _ => j) k)).trans ((gs_mul _ y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ y _ hy _) (gs_res _ y _ hy _)))))
  · intro H
    obtain ⟨θ, hθ⟩ := exists_pullSec F s
    refine ⟨θ, hθ, fun (j : PUnit → L.ι) k => fn_ext fun y hy => ?_⟩
    exact (gs_res _ y _ hy _).trans ((key θ hθ y j hy.1).trans ((H y _ k (le j hy.1) hy.2).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))))))

end Bundles

section Data

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {f : A →+* A'} {D₀ : DegPre A}
  {D₁ : DegPre A'} (p : IsPullDeg f D₀ D₁)

theorem letBC_iff (ν : GtPt D₀ (epsR A)) (ν₁ : GtPt D₁ (epsR A')) :
    LetBC p ν ν₁ ↔ ν₁.b.left ≫ prj p = spMap (dualMap f) ≫ ν.b.left ∧ ∀ χ,
      (∀ i, DegPre.gtφT D₁ (epsR A') ν₁.b χ i ≫ prj p = spMap (dualMap f) ≫ DegPre.gtφT D₀ (epsR A) ν.b (p.xe χ) i) ∧
      PMaps p.w _ _ DegPre.gtε (ν₁.s χ) (ν.s (p.xe χ)) (spMap (dualMap f)) :=
  and_congr Iff.rfl (forall_congr' fun χ =>
    ⟨fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff p.w _ _ _ (ν₁.s χ) (ν.s (p.xe χ)) _ _
      (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩,
    fun ⟨hψ, hm⟩ => ⟨hψ, (maps_iff p.w _ _ _ (ν₁.s χ) (ν.s (p.xe χ)) _ _
      (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩⟩)

omit [IsDomain A] [IsDomain A'] in
theorem dual_base (f : A →+* A') : spMap (dualMap f) ≫ (epsR A).hom = (epsR A').hom ≫ spMap f := by
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

omit [IsDomain A] [IsDomain A'] in
theorem dual_fst (f : A →+* A') : spMap (TrivSqZeroExt.fstHom A' A' A').toRingHom ≫ spMap (dualMap f) =
    spMap f ≫ spMap (TrivSqZeroExt.fstHom A A A).toRingHom := by
  refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (spMap_comp _ _))
  refine RingHom.ext fun x => ?_
  simp [dualMap]

theorem existsUnique_letBC (hG : GlobalFnsSt) (ν : GtPt D₀ (epsR A)) : ∃! ν', LetBC p ν ν' := by
  have gp := pull_grp p
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := epsR A) (T' := epsR A') (spMap (dualMap f)) (dual_base f) ν
  refine existsUnique_of_exists_of_unique ⟨g, (letBC_iff p _ _).2 ⟨(hg 0).1 2, fun χ => ⟨(hg χ).1,
    pmaps_of_val p.w_gen D₀.P.isLB D₁.P.isLB (hg χ).1 (g.isGen χ) (ν.isGen _) fun y J J' hJ hJ' =>
      (hg χ).2 _ (𝟙 _) y J J' hJ hJ'⟩⟩⟩ fun g₁ g₂ h₁ h₂ => ?_
  rw [letBC_iff] at h₁ h₂
  obtain ⟨b₁, s₁, _, _, _⟩ := g₁
  obtain ⟨b₂, s₂, _, _, _⟩ := g₂
  obtain rfl : b₁ = b₂ :=
    Over.OverMorphism.ext (gp.1.hom_ext (h₁.1.trans h₂.1.symm) ((Over.w b₁).trans (Over.w b₂).symm))
  obtain rfl : s₁ = s₂ := funext fun χ => pmaps_unique D₀.P.isLB (h₁.2 χ).2 (h₂.2 χ).2
  rfl

theorem gtTanR_of_letBC (hG : GlobalFnsSt) {ν : GtPt D₀ (epsR A)} {ν' : GtPt D₁ (epsR A')} (h : LetBC p ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  have gp := pull_grp p
  rw [letBC_iff] at h
  obtain ⟨g₀, ⟨z₁, z₂⟩, q₁, q₂⟩ := ht
  obtain ⟨g, hg⟩ := ConstPoint.exists_gtPt_through hG gp p.w_gen p.xe.toAddMonoidHom p.c_pr
    (T := Over.mk (𝟙 (Sp A))) (T' := Over.mk (𝟙 (Sp A'))) (spMap f)
    ((Category.comp_id _).trans (Category.id_comp _).symm) g₀
  let ρ : Over.mk (𝟙 (Sp A')) ⟶ epsR A' := Over.homMk (spMap (TrivSqZeroExt.fstHom A' A' A').toRingHom) (by
    refine (spMap_comp _ _).symm.trans (Eq.trans (congrArg spMap ?_) (Spec.map_id _))
    exact RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have hb : g.b.left ≫ prj p = spMap f ≫ g₀.b.left := (hg 0).1 2
  have b₀ : g.b = 1 := Over.OverMorphism.ext (gp.1.hom_ext (hb.trans (by
    rw [z₁]; exact ((hg 0).1 3).symm)) ((Over.w _).trans (Over.w _).symm))
  have b₁ : g.b = ρ ≫ ν'.b := Over.OverMorphism.ext (gp.1.hom_ext (hb.trans (by
    rw [q₁, ← Category.assoc, ← dual_fst, Category.assoc, ← h.1]
    exact (Category.assoc _ _ _).symm)) ((Over.w _).trans (Over.w _).symm))
  have v : ∀ χ (y : (Over.mk (𝟙 (Sp A'))).left) J J', Good D₀.P.L y J → Good D₁.P.L y J' → val (g₀.s (p.xe χ)) (𝟙 _ ≫ spMap f) y J =
      (ConstFam.wVal p.w y J J' (cP D₁ (Over.mk (𝟙 (Sp A'))) χ * (𝟙 _ ≫ g.b)).left)⁻¹ *
        ConstFam.wVal p.w y J J' (cP D₁ (Over.mk (𝟙 (Sp A'))) χ).left * ConstFam.wVal p.w y J J' (𝟙 _ ≫ g.b).left *
        (ConstFam.wVal p.w y J J' (1 : Over.mk (𝟙 (Sp A')) ⟶ D₁.P.A).left)⁻¹ * val (g.s χ) (𝟙 _) y J' :=
    fun χ y J J' hJ hJ' => ((hg χ).2 _ (𝟙 _) y J J' hJ hJ').trans (congrArg (· * _)
      (FormalPoint.prod_gtφT (𝟙 (Over.mk (𝟙 (Sp A')))) g.b χ (ConstFam.wVal p.w y J J')))
  refine ⟨g, ⟨b₀, fun χ => corr_of_val D₁.P.isLB fun y J' hJ' => ?_⟩, congrArg (fun q => q.left) b₁,
    fun χ => corr_of_val D₁.P.isLB fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D₀.P.isLB y
    have e := ((val_corr hJ (z₂ _) _).trans (val_one _)).symm.trans (v χ y J J' hJ hJ')
    have b₂ : 𝟙 _ ≫ g.b = 1 := (Category.id_comp _).trans b₀
    rw [b₂, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at e
    exact e.symm.trans (val_one _).symm
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D₀.P.isLB y
    have e := ((val_corr hJ (q₂ _) _).trans (val_pull hJ _ _ _)).symm.trans (v χ y J J' hJ hJ')
    have b₂ : 𝟙 _ ≫ g.b = ρ ≫ ν'.b := (Category.id_comp _).trans b₁
    have e' := (ConstFam.pmaps_val (h.2 χ).1 (h.2 χ).2 ρ.left hJ hJ').trans (congrArg (· * _)
      (FormalPoint.prod_gtφT ρ ν'.b χ (ConstFam.wVal p.w y J J')))
    rw [b₂] at e
    have m : ρ.left ≫ spMap (dualMap f) = (𝟙 _ ≫ spMap f) ≫ spMap (TrivSqZeroExt.fstHom A A A).toRingHom :=
      (dual_fst f).trans (by rw [Category.id_comp])
    have e'' := mul_left_cancel (e.symm.trans ((congrArg (fun r => val (ν.s (p.xe χ)) r y J) m).symm.trans e'))
    exact e''.trans ((congrArg (fun r => val (ν'.s χ) r y J') (Category.id_comp _).symm).trans
      (val_pull hJ' _ _ _).symm)

theorem existsUnique_thBC (th : D₀.P.L.Sec) : ∃! th', ThBC p th th' := by
  obtain ⟨s, hs⟩ := sec_pull_down ((isGen_iff p.w).1 p.w_gen) D₀.P.isLB D₁.P.isLB th
  refine existsUnique_of_exists_of_unique ⟨s, (through_iff _ _).2 fun y j k hj hk => hs _ (𝟙 _) y j k hj hk⟩
    fun s₁ s₂ h₁ h₂ => ?_
  have k₁ := (through_iff _ _).1 h₁
  have k₂ := (through_iff _ _).1 h₂
  obtain ⟨f₁, _⟩ := s₁
  obtain ⟨f₂, _⟩ := s₂
  obtain rfl : f₁ = f₂ := funext fun k => fn_ext fun y hy => by
    obtain ⟨j, hj⟩ := exists_chart D₀.P.isLB (prj p y)
    exact (Units.mul_right_inj _).1 ((k₁ y j k hj hy).symm.trans (k₂ y j k hj hy))
  rfl

theorem thNZ_of_thBC {th : D₀.P.L.Sec} {th' : D₁.P.L.Sec} (h : ThBC p th th') (hn : ThNZ th) : ThNZ th' := by
  intro y
  obtain ⟨x₀, hx₀, hm⟩ := hn (spMap f y)
  obtain ⟨x, hx₁, hx₂⟩ := Scheme.exists_preimage_of_isPullback (pull_grp p).1 x₀ y hx₀
  obtain rfl : prj p x = x₀ := hx₁
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have hj' : prj p x ∈ D₀.P.L.U j := D₀.P.A.left.basicOpen_le _ hj
  obtain ⟨k, hk⟩ := exists_chart D₁.P.isLB x
  have u₀ : IsUnit (gs (𝟙 _) (prj p x) _ (th.f j)) := by
    rw [gs_eq (𝟙 _) (prj p x) _ hj']; exact (D₀.P.A.left.mem_basicOpen _ _ hj').1 hj
  have u₁ : IsUnit (gs (prj p) x _ (th.f j)) := by rw [gs_stalkMap (prj p) x _ hj']; exact u₀.map _
  have e := (through_iff _ _).1 h x j k hj' hk
  rw [Category.id_comp] at e
  have u₂ := isUnit_of_mul_isUnit_right (e ▸ u₁)
  refine ⟨x, hx₂, TopologicalSpace.Opens.mem_iSup.2 ⟨k, (D₁.P.A.left.mem_basicOpen _ _ hk).2 ?_⟩⟩
  rwa [gs_eq _ _ _ hk] at u₂

end Data

theorem baseChanges : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A A' : Type) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing A'] [IsDomain A'] [IsPrincipalIdealRing A'] (b : O →+* A) (a : ArcIn Dw l β A b) (f : A →+* A'), Function.Injective f → ∀ b' : O →+* A', b' = f.comp b → (∃ (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀), InBC f a a' p) ∧ ∀ (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀), InBC f a a' p → (∀ (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ), ∃ W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ), WitBC f p W W') ∧ (∀ ν, ∃! ν', LetBC p ν ν') ∧ (∀ ν ν', LetBC p ν ν' → GtTanR ν → GtTanR ν') ∧ (∀ th, ∃! th', ThBC p th th') ∧ ∀ th th', ThBC p th th' → ThNZ th → ThNZ th' := by
  intro hL _ hU h5 E _ _ _ H Dw l Xo c O _ β Y A A' _ _ _ _ _ _ b a f hf b' hb'
  subst hb'
  refine ⟨?_, fun a' p h => ⟨fun χ W => ?_, existsUnique_letBC p hL.globalFns,
    fun ν ν' => gtTanR_of_letBC p hL.globalFns, existsUnique_thBC p, fun th th' => thNZ_of_thBC p⟩⟩
  · obtain ⟨a', p, h, -⟩ := ArcPull.exists_isBC hL.polBaseChange hL.globalFns a f hf
    exact ⟨a', p, rfl, h.xe_smul, h.be_eq, h.act, h.eta, h.etaA⟩
  · obtain ⟨-, h₁, h₂, h₃, h₄, h₅⟩ := h
    exact ArcPull.exists_witness_powerSeries hL.globalFns hL.polBaseChange hU h5 ⟨h₁, h₂, h₃, h₄, h₅⟩ W

end GlobalTheory.ArcQBC
