import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.ArcFramePointTruncation
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Formalism.LocalToGlobal.ProjectiveLattices.ArcTheta
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LieIdentityArcWitnessIffStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ArcWitnessThetaPullbackStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsPullQkIffFractionMapStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ArcWitnessTangentPointStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ArcWitnessTangentFamilyStatement

noncomputable section

namespace GlobalTheory.ArcCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
open GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints hiding Wit WitBC
open GlobalTheory.ConstTan GlobalTheory.FormalPoint ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj MonObj

section Gt

variable {A : Type} [CommRing A] [IsDomain A] {D₀ : Out.DegPre A}

theorem tan_iff (ν : Out.GtPt D₀ (epsR A)) : GtTanR ν ↔ IsTanGt ν := by
  have sec : spMap (TrivSqZeroExt.fstHom A A A).toRingHom ≫ (epsR A).hom = 𝟙 (Sp A) :=
    (ConstLie.spMap_comp' _ _).trans (Spec.map_id _)
  let p₀ : Over.mk (𝟙 (Sp A)) ⟶ epsR A := Over.homMk _ sec
  obtain ⟨g₀, h₀⟩ := ConstLie.exists_isPullGt p₀ ν
  have e₁ : GtTanR ν ↔ ConstLie.ZeroAlong ν p₀ :=
    ⟨fun ⟨_, hz, hp⟩ => (ConstLie.isZero_iff_zeroAlong (ρ := p₀) hp).1 hz,
      fun hz => ⟨g₀, (ConstLie.isZero_iff_zeroAlong h₀).2 hz, h₀⟩⟩
  have o : (1 : Over.mk (𝟙 (Sp A)) ⟶ D₀.P.A).left = η[D₀.P.A].left := Category.id_comp _
  refine e₁.trans (and_congr ⟨fun h => (congrArg (fun q : Over.mk (𝟙 (Sp A)) ⟶ D₀.P.A => q.left) h).trans o,
    fun h => Over.OverMorphism.ext (h.trans o.symm)⟩ (forall_congr' fun x => ⟨fun H => ?_, fun H Z r z J hJ => ?_⟩))
  · exact corr_of_val D₀.P.isLB fun y J hJ => (val_pull hJ _ _ _).trans ((H _ _ y J hJ).trans (val_one _).symm)
  · exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ H r).trans (val_one _))

theorem comb_iff {m : ℕ} (cf : Fin m → A) (e : Fin m → Out.GtPt D₀ (epsR A)) (ν : Out.GtPt D₀ (epsR A)) :
    GtComb cf e ν ↔ IsCombGt e cf ν := Iff.rfl

theorem thMul_iff (r : A) (th th' : D₀.P.L.Sec) : ThMul r th th' ↔ IsMulSec r th th' := Iff.rfl

theorem thNZ_iff (th : D₀.P.L.Sec) : ThNZ th ↔ FibrewiseNe th := Iff.rfl

variable {A' : Type} [CommRing A'] [IsDomain A'] {D₁ : Out.DegPre A'} {f : A →+* A'}

theorem letBC_iff (p : Out.IsPullDeg f D₀ D₁) (ν : Out.GtPt D₀ (epsR A)) (ν₁ : Out.GtPt D₁ (epsR A')) :
    LetBC p ν ν₁ ↔ LetterBC p ν ν₁ :=
  and_congr Iff.rfl (forall_congr' fun x =>
    ⟨fun ⟨hψ, h⟩ => ⟨hψ, (maps_iff p.w _ _ _ _ (ν.s (p.xe x)) _ _ (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) fun _ => rfl).1 h⟩,
      fun ⟨hψ, h⟩ => ⟨hψ, (maps_iff p.w _ _ _ _ (ν.s (p.xe x)) _ _ (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) fun _ => rfl).2 h⟩⟩)

theorem secThrough_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (s : L.Sec) (s' : L'.Sec) : (∃ θ : LB.Sec (L.pull F), PullSec F s θ ∧ IsoMaps w s' θ) ↔ SecThrough w s s' := by
  constructor
  · rintro ⟨θ, hp, hm⟩ j k V h₁ h₂ h₃
    refine fn_ext fun y hy => ?_
    have hz : (𝟙 X' : X' ⟶ X') y ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := h₂ hy
    have le : (L.pull F).U (fun _ => j) ≤ F ⁻¹ᵁ L.U j := fun q hq => mem_pull.1 hq
    have a := congrArg (gs (𝟙 X') y _) (hm (fun _ => j) k)
    have a' := (gs_res _ y _ hz _).symm.trans (a.trans ((gs_mul _ y _ hz _ _).trans
      (congrArg₂ (· * ·) rfl (gs_res _ y _ hz _))))
    rw [hp _ le] at a'
    refine (gs_appLE F _ _ h₁ (𝟙 _) y hy _).trans (((gs_appLE F _ _ le (𝟙 _) y hz.1 _).symm.trans a').trans ?_)
    exact ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ y h₂ hy _) (gs_res _ y h₃ hy _))).symm
  · intro h
    refine ⟨thfPull L F s, fun _ _ => rfl, fun (i : PUnit → L.ι) k => fn_ext fun y hy => ?_⟩
    have le : (L.pull F).U i ⊓ L'.U k ≤ F ⁻¹ᵁ L.U (i PUnit.unit) := fun q hq => mem_pull.1 hq.1
    have a := congrArg (gs (𝟙 X') y _) (h (i PUnit.unit) k _ le le_rfl inf_le_right)
    refine (gs_res _ y _ hy _).trans ((gs_appLE F _ _ _ (𝟙 _) y hy.1 _).trans
      ((gs_appLE F _ _ le (𝟙 _) y hy _).symm.trans (a.trans ?_)))
    exact (gs_mul _ y _ hy _ _).trans ((congrArg₂ (· * ·) (gs_res _ y le_rfl hy _) rfl).trans (gs_mul _ y _ hy _ _).symm)

theorem thBC_iff (p : Out.IsPullDeg f D₀ D₁) (th : D₀.P.L.Sec) (th₁ : D₁.P.L.Sec) : ThBC p th th₁ ↔ SecBC p th th₁ :=
  secThrough_iff p.w th th₁

theorem qkBC_iff (p : Out.IsPullDeg f D₀ D₁) (hB : D₀.TauBimult) (hf : Function.Injective f) {k : ℕ}
    (q : Out.QkPt D₀ (FractionRing A) k) (q' : Out.QkPt D₁ (FractionRing A') k) :
    QkBC p hf q q' ↔ ∃ r, GlobalTheory.ArcPull.IsPullQk p q r ∧ Out.QkPt.Equiv D₁ (FractionRing A') r q' :=
  exists_congr fun r => by
    rw [GlobalTheory.T.isPullQk_iff_fraction_map A A' f D₀ D₁ p hB k q r]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨hf, a, b, c⟩, d⟩, fun ⟨⟨_, a, b, c⟩, d⟩ => ⟨a, b, c, d⟩⟩

end Gt

theorem square_iff {X X₁ X₂ X' : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {L' : LB X'} {F₁ : X₁ ⟶ X}
    {F₂ : X₂ ⟶ X} {G₁ : X' ⟶ X₁} {G₂ : X' ⟶ X₂} (hL : L.IsLB) (hL₁ : L₁.IsLB) (hL' : L'.IsLB)
    (u₁ : LB.Iso L₁ (L.pull F₁)) (v₁ : LB.Iso L' (L₁.pull G₁)) (u₂ : LB.Iso L₂ (L.pull F₂))
    (v₂ : LB.Iso L' (L₂.pull G₂)) (hu : u₁.IsGen) (hv : v₁.IsGen) (e : G₂ ≫ F₂ = G₁ ≫ F₁) :
    (∃ (w₁ : LB.Iso L' (L.pull (G₁ ≫ F₁))) (w₂ : LB.Iso L' (L.pull (G₂ ≫ F₂))),
      HEq w₁ w₂ ∧ Tri u₁ v₁ w₁ ∧ Tri u₂ v₂ w₂) ↔
    ∀ (Z : Scheme.{0}) (f : Z ⟶ X') (z : Z) (j : L.ι) (i : L₁.ι) (i' : L₂.ι) (k : L'.ι), (f ≫ G₁ ≫ F₁) z ∈ L.U j →
      (f ≫ G₁) z ∈ L₁.U i → (f ≫ G₂) z ∈ L₂.U i' → f z ∈ L'.U k →
      gw u₁ (f ≫ G₁) z j i * gw v₁ f z i k = gw u₂ (f ≫ G₂) z j i' * gw v₂ f z i' k := by
  have tr : ∀ {F F' : X' ⟶ X} (_ : F' = F) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L' (L.pull F')), HEq w w' →
      ∀ (Z : Scheme.{0}) (f : Z ⟶ X') (z : Z) j k, gw w f z j k = gw w' f z j k := by
    intro F F' h w w' hw; subst h; cases hw; intros; rfl
  have ex : ∀ {F F' : X' ⟶ X} (_ : F' = F) (w : LB.Iso L' (L.pull F)), ∃ w' : LB.Iso L' (L.pull F'), HEq w w' := by
    intro F F' h w; subst h; exact ⟨w, HEq.rfl⟩
  have mem : ∀ (x : X') j, F₂ (G₂ x) ∈ L.U j ↔ F₁ (G₁ x) ∈ L.U j := fun x j =>
    iff_of_eq (congrArg (fun q => q x ∈ L.U j) e)
  constructor
  · rintro ⟨w₁, w₂, h, t₁, t₂⟩ Z f z j i i' k hj hi hi' hk
    exact (t₁ Z f z j i k hj hi hk).symm.trans ((tr e _ _ h Z f z j k).trans
      (t₂ Z f z j i' k ((mem _ _).2 hj) hi' hk))
  · intro h
    obtain ⟨w₁, t₁⟩ := exists_comp hL₁ u₁ v₁ ((isGen_iff _).1 hu) ((isGen_iff _).1 hv) hL hL'
    obtain ⟨w₂, hw⟩ := ex e w₁
    refine ⟨w₁, w₂, hw, t₁, fun Z f z j i' k hj hi' hk => ?_⟩
    obtain ⟨i, hi⟩ := exists_chart hL₁ (G₁ (f z))
    exact (tr e _ _ hw Z f z j k).symm.trans ((t₁ Z f z j i k ((mem _ _).1 hj) hi hk).trans
      (h Z f z j i i' k ((mem _ _).1 hj) hi hi' hk))

theorem existsUnique_sec {X : Scheme.{0}} {L : LB X} (σ : Out.H0 L 1) : ∃! θ : L.Sec, SectionOfLineBundleOne σ θ := by
  have le : ∀ j, L.U j ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := fun j y hy => Set.mem_iInter.2 fun _ => hy
  have g : ∀ (y : X) j j', y ∈ L.U j → y ∈ L.U j' → gm (𝟙 X) y _
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))).g (fun _ => j) (fun _ => j')) =
      gm (𝟙 X) y (L.U j ⊓ L.U j') (L.g j j') := fun y j j' h h' =>
    (gm_linComb L _ _ (𝟙 X) y _ _ (le j h) (le j' h')).trans (by
      rw [Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.id_comp])
  refine ⟨⟨fun j => resG X (le j) (σ.f fun _ => j), fun j j' => fn_ext fun y hy => ?_⟩, ?_, fun θ h => ?_⟩
  · exact (gs_res (𝟙 X) y _ hy _).trans ((gs_res (𝟙 X) y (le j) hy.1 _).trans ((gs_compat σ (𝟙 X) y (le j hy.1) (le j' hy.2)).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (g y j j' hy.1 hy.2).symm))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j') hy.2 _)))))))
  · intro (j : Fin 1 → L.ι) h
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
    exact fn_ext fun y hy => ((gs_res (𝟙 X) y h hy _).trans (gs_res (𝟙 X) y (le i) (h hy) _)).symm
  · obtain ⟨f, hf⟩ := θ
    congr 1
    funext j
    have l' : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) ≤ L.U j := LB.wchart_le L _ _ 0
    refine fn_ext fun y hy => Eq.symm ((gs_res (𝟙 X) y (le j) hy _).trans ?_)
    exact (congrArg (gs (𝟙 X) y _) (h (fun _ => j) l')).trans (gs_res (𝟙 X) y l' (le j hy) _)

theorem existsUnique_h0_section {X : Scheme.{0}} {L : LB X} (θ : L.Sec) : ∃! σ : Out.H0 L 1, SectionOfLineBundleOne σ θ := by
  refine ⟨thfPull1 L (𝟙 X) (Category.id_comp _) (thfPull L (𝟙 X) θ), fun j h => fn_ext fun y hy => ?_, fun σ h => ?_⟩
  · exact (gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy _).trans ((gs_appLE (𝟙 X) _ _ _ _ y (mem_pull.2 (h hy)) _).trans
      (gs_res (𝟙 X) y h hy _).symm)
  · obtain ⟨f, hf⟩ := σ
    unfold thfPull1
    congr 1
    funext j
    have l' : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := LB.wchart_le L _ _ 0
    refine (h j l').trans (fn_ext fun y hy => Eq.symm ?_)
    exact (gs_appLE (𝟙 X) _ _ _ (𝟙 _) y hy _).trans ((gs_appLE (𝟙 X) _ _ _ _ y (mem_pull.2 (l' hy)) _).trans
      (gs_res (𝟙 X) y l' hy _).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Inputs

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {b : O →+* A} {b' : O →+* A'}

def SameLevel (a : ArcIn Dw l β A b) (s : Dw.La → Out.QkPt a.D₀ (FractionRing A) l.M)
    (sA : Dw.La → Out.QkPt a.D₀ (FractionRing A) l.A) : Prop :=
  (∀ v, Out.QkPt.Equiv a.D₀ _ (sA v) (a.etaA v)) ∧
    ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), Out.QkPt.Equiv a.D₀ _ (s v) (a.eta v)

def relevel (a : ArcIn Dw l β A b) (s : Dw.La → Out.QkPt a.D₀ (FractionRing A) l.M)
    (sA : Dw.La → Out.QkPt a.D₀ (FractionRing A) l.A) (h : SameLevel a s sA) : ArcIn Dw l β A b :=
  { a with
    eta := s
    etaA := sA
    geom := fun F _ _ _ r z hr hz f hf => by
      obtain ⟨h₁, I, h₂, h₃, h₄⟩ := a.geom F r z hr hz f hf
      refine ⟨h₁, I, h₂, fun v q hq => ?_, fun v hv q hq => ?_⟩
      · obtain ⟨q', hq', -⟩ := TorusExt.existsUnique_qkExt (F' := F) a.bimult (algebraMap _ F) (RingHom.comp_id _) (a.etaA v)
        exact TorusExt.equiv_trans a.bimult
          (TorusExt.equiv_of_qkExt a.bimult _ (RingHom.comp_id _) hq hq' (h.1 v)) (h₃ v q' hq')
      · obtain ⟨q', hq', -⟩ := TorusExt.existsUnique_qkExt (F' := F) a.bimult (algebraMap _ F) (RingHom.comp_id _) (a.eta v)
        exact TorusExt.equiv_trans a.bimult
          (TorusExt.equiv_of_qkExt a.bimult _ (RingHom.comp_id _) hq hq' (h.2 v hv)) (h₄ v hv q' hq') }

variable (f : A →+* A') (a : ArcIn Dw l β A b) (a' : ArcIn Dw l β A' b') (p : Out.IsPullDeg f a.D₀ a'.D₀)

theorem inputBC_iff : InputBC f a a' p ↔ ∃ s sA h, InBC f a (relevel a' s sA h) p := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, hf, h₅, h₆⟩
    choose sA hA hA' using fun v => (qkBC_iff p a.bimult hf _ _).1 (h₅ v)
    have : ∀ v, ∃ r, GlobalTheory.ArcPull.IsPullQk p (a.eta v) r ∧
        (v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) → Out.QkPt.Equiv a'.D₀ _ r (a'.eta v)) := by
      intro v
      by_cases hv : v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La)
      · obtain ⟨r, h, h'⟩ := (qkBC_iff p a.bimult hf _ _).1 (h₆ v hv)
        exact ⟨r, h, fun _ => h'⟩
      · obtain ⟨r, h⟩ := GlobalTheory.ArcPull.exists_isPullQk GlobalTheory.globalFns_holds hf p a.bimult (a.eta v)
        exact ⟨r, h, fun h' => (hv h').elim⟩
    choose s hs hs' using this
    exact ⟨s, sA, ⟨hA', hs'⟩, h₁, h₂, h₄, h₃, hs, hA⟩
  · rintro ⟨s, sA, h, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨hf, -⟩ := (GlobalTheory.T.isPullQk_iff_fraction_map A A' f _ _ p a.bimult _ _ _).1 (h₆ 0)
    exact ⟨h₁, h₂, h₄, h₃, hf, fun v => (qkBC_iff p a.bimult hf _ _).2 ⟨_, h₆ v, h.1 v⟩,
      fun v hv => (qkBC_iff p a.bimult hf _ _).2 ⟨_, h₅ v, h.2 v hv⟩⟩

theorem inputBC_of_inBC (h : InBC f a a' p) : InputBC f a a' p :=
  (inputBC_iff f a a' p).2 ⟨a'.eta, a'.etaA, ⟨fun _ => qk_equiv_refl a'.bimult _, fun _ _ => qk_equiv_refl a'.bimult _⟩, h⟩

variable {Y : Model Xo c β} {a a'} {χ : Sp (PowerSeries A) ⟶ Y.X}

theorem witBC_iff (W : Wit Y a χ) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.WitBC f p W W' ↔ InputBC f a a' p ∧ WitBC f p W W' := by
  refine and_congr Iff.rfl ((and_iff_right rfl).trans (exists_congr fun hD => exists_congr fun bc =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))))
  refine and_left_comm.trans (and_congr Iff.rfl (and_congr_right fun e => ?_))
  exact (square_iff a.D₀.P.isLB W.P.D.toPre.P.isLB W'.P.D.toPre.P.isLB W.w hD.w p.w W'.w W.spec.2.1 hD.w_gen e).symm

theorem witBC_arc {χ' : Sp (PowerSeries A') ⟶ Y.X} (W : Wit Y a χ) (W' : Wit Y a' χ')
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.WitBC f p W W') : χ' = spMap (PowerSeries.map f) ≫ χ := h.2.1

end Inputs

section ThetaShiftProofs

variable {Y : Model Xo c β} {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)

theorem lieId_iff [IsLocalRing A] (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) :
    LieId W ν v ↔ GtTanR ν ∧ LieImg W ν v := by
  rw [tan_iff]; exact GlobalTheory.T.lie_identity_arc_witness_iff E H Dw l Xo c O β Y A b a χ W ν v

theorem thetaOf_iff (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L) :
    ThetaOf W th θ ↔ ∃ (σ : Out.H0 W.P.U.LG.L 1) (θ' : LB.Sec W.P.U.LG.L), ThetaId W th σ ∧ SectionOfLineBundleOne σ θ' ∧ HEq θ θ' :=
  ⟨fun ⟨σ, fam, θ', h₁, h₂, h₃⟩ => ⟨σ, θ', ⟨fam, h₁, h₂⟩, h₃⟩, fun ⟨σ, θ', ⟨fam, h₁, h₂⟩, h₃⟩ => ⟨σ, fam, θ', h₁, h₂, h₃⟩⟩

theorem thetaId_iff (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) :
    ThetaId W th σ ↔ ∃ (θ : LB.Sec W.t.PP.L) (θ' : LB.Sec W.P.U.LG.L), ThetaOf W th θ ∧ SectionOfLineBundleOne σ θ' ∧ HEq θ θ' := by
  constructor
  · intro h
    obtain ⟨θ', h', -⟩ := existsUnique_sec σ
    have : ∃ θ : LB.Sec W.t.PP.L, HEq θ θ' := by
      have e := W.P.bundle
      generalize W.t.PP = N at e
      subst e
      exact ⟨θ', HEq.rfl⟩
    obtain ⟨θ, e⟩ := this
    exact ⟨θ, θ', (thetaOf_iff W th θ).2 ⟨σ, θ', h, h', e⟩, h', e⟩
  · rintro ⟨θ, θ', h, h', e⟩
    obtain ⟨σ₁, θ₁, k, k', e₁⟩ := (thetaOf_iff W th θ).1 h
    obtain rfl : θ' = θ₁ := eq_of_heq (e.symm.trans e₁)
    rwa [(existsUnique_h0_section θ').unique h' k']

theorem arcBasis_iff [IsLocalRing A] [IsNoetherianRing A] (ρ : (E →+* ℂ) → (𝓞 E →+* A))
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) :
    ArcBasis W ρ e ↔ ∀ τ, (letI := H.starRing; IsEigBasisGt a.oa (ρ τ) (e τ)) := by
  have hG := GlobalTheory.globalFns_holds
  have ex := ConstLie.main hG E H Dw l Xo c O β Y A b a χ W
  have eg := GlobalTheory.T.arc_witness_tangent_point hG E H Dw l Xo c O β Y A b a χ W
  have ba := fun t m e v => GlobalTheory.T.arc_witness_tangent_family hG E H Dw l Xo c O β Y A b a χ W t m e v _ fun _ => Iff.rfl
  constructor
  · rintro ⟨v, hv, h⟩ τ
    refine ⟨fun i => (tan_iff _).1 (((ex _).2 _ (hv τ i)).2 ((h τ).1 i).1),
      fun i => (eg _ _ _ (hv τ i)).2 ((h τ).1 i).2, fun ω ht he => ?_⟩
    obtain ⟨w, hw, -⟩ := (ex ω).1
    exact (ba (ρ τ) _ (e τ) (v τ) (hv τ) (h τ).1).1 (h τ).2 ω w hw (((ex _).2 _ hw).1 ((tan_iff _).2 ht))
      ((eg _ _ _ hw).1 he)
  · intro h
    choose v hv _ using fun τ k => (ex (e τ k)).1
    have h₁ := fun τ k => And.intro (((ex _).2 _ (hv τ k)).1 ((tan_iff _).2 ((h τ).1 k)))
      ((eg _ _ _ (hv τ k)).1 ((h τ).2.1 k))
    exact ⟨v, hv, fun τ => ⟨h₁ τ, (ba (ρ τ) _ (e τ) (v τ) (hv τ) (h₁ τ)).2 fun ν w hw ht he =>
      (h τ).2.2 ν ((tan_iff _).1 (((ex _).2 _ hw).2 ht)) ((eg _ _ _ hw).2 he)⟩⟩

theorem isLetters_iff [IsLocalRing A] [IsNoetherianRing A] (io : c.F →+* FractionRing A)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) :
    IsLetters a io e ↔ io.comp β = (algebraMap A (FractionRing A)).comp b ∧ ∃ ρ : (E →+* ℂ) → (𝓞 E →+* A),
      (∀ τ, (algebraMap A (FractionRing A)).comp (ρ τ) = io.comp (embK c τ)) ∧ ArcBasis W ρ e :=
  and_congr Iff.rfl ⟨fun h => by
    choose ρ h₁ h₂ using h
    exact ⟨ρ, h₁, (arcBasis_iff W ρ e).2 h₂⟩, fun ⟨ρ, h₁, h₂⟩ τ => ⟨ρ τ, h₁ τ, (arcBasis_iff W ρ e).1 h₂ τ⟩⟩

variable [IsLocalRing A] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec)
  {S : Type} [CommRing S] [Algebra c.F S] (io : PowerSeries A →+* S) (y : FrPt Xo c S)

theorem dual_over {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [ConstLie.spMap_comp', ConstLie.spMap_comp']
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isArcFr_of_isArcFrPt (h : IsArcFrPt W e th io y) : (∀ τ k, GtTanR (e τ k)) ∧ IsArcFr W e th io y := by
  obtain ⟨z, ⟨zx, -, zj⟩, hu, hθ⟩ := h
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp S), Nonempty (SABMap t' Y.oF.t z) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull z Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  have comp : ∀ (x : Sp S ⟶ Xo.X) (_ : z ≫ pullback.fst _ _ = x),
      ∃ m1 : SABMap t' Xo.univ.t x, m1.φ = m.φ ≫ Y.m0.toSABMap.φ := by
    intro x hx; subst hx; exact sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m
  obtain ⟨m1, hm1⟩ := comp _ zx
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m
  have cancel : ∀ (p : Sp S ⟶ Y.X) (_ : p = spMap io ≫ χ) (n : SABMap t' Y.t p),
      ∃ m' : SABMap t' W.t (spMap io), n.φ = m'.φ ≫ W.m.φ := by
    intro p hp n; subst hp; exact sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ W.m n
  obtain ⟨m2, hm2⟩ := cancel _ zj n
  have φ2 : m.φ ≫ Y.m.φ = m2.φ ≫ W.m.φ := hn.symm.trans hm2
  refine ⟨fun τ k => ?_, z, t', m1, m2, m.φ, zj, zx, m.cart.1.w, hm1.symm, φ2, fun τ k => ?_,
    (GlobalTheory.T.arc_witness_theta_pullback GlobalTheory.globalFns_holds E H Dw l Xo c O β Y A b a χ W th S io y.x z t' m1 m2 m.φ y.s zj zx m.cart.1.w
      hm1.symm φ2).2 hθ⟩
  · obtain ⟨v, -, hv, -⟩ := hu τ k
    exact ((lieId_iff W _ _).1 hv).1
  · obtain ⟨v, uF, hv, h₁, h₂, h₃⟩ := hu τ k
    have a₁ := m.cart.1.lift_fst _ _ h₁
    have a₂ := m.cart.1.lift_snd _ _ h₁
    have vb : v.left ≫ W.t.G.hom = spMap (algebraMap _ (DualNumber (PowerSeries A))) := Over.w v
    refine ⟨v, m.cart.1.lift _ _ h₁, ((lieId_iff W _ _).1 hv).2, ?_, W.m.cart.1.hom_ext ?_ ?_, a₂⟩
    · rw [hm1, ← Category.assoc]
      exact (congrArg (· ≫ _) a₁).trans h₂
    · rw [Category.assoc, Category.assoc]
      exact (congrArg _ φ2.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) a₁).trans h₃))
    · rw [Category.assoc, Category.assoc, vb, dual_over, m2.cart.1.w, ← Category.assoc, a₂]

theorem isArcFrPt_of_isArcFr
    (hz : ∀ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = spMap io ≫ χ → z ≫ pullback.fst _ _ = y.x →
      z ≫ pullback.snd _ _ = spMap (algebraMap c.F S))
    (he : ∀ τ k, GtTanR (e τ k)) (h : IsArcFr W e th io y) : IsArcFrPt W e th io y := by
  obtain ⟨z, t', m1, m2, φ, zj, zx, φb, φ1, φ2, hu, hθ⟩ := h
  refine ⟨z, ⟨zx, hz z zj zx, zj⟩, fun τ k => ?_,
    (GlobalTheory.T.arc_witness_theta_pullback GlobalTheory.globalFns_holds E H Dw l Xo c O β Y A b a χ W th S io y.x z t' m1 m2 φ y.s zj zx φb φ1 φ2).1 hθ⟩
  obtain ⟨v, u, hv, h₁, h₂, h₃⟩ := hu τ k
  refine ⟨v, u ≫ φ, (lieId_iff W _ _).2 ⟨he τ k, hv⟩, ?_, ?_, ?_⟩
  · rw [Category.assoc, φb, ← Category.assoc, h₃]
  · rw [Category.assoc, φ1, h₁]
  · rw [Category.assoc, φ2, ← Category.assoc, h₂, Category.assoc]

theorem over_of_overBase [Mono (spMap β)] (hb : spMap io ≫ χ ≫ Y.s = spMap (algebraMap c.F S) ≫ spMap β)
    (z : Sp S ⟶ Xo.XF c) (zj : z ≫ Y.j = spMap io ≫ χ) : z ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  rw [← cancel_mono (spMap β), ← hb, ← Category.assoc (spMap io), ← zj, Model.j, Category.assoc, Category.assoc,
    Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]

theorem isArcFrPt_iff [Mono (spMap β)] :
    IsArcFrPt W e th io y ↔ (∀ τ k, GtTanR (e τ k)) ∧
      spMap io ≫ χ ≫ Y.s = spMap (algebraMap c.F S) ≫ spMap β ∧ IsArcFr W e th io y := by
  constructor
  · intro h
    refine ⟨(isArcFr_of_isArcFrPt W e th io y h).1, ?_, (isArcFr_of_isArcFrPt W e th io y h).2⟩
    obtain ⟨z, ⟨-, zs, zj⟩, -⟩ := h
    rw [← Category.assoc, ← zj, ← zs, Model.j, Category.assoc, Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc Y.jQ, Y.jQ_over]
  · rintro ⟨he, hb, h⟩
    exact isArcFrPt_of_isArcFr W e th io y (fun z zj _ => over_of_overBase io hb z zj) he h

end ThetaShiftProofs

theorem typings_agree :
    (∀ (A : Type) [CommRing A] [IsDomain A] (D₀ : Out.DegPre A),
      (∀ ν : Out.GtPt D₀ (epsR A), GtTanR ν ↔ IsTanGt ν) ∧
      (∀ (m : ℕ) (cf : Fin m → A) (e : Fin m → Out.GtPt D₀ (epsR A)) ν, GtComb cf e ν ↔ IsCombGt e cf ν) ∧
      (∀ (r : A) (th th' : D₀.P.L.Sec), ThMul r th th' ↔ IsMulSec r th th') ∧
      (∀ th : D₀.P.L.Sec, ThNZ th ↔ FibrewiseNe th) ∧
      ∀ (A' : Type) [CommRing A'] [IsDomain A'] (D₁ : Out.DegPre A') (f : A →+* A') (p : Out.IsPullDeg f D₀ D₁),
        (∀ ν ν₁, LetBC p ν ν₁ ↔ LetterBC p ν ν₁) ∧ ∀ th th₁, ThBC p th th₁ ↔ SecBC p th th₁) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
      (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A]
      (b : O →+* A) (a : ArcIn Dw l β A b),
      (∀ (A' : Type) [CommRing A'] [IsDomain A'] (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A')
        (p : Out.IsPullDeg f a.D₀ a'.D₀),
        (InBC f a a' p → InputBC f a a' p) ∧ (InputBC f a a' p ↔ ∃ s sA h, InBC f a (relevel a' s sA h) p) ∧
        ∀ (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ),
          (∀ (χ' : Sp (PowerSeries A') ⟶ Y.X) (W' : Wit Y a' χ'), GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.WitBC f p W W' →
            χ' = spMap (PowerSeries.map f) ≫ χ) ∧
          ∀ W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ),
            GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.WitBC f p W W' ↔ InputBC f a a' p ∧ WitBC f p W W') ∧
      ∀ (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ),
        (∀ th θ, ThetaOf W th θ ↔ ∃ σ θ', ThetaId W th σ ∧ SectionOfLineBundleOne σ θ' ∧ HEq θ θ') ∧
        (∀ th σ, ThetaId W th σ ↔ ∃ θ θ', ThetaOf W th θ ∧ SectionOfLineBundleOne σ θ' ∧ HEq θ θ') ∧
        ∀ [IsLocalRing A],
          (∀ ν v, LieId W ν v ↔ GtTanR ν ∧ LieImg W ν v) ∧
          (∀ [IsNoetherianRing A] (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)),
            (∀ ρ, ArcBasis W ρ e ↔ ∀ τ, (letI := H.starRing; IsEigBasisGt a.oa (ρ τ) (e τ))) ∧
            ∀ io : c.F →+* FractionRing A, IsLetters a io e ↔
              io.comp β = (algebraMap A (FractionRing A)).comp b ∧ ∃ ρ : (E →+* ℂ) → (𝓞 E →+* A),
                (∀ τ, (algebraMap A (FractionRing A)).comp (ρ τ) = io.comp (embK c τ)) ∧ ArcBasis W ρ e) ∧
          ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (th : a.D₀.P.L.Sec) (S : Type) [CommRing S]
            [Algebra c.F S] (io : PowerSeries A →+* S) (y : FrPt Xo c S),
            (IsArcFrPt W e th io y → (∀ τ k, GtTanR (e τ k)) ∧ IsArcFr W e th io y) ∧
            ((∀ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = spMap io ≫ χ → z ≫ pullback.fst _ _ = y.x →
                z ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) →
              (∀ τ k, GtTanR (e τ k)) → IsArcFr W e th io y → IsArcFrPt W e th io y) ∧
            (Mono (spMap β) → (IsArcFrPt W e th io y ↔ (∀ τ k, GtTanR (e τ k)) ∧
              spMap io ≫ χ ≫ Y.s = spMap (algebraMap c.F S) ≫ spMap β ∧ IsArcFr W e th io y)) :=
  ⟨fun _ _ _ _ => ⟨tan_iff, fun _ => comb_iff, thMul_iff, thNZ_iff, fun _ _ _ _ _ p => ⟨letBC_iff p, thBC_iff p⟩⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a =>
      ⟨fun _ _ _ _ a' f p => ⟨inputBC_of_inBC f a a' p, inputBC_iff f a a' p,
        fun _ W => ⟨fun _ W' => witBC_arc f p W W', witBC_iff f p W⟩⟩,
      fun _ W => ⟨thetaOf_iff W, thetaId_iff W, ⟨lieId_iff W,
        fun e => ⟨fun ρ => arcBasis_iff W ρ e, fun io => isLetters_iff W io e⟩,
        fun e th _ _ _ io y => ⟨isArcFr_of_isArcFrPt W e th io y, isArcFrPt_of_isArcFr W e th io y,
          fun _ => isArcFrPt_iff W e th io y⟩⟩⟩⟩⟩

end GlobalTheory.ArcCompare
