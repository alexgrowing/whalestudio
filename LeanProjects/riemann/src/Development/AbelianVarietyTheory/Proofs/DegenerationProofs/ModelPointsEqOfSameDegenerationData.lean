import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataIsoOfTwoWitnessesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcUnique

theorem genRel_cancel {F : Type} [Field F] {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''}
    {Φ : X' ⟶ X} {Φ' : X'' ⟶ X'} {w : LB.Iso L' (L.pull Φ)} {w' : LB.Iso L'' (L'.pull Φ')}
    {w'' : LB.Iso L'' (L.pull (Φ' ≫ Φ))} (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (hw : w.IsGen)
    (hw' : w'.IsGen) (hw'' : w''.IsGen) (T : Tri w w' w'') {K : Type} [Fintype K] {pt : K → (Sp F ⟶ X)}
    {pt' : K → (Sp F ⟶ X')} {pt'' : K → (Sp F ⟶ X'')} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L pt ε)}
    {t' : LB.Gen (LB.LinComb L' pt' ε)} {t'' : LB.Gen (LB.LinComb L'' pt'' ε)} (ht : t.IsGen) (ht' : t'.IsGen)
    (ht'' : t''.IsGen) {x : F} (h : GenRel w t' t x) (h' : GenRel w'' t'' t x) (hp : ∀ k, pt'' k ≫ Φ' = pt' k) :
    GenRel w' t'' t' ((1 : Fˣ) : F) := by
  have hx := MatchRigid.genRel_ne_zero hL' hL h
  obtain ⟨x, rfl⟩ : ∃ v : Fˣ, (v : F) = x := ⟨Units.mk0 x hx, rfl⟩
  obtain rfl : (fun k => pt'' k ≫ Φ') = pt' := funext hp
  refine (ArcTransport.genRel_val ((isGen_iff _).1 hw') hL' hL'' ht'' ht' 1).2 ⟨hp, fun y J' J'' hJ' hJ'' => ?_⟩
  obtain ⟨J, hJ⟩ := ArcTransport.exists_good' hL (Y := Sp F) y
  have a := ((ArcTransport.genRel_val ((isGen_iff _).1 hw) hL hL' ht' ht x).1 h).2 y J J' hJ hJ'
  have b := ((ArcTransport.genRel_val ((isGen_iff _).1 hw'') hL hL'' ht'' ht x).1 h').2 y J J'' hJ hJ''
  have c : ∀ k, Geo.Tor.gw w'' (pt'' k) y (J (pt'' k ≫ Φ' ≫ Φ)) (J'' (pt'' k)) =
      Geo.Tor.gw w (pt'' k ≫ Φ') y (J ((pt'' k ≫ Φ') ≫ Φ)) (J' (pt'' k ≫ Φ')) *
        Geo.Tor.gw w' (pt'' k) y (J' (pt'' k ≫ Φ')) (J'' (pt'' k)) := fun k =>
    T _ (pt'' k) y _ _ _ (hJ (pt'' k ≫ Φ' ≫ Φ)) (hJ' (pt'' k ≫ Φ')) (hJ'' _)
  simp only [c, mul_zpow, Finset.prod_mul_distrib] at b
  rw [← a, _root_.mul_assoc] at b
  rw [map_one, _root_.one_mul]
  exact mul_left_cancel b

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsFibre {S T : Scheme.{0}} (A : Over T) [GrpObj A] (act : 𝓞 E → (A ⟶ A)) (L : LB A.left) (t : SAB H S)
    (y : T ⟶ S) (φ : A.left ⟶ t.G.left) : Prop :=
  IsGrpPullback A t.G y φ ∧ (∀ a, (act a).left ≫ φ = φ ≫ (t.act.act a).left) ∧ LBIso L (t.PP.L.pull φ)

theorem lbIso_pull {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} (h : LBIso L' (L.pull Φ))
    (Φ' : X'' ⟶ X') : LBIso (L'.pull Φ') (L.pull (Φ' ≫ Φ)) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L' Φ' Φ' rfl) (chartPullSame L _ _ _ Φ' fun _ => rfl) h

theorem isFibre_of_sabMap {S T : Scheme.{0}} {t : SAB H S} {t' : SAB H T} {y : T ⟶ S} (m : SABMap t' t y) :
    IsFibre t'.G t'.act.act t'.PP.L t y m.φ := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨m.cart, m.act, w, hw⟩

theorem IsFibre.precomp {S T T' : Scheme.{0}} {A : Over T} [GrpObj A] {act : 𝓞 E → (A ⟶ A)} {L : LB A.left}
    {t : SAB H S} {y : T ⟶ S} {φ : A.left ⟶ t.G.left} (h : IsFibre A act L t y φ) (hL : L.IsLB) {A' : Over T'}
    [GrpObj A'] {act' : 𝓞 E → (A' ⟶ A')} {L' : LB A'.left} (hL' : L'.IsLB) {j : T' ⟶ T} {ρ : A'.left ⟶ A.left}
    (g : IsGrpPullback A' A j ρ) (ha : ∀ a, (act' a).left ≫ ρ = ρ ≫ (act a).left) (hi : LBIso L' (L.pull ρ)) :
    IsFibre A' act' L' t (j ≫ y) (ρ ≫ φ) :=
  ⟨g.comp h.1, fun a => by rw [← Category.assoc, ha, Category.assoc, h.2.1, Category.assoc],
    LBIso.trans hL' (pull_isLB hL ρ) (pull_isLB t.PP.isLB _) hi (lbIso_pull h.2.2 ρ)⟩

theorem IsFibre.cancel {S T T' : Scheme.{0}} {A : Over T} [GrpObj A] {act : 𝓞 E → (A ⟶ A)} {L : LB A.left}
    {t : SAB H S} {y : T ⟶ S} {φ : A.left ⟶ t.G.left} (h : IsFibre A act L t y φ) (hL : L.IsLB) {A' : Over T'}
    [GrpObj A'] {act' : 𝓞 E → (A' ⟶ A')} {L' : LB A'.left} (hL' : L'.IsLB) {j : T' ⟶ T} {y' : T' ⟶ S}
    {φ' : A'.left ⟶ t.G.left} (h' : IsFibre A' act' L' t y' φ') (e : j ≫ y = y') :
    ∃ ρ : A'.left ⟶ A.left, ρ ≫ φ = φ' ∧ IsGrpPullback A' A j ρ ∧ (∀ a, (act' a).left ≫ ρ = ρ ≫ (act a).left) ∧
      LBIso L' (L.pull ρ) := by
  subst e
  let ρ : A'.left ⟶ A.left := h.1.1.lift φ' (A'.hom ≫ j) (by rw [h'.1.1.w, Category.assoc])
  have e₁ : ρ ≫ φ = φ' := h.1.1.lift_fst _ _ _
  have e₂ : ρ ≫ A.hom = A'.hom ≫ j := h.1.1.lift_snd _ _ _
  refine ⟨ρ, e₁, h.1.cancel (by rw [e₁]; exact h'.1) e₂, fun a => h.1.1.hom_ext ?_ ?_, ?_⟩
  · rw [Category.assoc, e₁, h'.2.1, Category.assoc, h.2.1, ← Category.assoc, e₁]
  · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w, e₂]
  · have b := (lbIso_pull h.2.2 ρ).symm
    rw [e₁] at b
    exact LBIso.trans hL' (pull_isLB t.PP.isLB _) (pull_isLB hL ρ) h'.2.2 b

variable {D : Datum H} {l : Level H}

theorem points_eq (Xo : Moduli D l) (c : Coeff l)
    (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))
    (m0 : ObjMap o Xo.univ (pullback.fst _ _)) {T T' : Scheme.{0}} [IsReduced T'] (j : T' ⟶ T) {A : Over T} [GrpObj A]
    {act : 𝓞 E → (A ⟶ A)} {L : LB A.left} (hL : L.IsLB) {y y' : T ⟶ Xo.XF c} {φ φ' : A.left ⟶ o.t.G.left}
    (h : IsFibre A act L o.t y φ) (h' : IsFibre A act L o.t y' φ')
    (e₂ : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _)
    (hA : ∀ v (x : Over.mk j ⟶ A), x.left ≫ φ = j ≫ y ≫ (o.etaA v).left → x.left ≫ φ' = j ≫ y' ≫ (o.etaA v).left)
    (hM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ x : Over.mk j ⟶ A,
      x.left ≫ φ = j ≫ y ≫ (o.eta v).left → x.left ≫ φ' = j ≫ y' ≫ (o.eta v).left) : j ≫ y = j ≫ y' := by
  obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ T' _
    (((j ≫ y) ≫ pullback.fst _ _) ≫ Xo.s) (j ≫ y) rfl rfl
    ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).symm.trans
      (congrArg ((((j ≫ y) ≫ pullback.fst _ _) ≫ Xo.s) ≫ ·) (Spec.map_id _).symm))) o
  obtain ⟨ρ, e₁, g, ha, hi⟩ := h.cancel hL o'.t.PP.isLB (isFibre_of_sabMap m.toSABMap) rfl
  obtain ⟨f₁, f₂, f₃⟩ := h'.precomp hL o'.t.PP.isLB g ha hi
  have := o'.proper
  obtain ⟨m', hm'⟩ := exists_sabMap_of_lbIso E H _ _ o.t o'.t (j ≫ y') (ρ ≫ φ')
    ⟨inferInstance, fun s _ K _ _ t _ => inferInstance⟩ f₁ f₂ f₃
  have key : ∀ (x : 𝟙_ (Over T') ⟶ o'.t.G) (z : 𝟙_ (Over (Xo.XF c)) ⟶ o.t.G),
      x.left ≫ m.toSABMap.φ = (j ≫ y) ≫ z.left →
      (∀ x : Over.mk j ⟶ A, x.left ≫ φ = j ≫ y ≫ z.left → x.left ≫ φ' = j ≫ y' ≫ z.left) →
      x.left ≫ m'.φ = (j ≫ y') ≫ z.left := fun x z hx hz => by
    have := hz (Over.homMk (x.left ≫ ρ) (by
      show (x.left ≫ ρ) ≫ A.hom = j
      rw [Category.assoc, g.1.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)) (by
        show (x.left ≫ ρ) ≫ φ = _
        rw [Category.assoc, e₁, hx, Category.assoc])
    rw [hm']
    exact (Category.assoc _ _ _).symm.trans (this.trans (Category.assoc _ _ _).symm)
  have a₁ : ∀ a, (o'.eta a).left ≫ m'.φ = (j ≫ y') ≫ (o.eta a).left := fun a => by
    have : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La) := by
      rw [l.coprime, Submodule.top_smul]; trivial
    rw [Submodule.sup_smul] at this
    obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := Submodule.mem_sup.1 this
    rw [o'.eta_add, o.eta_add, o'.eta_ker _ h₁, o.eta_ker _ h₁, _root_.one_mul, _root_.one_mul]
    exact key _ _ (m.eta v₂) (hM v₂ h₂)
  have a₂ : ∀ a, (o'.etaA a).left ≫ m'.φ = (j ≫ y') ≫ (o.etaA a).left := fun a => key _ _ (m.etaA a) (hA a)
  have comp : ∀ (g : T' ⟶ Xo.XF c), ObjMap o' o g → Nonempty (ObjMap o' Xo.univ (g ≫ pullback.fst _ _)) :=
    fun g u => (ObjComp.objMap_comp m0 u).nonempty
  have e₃ : (j ≫ y) ≫ pullback.snd _ _ = (j ≫ y') ≫ pullback.snd _ _ := by rw [Category.assoc, e₂, Category.assoc]
  refine pullback.hom_ext ?_ e₃
  refine (Xo.rep _ _ inferInstance o').unique ⟨rfl, comp _ m⟩ ⟨?_, comp _ ⟨m', a₁, a₂⟩⟩
  rw [Category.assoc (j ≫ y'), Category.assoc (j ≫ y), pullback.condition, ← Category.assoc, ← e₃, Category.assoc]

section Witness

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : O' →+* R} {u : R}

theorem exists_isFibre {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) {y : Sp (FractionRing R) ⟶ Xo.XF c}
    (hy : y ≫ Y.j = jK R ≫ χ) :
    ∃ φ : W.P.A.A.left ⟶ Y.oF.t.G.left,
      φ ≫ Y.m.φ = W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) ≫ W.m.φ ∧
      IsFibre W.P.A.A (letI := H.starRing; W.P.oA.act) W.P.A.L Y.oF.t y φ := by
  let _ := H.starRing
  have gpG : IsGrpPullback W.P.A.A W.t.G (jK R) (W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R)) := by
    have := W.P.U.gen_hom
    have : IsMonHom W.P.U.gen.symm.hom := by show IsMonHom W.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W.P.U.gen.symm).comp (isGrpPullback_pullback W.t.G (jK R))).congr
      (Category.id_comp _) rfl
  have hgi : W.P.U.gen.inv.left ≫ W.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have actA : ∀ x, (W.P.oA.act x).left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) =
      (W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R)) ≫ (W.t.act.act x).left := by
    intro x
    have e : W.P.oA.act x ≫ W.P.U.gen.inv = W.P.U.gen.inv ≫ (Over.pullback (jK R)).map (W.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have wA : LBIso W.P.A.L (W.t.PP.L.pull (W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R))) := by
    rw [← W.P.bundle]
    exact LBIso.chartPull (h := W.P.U.gen.inv.left) (chartPullSec W.P.A.L _ _ hgi)
      (chartPullSame W.P.U.LG.L _ (fun _ => pullback.fst W.t.G.hom (jK R)) _ _ fun _ => rfl) W.P.U.ext
  have h₁ := (isFibre_of_sabMap W.m).precomp W.t.PP.isLB W.P.A.isLB gpG actA wA
  obtain ⟨ρ, e, g⟩ := (isFibre_of_sabMap Y.m).cancel Y.oF.t.PP.isLB W.P.A.isLB h₁ hy
  exact ⟨ρ, e.trans (Category.assoc _ _ _), g⟩

theorem match_of_wit {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) :
    LN.Match a f u W.P.D.toPre W.P.oD W.φ W.he W.w W.e :=
  ⟨W.spec.1, W.spec.2.1, W.spec.2.2.1, W.spec.2.2.2.1, W.spec.2.2.2.2.1,
    fun F _ _ _ _ uF h h' => (W.spec.2.2.2.2.2 F uF h h').1⟩

theorem isPullGtF_of_transport {χ χ' : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (W' : ArcWit Y a I f u χ')
    (hD : IsPullDeg (RingHom.id R) W.P.D.toPre W'.P.D.toPre) (he : ∀ y, hD.xe (W'.e y) = W.e y)
    (w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫
      pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)))
    (hφ : W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ W.φ)
    (hw : HEq W'.w w') (T : Tri W.w hD.w w') {F : Type} [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing O') F] {g₀ : GtPtF a.D₀ F} {g : GtPtF W.P.D.toPre F} {g' : GtPtF W'.P.D.toPre F}
    {x : a.D₀.X → F} (h : ∀ z, GenRel W.w (g.s (W.e z)) (g₀.s z) (x z))
    (h' : ∀ z, GenRel W'.w (g'.s (W'.e z)) (g₀.s z) (x z)) : IsPullGtF (RingHom.id R) hD F g g' := by
  have hF : ArcPull.Compat (RingHom.id R) F := fun _ => rfl
  have hg' : w'.IsGen ∧ ∀ z, GenRel w' (g'.s (W'.e z)) (g₀.s z) (x z) := by
    have k := And.intro W'.spec.2.1 h'
    generalize W'.w = w₀ at hw k
    generalize W'.φ = φ₀ at hφ w₀
    subst hφ
    obtain rfl := eq_of_heq hw
    exact k
  have gp := pull_grp hD
  have hb : ArcTransport.pushF gp hF.base g'.b = g.b := Over.OverMorphism.ext (W.spec.1.1.hom_ext
    ((Category.assoc _ _ _).trans (((hg'.2 0).1 2).trans ((h 0).1 2).symm)) (by rw [Over.w, Over.w]))
  refine (ArcPull.isPullGtF_iff hD hF g g').2 fun z => ?_
  obtain ⟨z, rfl⟩ := W.e.surjective z
  have e : hD.xe.symm (W.e z) = W'.e z := hD.xe.symm_apply_eq.2 (he z).symm
  have p := ArcTransport.gtφ_push gp hF.base (ArcPull.c_symm hD) g'.b (W.e z)
  rw [hb] at p
  rw [e] at p ⊢
  exact genRel_cancel a.D₀.P.isLB W.P.D.toPre.P.isLB W'.P.D.toPre.P.isLB W.spec.2.1 hD.w_gen hg'.1 T (g₀.isGen _)
    (g.isGen _) (g'.isGen _) (h z) (hg'.2 z) p

end Witness

theorem eq_of_hasArcData : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (y y' : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → y' ≫ Y.j = jK R ≫ χ' → χ ≫ Y.s = spMap f ≫ spMap b → χ' ≫ Y.s = spMap f ≫ spMap b → Y.HasArcData a I f u χ → Y.HasArcData a I f u χ' → χ = χ' := by
  intro h1 h2 h3 h4 h5 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a R _ _ _ _ I f u hR hI hf χ χ' y y' hy hy' hs hs' hχ hχ'
  let _ := H.starRing
  obtain ⟨W⟩ := (Y.hasArcData_iff a I f u χ).1 hχ
  obtain ⟨W'⟩ := (Y.hasArcData_iff a I f u χ').1 hχ'
  obtain ⟨hD, he, hact, w', hφ, hw, T⟩ := GlobalTheory.T.degenerationData_iso_of_two_witnesses h1 h2 h5 E H D l Xo c W₀ Y O' b a R I f u hR hI hf χ χ' W W'
  obtain ⟨ψ, mψ, hL, hQ, hO⟩ := GlobalTheory.T.exists_generic_iso_of_uniformisations_isoData h1 h2 R I hR hI W.P.D W'.P.D W.P.A W'.P.A W.t.G W'.t.G W.t.semi W'.t.semi
    W.P.U W'.P.U hD
  have hψ := hO (𝓞 E) W.P.oD W'.P.oD W.P.oA W'.P.oA _ _ W.P.lin W'.P.lin (fun x z => by
    obtain ⟨z, rfl⟩ := W'.e.surjective z
    rw [← map_smul, he, he, map_smul]) hact
  obtain ⟨φ, eφ, fφ⟩ := exists_isFibre W hy
  obtain ⟨φ', eφ', fφ'⟩ := exists_isFibre W' hy'
  have fψ := fφ.precomp W.P.A.isLB W'.P.A.isLB (act' := W'.P.oA.act) (isGrpPullback_of_iso ψ)
    (fun x => by rw [← Over.comp_left, hψ, Over.comp_left]) hL
  rw [Category.id_comp] at fψ
  let F := AlgebraicClosure (FractionRing R)
  let g : O' →+* F := ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).comp f
  have hinj : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)
  have hg : Function.Injective g := hinj.comp hf
  letI : Algebra (FractionRing O') F := (IsFractionRing.lift (K := FractionRing O') hg).toAlgebra
  have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) :=
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing O') hg x
  let j : Sp F ⟶ Sp (FractionRing R) := jFK (R := R) F
  have lev : ∀ (k : ℕ) (p₀ : QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), 1 ≤ k → k ∣ l.M' →
      ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
        (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
          HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v)) →
      ∀ x : Over.mk j ⟶ W'.P.A.A, x.left ≫ ψ.hom.left ≫ φ = j ≫ y ≫ σ.left → x.left ≫ φ' = j ≫ y' ≫ σ.left := by
    intro k p₀ σ hk hd hσ x hx
    obtain ⟨q₀, hq₀, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing O') F) (by ext; rfl) p₀
    obtain ⟨q, hq⟩ := MatchRigid.exists_transport (match_of_wit W) hF rfl h1.globalFns hd q₀
    obtain ⟨q', hq'⟩ := MatchRigid.exists_transport (match_of_wit W') hF rfl h1.globalFns hd q₀
    have t₁ := (W.spec.2.2.2.2.2 F _ hF rfl).2 (j ≫ y) (by rw [Category.assoc, hy]) k p₀ σ hσ q₀ q (x ≫ ψ.hom) hq₀
      hq.1 hq.2 (by
        rw [← eφ, Over.comp_left, Category.assoc, Category.assoc]
        exact (by simpa only [Category.assoc] using congrArg (· ≫ Y.m.φ) hx))
    have t₂ := (hQ F k hk q q' x (by rw [hq'.1, hq.1, ← he, AddEquiv.symm_apply_apply])
      (isPullGtF_of_transport W W' hD he w' hφ hw T hq.2 hq'.2)).2 t₁
    have w₀ : (j ≫ y' ≫ σ.left) ≫ Y.oF.t.G.hom = j ≫ y' := by
      rw [Category.assoc, Category.assoc, Over.w]
      exact congrArg _ (Category.comp_id _)
    let x' : Over.mk j ⟶ W'.P.A.A := Over.homMk (fφ'.1.1.lift (j ≫ y' ≫ σ.left) j w₀) (fφ'.1.1.lift_snd _ _ _)
    have hx' : x'.left ≫ φ' = j ≫ y' ≫ σ.left := fφ'.1.1.lift_fst _ _ _
    have t₃ := (W'.spec.2.2.2.2.2 F _ hF rfl).2 (j ≫ y') (by rw [Category.assoc, hy']) k p₀ σ hσ q₀ q' x' hq₀
      hq'.1 hq'.2 (by
        rw [← eφ']
        exact (by simpa only [Category.assoc] using congrArg (· ≫ Y.m.φ) hx'))
    obtain ⟨τ, hτ, -⟩ := TorsionIso.torsion_eq ⟨h1, h2, h3, h4, h5⟩ R I hR W'.P.D W'.P.A W'.t.G W'.t.semi W'.P.U F k hk
    rw [((hτ _ _).1 t₂).trans ((hτ _ _).1 t₃).symm]
    exact hx'
  have hm : Mono (spMap (c.V W₀).subtype) := by
    have : IsPreimmersion (spMap (c.V W₀).subtype) :=
      IsPreimmersion.of_isLocalization (R := c.V W₀) (S := c.F) (nonZeroDivisors _)
    infer_instance
  have sn : ∀ {z : Sp (FractionRing R) ⟶ Xo.XF c} {ξ : Sp R ⟶ Y.X}, z ≫ Y.j = jK R ≫ ξ →
      (z ≫ pullback.snd _ _) ≫ spMap (c.V W₀).subtype = jK R ≫ ξ ≫ Y.s := fun {z ξ} hz => by
    rw [← Y.jQ_over, Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc (jK R), ← hz, Model.j,
      Category.assoc, Category.assoc]
  have key : j ≫ y = j ≫ y' := points_eq Xo c Y.oF Y.m0 j W'.P.A.isLB fψ fφ'
    ((cancel_mono (spMap (c.V W₀).subtype)).1 (by rw [sn hy, sn hy', hs, hs']))
    (fun v => lev _ (a.etaA v) _ l.A_pos (Nat.dvd_lcm_right _ _) (Or.inl ⟨rfl, v, HEq.rfl, rfl⟩))
    (fun v hv => lev _ (a.eta v) _ (le_trans (by norm_num) l.three_le) (Nat.dvd_lcm_left _ _)
      (Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩))
  have := ThetaDescent.isProper_of_isProjOver Y.proj
  have : IsDominant (j ≫ jK R) := by
    have e : j ≫ jK R = spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
      (Spec.map_comp _ _).symm
    rw [e]
    exact ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 hinj).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated Y.s (hs.trans hs'.symm) (j ≫ jK R) ?_
  rw [Category.assoc, Category.assoc, ← hy, ← hy', ← Category.assoc, key, Category.assoc]

end GlobalTheory.ArcUnique
