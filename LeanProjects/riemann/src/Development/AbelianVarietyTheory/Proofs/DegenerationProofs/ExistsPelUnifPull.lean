import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWitOfPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionOfIsPullDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ArcDataDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

set_option maxHeartbeats 1600000 in

theorem exists_pelUnif_pull (hC : CubePullSt) (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (h5 : Laws5)
    {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (t : SAB H (Sp R)) (P : PELUnif I t) (g : R →+* R')
    (hg : Function.Injective g) (hI : I.map g ≤ I') :
    ∃ (t' : SAB H (Sp R')) (m₀ : SABMap t' t (spMap g)) (P' : PELUnif I' t') (hD : IsPullDeg g P.D.toPre P'.D.toPre)
      (bc : t'.G ≅ (Over.pullback (specOf g)).obj t.G), IsMonHom bc.hom ∧ IsPullUnif g hD bc P.U P'.U ∧
      m₀.φ = bc.hom.left ≫ pullback.fst t.G.hom (specOf g) ∧ (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (specOf g)).map (P.oD.onB.act x)) := by
  letI := H.starRing
  have hO := polOActPull
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull hC (spMap g) t
  let t' : SAB H (Sp R') := ⟨(Over.pullback (spMap g)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (spMap g) := m₁
  have hm₀ : m₀.φ = pullback.fst t.G.hom (spMap g) := hm₁
  let gam : FractionRing R →+* FractionRing R' :=
    IsFractionRing.lift (g := (algebraMap R' (FractionRing R')).comp g) ((IsFractionRing.injective R' _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  have sq : spMap gam ≫ Out.jK R = Out.jK R' ≫ spMap g :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp g _))
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap gam) P.A
  have gpA : IsGrpPullback A'.A P.A.A (spMap gam) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A t.G (Out.jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp' : IsGrpPullback ((Over.pullback (Out.jK R')).obj t'.G) t.G (spMap gam ≫ Out.jK R)
      (pullback.fst t'.G.hom (Out.jK R') ≫ pullback.fst t.G.hom (spMap g)) :=
    ((isGrpPullback_pullback t'.G (Out.jK R')).comp (isGrpPullback_pullback t.G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (Out.specOf g) = pullback.fst t.G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (P.U.LG.L.pull (pullback.fst t'.G.hom (Out.jK R') ≫
      (Iso.refl t'.G).hom.left ≫ pullback.fst t.G.hom (Out.specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB P.A.isLB gA) eA.hom.left)
      (pull_isLB P.U.LG.isLB _)
      ((LBIso.symm tA).chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl) (Geo.Tor.chartPullPull (P.A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ P.U.gen.inv.left)
      (chartPullLinComb P.A.L gA (fun _ => eA.hom.left) (fun _ => P.U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame P.U.LG.L _ (fun _ => pullback.fst t.G.hom (Out.jK R)) _ _ fun _ => ?_) P.U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr P.bundle m₀.cm m₀.lin (hbc.trans hm₀.symm) (e := Out.specOf g) m₀.base.symm
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R I hR P.D
  have hgen : (Out.specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (Out.specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl t'.G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI P.D P.A t.G t.semi P.U Wo hψ hgen t'.G
    (Iso.refl _) mR A' dA eA mE wA PP' wL heL gL rL
  obtain ⟨oA', hoA'⟩ := hO _ _ (spMap gam) P.A A' gA gpA tA (𝓞 E) P.oA
  have actA : ∀ x, (P.oA.act x).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R')).map (t'.act.toRingAct.act x) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply (gpA.comp gpG).1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R')).map (t'.act.toRingAct.act x)).left ≫ pullback.fst t'.G.hom (Out.jK R') =
          pullback.fst t'.G.hom (Out.jK R') ≫ (t'.act.act x).left := pullback.lift_fst _ _ _
      have a₂ : (t'.act.act x).left ≫ pullback.fst t.G.hom (spMap g) =
          pullback.fst t.G.hom (spMap g) ≫ (t.act.act x).left := pullback.lift_fst _ _ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₂, Over.comp_left, Category.assoc,
        ← Category.assoc (oA'.act x).left, hoA', Category.assoc, actA, ← Category.assoc, ← heA]
      simp only [Category.assoc]
    · rw [Over.w, Over.w]
  obtain ⟨mod', oD', xl, el, lin', w0'⟩ := h5.oLinBaseChange R R' I I' hR hR' g P.D P.A t.G P.U t'.G (Iso.refl _) mR
    A' D' hD U' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct
    (fun x => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA
  let P' : PELUnif I' t' := { D := D', mod := mod', oD := oD', A := A', oA := oA', U := U', bundle := hLG, lin := lin'
                              w0 := w0' H.w0 P.w0 }
  exact ⟨t', m₀, P', hD, Iso.refl _, mR, hPU, hm₀.trans hbc.symm, xl, el⟩

theorem exists_genericPt {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t)
    {F : Type} [Field F] [Algebra (FractionRing R) F] (z : Sp F ⟶ t.G.left)
    (hz : z ≫ t.G.hom = jFK (R := R) F ≫ jK R) :
    ∃ x : TFK (R := R) F ⟶ P.A.A, x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = z := by
  let z₁ : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj t.G :=
    Over.homMk (pullback.lift z (jFK (R := R) F) hz) (pullback.lift_snd _ _ _)
  refine ⟨z₁ ≫ P.U.gen.hom, ?_⟩
  have hgi : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  show (z₁.left ≫ P.U.gen.hom.left) ≫ _ = _
  rw [Category.assoc, ← Category.assoc P.U.gen.hom.left, hgi, Category.id_comp]
  exact pullback.lift_fst _ _ _

theorem jFK_comm {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'} {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (g r))) :
    jFK (R := R') F ≫ jK R' ≫ spMap g = jFK (R := R) F ≫ jK R :=
  ((congrArg (jFK (R := R') F ≫ ·) (spMap_comp g _).symm).trans (spMap_comp _ _).symm).trans
    ((congrArg spMap (RingHom.ext fun r => (hF r).symm)).trans (spMap_comp _ _))

theorem pmaps_of_isPullGtF {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg g D D'} {F : Type} [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F] {p : GtPtF D F} {p' : GtPtF D' F} (h : IsPullGtF g hD F p p') {χ' : D'.X} {χ : D.X}
    (e : hD.xe χ' = χ) :
    (∀ k, DegPre.gtφ D' F p'.b χ' k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf g) =
      𝟙 _ ≫ DegPre.gtφ D F p.b χ k) ∧ PMaps hD.w _ _ _ (p'.s χ') (p.s χ) (𝟙 _) := by
  subst e
  obtain ⟨hψ, hm⟩ := h.2 χ'
  exact ⟨hψ, (maps_iff hD.w _ _ _ (p'.s χ') (p.s (hD.xe χ')) (𝟙 _) _
    (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩

theorem pmaps_psi' {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg g D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F] (hj : jFK (R := R') F ≫ jK R' ≫ spMap g = jFK (R := R) F ≫ jK R) {χ' : D'.X} {χ : D.X}
    (e : hD.xe χ' = χ) :
    (jFK (R := R') F ≫ D'.xK χ') ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf g) = 𝟙 _ ≫ jFK (R := R) F ≫ D.xK χ ∧
    PMaps hD.w (K := PUnit) (fun _ => jFK (R := R') F ≫ D'.xK χ') (fun _ => jFK (R := R) F ≫ D.xK χ)
      (fun _ => -1) (LB.pullGen _ _ _ (D'.psi χ') (jFK (R := R') F))
      (LB.pullGen _ _ _ (D.psi χ) (jFK (R := R) F)) (𝟙 _) := by
  subst e
  refine ⟨?_, pmaps_psi hD F hj χ'⟩
  have hx : D'.xK χ' ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf g) =
      jK R' ≫ specOf g ≫ (D.c (hD.xe χ')).left := by
    rw [← hD.c_pr, ← Category.assoc]; rfl
  rw [Category.id_comp, Category.assoc, hx, ← Category.assoc (jK R'), ← Category.assoc]
  exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)

theorem act_proj {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg g D D') {s : D.P.A ⟶ D.P.A} {s' : D'.P.A ⟶ D'.P.A}
    (h : s' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf g)).map s) :
    s'.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf g) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf g)) ≫ s.left := by
  have e₀ := congrArg (fun z => z.left ≫ pullback.fst D.P.A.hom (specOf g)) h
  have e₂ : ((Over.pullback (specOf g)).map s).left ≫ pullback.fst D.P.A.hom (specOf g) = pullback.fst _ _ ≫ s.left :=
    pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc, e₂] at e₀
  simpa only [Category.assoc] using e₀

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b}
  {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V} {f : O' →+* R} {u : R}
  {χ : Sp R ⟶ Y.X} {t : SAB H (Sp R)} {g : R →+* V}

set_option maxHeartbeats 1600000 in

theorem toA_down (hL : Laws) (hR : AdmBase R I) (hV : AdmBase V I') (m : SABMap t Y.t χ) (P : PELUnif I t)
    (W : ArcWit Y a I' (g.comp f) (g u) (spMap g ≫ χ)) (hD : IsPullDeg g P.D.toPre W.P.D.toPre)
    (bc : W.t.G ≅ (Over.pullback (specOf g)).obj t.G) (mbc : IsMonHom bc.hom) (hPU : IsPullUnif g hD bc P.U W.P.U)
    (hm : W.m.φ = (bc.hom.left ≫ pullback.fst t.G.hom (specOf g)) ≫ m.φ)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F]
    [Algebra (FractionRing O') F]
    (hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g r))) (uF : F)
    (ha : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x)))
    (hu : uF = algebraMap (FractionRing R) F (algebraMap R _ u))
    (yF : Sp F ⟶ Xo.XF c) (hyF : yF ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ) (k : ℕ) (p₀ : QkPt a.D₀ (FractionRing O') k)
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G)
    (hσ : (k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
      (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v))
    (q₀ : QkPt a.D₀ F k) (q : QkPt P.D.toPre F k) (q' : QkPt W.P.D.toPre F k) (x : TFK (R := R) F ⟶ P.A.A)
    (e₁ : QkExt (algebraMap _ F) p₀ q₀) (h₁ : q'.y = hD.xe.symm q.y) (h₂ : IsPullGtF g hD F q.g q'.g)
    (e₂ : q'.y = W.e q₀.y) (e₃ : ∀ z, GenRel W.w (q'.g.s (W.e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / k)))
    (e₄ : x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = yF ≫ σ.left ≫ Y.m.φ) : P.ToA F k q x := by
  have hj := jFK_comm hF
  have w₀ : (x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ≫ t.G.hom =
      (jFK (R := V) F ≫ jK V) ≫ specOf g := by
    have w₁ : P.U.gen.inv.left ≫ pullback.snd t.G.hom (jK R) = P.A.A.hom := Over.w P.U.gen.inv
    have w₂ : x.left ≫ P.A.A.hom = jFK (R := R) F := Over.w x
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% w₁, reassoc_of% w₂, Category.assoc]
    exact hj.symm
  obtain ⟨x', hx'⟩ := exists_genericPt W.P (F := F) (pullback.lift _ _ w₀ ≫ bc.inv.left) (by
    rw [Category.assoc, Over.w bc.inv]; exact pullback.lift_snd _ _ _)
  have hb : bc.inv.left ≫ bc.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hx : x'.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst t.G.hom (specOf g) =
      x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) := by
    rw [reassoc_of% hx', reassoc_of% hb]; exact pullback.lift_fst _ _ _
  have hk : 1 ≤ k := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact l.A_pos
    · exact le_trans (by norm_num) l.three_le
  refine qkToAk_of_baseChange hL.globalFns hL.secBaseChange R V I I' hR hV g P.D P.A t.G P.U W.t.G bc mbc W.P.A W.P.D hD
    W.P.U hPU F hF k hk q x q' x' h₁ h₂ hx ?_
  refine (W.spec.2.2.2.2.2 F uF (fun x => (ha x).trans (hF (f x))) (hu.trans (hF u))).2 yF ?_ k p₀ σ hσ q₀ q' x' e₁ e₂ e₃ ?_
  · rw [hyF, reassoc_of% hj]
  · rw [hm, ← e₄, Category.assoc, reassoc_of% hx]

theorem exists_span {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} (hL : L.IsLB) (hL' : L'.IsLB)
    (hL'' : L''.IsLB) {Φ : X' ⟶ X} {Φ'' : X'' ⟶ X} (r : X'' ⟶ X') (e : r ≫ Φ = Φ'') {w : LB.Iso L' (L.pull Φ)}
    {w'' : LB.Iso L'' (L.pull Φ'')} (hw : PGen w) (hw'' : PGen w'') :
    ∃ v : LB.Iso L'' (L'.pull r), PGen v ∧ ∀ {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)}
      {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
      {t' : LB.Gen (LB.LinComb L' φ' ε)} {t'' : LB.Gen (LB.LinComb L'' φ'' ε)} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
      {h'' : Y'' ⟶ Y}, h'' = h' ≫ h → (∀ k, φ'' k ≫ r = h' ≫ φ' k) → PMaps w φ' φ ε t' t h →
      PMaps w'' φ'' φ ε t'' t h'' → PMaps v φ'' φ' ε t'' t' h' := by
  subst e
  obtain ⟨v, T⟩ := exists_cancel hL w w'' hw hw'' hL' hL''
  refine ⟨v, T.pgen_cancel hL hw hw'', fun e hc m m'' => ?_⟩
  subst e
  exact T.pmaps_cancel hL hc m m''

theorem pmaps_rig' {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
  (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig

set_option maxHeartbeats 3200000 in

theorem exists_match (hL : Laws) (h2 : Laws2) (hR : AdmBase R I) (hV : AdmBase V I') (hginj : Function.Injective g)
    (m : SABMap t Y.t χ) (P : PELUnif I t) (W : ArcWit Y a I' (g.comp f) (g u) (spMap g ≫ χ)) (hD : IsPullDeg g P.D.toPre W.P.D.toPre)
    (bc : W.t.G ≅ (Over.pullback (specOf g)).obj t.G) (mbc : IsMonHom bc.hom) (hPU : IsPullUnif g hD bc P.U W.P.U)
    (hm : W.m.φ = (bc.hom.left ≫ pullback.fst t.G.hom (specOf g)) ≫ m.φ)
    (el : letI := H.starRing; ∀ x, W.P.oD.onB.act x ≫ hD.e.hom =
      hD.e.hom ≫ (Over.pullback (specOf g)).map (P.oD.onB.act x))
    {S : Type} [CommRing S] [IsDomain S] {h : R →+* S} (N : DegPre S) [Module (𝓞 E) N.X]
    (oN : letI := H.starRing; N.OAct (𝓞 E)) (hN : IsPullDeg h P.D.toPre N)
    (elN : letI := H.starRing; ∀ x, oN.onB.act x ≫ hN.e.hom =
      hN.e.hom ≫ (Over.pullback (specOf h)).map (P.oD.onB.act x))
    (e : a.D₀.X ≃ₗ[𝓞 E] N.X) (hxe : ∀ y, hN.xe (e y) = hD.xe (W.e y)) (i : V →+* S) (hi : Function.Injective i)
    (hig : h = i.comp g) :
    ∃ (r : N.P.A.left ⟶ W.P.D.toPre.P.A.left)
      (he : eSec N.P.A ≫ r ≫ W.φ = spMap (h.comp f) ≫ eSec a.D₀.P.A) (w : LB.Iso N.P.L (a.D₀.P.L.pull (r ≫ W.φ))),
      r ≫ W.P.D.toPre.P.A.hom = N.P.A.hom ≫ spMap i ∧
      r ≫ hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g) =
        hN.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf h) ∧
      Match a (h.comp f) (h u) N oN (r ≫ W.φ) he w e ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing S) F]
        [Algebra (FractionRing O') F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
          algebraMap (FractionRing S) F (algebraMap S (FractionRing S) (h r))) → ∀ uF : F,
        (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
        uF = algebraMap (FractionRing R) F (algebraMap R _ u) →
        ∀ yF : Sp F ⟶ Xo.XF c, yF ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ →
        ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        ∀ (q₀ : QkPt a.D₀ F l.M) (p : QkPt P.D.toPre F l.M) (q : QkPt N F l.M) (x : TFK (R := R) F ⟶ P.A.A),
          QkExt (algebraMap _ F) (a.eta v) q₀ → q.y = hN.xe.symm p.y → IsPullGtF h hN F p.g q.g → q.y = e q₀.y →
          (∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / l.M))) →
          x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = yF ≫ (Y.oF.eta v).left ≫ Y.m.φ →
          P.ToA F l.M p x := by
  letI := H.starRing
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  have gD := pull_grp hD
  have gN := pull_grp hN
  have hs : spMap h = spMap i ≫ spMap g := by rw [hig, spMap_comp]
  have a₁ := fun x => act_proj hD (el x)
  have a₂ := fun x => act_proj hN (elN x)
  have c₁ := hD.c_pr
  have c₂ := hN.c_pr
  have z₁ := hD.he
  have z₂ := hN.he
  set Φ := hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g) with hΦ
  set Ψ := hN.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf h) with hΨ
  obtain ⟨r, r₁, r₂⟩ : ∃ r : N.P.A.left ⟶ W.P.D.toPre.P.A.left, r ≫ Φ = Ψ ∧
      r ≫ W.P.D.toPre.P.A.hom = N.P.A.hom ≫ spMap i :=
    ⟨gD.1.lift Ψ (N.P.A.hom ≫ spMap i) (by rw [gN.1.w, hs, Category.assoc]), gD.1.lift_fst _ _ _, gD.1.lift_snd _ _ _⟩
  have gr : IsGrpPullback N.P.A W.P.D.toPre.P.A (spMap i) r := gD.cancel (gN.congr hs r₁.symm) r₂
  have er : eSec N.P.A ≫ r = spMap i ≫ eSec W.P.D.toPre.P.A := (cubeMapOf gr).e_comm
  obtain ⟨v, gv, hv⟩ := exists_span P.D.toPre.P.isLB W.P.D.toPre.P.isLB N.P.isLB r r₁ ((isGen_iff hD.w).1 hD.w_gen)
    ((isGen_iff hN.w).1 hN.w_gen)
  have g0 := (isGen_iff W.w).1 s2
  obtain ⟨w, T⟩ := exists_comp W.P.D.toPre.P.isLB W.w v g0 gv a.D₀.P.isLB N.P.isLB
  have hs' : spMap (h.comp f) = spMap i ≫ spMap (g.comp f) := by rw [hig, ← spMap_comp]; try rfl
  have he : eSec N.P.A ≫ r ≫ W.φ = spMap (h.comp f) ≫ eSec a.D₀.P.A := by
    rw [reassoc_of% er, W.he, hs', Category.assoc]
  have cr : ∀ y, (N.c (e y)).left ≫ r = spMap i ≫ (W.P.D.toPre.c (W.e y)).left := fun y => by
    apply gD.1.hom_ext
    · rw [Category.assoc, r₁, c₂, Category.assoc, c₁, hxe, ← Category.assoc]
      exact congrArg (· ≫ _) hs
    · rw [Category.assoc, r₂, Category.assoc, Over.w, ← Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  let gam : FractionRing V →+* FractionRing S :=
    IsFractionRing.lift (g := (algebraMap S (FractionRing S)).comp i) ((IsFractionRing.injective S _).comp hi)
  have hgam : ∀ x, gam (algebraMap V _ x) = algebraMap S _ (i x) := fun x => IsFractionRing.lift_algebraMap _ x
  refine ⟨r, he, w, r₂, r₁, ⟨(gr.comp s1).congr hs'.symm rfl,
    (isGen_iff w).2 (T.pgen_comp W.P.D.toPre.P.isLB g0 gv), ?_, fun x => ?_, fun y => ?_, fun F _ _ _ _ uF ha hu y => ?_⟩,
    fun F _ _ _ _ _ hF uF ha hu yF hyF v₀ hv₀ q₀ p q x e₁ h₁ h₂ e₂ e₃ e₄ => ?_⟩
  · have r₀ := (maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap (g.comp f)) _
      (rigPull_le W.φ (spMap (g.comp f)) W.he a.D₀.P.L) (fun _ => rfl)).1 s3
    have r₃ := T.pmaps_comp W.P.D.toPre.P.isLB (fun _ => er) r₀ (hv hs (fun _ => er) (pmaps_rig' hD) (pmaps_rig' hN))
    rw [← hs'] at r₃
    exact (maps_iff w _ (fun _ => eSec a.D₀.P.A) _ N.rig a.D₀.rig (spMap (h.comp f)) _
      (rigPull_le (r ≫ W.φ) (spMap (h.comp f)) he a.D₀.P.L) (fun _ => rfl)).2 r₃
  · have k : (oN.onB.act x).left ≫ r = r ≫ (W.P.oD.onB.act x).left := by
      apply gD.1.hom_ext
      · exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) r₁).trans (a₂ x))).trans (((Category.assoc _ _ _).trans
          ((congrArg (r ≫ ·) (a₁ x)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) r₁)))).symm)
      · rw [Category.assoc, r₂, Category.assoc, Over.w, r₂, ← Category.assoc, Over.w]
    rw [reassoc_of% k, s4 x, Category.assoc]
  · rw [reassoc_of% (cr y), s5 y, hs', Category.assoc]
  · letI : Algebra (FractionRing V) F := ((algebraMap (FractionRing S) F).comp gam).toAlgebra
    have hF : ∀ x : V, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) x) =
        algebraMap (FractionRing S) F (algebraMap S (FractionRing S) (i x)) := fun x =>
      congrArg (algebraMap (FractionRing S) F) (hgam x)
    have k := (s6 F uF (fun x => (ha x).trans (by rw [hF, hig]; rfl)) (hu.trans (by rw [hF, hig]; rfl))).1 y
    have hj := jFK_comm hF
    have hc : (jFK (R := S) F ≫ N.xK (e y)) ≫ r = 𝟙 _ ≫ jFK (R := V) F ≫ W.P.D.toPre.xK (W.e y) := by
      show (jFK (R := S) F ≫ jK S ≫ (N.c (e y)).left) ≫ r =
        𝟙 _ ≫ jFK (R := V) F ≫ jK V ≫ (W.P.D.toPre.c (W.e y)).left
      rw [Category.id_comp, Category.assoc, Category.assoc, cr, reassoc_of% hj]
    obtain ⟨G, _, G₁, G₂⟩ : ∃ (_ : Algebra (FractionRing R) F) (_ : True),
        jFK (R := V) F ≫ jK V ≫ spMap g = jFK (R := R) F ≫ jK R ∧
        jFK (R := S) F ≫ jK S ≫ spMap h = jFK (R := R) F ≫ jK R := by
      let ga : FractionRing R →+* F := IsFractionRing.lift
        (g := (algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp g))
        ((algebraMap (FractionRing V) F).injective.comp ((IsFractionRing.injective V _).comp hginj))
      letI := ga.toAlgebra
      have k₁ : ∀ x : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) x) =
          algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g x)) := fun x =>
        IsFractionRing.lift_algebraMap _ x
      exact ⟨ga.toAlgebra, trivial, jFK_comm k₁, jFK_comm fun x => (k₁ x).trans (by rw [hF, hig]; rfl)⟩
    exact (genRel_transfer T W.P.D.toPre.P.isLB N.P.isLB (fun _ => hc) (hv (Category.id_comp _).symm (fun _ => hc)
      (pmaps_psi' hD G₁ rfl).2 (pmaps_psi' hN G₂ (hxe y)).2) _ _).1 k
  · letI : Algebra (FractionRing V) F := ((algebraMap (FractionRing S) F).comp gam).toAlgebra
    have hF₁ : ∀ x : V, algebraMap (FractionRing V) F (algebraMap V (FractionRing V) x) =
        algebraMap (FractionRing S) F (algebraMap S (FractionRing S) (i x)) := fun x =>
      congrArg (algebraMap (FractionRing S) F) (hgam x)
    have hF₂ : ∀ x : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) x) =
        algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (g x)) := fun x =>
      (hF x).trans (by rw [hF₁, hig]; rfl)
    have hj := jFK_comm hF₁
    obtain ⟨τ, hτ, -⟩ := exists_qk_pull_equiv hL h2 R V g P.D.toPre W.P.D.toPre hD P.D.tau_bimult W.P.D.tau_bimult F hF₂ l.M
    obtain ⟨k₁, k₂⟩ := (hτ p _).1 rfl
    refine toA_down hL hR hV m P W hD bc mbc hPU hm F hF₂ uF ha hu yF hyF l.M (a.eta v₀) (Y.oF.eta v₀)
      (Or.inr ⟨rfl, v₀, hv₀, HEq.rfl, rfl⟩) q₀ p (τ p) x e₁ k₁ k₂ ?_ (fun z => ?_) e₄
    · rw [k₁, AddEquiv.symm_apply_eq, ← hxe, ← e₂, h₁, AddEquiv.apply_symm_apply]
    · obtain ⟨m₁, m₂⟩ := pmaps_of_isPullGtF k₂ (χ' := W.e z) rfl
      obtain ⟨n₁, n₂⟩ := pmaps_of_isPullGtF h₂ (hxe z)
      have hc : ∀ k, DegPre.gtφ N F q.g.b (e z) k ≫ r = 𝟙 _ ≫ DegPre.gtφ W.P.D.toPre F (τ p).g.b (W.e z) k := fun k => by
        have u₁ : ∀ {T : Type} [CommRing T] [IsDomain T] [Algebra (FractionRing T) F] (D : DegPre T)
            (b : TF (R := T) F ⟶ D.P.A) (x : D.X), DegPre.gtφ D F b x k ≫ D.P.A.hom = jFK (R := T) F ≫ jK T :=
          fun D b x => by fin_cases k <;> exact Over.w _
        apply gD.1.hom_ext
        · rw [Category.assoc, r₁, Category.assoc]
          exact (n₁ k).trans ((m₁ k).symm.trans (Category.id_comp _).symm)
        · rw [Category.assoc, r₂, ← Category.assoc, u₁, Category.assoc, Category.assoc, u₁, hj]
          exact (Category.id_comp _).symm
      exact (genRel_transfer T W.P.D.toPre.P.isLB N.P.isLB hc (hv (Category.id_comp _).symm hc m₂ n₂) _ _).2 (e₃ z)

end GlobalTheory.ArcDataDescent

namespace GlobalTheory.ArcDataDescent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {W₀ : ValuationSubring ℂ}
  {Y : Model Xo c (c.V W₀).subtype} {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O'] {b : c.V W₀ →+* O'}
  {a : ArcIn D l (c.V W₀).subtype O' b}
  {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V} {f : O' →+* R} {u : R}
  {χ : Sp R ⟶ Y.X} {t : SAB H (Sp R)} {g : R →+* V}

set_option maxHeartbeats 3200000 in

theorem agree (hL : Laws) (h2 : Laws2) (h5 : Laws5) (hR : AdmBase R I) (hV : AdmBase V I') (hf : Function.Injective f)
    (hg : Function.Injective g) (y : Sp (FractionRing R) ⟶ Xo.XF c) (hy : y ≫ Y.j = jK R ≫ χ) (m : SABMap t Y.t χ)
    (P : PELUnif I t) (hT : P.TorsionIso) (W : ArcWit Y a I' (g.comp f) (g u) (spMap g ≫ χ))
    (hD : IsPullDeg g P.D.toPre W.P.D.toPre)
    (bc : W.t.G ≅ (Over.pullback (specOf g)).obj t.G) (mbc : IsMonHom bc.hom) (hPU : IsPullUnif g hD bc P.U W.P.U)
    (hm : W.m.φ = (bc.hom.left ≫ pullback.fst t.G.hom (specOf g)) ≫ m.φ)
    (xl : ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y)
    (el : letI := H.starRing; ∀ x, W.P.oD.onB.act x ≫ hD.e.hom =
      hD.e.hom ≫ (Over.pullback (specOf g)).map (P.oD.onB.act x))
    (S : Type) [Field S] (i₁ i₂ : V →+* S) (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂)
    (x₁ x₂ : Sp S ⟶ W.P.D.toPre.P.A.left) (hx₁ : x₁ ≫ W.P.D.toPre.P.A.hom = spMap i₁)
    (hx₂ : x₂ ≫ W.P.D.toPre.P.A.hom = spMap i₂)
    (hx : x₁ ≫ hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g) =
      x₂ ≫ hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g)) : x₁ ≫ W.φ = x₂ ≫ W.φ := by
  letI := H.starRing
  have gD := pull_grp hD
  have k₀ : ∀ (x : Sp S ⟶ W.P.D.toPre.P.A.left) (i : V →+* S), x ≫ W.P.D.toPre.P.A.hom = spMap i →
      (x ≫ hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf g)) ≫ P.D.toPre.P.A.hom = spMap (i.comp g) :=
    fun x i e => by rw [Category.assoc, gD.1.w, reassoc_of% e, spMap_comp]
  obtain ⟨h, e₁⟩ : ∃ h : R →+* S, h = i₁.comp g := ⟨_, rfl⟩
  have e₂ : h = i₂.comp g := e₁.trans (congrArg (fun q => q.hom)
    (Spec.map_injective ((k₀ x₁ i₁ hx₁).symm.trans ((congrArg (· ≫ _) hx).trans (k₀ x₂ i₂ hx₂)))))
  have hh : Function.Injective h := by rw [e₁]; exact hi₁.comp hg
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R I hR P.D
  have hgen : (specOf h).base (genericPoint (Spec (CommRingCat.of S))) ∈ Wo := by
    have : (specOf h).base (genericPoint (Spec (CommRingCat.of S))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective h hh)
    rw [this]; exact hWo
  obtain ⟨N, hN, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange R S h P.D.toPre Wo hψ hgen
  obtain ⟨modN, oN, xlN, elN⟩ := exists_oAct_of_isPullDeg hL.globalFns R S h P.D.toPre N hN (𝓞 E) P.oD
  have bN := TauPull.tauBimult_pull hL.globalFns hN P.D.tau_bimult
  let xD : W.P.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  let xN : N.X ≃ₗ[𝓞 E] P.D.toPre.X := { hN.xe with map_smul' := xlN }
  let e : a.D₀.X ≃ₗ[𝓞 E] N.X := (W.e.trans xD).trans xN.symm
  have hxe : ∀ y, hN.xe (e y) = hD.xe (W.e y) := fun y => xN.apply_symm_apply _
  obtain ⟨r₁, he₁, w₁, a₁, b₁, M₁, L₁⟩ := exists_match hL h2 hR hV hg m P W hD bc mbc hPU hm el N oN hN elN e hxe i₁ hi₁ e₁
  obtain ⟨r₂, he₂, w₂, a₂, b₂, M₂, L₂⟩ := exists_match hL h2 hR hV hg m P W hD bc mbc hPU hm el N oN hN elN e hxe i₂ hi₂ e₂
  obtain ⟨hφ, -, -⟩ := MatchRigid.rigid hL h2 E H D l c W₀ O' b a S (h.comp f) (h u) (hh.comp hf) N oN _ _ he₁ he₂ w₁ w₂ e e
    bN M₁ M₂ (fun _ => rfl) (fun F _ _ _ _ uF ha hu v hv q₀ q₁ q₂ hq₀ hy₁ hy₂ hg₁ hg₂ => by
      let ga : FractionRing R →+* F := IsFractionRing.lift
        (g := (algebraMap (FractionRing S) F).comp ((algebraMap S (FractionRing S)).comp h))
        ((algebraMap (FractionRing S) F).injective.comp ((IsFractionRing.injective S _).comp hh))
      letI := ga.toAlgebra
      have hF : ∀ x : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) x) =
          algebraMap (FractionRing S) F (algebraMap S (FractionRing S) (h x)) := fun x =>
        IsFractionRing.lift_algebraMap _ x
      obtain ⟨τ, hτ, hτ', -⟩ := exists_qk_pull_equiv hL h2 R S h P.D.toPre N hN P.D.tau_bimult bN F hF l.M
      obtain ⟨p₁, rfl⟩ := τ.surjective q₁
      obtain ⟨p₂, rfl⟩ := τ.surjective q₂
      have hyF : (jFK (R := R) F ≫ y) ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ := by rw [Category.assoc, hy]
      have hσw : (Y.oF.eta v).left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w (Y.oF.eta v)
      have hmw : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.jQ ≫ pullback.fst _ _ := Y.m.cart.1.w
      have hc0 : ((jFK (R := R) F ≫ y) ≫ (Y.oF.eta v).left ≫ Y.m.φ) ≫ Y.t.G.hom = (jFK (R := R) F ≫ jK R) ≫ χ := by
        simp only [Category.assoc]
        rw [hmw, reassoc_of% hσw]
        simpa only [Category.assoc, Model.j] using hyF
      obtain ⟨x, hx⟩ := exists_genericPt P (m.cart.1.lift _ _ hc0) (m.cart.1.lift_snd _ _ hc0)
      have hx' : x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ =
          (jFK (R := R) F ≫ y) ≫ (Y.oF.eta v).left ≫ Y.m.φ := by
        rw [reassoc_of% hx]; exact m.cart.1.lift_fst _ _ hc0
      have A₁ := L₁ F hF uF (fun x => (ha x).trans (hF _).symm) (hu.trans (hF _).symm) _ hyF v hv q₀ p₁ _ x hq₀
        ((hτ p₁ _).1 rfl).1 ((hτ p₁ _).1 rfl).2 hy₁ hg₁ hx'
      have A₂ := L₂ F hF uF (fun x => (ha x).trans (hF _).symm) (hu.trans (hF _).symm) _ hyF v hv q₀ p₂ _ x hq₀
        ((hτ p₂ _).1 rfl).1 ((hτ p₂ _).1 rfl).2 hy₂ hg₂ hx'
      obtain ⟨fn, f₁, -, f₂, -⟩ := hT F l.M (le_trans (by norm_num) l.three_le)
      exact (hτ' p₁ p₂).1 ((f₂ p₁ p₂).1 (((f₁ p₁ x).1 A₁).symm.trans ((f₁ p₂ x).1 A₂))))
  have gN := pull_grp hN
  have w₀ := (k₀ x₁ i₁ hx₁).trans ((congrArg spMap e₁.symm).trans (Category.id_comp _).symm)
  have z₁ := gN.1.lift_fst _ _ w₀
  have z₂ := gN.1.lift_snd _ _ w₀
  have c₁ : gN.1.lift _ _ w₀ ≫ r₁ = x₁ := gD.1.hom_ext (by rw [Category.assoc, b₁, z₁])
    (by rw [Category.assoc, a₁, reassoc_of% z₂, hx₁])
  have c₂ : gN.1.lift _ _ w₀ ≫ r₂ = x₂ := gD.1.hom_ext (by rw [Category.assoc, b₂, z₁, hx])
    (by rw [Category.assoc, a₂, reassoc_of% z₂, hx₂])
  rw [← c₁, Category.assoc, hφ, ← Category.assoc, c₂]

end GlobalTheory.ArcDataDescent
end
