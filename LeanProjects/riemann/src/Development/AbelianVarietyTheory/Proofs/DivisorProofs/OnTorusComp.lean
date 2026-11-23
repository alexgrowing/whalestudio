import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbacksMatchTorsionPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackDvrTorsionPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTorsionRigidOverModuliFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.UInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def OverU {X S : Scheme.{0}} (u : SAB H X) (A : PolAV S) (oA : letI := H.starRing; A.OAct (𝓞 E)) (y : S ⟶ X)
    (α : A.A.left ⟶ u.G.left) : Prop :=
  letI := H.starRing
  IsGrpPullback A.A u.G y α ∧ (∀ a, (oA.act a).left ≫ α = α ≫ (u.act.act a).left) ∧
    CechPic.pull α (CechPic.cls u.PP.L u.PP.isLB) = CechPic.cls A.L A.isLB

theorem cls_sabMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    CechPic.pull m.φ (CechPic.cls t.PP.L t.PP.isLB) = CechPic.cls t'.PP.L t'.PP.isLB := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ((CechPic.cls_eq_iff t'.PP.isLB (pull_isLB t.PP.isLB m.φ)).2 ⟨w, hw⟩).symm

theorem OverU.comp {X X' S : Scheme.{0}} {u : SAB H X} {u' : SAB H X'} {A : PolAV S} {oA} {y : S ⟶ X} {α}
    (h : OverU u A oA y α) {f : X ⟶ X'} (m : SABMap u u' f) : OverU u' A oA (y ≫ f) (α ≫ m.φ) :=
  ⟨h.1.comp m.cart, fun a => by rw [← Category.assoc, h.2.1, Category.assoc, m.act, Category.assoc],
    by rw [CechPic.pull_comp, cls_sabMap m, h.2.2]⟩

theorem OverU.cancel {X X' S : Scheme.{0}} {u : SAB H X} {u' : SAB H X'} {A : PolAV S} {oA} {y : S ⟶ X} {f : X ⟶ X'} {α}
    (h : OverU u' A oA (y ≫ f) α) (m : SABMap u u' f) : ∃ π, OverU u A oA y π ∧ π ≫ m.φ = α := by
  let π : A.A.left ⟶ u.G.left := m.cart.1.lift α (A.A.hom ≫ y) (by rw [h.1.1.w, Category.assoc])
  have e₁ : π ≫ m.φ = α := m.cart.1.lift_fst _ _ _
  have e₂ : π ≫ u.G.hom = A.A.hom ≫ y := m.cart.1.lift_snd _ _ _
  refine ⟨π, ⟨m.cart.cancel (h.1.congr rfl e₁.symm) e₂, fun a => ?_, ?_⟩, e₁⟩
  · apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      erw [e₁, m.act]
      rw [← Category.assoc π]
      erw [e₁]
      exact h.2.1 a
    · rw [Category.assoc, Category.assoc, e₂, Over.w, e₂, ← Category.assoc, Over.w]
  · rw [← cls_sabMap m, ← CechPic.pull_comp, e₁, h.2.2]

theorem overU_gen {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) :
    OverU t P.A P.oA (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := by
  letI := H.starRing
  have := P.U.gen_hom
  refine ⟨?_, fun x => ?_, ?_⟩
  · have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  · have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  · have e : CechPic.pull P.U.gen.hom.left (CechPic.cls P.A.L P.A.isLB) =
        CechPic.pull (pullback.fst t.G.hom (jK R)) (CechPic.cls P.U.LG.L P.U.LG.isLB) :=
      (CechPic.cls_eq_iff (pull_isLB P.A.isLB _) (pull_isLB P.U.LG.isLB _)).2 P.U.ext
    rw [P.bundle] at e
    rw [CechPic.pull_comp, ← e, ← CechPic.pull_comp, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, CechPic.pull_id]

theorem onTorus_comp {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} {Da Db Dc : DegData R J}
    {Aa Ab Ac : PolAV (Sp (FractionRing R))} {Ga Gb Gc : Over (Sp R)}
    [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb] [GrpObj Gc] [IsCommMonObj Gc]
    {Ua : UnifPre J Da Aa Ga} {Ub : UnifPre J Db Ab Gb} {Uc : UnifPre J Dc Ac Gc} {f : Ga ⟶ Gb} {g : Gb ⟶ Gc} {k k'}
    (hf : OnTorus Ua Ub f k) (hg : OnTorus Ub Uc g k') : OnTorus Ua Uc (f ≫ g) (fun χ => k (k' χ)) := by
  intro e
  obtain ⟨t, ht, hi⟩ := hf e
  obtain ⟨s, hs, hj⟩ := hg e
  refine ⟨t ≫ s, torusHomOf_comp' ht hs, ?_⟩
  rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]

theorem over_comp {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} {Da Db Dc : DegData R J}
    {Aa Ab Ac : PolAV (Sp (FractionRing R))} {Ga Gb Gc : Over (Sp R)}
    [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb] [GrpObj Gc] [IsCommMonObj Gc]
    {Ua : UnifPre J Da Aa Ga} {Ub : UnifPre J Db Ab Gb} {Uc : UnifPre J Dc Ac Gc} {f : Ga ⟶ Gb} {g : Gb ⟶ Gc} {c c'}
    (hf : Over₀ Ua Ub f c) (hg : Over₀ Ub Uc g c') : Over₀ Ua Uc (f ≫ g) (c ≫ c') := by
  intro e
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg e, ← Category.assoc, hf e, Category.assoc]

set_option maxHeartbeats 1000000 in

theorem two_match {X : Scheme.{0}} (u : SAB H X) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hc : IsAdicComplete (maximalIdeal V) V) {t₁ t₂ : SAB H (Sp V)} (P₁ : PELUnif (maximalIdeal V) t₁)
    (P₂ : PELUnif (maximalIdeal V) t₂) (y : Sp (FractionRing V) ⟶ X) (α₁ : P₁.A.A.left ⟶ u.G.left)
    (α₂ : P₂.A.A.left ⟶ u.G.left) (hO₁ : OverU u P₁.A P₁.oA y α₁) (hO₂ : OverU u P₂.A P₂.oA y α₂) :
    ∃ (b : P₁.D.toPre.P.A ⟶ P₂.D.toPre.P.A) (φ : P₁.D.toPre.X ≃+ P₂.D.toPre.X),
      Match P₁.D.toPre P₂.D.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ (∀ (x : 𝓞 E) y, φ (x • y) = x • φ y) ∧
      (letI := H.starRing; ∀ x : 𝓞 E, P₁.oD.onB.act x ≫ b = b ≫ P₂.oD.onB.act x) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ (p₁ : QkPt P₁.D.toPre (AlgebraicClosure (FractionRing V)) k)
        (p₂ : QkPt P₂.D.toPre (AlgebraicClosure (FractionRing V)) k)
        (x₁ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ P₁.A.A)
        (x₂ : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ P₂.A.A),
        QkToAkU P₁.U.toUnifPre (AlgebraicClosure (FractionRing V)) k p₁ x₁ →
        QkToAkU P₂.U.toUnifPre (AlgebraicClosure (FractionRing V)) k p₂ x₂ → x₁.left ≫ α₁ = x₂.left ≫ α₂ →
        QImg b φ p₁ p₂ := by
  letI := H.starRing
  obtain ⟨D₁, o₁, A₁, oA₁, U₁, bu₁, l₁, ww₁⟩ := P₁
  obtain ⟨D₂, o₂, A₂, oA₂, U₂, bu₂, l₂, ww₂⟩ := P₂
  dsimp only at *
  have hG₁ := t₁.semi
  have hG₂ := t₂.semi
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨cA, hcA, hα⟩ := grpPullback_iso hO₁.1 hO₂.1
  haveI := U₁.gen_hom
  haveI := U₂.gen_hom
  haveI := hcA
  let e : (Over.pullback (jK V)).obj t₁.G ≅ (Over.pullback (jK V)).obj t₂.G := U₁.gen ≪≫ cA ≪≫ U₂.gen.symm
  haveI : IsMonHom e.hom := by
    show IsMonHom (U₁.gen.hom ≫ cA.hom ≫ U₂.gen.inv)
    infer_instance
  obtain ⟨a, ⟨ha, hae⟩, -⟩ :=
    GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing V) t₁.G t₂.G hG₁ hG₂ e
  have gen : Gen₀ U₁.toUnifPre U₂.toUnifPre a.hom cA.hom := by
    show (Over.pullback (jK V)).map a.hom ≫ U₂.gen.hom = U₁.gen.hom ≫ cA.hom
    rw [show (Over.pullback (jK V)).map a.hom = e.hom from hae]
    simp [e]
  have hL : LBIso A₁.L (A₂.L.pull cA.hom.left) :=
    (CechPic.cls_eq_iff A₁.isLB (pull_isLB A₂.isLB _)).1 (by
      rw [CechPic.cls_pull A₂.isLB, ← hO₂.2.2, ← CechPic.pull_comp, hα, hO₁.2.2])
  have hlbA : LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull
      (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left) :=
    GlobalTheory.LamPull.lbIso_lam_pull (isGrpPullback_of_iso cA) A₂.isLB A₁.isLB hL
      ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hactA : ∀ x, oA₁.act x ≫ cA.hom = cA.hom ≫ oA₂.act x := fun x => by
    apply Over.OverMorphism.ext
    apply hO₂.1.1.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hα, hO₂.2.1, hO₁.2.1, ← Category.assoc, hα]
    · rw [Over.w, Over.w]
  have hactG : ∀ x, t₁.act.toRingAct.act x ≫ a.hom = a.hom ≫ t₂.act.toRingAct.act x := fun x => by
    have := t₁.act.toRingAct.hom x
    have := t₂.act.toRingAct.hom x
    have h₀ : (Over.pullback (jK V)).map (t₁.act.toRingAct.act x ≫ a.hom) =
        (Over.pullback (jK V)).map (a.hom ≫ t₂.act.toRingAct.act x) := by
      rw [← cancel_mono U₂.gen.hom, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, l₂.ext, gen,
        ← Category.assoc, l₁.ext, ← Category.assoc, gen, Category.assoc, hactA, Category.assoc]
    exact (GlobalTheory.SemiAbExtDomain.existsUnique_hom_extension_generic (FractionRing V) t₁.G t₂.G hG₁ hG₂
      ((Over.pullback (jK V)).map (a.hom ≫ t₂.act.toRingAct.act x))).unique ⟨inferInstance, h₀⟩ ⟨inferInstance, rfl⟩
  obtain ⟨b, h, hbi, lin, coord⟩ := GlobalTheory.T.uniformisedGroupIso_abelianPart_character_isos V (maximalIdeal V) hA D₁ A₁ t₁.G U₁.toUnifPre D₂ A₂ t₂.G U₂.toUnifPre a ha
  have hb : IsMonHom b := lin.2.1
  have hov : Over₀ U₁.toUnifPre U₂.toUnifPre a.hom b := lin.2.2.1
  have uq := fun x => over₀_onTorus_unique V (maximalIdeal V) hA D₁ D₂ A₁ A₂ t₁.G t₂.G U₁.toUnifPre U₂.toUnifPre
    (a.hom ≫ t₂.act.toRingAct.act x)
  have hhl : ∀ (x : 𝓞 E) χ, h (star x • χ) = star x • h χ := fun x χ =>
    congrFun ((uq x).2 (fun χ => h.toAddMonoidHom (star x • χ)) (fun χ => star x • h.toAddMonoidHom χ) (onTorus_comp lin.2.2.2 (fun e => l₂.i_lin e x))
      (hactG x ▸ onTorus_comp (fun e => l₁.i_lin e x) lin.2.2.2)) χ
  have hbl : ∀ x : 𝓞 E, o₁.onB.act x ≫ b = b ≫ o₂.onB.act x := fun x =>
    (uq x).1 _ _ (hactG x ▸ over_comp (fun e => l₁.q_lin e x) hov) (over_comp hov (fun e => l₂.q_lin e x))
  have hlbG := GlobalTheory.T.mumfordBundleIso_genericFibre_extends_uniformisedGroups V (maximalIdeal V) hA D₁ A₁ t₁.G U₁.toUnifPre D₂ A₂ t₂.G U₂.toUnifPre hG₁ a.hom cA.hom ha hcA
    gen hlbA
  have hlbB := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart V hA D₁ D₂ A₁ A₂ t₁.G t₂.G hG₁ hG₂ U₁ U₂ a.hom a.hom b b ha ha hb hb hov hov hlbG
  have hnrm : ∀ χ, ∃ u : LB.Gen (CmpLB D₁.toPre D₂.toPre b (h.toAddMonoidHom χ) χ), Nrm u :=
    fun χ => (coord χ).imp fun _ => And.left
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
  have key := GlobalTheory.Mum.Two.KeyDvr.main V hc ϖ hϖ (AlgebraicClosure (FractionRing V)) v hv D₁ D₂ A₁ A₂ t₁.G t₂.G hG₁ hG₂
    U₁ U₂ a.hom cA.hom b h.toAddMonoidHom hcA gen lin coord h.injective
  obtain ⟨E', eG, eA, -, eh, -⟩ :=
    (GlobalTheory.IntEnd.exists_nsmul_and_neg GlobalTheory.firstFiveLaws V (maximalIdeal V) hA D₁ A₁ t₁.G hG₁ U₁).1 1
  have H₁ : LBIso (cubeLB t₁.G ![fst t₁.G t₁.G ≫ E'.aG, snd t₁.G t₁.G] U₁.LG.L)
      (cubeLB t₁.G ![fst t₁.G t₁.G, snd t₁.G t₁.G ≫ E'.aG] U₁.LG.L) := by
    rw [eG, pow_one, Category.comp_id, Category.comp_id]
    exact GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_linComb U₁.LG.isLB _ _)
  have H₂ : LBIso (cubeLB A₂.A ![fst A₁.A A₁.A ≫ cA.hom, snd A₁.A A₁.A ≫ cA.hom] A₂.L)
      (cubeLB A₁.A ![fst A₁.A A₁.A ≫ E'.aA, snd A₁.A A₁.A ≫ 𝟙 A₁.A] A₁.L) := by
    rw [eA, pow_one]
    exact lbIso_cube_of_lam A₁.isLB A₂.isLB cA.hom hlbA
  obtain ⟨φ', hφ', hhφ'⟩ := GlobalTheory.Mum.Two.periods_of_key V (maximalIdeal V) hA D₁ D₂ A₁ A₂ t₁.G t₂.G hG₁ hG₂ U₁ U₂ a.hom
    cA.hom b h.toAddMonoidHom hcA gen lin coord E' E' H₁ H₂ _ key
  have hφe : ∀ y₀, φ' y₀ = h.symm y₀ := fun y₀ => h.injective (by
    show h (φ' y₀) = h (h.symm y₀)
    rw [h.apply_symm_apply]
    exact (hhφ' y₀).trans (by rw [eh, one_smul]))
  have hM : Match D₁.toPre D₂.toPre b h.symm (AlgebraicClosure (FractionRing V)) := by
    refine ⟨hb, hbi, hlbB, hnrm, fun y₀ g₀ hy => ?_⟩
    obtain ⟨g', h1, h2⟩ := hφ' y₀ g₀ hy
    exact ⟨g', h1, hφe y₀ ▸ h2⟩
  refine ⟨b, h.symm, hM, fun x y => h.injective ?_, hbl, fun k hk p₁ p₂ x₁ x₂ hq₁ hq₂ hx => ?_⟩
  · have := hhl (star x) (h.symm y)
    rw [star_star] at this
    rw [this, h.apply_symm_apply, h.apply_symm_apply]
  obtain ⟨g', hg', -⟩ :=
    (GlobalTheory.Mum.Two.act_two_hom V D₁.toPre D₂.toPre b h.toAddMonoidHom hb hnrm (AlgebraicClosure (FractionRing V))).1 p₁.g
  obtain ⟨p', rfl, hp'⟩ := key k hk p₁ x₁ hq₁ g' hg'
  have hxx : x₁ ≫ cA.hom = x₂ := by
    apply Over.OverMorphism.ext
    apply hO₂.1.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hα, hx]
    · rw [Over.comp_left, Category.assoc, Over.w, Over.w, Over.w]
  refine ⟨p', GlobalTheory.T.torsionPairImage_latticePart_eq_of_match V (maximalIdeal V) hA D₁ D₂ b h.symm _ hM k p₁ p' hg', hg',
    (GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv V (maximalIdeal V) hA D₂ A₂ t₂.G U₂ hG₂ _ k hk).2 p' p₂ x₂ (hxx ▸ hp') hq₂⟩

open GlobalTheory.TorusExt GlobalTheory.Balanced in
set_option maxHeartbeats 1000000 in

theorem pull_tors {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] [CommRing V] [IsDomain V] [IsLocalRing V]
    (hR : AdmBase R (maximalIdeal R)) (hV : AdmBase V (maximalIdeal V)) {t : SAB H (Sp R)} (P : PELUnif (maximalIdeal R) t)
    (f : R →+* V) (hf : Function.Injective f) [IsLocalHom f] :
    ∃ (t' : SAB H (Sp V)) (m : SABMap t' t (spMap f)) (P' : PELUnif (maximalIdeal V) t')
      (hD : IsPullDeg f P.D.toPre P'.D.toPre), (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf f)).map (P.oD.onB.act x)) ∧
      ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F]
        [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k →
        ∀ (p₀ : QkPt P.D.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ P.A.A), QkToAkU P.U.toUnifPre F₀ k p₀ x₀ →
        ∃ (p : QkPt P'.D.toPre F k) (x : TFK (R := V) F ⟶ P'.A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧
          QkToAkU P'.U.toUnifPre F k p x ∧
          x.left ≫ (P'.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V)) ≫ m.φ =
            spMap j ≫ x₀.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have hI : (maximalIdeal R).map f ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit f a ha
  obtain ⟨t', m, P', hD, bc, hbc, hU, hm, xl, el⟩ := GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange
    h4.unifBaseChange h5 hR hV t P f hf hI
  refine ⟨t', m, P', hD, xl, el, ?_⟩
  intro F₀ _ _ _ F _ _ _ j hj k hk p₀ x₀ hx₀
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  let σ : F₀ →ₐ[FractionRing R] F := { j with commutes' := fun _ => rfl }
  have hB := P.D.tau_bimult
  have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (f r)) := hj
  let p₁ : QkPt P.D.toPre F k := qkExt hB σ.toRingHom (hom_comp σ) p₀
  let x₁ : TFK (R := R) F ⟶ P.A.A := extPt σ x₀
  have hx₁ : QkToAkU P.U.toUnifPre F k p₁ x₁ := (GlobalTheory.T.qkToAkU_iff_galois_equivariant GlobalTheory.firstFiveLaws R _ hR P.D P.A t.G t.semi P.U F₀ F σ k hk
    p₀ p₁ x₀ x₁ ((qkExt_iff hB _ (hom_comp σ) _ _).2 rfl) rfl).1 hx₀
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.exists_qk_pull_equiv h1 h2 R V f P.D.toPre P'.D.toPre hD hB P'.D.tau_bimult F hF k
  obtain ⟨hy, hg⟩ := (hτ p₁ _).1 rfl
  have w : toG P.U.toUnifPre x₁ ≫ t.G.hom = (jFK (R := V) F ≫ jK V) ≫ spMap f := by
    rw [toG_over]
    simp only [jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hF
  obtain ⟨x, hx⟩ := exists_toG P'.U.toUnifPre (m.cart.1.lift _ _ w) (m.cart.1.lift_snd _ _ _)
  have hx' : x.left ≫ (P'.U.gen.inv.left ≫ pullback.fst t'.G.hom (jK V)) ≫ m.φ = toG P.U.toUnifPre x₁ := by
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) hx).trans (m.cart.1.lift_fst _ _ _)
  refine ⟨τ p₁, x, hy, ⟨p₁.g, (eq_gtExt_iff σ.toRingHom (hom_comp σ) _ _).1 rfl, hg⟩, ?_, ?_⟩
  · exact h5.qkBaseChange R V _ _ hR hV f P.D P.A t.G P.U t'.G bc hbc P'.A P'.D hD P'.U hU F hF k hk p₁ x₁ _ x hy hg
      (by rw [← hm]; simpa only [toG, Category.assoc] using hx') hx₁
  · rw [hx']
    simp only [toG, Category.assoc, x₁, extPt, Over.homMk_left]

theorem pair_match : ∀ {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (_ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap f₁ → κ₂ ≫ jK R = jK V ≫ spMap f₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∃ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ ∧ Ext f₂ j₂ ∧ Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ (∀ (x : 𝓞 E) (y : C.P.D.toPre.X), hD₂.xe (φ (hD₁.xe.symm (x • y))) = x • hD₂.xe (φ (hD₁.xe.symm y))) ∧ (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) ∧ (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) := by
  intro Dw l Xo c φ0 R _ _ _ hR C V _ _ _ _ hV f₁ f₂ hf₁ hf₂ l₁ l₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have := hR.2
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have hn : 1 ≤ l.M' := level_pos l
  obtain ⟨tK, ⟨n₁⟩, ⟨n₂⟩⟩ := C.gen
  obtain ⟨t₁, m₁, P₁, hD₁, xl₁, el₁, tr₁⟩ := pull_tors hR.1 hA C.P f₁ hf₁
  obtain ⟨t₂, m₂, P₂, hD₂, xl₂, el₂, tr₂⟩ := pull_tors hR.1 hA C.P f₂ hf₂
  obtain ⟨π₁, o₁, e₁⟩ := OverU.cancel (hκ₁ ▸ (overU_gen P₁).comp m₁) n₁
  obtain ⟨π₂, o₂, e₂⟩ := OverU.cancel (hκ₂ ▸ (overU_gen P₂).comp m₂) n₁
  obtain ⟨π₀, o₀, e₀⟩ := OverU.cancel (y := 𝟙 _) (f := jK R) (by rw [Category.id_comp]; exact overU_gen C.P) n₁
  have O₁ := o₁.comp n₂
  have O₂ := o₂.comp n₂
  rw [← Category.assoc, ← hy, Category.assoc] at O₂
  obtain ⟨b, φ, hM, hφ, hbl, hQ⟩ := two_match Xo.univ.t V hV P₁ P₂ _ _ _ O₁ O₂
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.TInj.Pair.exists_ext f₁ hf₁
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.TInj.Pair.exists_ext f₂ hf₂
  refine ⟨P₁.D, P₂.D, hD₁, hD₂, j₁, j₂, b, φ, hj₁, hj₂, hM, fun x y => ?_, fun p₀ => ?_,
    fun x => ⟨_, _, el₁ x, el₂ x, hbl x⟩⟩
  · rw [← xl₂, ← hφ]
    congr 2
    apply hD₁.xe.injective
    rw [xl₁, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  obtain ⟨x₀, hx₀, hpow⟩ := (GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv R _ hR.1 C.P.D C.P.A C.t.G C.P.U C.t.semi (AlgebraicClosure (FractionRing R))
    l.M' hn).1 p₀
  obtain ⟨p₁, x₁, hy₁, hT₁, hq₁, hc₁⟩ := tr₁ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₁ hj₁ _ hn p₀ x₀ hx₀
  obtain ⟨p₂, x₂, hy₂, hT₂, hq₂, hc₂⟩ := tr₂ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₂ hj₂ _ hn p₀ x₀ hx₀
  have s₁ := GlobalTheory.TInj.Pair.sq f₁ j₁ hj₁ κ₁ hκ₁
  have s₂ := GlobalTheory.TInj.Pair.sq f₂ j₂ hj₂ κ₂ hκ₂
  have : Mono (jK R) := GlobalTheory.GenericBundleDescent.mono_jK R
  have : Mono n₁.φ := (MorphismProperty.monomorphisms _).of_isPullback n₁.cart.1.flip (.infer_property _)
  have a₁ : x₁.left ≫ π₁ = spMap j₁ ≫ x₀.left ≫ π₀ := by
    rw [← cancel_mono n₁.φ, Category.assoc, e₁, hc₁, Category.assoc, Category.assoc, e₀]
  have a₂ : x₂.left ≫ π₂ = spMap j₂ ≫ x₀.left ≫ π₀ := by
    rw [← cancel_mono n₁.φ, Category.assoc, e₂, hc₂, Category.assoc, Category.assoc, e₀]
  have O₀ := (o₀.comp n₂).1
  have hz : pushHom O₀ (TFK (R := R) (AlgebraicClosure (FractionRing R))) x₀ ^ l.M' = 1 := by rw [← map_pow, hpow, map_one]
  let z : Over.mk ((jFK (R := R) (AlgebraicClosure (FractionRing R)) ≫ C.y) ≫ pullback.fst _ _) ⟶
      Over.mk ((TFK (R := R) (AlgebraicClosure (FractionRing R))).hom ≫ 𝟙 _ ≫ C.y ≫ pullback.fst _ _) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans ((congrArg _ (Category.id_comp _)).trans (Category.assoc _ _ _).symm))
  have key := GlobalTheory.T.universal_torsion_rigid_over_moduli_fieldPoint Xo c φ0 _ _ (jFK (R := R) (AlgebraicClosure (FractionRing R)) ≫ C.y)
    (z ≫ pushHom O₀ _ x₀) (by rw [← MonObj.comp_pow, hz, MonObj.comp_one]) (spMap j₁) (spMap j₂)
    (by rw [← Category.assoc, ← Category.assoc, s₁, s₂, Category.assoc, Category.assoc, hy])
  refine ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ _ hn p₁ p₂ x₁ x₂ hq₁ hq₂ ?_⟩
  rw [← Category.assoc, ← Category.assoc, a₁, a₂]
  have hl : (z ≫ pushHom O₀ _ x₀).left = x₀.left ≫ π₀ ≫ n₂.φ := Category.id_comp _
  rw [hl] at key
  simpa only [Category.assoc] using key

end GlobalTheory.UInj
