import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothOfRelativeDimensionOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPsiOnBasicOpen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUSpecialises

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcSpecialise

open NumberField ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArcPull (om)
open GlobalTheory.ArcTransport (unitStk GtRel)

theorem qkExt_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F₀ F₁ F₂ : Type} [Field F₀] [Field F₁]
    [Field F₂] [Algebra (FractionRing R) F₀] [Algebra (FractionRing R) F₁] [Algebra (FractionRing R) F₂]
    {f : F₀ →+* F₁} {g : F₁ →+* F₂} {k : ℕ} {p₀ : QkPt D F₀ k} {p₁ : QkPt D F₁ k} {p₂ : QkPt D F₂ k}
    (h : QkExt f p₀ p₁) (h' : QkExt g p₁ p₂) : QkExt (g.comp f) p₀ p₂ := by
  refine ⟨h'.1.trans h.1, ?_, fun χ => corr_of_val D.P.isLB fun (y : Sp F₂) J hJ => ?_⟩
  · exact h'.2.1.trans ((congrArg (spMap g ≫ ·) h.2.1).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ p₀.g.b.left) (spMap_comp f g).symm)))
  · refine (val_corr hJ (h'.2.2 χ) _).trans ((val_pull hJ _ _ _).trans ((val_corr hJ (h.2.2 χ) _).trans
      ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))))
    exact congrArg (fun q => val (p₀.g.s χ) q y J) ((Category.assoc _ _ _).trans
      (congrArg (𝟙 (Sp F₂) ≫ ·) (spMap_comp f g).symm))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R R' : Type} [CommRing R]
  [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'} {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}

set_option maxHeartbeats 1600000 in

theorem level_specialises (hL : Laws) (hL₂ : Laws2) (hT : TwistBaseChangeStatement) (hR : AdmBase R I)
    (hR' : AdmBase R' I') (W : ArcWit Y a I f u χ) (hχ : χ ≫ Y.s = spMap f ≫ spMap b) {g : R →+* R'}
    {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {bc : G' ≅ (Over.pullback (specOf g)).obj W.t.G}
    (mbc : IsMonHom bc.hom) {A' : PolAV (Sp (FractionRing R'))} {D' : DegData R' I'}
    {hD : IsPullDeg g W.P.D.toPre D'.toPre} {U' : Unif I' D' A' G'} (hPU : IsPullUnif g hD bc W.P.U U')
    {w' : LB.Iso D'.toPre.P.L (a.D₀.P.L.pull (PsiEvenPull.proj hD ≫ W.φ))} (T : Tri W.w hD.w w')
    {F' : Type} [Field F'] [Algebra (FractionRing R') F'] [Algebra (FractionRing O') F'] (σ : R →+* PowerSeries F')
    (hσ : Function.Injective σ)
    (h₁ : ∀ x, σ (f x) = PowerSeries.C (algebraMap (FractionRing O') F' (algebraMap O' _ x)))
    (h₂ : ∀ r, PowerSeries.constantCoeff (σ r) = algebraMap (FractionRing R') F' (algebraMap R' _ (g r)))
    {uF : F'} (huF : uF = algebraMap (FractionRing R') F' (algebraMap R' _ (g u))) (h0 : uF ≠ 0)
    (yF : Sp F' ⟶ Xo.XF c) (hyF : yF ≫ Y.j = jFK (R := R') F' ≫ jK R' ≫ spMap g ≫ χ)
    (k : ℕ) (p₀ : QkPt a.D₀ (FractionRing O') k) (s : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G)
    (hs : (k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ s = Y.oF.etaA v) ∨
      (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        HEq p₀ (a.eta v) ∧ s = Y.oF.eta v))
    (q₀ : QkPt a.D₀ F' k) (q : QkPt D'.toPre F' k) (x : TFK (R := R') F' ⟶ A'.A)
    (e₁ : QkExt (algebraMap _ F') p₀ q₀) (e₂ : hD.xe q.y = W.e q₀.y)
    (e₃ : ∀ z z', hD.xe z' = W.e z → GenRel w' (q.g.s z') (q₀.g.s z) (uF ^ (a.be q₀.y z / k)))
    (e₄ : x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫
      pullback.fst W.t.G.hom (specOf g) ≫ W.m.φ = yF ≫ s.left ≫ Y.m.φ) :
    QkToAkU U'.toUnifPre F' k q x := by
  obtain ⟨s1, s2, -, -, s5, s6⟩ := W.spec
  have hk : 1 ≤ k := by
    rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact l.A_pos
    · exact le_trans (by norm_num) l.three_le
  have hkM : k ∣ l.M' := by
    rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Nat.dvd_lcm_right _ _
    · exact Nat.dvd_lcm_left _ _
  obtain ⟨π, hπ⟩ : ∃ π : PowerSeries F' →+* F', π = PowerSeries.constantCoeff := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : F' →+* PowerSeries F', κ = PowerSeries.C := ⟨_, rfl⟩
  rw [← hκ] at h₁
  rw [← hπ] at h₂
  have πκ : ∀ t, π (κ t) = t := fun t => by rw [hπ, hκ]; exact PowerSeries.constantCoeff_C t
  have loc : IsLocalHom π := ⟨fun t ht => by rw [hπ] at ht; exact PowerSeries.isUnit_iff_constantCoeff.2 ht⟩
  obtain ⟨F, _, _, ιF, hιF⟩ : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (ιF : PowerSeries F' →+* F),
      Function.Injective ιF :=
    ⟨AlgebraicClosure (FractionRing (PowerSeries F')), inferInstance, inferInstance,
      (algebraMap (FractionRing (PowerSeries F')) _).comp (algebraMap (PowerSeries F') _),
      (algebraMap (FractionRing (PowerSeries F')) (AlgebraicClosure (FractionRing (PowerSeries F')))).injective.comp
        (IsFractionRing.injective (PowerSeries F') (FractionRing (PowerSeries F')))⟩
  letI : Algebra (FractionRing R) F := (IsFractionRing.lift (g := ιF.comp σ) (hιF.comp hσ)).toAlgebra
  letI : Algebra (FractionRing O') F := ((ιF.comp κ).comp (algebraMap (FractionRing O') F')).toAlgebra
  have hRF : ∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = ιF (σ r) := fun r =>
    IsFractionRing.lift_algebraMap _ r
  have hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
      algebraMap (FractionRing R) F (algebraMap R _ (f x)) := fun x => by rw [hRF, h₁]; rfl
  have hρ : spMap ιF ≫ spMap σ = jFK (R := R) F ≫ jK R :=
    (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun r => (hRF r).symm)).trans (spMap_comp _ _))
  have hπσ : spMap π ≫ spMap σ = jFK (R := R') F' ≫ jK R' ≫ spMap g :=
    (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext h₂)).trans ((spMap_comp _ _).trans
      (congrArg (jFK (R := R') F' ≫ ·) (spMap_comp g _))))
  have hπκ : spMap π ≫ spMap κ = 𝟙 _ :=
    (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext πκ : _ = RingHom.id F')).trans (Spec.map_id _))
  have hσf : spMap σ ≫ spMap f = spMap κ ≫ jFK (R := O') F' ≫ jK O' :=
    (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext h₁)).trans ((spMap_comp _ _).trans
      (congrArg (spMap κ ≫ ·) (spMap_comp _ _))))
  let ρ : TF (R := R) F ⟶ Over.mk (specOf σ) := Over.homMk (spMap ιF) hρ

  obtain ⟨yS, y₁, y₂⟩ := exists_lift_open π κ hπκ (spMap σ ≫ χ) yF
    (by rw [hyF, reassoc_of% hπσ]) (by
      rw [Category.assoc, hχ, reassoc_of% hσf, reassoc_of% hπκ])
  have sw : s.left ≫ Y.m.φ ≫ Y.t.G.hom = Y.j := by
    have e : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
    have e' : s.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w s
    rw [e, ← Category.assoc, e', Category.id_comp]
  obtain ⟨xS, hxS⟩ : ∃ xS : Over.mk (specOf σ) ⟶ W.t.G, xS.left ≫ W.m.φ = yS ≫ s.left ≫ Y.m.φ :=
    ⟨Over.homMk (W.m.cart.1.lift (yS ≫ s.left ≫ Y.m.φ) (spMap σ) (by
      rw [Category.assoc, Category.assoc, sw, y₁])) (W.m.cart.1.lift_snd _ _ _), W.m.cart.1.lift_fst _ _ _⟩
  have xw : xS.left ≫ W.t.G.hom = spMap σ := Over.w xS
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : TFK (R := R) F ⟶ W.P.A.A,
      x₀.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (jK R) = ρ.left ≫ xS.left := by
    let z : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj W.t.G :=
      Over.homMk (pullback.lift (ρ.left ≫ xS.left) (jFK (R := R) F) (Over.w (ρ ≫ xS))) (pullback.lift_snd _ _ _)
    refine ⟨z ≫ W.P.U.gen.hom, ?_⟩
    have hgi : W.P.U.gen.hom.left ≫ W.P.U.gen.inv.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    show (z.left ≫ W.P.U.gen.hom.left) ≫ _ = _
    rw [Category.assoc, ← Category.assoc W.P.U.gen.hom.left, hgi, Category.id_comp]
    exact pullback.lift_fst _ _ _
  have hx : x.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫
      pullback.fst W.t.G.hom (specOf g) = specOf π ≫ xS.left := by
    apply W.m.cart.1.hom_ext
    · refine Eq.trans ?_ (e₄.trans ?_)
      · simp only [Category.assoc]
      · rw [← y₂, Category.assoc, ← hxS, Category.assoc]
    · have a1 : bc.hom.left ≫ pullback.snd W.t.G.hom (specOf g) = G'.hom := Over.w bc.hom
      have a2 : U'.gen.inv.left ≫ pullback.snd G'.hom (jK R') = A'.A.hom := Over.w U'.gen.inv
      have a3 : x.left ≫ A'.A.hom = jFK (R := R') F' := Over.w x
      rw [Category.assoc (specOf π), xw, hπσ]
      simp only [Category.assoc, pullback.condition, pullback.condition_assoc, reassoc_of% a1, reassoc_of% a2,
        reassoc_of% a3]

  obtain ⟨uS, huS⟩ : IsUnit (σ u) := loc.1 _ (by rw [h₂, ← huF]; exact h0.isUnit)
  obtain ⟨q₁, hq₁, -⟩ := TorusExt.existsUnique_qkExt a.bimult (ιF.comp κ) rfl q₀
  have hv : ((Units.map ιF.toMonoidHom uS : Fˣ) : F) = algebraMap (FractionRing R) F (algebraMap R _ u) := by
    rw [hRF, ← huS]; rfl
  obtain ⟨p₁, hp₁, hp₁'⟩ := exists_partner hL.globalFns W (Units.map ιF.toMonoidHom uS) hF hv hkM q₁
  obtain ⟨gp, gb, gv⟩ := exists_gtPt hL.globalFns s1 s2 (e := W.e.toAddEquiv) s5 q₀.g (Over.mk (specOf σ)) (spMap κ) hσf
    (fun z => unitOn (uS ^ (a.be q₀.y z / k))) (fun y z => by
      rw [map_add, Int.add_ediv_of_dvd_left (dvd_be a hkM _ _), zpow_add]
      exact map_mul (Units.map _) _ _)
  have pull : GtPt.IsPullF F ρ.left gp p₁.g := by
    obtain ⟨c₁, c₂, c₃⟩ := hq₁
    rw [spMap_comp] at c₂ c₃
    exact isPullF_of_genRel s1 s2 gb gv (spMap ιF) hρ c₂ c₃ (fun z y => by
      rw [c₁, ← map_zpow]
      exact gm_unitOn_spMap ιF _ y) hp₁'
  have toA : QkToAkU W.P.U.toUnifPre F k p₁ x₀ :=
    (s6 F _ hF hv).2 (spMap ιF ≫ yS) (by rw [Category.assoc, y₁, reassoc_of% hρ]) k p₀ s hs q₁ p₁ x₀
      (qkExt_trans e₁ hq₁) hp₁ (fun z => by
        have := hp₁' z
        rw [Units.val_zpow_eq_zpow_val] at this
        exact this) (by
        refine Eq.trans ?_ ((congrArg (· ≫ W.m.φ) hx₀).trans ?_)
        · simp only [Category.assoc]
        · rw [Category.assoc, hxS, Category.assoc]; rfl)

  have gD := pull_grp hD
  have hb : q.g.b.left ≫ PsiEvenPull.proj hD = specOf π ≫ gp.b.left := by
    apply s1.1.hom_ext
    · have b₀ : q.g.b.left ≫ PsiEvenPull.proj hD ≫ W.φ = q₀.g.b.left := (e₃ 0 0 (by rw [map_zero, map_zero])).1 2
      refine (Category.assoc _ _ _).trans (b₀.trans (Eq.symm ((Category.assoc _ _ _).trans ?_)))
      exact (congrArg (spMap π ≫ ·) gb).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ q₀.g.b.left) hπκ).trans (Category.id_comp _)))
    · have b₁ : q.g.b.left ≫ D'.toPre.P.A.hom = jFK (R := R') F' ≫ jK R' := Over.w q.g.b
      have b₂ : gp.b.left ≫ W.P.D.toPre.P.A.hom = spMap σ := Over.w gp.b
      refine (Category.assoc _ _ _).trans ((congrArg (q.g.b.left ≫ ·) gD.1.w).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ spMap g) b₁).trans ((Category.assoc _ _ _).trans (hπσ.symm.trans ?_)))))
      exact ((Category.assoc _ _ _).trans (congrArg (spMap π ≫ ·) b₂)).symm
  refine _root_.GlobalTheory.qkToAkU_specialises hL hL₂ hT R R' I I' hR hR' g W.P.D W.P.A W.t.G W.P.U G' bc mbc A' D' hD U' hPU W.t.semi
    (PowerSeries F') σ F ιF hιF ρ rfl F' π loc h₂ k hk gp p₁ q pull ?_ hb (fun z' => ?_) xS x₀ x hx₀ hx toA
  · rw [hp₁, hq₁.1, ← e₂, AddEquiv.symm_apply_apply]
  · obtain ⟨z, hz⟩ := W.e.surjective (hD.xe z')
    have hπu : ((Units.map π.toMonoidHom (uS ^ (a.be q₀.y z / k)) : F'ˣ) : F') = uF ^ (a.be q₀.y z / k) := by
      rw [map_zpow, Units.val_zpow_eq_zpow_val, huF, ← h₂, ← huS]; rfl
    refine pmaps_of_genRel T ((isGen_iff _).1 s2) ((isGen_iff _).1 hD.w_gen) a.D₀.P.isLB W.P.D.toPre.P.isLB
      D'.toPre.P.isLB (gp.isGen _) (q₀.g.isGen z) (q.g.isGen z') (spMap π)
      (gtφT_push gD (hD.c_pr z') (T := Over.mk (specOf σ)) (T' := TF (R := R') F') (spMap π) hb)
      (Units.map π.toMonoidHom (uS ^ (a.be q₀.y z / k))) (fun y J J' hJ hJ' => ?_) (hπu ▸ e₃ z z' hz.symm)
    exact (congrArg₂ (· * ·) (gm_unitOn_spMap π _ y).symm
      (congrArg (fun r => val (q₀.g.s z) r y J) hπκ.symm)).trans (gv z _ hz _ (spMap π) y J J' hJ hJ')

set_option maxHeartbeats 1600000 in

theorem specialise (hL : Laws) (hL₂ : Laws2) (hT : TwistBaseChangeStatement) (hU : UnifBaseChangeSt) (h5 : Laws5)
    (hR : AdmBase R I) (hR' : AdmBase R' I') (hf : Function.Injective f) (W : ArcWit Y a I f u χ)
    (hχ : χ ≫ Y.s = spMap f ≫ spMap b) (g : R →+* R') (hI : I.map g ≤ I') (hu : g u ≠ 0)
    (hj : Set.range (jK R' ≫ spMap g ≫ χ) ⊆ Set.range Y.j)
    (hS : ∀ (F : Type) [Field F] (i : R' →+* F), Function.Injective i → ∃ σ : R →+* PowerSeries F,
      Function.Injective σ ∧ (∀ x, σ (f x) = PowerSeries.C (i (g (f x)))) ∧
      ∀ r, PowerSeries.constantCoeff (σ r) = i (g r)) :
    Nonempty (ArcWit Y a I' (g.comp f) (g u) (spMap g ≫ χ)) := by
  letI := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (spMap g) W.t
  let t' : SAB H (Sp R') := ⟨(Over.pullback (spMap g)).obj W.t.G, IsSemiAbelian.pullback _ W.t.G W.t.semi,
    OAct.pullback _ W.t.G W.t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' W.t (spMap g) := m₁
  have hm₀ : m₀.φ = pullback.fst W.t.G.hom (spMap g) := hm₁
  obtain ⟨m', hm'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ W.m m₀
  have dimG : SmoothOfRelativeDimension W.P.A.g W.t.G.hom := by
    have := W.t.semi.smooth
    have := W.t.semi.geomConnected
    refine GenericDim.smoothOfRelativeDimension_of_generic R W.t.G _ ?_
    have := W.P.U.gen_hom
    exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (isGrpPullback_of_iso W.P.U.gen).1
      W.P.A.smoothDim
  have dimG' : SmoothOfRelativeDimension W.P.A.g t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) dimG
  obtain ⟨A', eA, oA', dA, mE, tA, extA₀⟩ := exists_polAV_genericFibre E H D l Xo c O β Y R' _ t' m' hj _ dimG'
  have hbc : (Iso.refl t'.G).hom.left ≫ pullback.fst W.t.G.hom (specOf g) = pullback.fst W.t.G.hom (spMap g) :=
    Category.id_comp _
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr W.P.bundle m₀.cm m₀.lin (hbc.trans hm₀.symm) (e := specOf g) m₀.base.symm
  have wA : LBIso (A'.L.pull eA.hom.left) (W.P.U.LG.L.pull (pullback.fst t'.G.hom (jK R') ≫
      (Iso.refl t'.G).hom.left ≫ pullback.fst W.t.G.hom (specOf g))) :=
    LBIso.trans (pull_isLB A'.isLB _) (pull_isLB t'.PP.isLB _) (pull_isLB W.P.U.LG.isLB _) tA
      (LBIso.chartPull (h := pullback.fst t'.G.hom (jK R')) (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame W.P.U.LG.L _ (fun _ => (Iso.refl t'.G).hom.left ≫ pullback.fst W.t.G.hom (specOf g)) _ _
          fun _ => rfl) ⟨wL, gL⟩)
  have hu₀ : u ≠ 0 := fun h => hu (by rw [h, map_zero])
  obtain ⟨ψW, hψW⟩ := arcWit_psiOn_basicOpen E H D l Xo c O β Y O' b a R I f hf u hu₀ χ W
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈
      (PrimeSpectrum.basicOpen u : (Spec (CommRingCat.of R)).Opens) := by
    rw [genericPoint_eq_bot_of_affine]
    exact hu
  have mR : IsMonHom (Iso.refl t'.G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI W.P.D W.P.A W.t.G W.t.semi W.P.U _ ⟨ψW⟩ hgen t'.G
    (Iso.refl _) mR A' dA eA mE wA PP' wL heL gL rL
  have extA : ∀ x, (Over.pullback (jK R')).map (t'.act.toRingAct.act x) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act x := by
    intro x
    rw [hgenU]
    exact extA₀ x
  obtain ⟨mod', oD', xl, el, lin', w0'⟩ := h5.oLinBaseChange R R' I I' hR hR' g W.P.D W.P.A W.t.G W.P.U t'.G (Iso.refl _) mR
    A' D' hD U' hPU (𝓞 E) W.P.oD W.P.oA W.t.act.toRingAct W.P.lin t'.act.toRingAct
    (fun x => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA
  let P' : PELUnif I' t' := { D := D', mod := mod', oD := oD', A := A', oA := oA', U := U', bundle := hLG, lin := lin'
                              w0 := w0' H.w0 W.P.w0 }
  obtain ⟨s1, s2, s3, s4, s5, -⟩ := W.spec
  set Φ := hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf g) with hΦ
  have gD := (isGen_iff hD.w).1 hD.w_gen
  have g0 := (isGen_iff W.w).1 s2
  obtain ⟨w', T⟩ := exists_comp W.P.D.toPre.P.isLB W.w hD.w g0 gD a.D₀.P.isLB D'.toPre.P.isLB
  have he' : eSec D'.toPre.P.A ≫ Φ ≫ W.φ = spMap (g.comp f) ≫ eSec a.D₀.P.A := by
    rw [← Category.assoc, hD.he, Category.assoc, W.he, spMap_comp, Category.assoc]
  let xe' : D'.toPre.X ≃ₗ[𝓞 E] W.P.D.toPre.X := { hD.xe with map_smul' := xl }
  have gpB : IsGrpPullback D'.toPre.P.A W.P.D.toPre.P.A (spMap g) Φ := pull_grp hD
  have hxe : ∀ y, hD.xe (xe'.symm (W.e y)) = W.e y := fun y => xe'.apply_symm_apply _
  refine ⟨⟨t', m', P', Φ ≫ W.φ, he', w', W.e.trans xe'.symm, (gpB.comp s1).congr (spMap_comp f g).symm rfl,
    (isGen_iff w').2 (T.pgen_comp W.P.D.toPre.P.isLB g0 gD), ?_, fun x => ?_, fun y => ?_,
    fun F _ _ _ _ uF ha huF => ?_⟩⟩
  · have r₀ := (maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le W.φ (spMap f) W.he a.D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff hD.w _ (fun _ => eSec W.P.D.toPre.P.A) _ D'.toPre.rig W.P.D.toPre.rig (specOf g) _
      (rigPull_le Φ (specOf g) hD.he W.P.D.toPre.P.L) (fun _ => rfl)).1 hD.w_rig
    have r₂ := T.pmaps_comp W.P.D.toPre.P.isLB (fun _ => hD.he) r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w' _ (fun _ => eSec a.D₀.P.A) _ D'.toPre.rig a.D₀.rig (spMap (g.comp f)) _
      (rigPull_le (Φ ≫ W.φ) (spMap (g.comp f)) he' a.D₀.P.L) (fun _ => rfl)).2 r₂
  · have e₁ : (oD'.onB.act x).left ≫ Φ = Φ ≫ (W.P.oD.onB.act x).left := by
      have e₀ := congrArg (fun z => z.left ≫ pullback.fst W.P.D.toPre.P.A.hom (specOf g)) (el x)
      have e₂ : ((Over.pullback (specOf g)).map (W.P.oD.onB.act x)).left ≫
          pullback.fst W.P.D.toPre.P.A.hom (specOf g) = pullback.fst _ _ ≫ (W.P.oD.onB.act x).left :=
        pullback.lift_fst _ _ _
      simp only [Over.comp_left, Category.assoc, e₂] at e₀
      simpa only [hΦ, Category.assoc] using e₀
    show (oD'.onB.act x).left ≫ Φ ≫ W.φ = (Φ ≫ W.φ) ≫ (a.oa.onB.act x).left
    rw [← Category.assoc, e₁, Category.assoc, s4 x, Category.assoc]; rfl
  · show (D'.toPre.c (xe'.symm (W.e y))).left ≫ Φ ≫ W.φ = spMap (g.comp f) ≫ (a.D₀.c y).left
    rw [← Category.assoc, hD.c_pr, hxe, Category.assoc, s5 y, spMap_comp, Category.assoc]
  · let i : R' →+* F := (algebraMap (FractionRing R') F).comp (algebraMap R' _)
    have hi : Function.Injective i := (algebraMap (FractionRing R') F).injective.comp (IsFractionRing.injective R' _)
    have h0 : i (g u) ≠ 0 := (map_ne_zero_iff i hi).2 hu
    refine ⟨fun y => ?_, fun yF hyF k p₀ s hs q₀ q x e₁ e₂ e₃ e₄ => ?_⟩
    · let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen u
      obtain ⟨zo, hz⟩ : ∃ zo : Sp F ⟶ U.toScheme, zo ≫ U.ι = specOf (i.comp g) :=
        ⟨IsOpenImmersion.lift U.ι (specOf (i.comp g)) (by
          rintro _ ⟨p, rfl⟩
          rw [Scheme.Opens.range_ι]
          have hp : PrimeSpectrum.asIdeal (R := F) p = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime _)
          intro hm
          have hm' : i (g u) ∈ PrimeSpectrum.asIdeal (R := F) p := hm
          rw [hp] at hm'
          exact h0 hm'), IsOpenImmersion.lift_fac _ _ _⟩
      obtain ⟨pt, pm⟩ := pmaps_psiOn hD ψW (jFK (R := R') F) zo (hz.trans ((spMap_comp g i).trans
        ((congrArg (· ≫ spMap g) (spMap_comp _ _)).trans (Category.assoc _ _ _)))) (xe'.symm (W.e y))
      have k := hψW F (i.comp g) zo hz ha y
      rw [← hxe y] at k
      rw [huF]
      exact (genRel_transfer T W.P.D.toPre.P.isLB D'.toPre.P.isLB (fun _ => pt) pm _ _).1 k
    · obtain ⟨σ, σ₁, σ₂, σ₃⟩ := hS F i hi
      refine level_specialises hL hL₂ hT hR hR' W hχ mR hPU T σ σ₁ (fun x => (σ₂ x).trans (congrArg _ (ha x).symm)) σ₃
        huF (huF ▸ h0) yF hyF k p₀ s hs q₀ q x e₁ ?_ (fun z z' hz => ?_) ?_
      · rw [e₂]; exact hxe _
      · obtain rfl : z' = xe'.symm (W.e z) := hD.xe.injective (hz.trans (hxe z).symm)
        exact e₃ z
      · have e₅ : x.left ≫ U'.gen.inv.left ≫ pullback.fst t'.G.hom (jK R') ≫ m'.φ = yF ≫ s.left ≫ Y.m.φ := e₄
        rw [hm', hm₀, ← hbc] at e₅
        rw [← e₅]
        simp only [Category.assoc]

theorem eval_unique {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (hV : IsAdicComplete (IsLocalRing.maximalIdeal V) V) {ev ev' : PowerSeries V →+* V}
    (h₁ : ∀ x, ev (PowerSeries.C x) = x) (h₂ : ev PowerSeries.X = ϖ) (h₁' : ∀ x, ev' (PowerSeries.C x) = x)
    (h₂' : ev' PowerSeries.X = ϖ) : ev = ev' := by
  have step : ∀ (n : ℕ) (p : PowerSeries V), ϖ ^ n ∣ ev p - ev' p := by
    intro n
    induction n with
    | zero => intro p; simp
    | succ n ih =>
      intro p
      obtain ⟨t, ht⟩ := ih (PowerSeries.mk fun i => PowerSeries.coeff (i + 1) p)
      refine ⟨t, ?_⟩
      rw [PowerSeries.eq_shift_mul_X_add_const p, map_add, map_add, map_mul, map_mul, h₁, h₁', h₂, h₂']
      linear_combination ϖ * ht
  refine RingHom.ext fun p => sub_eq_zero.1 (IsHausdorff.haus hV.toIsHausdorff _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact step n p

end GlobalTheory.ArcSpecialise

open GlobalTheory.ArcSpecialise ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem GlobalTheory.hasArcData_specialise : Laws → Laws2 → DVR.TwistBaseChangeStatement → UnifBaseChangeSt → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (V : Type) [CommRing V] [IsDomain V] [CharZero V] [IsDiscreteValuationRing V] (b : O →+* V) (ϖ : V) (a : Geo.Tor.ArcIn Dm l β V b), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (ev : PowerSeries V →+* V), (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = ϖ → ∀ χ : Geo.Tor.Sp (PowerSeries V) ⟶ Y.X, χ ≫ Y.s = Geo.Tor.spMap (PowerSeries.C (R := V)) ≫ Geo.Tor.spMap b → Set.range (jK V ≫ Geo.Tor.spMap ev ≫ χ) ⊆ Set.range Y.j → Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := V)) PowerSeries.X χ → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id V) ϖ (Geo.Tor.spMap ev ≫ χ) := by
  intro hL hL₂ hT hU h5 E _ _ _ H Dm l Xo c O _ β Y V _ _ _ _ b ϖ a hϖ hV ev ev₁ ev₂ χ hχ hj h
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ _).1 h
  obtain ⟨hR', hR, ev', ev'₁, ev'₂, hσ⟩ := UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser V ϖ hϖ hV
  obtain rfl : ev = ev' := eval_unique hϖ hV ev₁ ev₂ ev'₁ ev'₂
  have key := specialise hL hL₂ hT hU h5 hR hR' PowerSeries.C_injective W hχ ev
    (by rw [Ideal.map_span, Set.image_singleton, ev₂]) (by rw [ev₂]; exact hϖ.ne_zero) hj (fun F _ i hi => by
      obtain ⟨σ, σ₁, σ₂, -, σ₃⟩ := hσ F i hi
      exact ⟨σ, σ₁, fun x => by rw [σ₂, ev₁], σ₃⟩)
  rw [show ev.comp PowerSeries.C = RingHom.id V from RingHom.ext ev₁, ev₂] at key
  exact (Y.hasArcData_iff _ _ _ _ _).2 key
