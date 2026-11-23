import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem rigIso_congr {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {LG PP : RigLB G} (hL : LG = PP) {PP' : RigLB G'} (m : CubeMap G' G) {c : CubicalStr G PP}
    {c' : CubicalStr G' PP'} (h : m.IsPullCubical c' c) {F : G'.left ⟶ G.left} (hF : F = m.F) {e : S' ⟶ S}
    (he : e = m.e) : ∃ (w : LB.Iso PP'.L (LG.L.pull F)) (h₀ : eSec G' ≫ F = e ≫ eSec G), w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) PP'.rig (rigPullOf F e h₀ LG.L LG.rig) := by
  subst hL hF he
  obtain ⟨w, h₁, h₂, -⟩ := h
  exact ⟨w, m.e_comm, h₁, h₂⟩

set_option maxHeartbeats 1600000 in
theorem pmaps_psi {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {g : R →+* R'} {D : Out.DegPre R}
    {D' : Out.DegPre R'} (hD : Out.IsPullDeg g D D') (F : Type) [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F]
    (hj : Out.jFK (R := R') F ≫ Out.jK R' ≫ spMap g = Out.jFK (R := R) F ≫ Out.jK R) (x : D'.X) :
    PMaps hD.w (K := PUnit) (fun _ => Out.jFK (R := R') F ≫ D'.xK x) (fun _ => Out.jFK (R := R) F ≫ D.xK (hD.xe x))
      (fun _ => -1) (LB.pullGen _ _ _ (D'.psi x) (Out.jFK (R := R') F))
      (LB.pullGen _ _ _ (D.psi (hD.xe x)) (Out.jFK (R := R) F)) (𝟙 _) := by
  intro Z r z p q hp hq
  obtain ⟨b, hb, hcorr⟩ := hD.psi_pr x
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (Out.specOf g) with hΦ
  have hx : D'.xK x ≫ Φ = Out.jK R' ≫ Out.specOf g ≫ (D.c (hD.xe x)).left := by
    rw [← hD.c_pr x, ← Category.assoc]; rfl
  have hpt : Out.jFK (R := R') F ≫ D'.xK x ≫ Φ = Out.jFK (R := R) F ≫ D.xK (hD.xe x) := by
    rw [hx, ← Category.assoc (Out.jK R'), ← Category.assoc, ← Category.assoc (Out.jFK F)]
    exact (congrArg (· ≫ (D.c (hD.xe x)).left) ((Category.assoc _ _ _).trans hj)).trans (Category.assoc _ _ _)

  have hW : Out.jFK (R := R) F ≫ Out.jK R = (Out.jFK (R := R') F ≫ hD.g) ≫ hD.W.ι := by
    rw [Category.assoc, hD.g_comm]; exact hj.symm
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : Sp F ⟶ (Out.jK R ⁻¹ᵁ hD.W).toScheme, lam ≫ (Out.jK R ⁻¹ᵁ hD.W).ι = Out.jFK (R := R) F ∧
      lam ≫ (Out.jK R ∣_ hD.W) = Out.jFK (R := R') F ≫ hD.g :=
    ⟨(isPullback_morphismRestrict (Out.jK R) hD.W).lift _ _ hW.symm,
      (isPullback_morphismRestrict (Out.jK R) hD.W).lift_snd _ _ _,
      (isPullback_morphismRestrict (Out.jK R) hD.W).lift_fst _ _ _⟩
  have mp : Φ (D'.xK x (Out.jFK (R := R') F (r z))) ∈ D.P.L.U (p PUnit.unit) := hp PUnit.unit
  have mq : D'.xK x (Out.jFK (R := R') F (r z)) ∈ D'.P.L.U (q PUnit.unit) := hq PUnit.unit
  have mp' : D.xK (hD.xe x) (Out.jFK (R := R) F (r z)) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun h => h (r z) ∈ D.P.L.U (p PUnit.unit)) hpt).mp mp
  have cW : hD.g ≫ (toUnit (Out.TW hD.W) ≫ D.c (hD.xe x)).left = D'.xK x ≫ Φ := by
    rw [hx, ← Category.assoc (Out.jK R'), ← hD.g_comm, Category.assoc]; rfl
  have mW : (toUnit (Out.TW hD.W) ≫ D.c (hD.xe x)).left (hD.g (Out.jFK (R := R') F (r z))) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun h => h (Out.jFK (R := R') F (r z)) ∈ D.P.L.U (p PUnit.unit)) cW).mpr mp
  have one : ∀ {Y : Scheme.{0}} {B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (y : Y) (j : M.ι), φ y ∈ M.U j →
      y ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => j) := fun M φ y j h => Set.mem_iInter.2 fun _ => h

  have m₁ : (r ≫ Out.jFK (R := R') F) z ∈ D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p PUnit.unit) ⊓ D'.P.L.U (q PUnit.unit)) :=
    ⟨mem_pull.2 mp, mq⟩
  have e₁ := congrArg (gm (r ≫ Out.jFK (R := R') F) z
    (D'.xK x ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => p PUnit.unit) ⊓ D'.P.L.U (q PUnit.unit))))
    (hb (fun _ => p PUnit.unit) (q PUnit.unit))
  have e₁' := (gm_res _ z _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK x) z
      ((D.P.L.pull Φ).U (fun _ => p PUnit.unit) ⊓ D'.P.L.U (q PUnit.unit)) m₁ _))) (gm_res _ z _ m₁ _))))

  have e₂ := (gm_corr D.P.L hcorr (r ≫ Out.jFK (R := R') F) z (p PUnit.unit) (one _ _ _ _ mp) (one _ _ _ _ mW)).trans
    (gm_pullGen D.P.L _ _ _ hD.g (r ≫ Out.jFK (R := R') F) z _ (one _ _ _ _ mW))

  have n₁ : (toUnit (Out.TW hD.W) ≫ D.c (hD.xe x)).left ((Out.jK R ∣_ hD.W) (lam (r z))) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun h => (toUnit (Out.TW hD.W) ≫ D.c (hD.xe x)).left (h (r z)) ∈ D.P.L.U (p PUnit.unit)) l₂).mpr mW
  have n₂ : D.xK (hD.xe x) ((Out.jK R ⁻¹ᵁ hD.W).ι (lam (r z))) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun h => D.xK (hD.xe x) (h (r z)) ∈ D.P.L.U (p PUnit.unit)) l₁).mpr mp'
  have e₃ := (gm_pullGen D.P.L _ _ _ (Out.jK R ∣_ hD.W) (r ≫ lam) z _ (one _ _ _ _ n₁)).symm.trans
    ((gm_corr D.P.L (hD.psiW.psi_eq (hD.xe x)) (r ≫ lam) z (p PUnit.unit) (one _ _ _ _ n₁) (one _ _ _ _ n₂)).trans
      (gm_pullGen D.P.L _ _ _ (Out.jK R ⁻¹ᵁ hD.W).ι (r ≫ lam) z _ (one _ _ _ _ n₂)))
  rw [Category.assoc, l₂, Category.assoc, l₁, ← Category.assoc] at e₃
  rw [Category.comp_id, Fintype.prod_unique]
  refine (gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe x)) _ (D.psi (hD.xe x)) (Out.jFK (R := R) F) r z p
    (Set.mem_iInter.2 fun _ => mp')).trans ?_
  refine e₃.symm.trans (e₂.symm.trans (e₁'.trans (congrArg₂ (· * ·) ?_ ?_)))
  · rw [Category.assoc]; rfl
  · exact (gm_pullGen D'.P.L _ _ _ (Out.jFK (R := R') F) r z _ (one _ _ _ _ mq)).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

set_option maxHeartbeats 1600000 in

theorem ArcWit.baseChange (hC : Out.CubePullSt) (hP : Out.PolBaseChangeSt) (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5)
    (hQ : QkPullExistsSt) (hO : PolOActPullSt) {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O']
    {b : O →+* O'} {a : ArcIn D l β O' b} {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {I : Ideal R} {I' : Ideal R'} (hR : Out.AdmBase R I) (hR' : Out.AdmBase R' I') {f : O' →+* R} {u : R}
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I') :
    ∃ (W' : ArcWit Y a I' (g.comp f) (g u) (spMap g ≫ χ)) (hD : Out.IsPullDeg g W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G), IsMonHom bc.hom ∧ Out.IsPullUnif g hD bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g)) ≫ W.m.φ ∧
      (∀ y, hD.xe (W'.e y) = W.e y) ∧
      ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull
          ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ)),
        W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ ∧ HEq W'.w w' ∧
          Tri W.w hD.w w' := by
  letI := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull hC (spMap g) W.t
  let t' : SAB H (Sp R') := ⟨(Over.pullback (spMap g)).obj W.t.G, IsSemiAbelian.pullback _ W.t.G W.t.semi,
    OAct.pullback _ W.t.G W.t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' W.t (spMap g) := m₁
  have hm₀ : m₀.φ = pullback.fst W.t.G.hom (spMap g) := hm₁
  obtain ⟨m', hm'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ W.m m₀
  let gam : FractionRing R →+* FractionRing R' :=
    IsFractionRing.lift (g := (algebraMap R' (FractionRing R')).comp g) ((IsFractionRing.injective R' _).comp hg)
  have hgam : ∀ r, gam (algebraMap R _ r) = algebraMap R' _ (g r) := fun r => IsFractionRing.lift_algebraMap _ r
  have sq : spMap gam ≫ Out.jK R = Out.jK R' ≫ spMap g :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp g _))
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap gam) W.P.A
  have gpA : IsGrpPullback A'.A W.P.A.A (spMap gam) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have := W.P.U.gen_hom
  have gpG : IsGrpPullback W.P.A.A W.t.G (Out.jK R) (W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK R)) := by
    have : IsMonHom W.P.U.gen.symm.hom := by show IsMonHom W.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso W.P.U.gen.symm).comp (isGrpPullback_pullback W.t.G (Out.jK R))).congr
      (Category.id_comp _) rfl
  have gp' : IsGrpPullback ((Over.pullback (Out.jK R')).obj t'.G) W.t.G (spMap gam ≫ Out.jK R)
      (pullback.fst t'.G.hom (Out.jK R') ≫ pullback.fst W.t.G.hom (spMap g)) :=
    ((isGrpPullback_pullback t'.G (Out.jK R')).comp (isGrpPullback_pullback W.t.G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : W.P.U.gen.inv.left ≫ W.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl t'.G).hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g) = pullback.fst W.t.G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (W.P.U.LG.L.pull (pullback.fst t'.G.hom (Out.jK R') ≫
      (Iso.refl t'.G).hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB W.P.A.isLB gA) eA.hom.left)
      (pull_isLB W.P.U.LG.isLB _)
      ((LBIso.symm tA).chartPull (chartPullPull A'.L _ _ rfl) (chartPullPull (W.P.A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ W.P.U.gen.inv.left)
      (chartPullLinComb W.P.A.L gA (fun _ => eA.hom.left) (fun _ => W.P.U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame W.P.U.LG.L _ (fun _ => pullback.fst W.t.G.hom (Out.jK R)) _ _ fun _ => ?_) W.P.U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  obtain ⟨wL, heL, gL, rL⟩ := rigIso_congr W.P.bundle m₀.cm m₀.lin (hbc.trans hm₀.symm) (e := Out.specOf g) m₀.base.symm
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R I hR W.P.D
  have hgen : (Out.specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (Out.specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl t'.G).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI W.P.D W.P.A W.t.G W.t.semi W.P.U Wo hψ hgen t'.G
    (Iso.refl _) mR A' dA eA mE wA PP' wL heL gL rL
  obtain ⟨oA', hoA'⟩ := hO _ _ (spMap gam) W.P.A A' gA gpA tA (𝓞 E) W.P.oA
  have actA : ∀ x, (W.P.oA.act x).left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK R) =
      W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK R) ≫ (W.t.act.act x).left := by
    intro x
    have e : W.P.oA.act x ≫ W.P.U.gen.inv = W.P.U.gen.inv ≫ (Over.pullback (Out.jK R)).map (W.t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (W.P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (Out.jK R')).map (t'.act.toRingAct.act x) ≫ U'.gen.hom = U'.gen.hom ≫ oA'.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply (gpA.comp gpG).1.hom_ext
    · have a₁ : ((Over.pullback (Out.jK R')).map (t'.act.toRingAct.act x)).left ≫ pullback.fst t'.G.hom (Out.jK R') =
          pullback.fst t'.G.hom (Out.jK R') ≫ (t'.act.act x).left := pullback.lift_fst _ _ _
      have a₂ : (t'.act.act x).left ≫ pullback.fst W.t.G.hom (spMap g) =
          pullback.fst W.t.G.hom (spMap g) ≫ (W.t.act.act x).left := pullback.lift_fst _ _ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₂, Over.comp_left, Category.assoc,
        ← Category.assoc (oA'.act x).left, hoA', Category.assoc, actA, ← Category.assoc, ← heA]
      simp only [Category.assoc]
    · rw [Over.w, Over.w]
  obtain ⟨mod', oD', xl, el, lin', w0'⟩ := h5.oLinBaseChange R R' I I' hR hR' g W.P.D W.P.A W.t.G W.P.U t'.G (Iso.refl _) mR
    A' D' hD U' hPU (𝓞 E) W.P.oD W.P.oA W.t.act.toRingAct W.P.lin t'.act.toRingAct
    (fun x => (Category.comp_id _).trans (Category.id_comp _).symm) oA' extA
  let P' : PELUnif I' t' := { D := D', mod := mod', oD := oD', A := A', oA := oA', U := U', bundle := hLG, lin := lin'
                              w0 := w0' H.w0 W.P.w0 }
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  set Φ := hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g) with hΦ
  have gD := (isGen_iff hD.w).1 hD.w_gen
  have g0 := (isGen_iff W.w).1 s2
  obtain ⟨w', T⟩ := exists_comp W.P.D.toPre.P.isLB W.w hD.w g0 gD a.D₀.P.isLB D'.toPre.P.isLB
  have he' : eSec D'.toPre.P.A ≫ Φ ≫ W.φ = spMap (g.comp f) ≫ eSec a.D₀.P.A := by
    rw [← Category.assoc, hD.he, Category.assoc, W.he, spMap_comp, Category.assoc]
  let xe' : D'.toPre.X ≃ₗ[𝓞 E] W.P.D.toPre.X := { hD.xe with map_smul' := xl }
  have := hD.e_hom
  have gpB : IsGrpPullback D'.toPre.P.A W.P.D.toPre.P.A (spMap g) Φ :=
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback W.P.D.toPre.P.A (Out.specOf g))).congr
      (Category.id_comp _) rfl
  have hxe : ∀ y, hD.xe (xe'.symm (W.e y)) = W.e y := fun y => xe'.apply_symm_apply _
  refine ⟨⟨t', m', P', Φ ≫ W.φ, he', w', W.e.trans xe'.symm, (gpB.comp s1).congr (spMap_comp f g).symm rfl,
    (isGen_iff w').2 (T.pgen_comp W.P.D.toPre.P.isLB g0 gD), ?_, fun x => ?_, fun y => ?_,
    fun F _ _ _ _ uF ha hu => ?_⟩, hD, Iso.refl _, mR, hPU, ?_, hxe, w', rfl, HEq.rfl, T⟩
  · have r₀ := (maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig (spMap f) _
      (rigPull_le W.φ (spMap f) W.he a.D₀.P.L) (fun _ => rfl)).1 s3
    have r₁ := (maps_iff hD.w _ (fun _ => eSec W.P.D.toPre.P.A) _ D'.toPre.rig W.P.D.toPre.rig (Out.specOf g) _
      (rigPull_le Φ (Out.specOf g) hD.he W.P.D.toPre.P.L) (fun _ => rfl)).1 hD.w_rig
    have r₂ := T.pmaps_comp W.P.D.toPre.P.isLB (fun _ => hD.he) r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w' _ (fun _ => eSec a.D₀.P.A) _ D'.toPre.rig a.D₀.rig (spMap (g.comp f)) _
      (rigPull_le (Φ ≫ W.φ) (spMap (g.comp f)) he' a.D₀.P.L) (fun _ => rfl)).2 r₂
  · have e₁ : (oD'.onB.act x).left ≫ Φ = Φ ≫ (W.P.oD.onB.act x).left := by
      have e₀ := congrArg (fun z => z.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) (el x)
      have e₂ : ((Over.pullback (Out.specOf g)).map (W.P.oD.onB.act x)).left ≫
          pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g) = pullback.fst _ _ ≫ (W.P.oD.onB.act x).left :=
        pullback.lift_fst _ _ _
      simp only [Over.comp_left, Category.assoc, e₂] at e₀
      simpa only [hΦ, Category.assoc] using e₀
    show (oD'.onB.act x).left ≫ Φ ≫ W.φ = (Φ ≫ W.φ) ≫ (a.oa.onB.act x).left
    rw [← Category.assoc, e₁, Category.assoc, s4 x, Category.assoc]; rfl
  · show (D'.toPre.c (xe'.symm (W.e y))).left ≫ Φ ≫ W.φ = spMap (g.comp f) ≫ (a.D₀.c y).left
    rw [← Category.assoc, hD.c_pr, hxe, Category.assoc, s5 y, spMap_comp, Category.assoc]
  · letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing R') F).comp gam).toAlgebra
    have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (g r)) := fun r =>
      congrArg (algebraMap (FractionRing R') F) (hgam r)
    have hjg : Out.jFK (R := R) F = Out.jFK (R := R') F ≫ spMap gam := spMap_comp gam _
    have hj : Out.jFK (R := R') F ≫ Out.jK R' ≫ spMap g = Out.jFK (R := R) F ≫ Out.jK R := by
      rw [hjg, Category.assoc, sq]
    obtain ⟨k₁, k₂⟩ := s6 F uF (fun x => (ha x).trans (hF (f x)).symm) (hu.trans (hF u).symm)
    refine ⟨fun y => ?_, fun yF hyF k p₀ σ hσ q₀ q' x' e1 e2 e3 e4 => ?_⟩
    · have pm := pmaps_psi hD F hj (xe'.symm (W.e y))
      have k := k₁ y
      rw [← hxe y] at k
      refine (genRel_transfer T W.P.D.toPre.P.isLB D'.toPre.P.isLB (fun _ => ?_) pm _ _).1 k
      have hx : D'.toPre.xK (xe'.symm (W.e y)) ≫ Φ =
          Out.jK R' ≫ Out.specOf g ≫ (W.P.D.toPre.c (hD.xe (xe'.symm (W.e y)))).left := by
        rw [← hD.c_pr, ← Category.assoc]; rfl
      rw [Category.id_comp, Category.assoc, hx, ← Category.assoc (Out.jK R'), ← Category.assoc]
      exact (congrArg (· ≫ _) hj).trans (Category.assoc _ _ _)
    · obtain ⟨q, hq₁, hq₂⟩ := hQ R R' g W.P.D.toPre D'.toPre hD F hF k q'
      let x : Out.TFK (R := R) F ⟶ W.P.A.A := Over.homMk (x'.left ≫ gA) (by
        have a₂ : x'.left ≫ A'.A.hom = Out.jFK (R := R') F := Over.w x'
        show (x'.left ≫ gA) ≫ W.P.A.A.hom = Out.jFK (R := R) F
        rw [Category.assoc, pA.w, ← Category.assoc, a₂, hjg])
      have hx : x'.left ≫ U'.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R') ≫ (Iso.refl t'.G).hom.left ≫
          pullback.fst W.t.G.hom (Out.specOf g) =
          x.left ≫ W.P.U.gen.inv.left ≫ pullback.fst W.t.G.hom (Out.jK R) := by
        have hi : eA.inv.left ≫ eA.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
        rw [hbc, hgenU, ← heA, ← Category.assoc eA.inv.left, hi, Category.id_comp]
        exact (Category.assoc _ _ _).symm
      have hk : 1 ≤ k := by
        rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact l.A_pos
        · exact le_trans (by norm_num) l.three_le
      refine h5.qkBaseChange R R' I I' hR hR' g W.P.D W.P.A W.t.G W.P.U t'.G (Iso.refl _) mR A' D' hD U' hPU F hF k hk
        q x q' x' hq₁ hq₂ hx (k₂ yF ?_ k p₀ σ hσ q₀ q x e1 ?_ (fun z => ?_) ?_)
      · rw [hyF, ← Category.assoc (Out.jK R'), ← Category.assoc, hj, Category.assoc]
      · have : hD.xe q'.y = q.y := by rw [hq₁, AddEquiv.apply_symm_apply]
        rw [← this, e2]; exact hxe _
      · obtain ⟨hψ', hm⟩ := hq₂.2 (xe'.symm (W.e z))
        have pm := (maps_iff hD.w _ _ _ (q'.g.s (xe'.symm (W.e z))) (q.g.s (hD.xe (xe'.symm (W.e z)))) (𝟙 _) _
          (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ') (fun _ => rfl)).1 hm
        have k' := (genRel_transfer T W.P.D.toPre.P.isLB D'.toPre.P.isLB hψ' pm _ _).2 (e3 z)
        rw [hxe z] at k'
        exact k'
      · have e5 : x'.left ≫ U'.gen.inv.left ≫ pullback.fst t'.G.hom (Out.jK R') ≫ m'.φ = yF ≫ σ.left ≫ Y.m.φ := e4
        rw [hm', hm₀, ← hbc] at e5
        rw [← e5]
        simpa only [Category.assoc] using congrArg (· ≫ W.m.φ) hx.symm
  · show m'.φ = ((Iso.refl t'.G).hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g)) ≫ W.m.φ
    rw [hm', hm₀, hbc]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
