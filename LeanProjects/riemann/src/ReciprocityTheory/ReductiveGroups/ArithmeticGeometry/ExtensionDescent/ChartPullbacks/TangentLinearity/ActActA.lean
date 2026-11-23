import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.PairProp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

include hO in

theorem hB_act (k : Fin 4) :
    (WeightPf.act (U.gt e)).left ≫ φB U ιG e a χ k =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φB U ιG e a χ k := by

  have hq0 : WeightPf.act (U.gt e) ≫ (U.gt e).q =
      snd (WeightPf.Te D.toPre I e) (thickObj R I e G) ≫ (U.gt e).q := by
    haveI := (U.gt e).q_hom
    have hiq := (U.gt e).isKernel.w
    simp only [WeightPf.act, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, hiq,
      comp_toUnit_assoc, MonObj.lift_comp_one_left]
  have hq : (WeightPf.act (U.gt e) ≫ (Over.pullback (thick R I e)).map (ιG.act a)) ≫ (U.gt e).q =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G) ≫
        (Over.pullback (thick R I e)).map (ιG.act a)) ≫ (U.gt e).q := by
    rw [Category.assoc, Category.assoc, hO, reassoc_of% hq0]

  have gen : ∀ {f g : WeightPf.Te D.toPre I e ⊗ thickObj R I e G ⟶ thickObj R I e G},
      f ≫ (U.gt e).q = g ≫ (U.gt e).q → ∀ k : Fin 4,
      f.left ≫ D.toPre.Oφ (U.gt e).pG χ k = g.left ≫ D.toPre.Oφ (U.gt e).pG χ k := by
    intro f g hfg k
    have h2 : (Over.map (thick R I e)).map f ≫ (U.gt e).pG =
        (Over.map (thick R I e)).map g ≫ (U.gt e).pG := by
      simp only [GtCoord.pG, ← Functor.map_comp_assoc, hfg]
    fin_cases k
    · exact congrArg CommaMorphism.left
        (show (Over.map (thick R I e)).map f ≫
            padd D.toPre.P.A (U.gt e).pG (toUnit _ ≫ D.toPre.c χ) =
          (Over.map (thick R I e)).map g ≫
            padd D.toPre.P.A (U.gt e).pG (toUnit _ ≫ D.toPre.c χ) by
          simp only [padd, comp_lift_assoc, h2, comp_toUnit_assoc])
    · exact congrArg CommaMorphism.left
        (show (Over.map (thick R I e)).map f ≫ (toUnit _ ≫ D.toPre.c χ) =
          (Over.map (thick R I e)).map g ≫ (toUnit _ ≫ D.toPre.c χ) by
          simp only [comp_toUnit_assoc])
    · exact congrArg CommaMorphism.left h2
    · exact congrArg CommaMorphism.left
        (show (Over.map (thick R I e)).map f ≫ (toUnit _ ≫ η[D.toPre.P.A]) =
          (Over.map (thick R I e)).map g ≫ (toUnit _ ≫ η[D.toPre.P.A]) by
          simp only [comp_toUnit_assoc])
  simpa only [Over.comp_left, Category.assoc, φB] using gen hq k

section Rhs

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)

abbrev actA : thickObj R I e G ⟶ thickObj R I e G := (Over.pullback (thick R I e)).map (ιG.act a)

def mA (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e) :
    WeightPf.Te D.toPre I e ⊗ thickObj R I e G ⟶ WeightPf.Te D.toPre I e ⊗ thickObj R I e G :=
  lift (fst _ _ ≫ ta) (snd _ _ ≫ actA ιG e a)

theorem mA_fst (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e) :
    mA ιG e a ta ≫ fst _ _ = fst _ _ ≫ ta := by
  simp only [mA, lift_fst]

theorem mA_snd (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e) :
    mA ιG e a ta ≫ snd _ _ = snd _ _ ≫ actA ιG e a := by
  simp only [mA, lift_snd]

theorem act_actA (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e)
    (hia : (U.gt e).i ≫ actA ιG e a = ta ≫ (U.gt e).i) :
    WeightPf.act (U.gt e) ≫ actA ιG e a = mA ιG e a ta ≫ WeightPf.act (U.gt e) := by
  haveI := ιG.hom a
  have hμ : μ[thickObj R I e G] ≫ actA ιG e a =
      (actA ιG e a ⊗ₘ actA ιG e a) ≫ μ[thickObj R I e G] := IsMonHom.mul_hom _
  simp only [WeightPf.act, mA, Category.assoc, hμ, lift_map_assoc, comp_lift_assoc,
    lift_fst_assoc, lift_snd, hia]

set_option maxHeartbeats 800000 in

theorem mA_chiP (ta : WeightPf.Te D.toPre I e ⟶ WeightPf.Te D.toPre I e)
    (hta : TorusEndOf D.toPre.X (fun χ => star a • χ) ta) (χ : D.toPre.X)
    (W2 W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hm : W' ≤ (mA ιG e a ta).left ⁻¹ᵁ W2) :
    ((mA ιG e a ta).left.appLE W2 W' hm).hom
        (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
          (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) χ)) =
      ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) := by
  have hF : (mA ιG e a ta).left ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left =
      (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ ta.left := by
    rw [← Over.comp_left, mA_fst, Over.comp_left]
  have hTop : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫
      (mA ιG e a ta).left.appTop =
      ta.left.appTop ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop := by
    rw [← Scheme.Hom.comp_appTop, hF, Scheme.Hom.comp_appTop]
  have hval := congrArg Units.val (hta χ)
  simp only [Semi.res, Semi.pullU, Units.coe_map, MonoidHom.coe_coe] at hval
  simp only [Semi.TorusInj.chiP, ← hval]
  simp only [Scheme.Hom.appLE]
  have hTop' : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫ (mA ιG e a ta).left.app ⊤ = ta.left.app ⊤ ≫ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.app ⊤ := hTop

  have key : (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W2 ≤ ⊤)).op ≫
      (mA ιG e a ta).left.app W2 ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE hm).op =
      ta.left.app ⊤ ≫
      (WeightPf.Te D.toPre I e).left.presheaf.map
        (homOfLE (fun _ _ => trivial : (⊤ : (WeightPf.Te D.toPre I e).left.Opens) ≤ ta.left ⁻¹ᵁ ⊤)).op ≫
      (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.app ⊤ ≫
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (fun _ _ => trivial : W' ≤ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ ⊤)).op := by
    rw [Scheme.Hom.naturality_assoc, Scheme.Hom.naturality_assoc, reassoc_of% hTop']
    simp only [← Functor.map_comp]
    rfl
  have hk := congrArg (fun φ => φ.hom (charUnit _ D.toPre.X χ).val) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hk ⊢
  exact hk

end Rhs

include hO in

theorem rhs_act
    (hi : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
        (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i)
    (jB : Fin 4 → D.toPre.P.L.ι) (cB : LB.Coh D.toPre.P.L (φB U ιG e a χ) jB)
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      LB.wchart D.toPre.P.L (φB U ιG e a χ) jB)
    (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) :
    ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom ((rhs U ιG e a χ).s jB).val =
      ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) *
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hs).hom
        ((rhs U ιG e a χ).s jB).val := by
  obtain ⟨ta, hta, hia⟩ := hi
  set hL := (actA ιG e a).left with hhL
  set actL := (WeightPf.act (U.gt e)).left with hactL
  set sndL := (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left with hsndL
  set mL := (mA ιG e a ta).left with hmL
  set Wt := LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG χ) jB with hWt
  have hWb : LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ≤ hL ⁻¹ᵁ Wt :=
    Semi.LBVal.wchart_pull_le D.toPre.P.L (D.toPre.Oφ (U.gt e).pG χ) hL jB
  have eqA : actL ≫ hL = mL ≫ actL := by
    rw [hactL, hhL, hmL, ← Over.comp_left, act_actA U ιG e a ta hia, Over.comp_left]
  have eqS : mL ≫ sndL = sndL ≫ hL := by
    rw [hsndL, hhL, hmL, ← Over.comp_left, mA_snd, Over.comp_left]
  let W2 : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens := sndL ⁻¹ᵁ Wt ⊓ actL ⁻¹ᵁ Wt
  have hs2 : W2 ≤ sndL ⁻¹ᵁ Wt := inf_le_left
  have ha2 : W2 ≤ actL ⁻¹ᵁ Wt := inf_le_right
  have hm : W' ≤ mL ⁻¹ᵁ W2 := by
    intro z hz
    refine ⟨?_, ?_⟩
    · show sndL (mL z) ∈ Wt
      rw [← Scheme.Hom.comp_apply, eqS, Scheme.Hom.comp_apply]
      exact hWb (hs hz)
    · show actL (mL z) ∈ Wt
      rw [← Scheme.Hom.comp_apply, ← eqA, Scheme.Hom.comp_apply]
      exact hWb (ha hz)
  have hjt : LB.Coh D.toPre.P.L (D.toPre.Oφ (U.gt e).pG χ) jB :=
    fun k1 k2 h => cB k1 k2 (congrArg (hL ≫ ·) h)
  have T := WeightPf.t_act (U.gt e) χ jB hjt W2 hs2 ha2
  have M1 : hL.appLE Wt _ hWb ≫ actL.appLE _ W' ha =
      actL.appLE Wt W2 ha2 ≫ mL.appLE W2 W' hm := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, Semi.TorusInj.appLE_of_eq eqA]
  have M3 : sndL.appLE Wt W2 hs2 ≫ mL.appLE W2 W' hm =
      hL.appLE Wt _ hWb ≫ sndL.appLE _ W' hs := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, Semi.TorusInj.appLE_of_eq eqS]
  have C := mA_chiP ιG e a ta hta χ W2 W' hm
  set x := (((U.gt e).t χ).s jB).val with hx
  calc ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom ((rhs U ιG e a χ).s jB).val
      = (hL.appLE Wt _ hWb ≫ actL.appLE _ W' ha).hom x := rfl
    _ = (mL.appLE W2 W' hm).hom ((actL.appLE Wt W2 ha2).hom x) :=
        congrArg (fun φ => φ.hom x) M1
    _ = (mL.appLE W2 W' hm).hom
          (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
            (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) χ)) *
        (mL.appLE W2 W' hm).hom ((sndL.appLE Wt W2 hs2).hom x) := by
        rw [T, map_mul]
    _ = _ := by
        rw [C]
        congr 1
        exact congrArg (fun φ => φ.hom x) M3

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
