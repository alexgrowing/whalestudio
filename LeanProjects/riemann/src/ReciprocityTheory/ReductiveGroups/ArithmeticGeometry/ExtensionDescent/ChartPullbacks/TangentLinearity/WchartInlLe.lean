import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.PairProp

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

section SlopeTestRemainingChoices

variable {Y Z : Scheme.{0}} (L : LB Y) {K K' : Type} [Fintype K] [Fintype K']

lemma wchart_inl_le (φ : K → (Z ⟶ Y)) (φ' : K' → (Z ⟶ Y)) (j : K ⊕ K' → L.ι) :
    LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (j ∘ Sum.inl) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)

lemma wchart_inr_le (φ : K → (Z ⟶ Y)) (φ' : K' → (Z ⟶ Y)) (j : K ⊕ K' → L.ι) :
    LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (j ∘ Sum.inr) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)

private lemma appLE_res_lemma {T₀ Z₀ : Scheme.{0}} (f : T₀ ⟶ Z₀) {V₀ U₀ : Z₀.Opens} (hVU : V₀ ≤ U₀)
    (W₀ : T₀.Opens) (h : W₀ ≤ f ⁻¹ᵁ V₀) (h' : W₀ ≤ f ⁻¹ᵁ U₀) (x : Γ(Z₀, U₀)ˣ) :
    (f.appLE V₀ W₀ h).hom (res hVU x).val = (f.appLE U₀ W₀ h').hom x.val := by
  rw [← Scheme.Hom.map_appLE f h (homOfLE hVU).op]
  rfl

lemma appLE_mulGen {T : Scheme.{0}} (f : T ⟶ Z) (φ : K → (Z ⟶ Y)) (ε : K → ℤ) (φ' : K' → (Z ⟶ Y))
    (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (j : K ⊕ K' → L.ι) (W' : T.Opens) (h : W' ≤ f ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j) :
    (f.appLE _ W' h).hom ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      (f.appLE (LB.wchart L φ (j ∘ Sum.inl)) W' (fun _ hz => wchart_inl_le L φ φ' j (h hz))).hom (t.s (j ∘ Sum.inl)).val *
      (f.appLE (LB.wchart L φ' (j ∘ Sum.inr)) W' (fun _ hz => wchart_inr_le L φ φ' j (h hz))).hom (t'.s (j ∘ Sum.inr)).val := by
  simp only [LB.mulGen, Units.val_mul, map_mul]
  congr 1 <;> exact appLE_res_lemma _ _ _ _ _ _

lemma appLE_pullGen {T X : Scheme.{0}} (f : T ⟶ Z) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (L : LB X)
    (c : LB.Gen (LB.LinComb L φ ε)) (hh : Z ⟶ Y) (j : K → L.ι) (W' : T.Opens)
    (h : W' ≤ f ⁻¹ᵁ LB.wchart L (fun k => hh ≫ φ k) j) :
    (f.appLE _ W' h).hom ((LB.pullGen L φ ε c hh).s j).val =
      ((f ≫ hh).appLE (LB.wchart L φ j) W'
        (fun _ hz => Semi.LBVal.wchart_pull_le L φ hh j (h hz))).hom (c.s j).val := by
  simp only [LB.pullGen]
  refine (appLE_res_lemma f _ W' h ?_ _).trans ?_
  · exact fun _ hz => Semi.LBVal.wchart_pull_le L φ hh j (h hz)
  · first
      | rfl
      | (rw [Scheme.Hom.appLE, Scheme.Hom.appLE, Scheme.comp_app]; rfl)
      | simp [pullU, Scheme.Hom.appLE, Scheme.comp_app]

end SlopeTestRemainingChoices

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

private lemma q_act_lemma :
    (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫ (Over.map (thick R I e)).map (U.gt e).q =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫
        (Over.map (thick R I e)).map (U.gt e).q := by
  rw [← Functor.map_comp, WeightPf.act_q, Functor.map_comp]

private lemma pG_act_lemma :
    (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫ (U.gt e).pG =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫
        (U.gt e).pG := by
  first
    | (simp only [GtCoord.pG]
       rw [← Category.assoc, ← Functor.map_comp, WeightPf.act_q, Functor.map_comp, Category.assoc])
    | simp [GtCoord.pG, ← Functor.map_comp_assoc, WeightPf.act_q]

private lemma unit_act_lemma :
    (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫
        toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫
        toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) :=
  toUnit_unique _ _

private lemma left_act_lemma {A' : Over (Spec (CommRingCat.of R))}
    (p : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ A')
    (hp : (Over.map (thick R I e)).map (WeightPf.act (U.gt e)) ≫ p =
      (Over.map (thick R I e)).map (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)) ≫ p) :
    (WeightPf.act (U.gt e)).left ≫ p.left =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ p.left := by
  simpa using congrArg CommaMorphism.left hp

lemma act_lift_xc :
    (WeightPf.act (U.gt e)).left ≫ (lift (xc e χ (G := G)) (U.gt e).pG).left =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
        (lift (xc e χ (G := G)) (U.gt e).pG).left := by
  refine left_act_lemma (U := U) (e := e) _ ?_
  first
    | (rw [comp_lift, comp_lift, pG_act_lemma]
       simp only [xc, ← Category.assoc, unit_act_lemma])
    | simp [xc, pG_act_lemma, unit_act_lemma]

theorem hA_act (k : Fin 4 ⊕ Fin 6) :
    (WeightPf.act (U.gt e)).left ≫ φA U ιD e a χ k =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φA U ιD e a χ k := by
  rcases k with k | k
  · simp only [φA, Sum.elim_inl]
    fin_cases k
    · exact left_act_lemma (U := U) (e := e)
        (padd D.toPre.P.A (U.gt e).pG (toUnit _ ≫ D.toPre.c (star a • χ)))
        (by simp only [padd, ← Category.assoc, comp_lift, pG_act_lemma, q_act_lemma, unit_act_lemma])
    · exact left_act_lemma (U := U) (e := e) (toUnit _ ≫ D.toPre.c (star a • χ))
        (by simp only [← Category.assoc, unit_act_lemma])
    · exact left_act_lemma (U := U) (e := e) (U.gt e).pG (pG_act_lemma U e)
    · exact left_act_lemma (U := U) (e := e) (toUnit _ ≫ η[D.toPre.P.A])
        (by simp only [← Category.assoc, unit_act_lemma])
  · simp only [φA, Sum.elim_inr, ← Category.assoc, act_lift_xc]

private lemma res_val_lemma {X₀ : Scheme.{0}} {U₀ V₀ W₀ : X₀.Opens} (e₀ : V₀ ≤ U₀) (hW : W₀ ≤ V₀)
    (x : Γ(X₀, U₀)ˣ) :
    (X₀.presheaf.map (homOfLE hW).op).hom (res e₀ x).val =
      (X₀.presheaf.map (homOfLE (hW.trans e₀)).op).hom x.val := by
  show (X₀.presheaf.map (homOfLE e₀).op ≫ X₀.presheaf.map (homOfLE hW).op).hom x.val = _
  rw [← Functor.map_comp]
  rfl

private lemma pull_val_lemma {X₀ Y₀ : Scheme.{0}} (g : Y₀ ⟶ X₀) (U₀ : X₀.Opens) {W₀ : Y₀.Opens}
    (hW : W₀ ≤ g ⁻¹ᵁ U₀) (x : Γ(X₀, U₀)ˣ) :
    (Y₀.presheaf.map (homOfLE hW).op).hom (pullU g U₀ x).val = (g.appLE U₀ W₀ hW).hom x.val :=
  rfl

private lemma corr_val_lemma {X₀ : Scheme.{0}} {V₀ V₁ V₂ W₀ : X₀.Opens} (h₁ : V₀ ≤ V₁) (h₂ : V₀ ≤ V₂)
    (x : Γ(X₀, V₁)ˣ) (y : Γ(X₀, V₂)ˣ) (hE : res h₁ x = res h₂ y) (hW₁ : W₀ ≤ V₁) (hW₂ : W₀ ≤ V₂)
    (hW : W₀ ≤ V₀) :
    (X₀.presheaf.map (homOfLE hW₁).op).hom x.val = (X₀.presheaf.map (homOfLE hW₂).op).hom y.val := by
  have h3 := congrArg (fun z => (X₀.presheaf.map (homOfLE hW).op).hom (Units.val z)) hE
  simp only [res_val_lemma] at h3
  exact h3

private lemma mulGen_val_lemma {X₀ Y₀ : Scheme.{0}} (L₀ : LB X₀) {K₀ K₁ : Type} [Fintype K₀]
    [Fintype K₁] (φ : K₀ → (Y₀ ⟶ X₀)) (ε : K₀ → ℤ) (φ' : K₁ → (Y₀ ⟶ X₀)) (ε' : K₁ → ℤ)
    (t : LB.Gen (LB.LinComb L₀ φ ε)) (t' : LB.Gen (LB.LinComb L₀ φ' ε')) (j : K₀ ⊕ K₁ → L₀.ι)
    {W₀ : Y₀.Opens} (hW : W₀ ≤ LB.wchart L₀ (Sum.elim φ φ') j) :
    (Y₀.presheaf.map (homOfLE hW).op).hom ((LB.mulGen L₀ φ ε φ' ε' t t').s j).val =
      (Y₀.presheaf.map (homOfLE (hW.trans (wchart_inl_le L₀ φ φ' j))).op).hom
          (t.s (j ∘ Sum.inl)).val *
        (Y₀.presheaf.map (homOfLE (hW.trans (wchart_inr_le L₀ φ φ' j))).op).hom
          (t'.s (j ∘ Sum.inr)).val := by
  simp only [LB.mulGen, Units.val_mul, map_mul]
  congr 1 <;> exact res_val_lemma _ _ _

private lemma pullGen_val_lemma {X₀ Y₀ Z₀ : Scheme.{0}} (L₀ : LB X₀) {K₀ : Type} [Fintype K₀]
    (φ : K₀ → (Y₀ ⟶ X₀)) (ε : K₀ → ℤ) (c : LB.Gen (LB.LinComb L₀ φ ε)) (h : Z₀ ⟶ Y₀)
    (j : K₀ → L₀.ι) {W₀ : Z₀.Opens} (hW : W₀ ≤ LB.wchart L₀ (fun k => h ≫ φ k) j) :
    (Z₀.presheaf.map (homOfLE hW).op).hom ((LB.pullGen L₀ φ ε c h).s j).val =
      (h.appLE (LB.wchart L₀ φ j) W₀ (hW.trans (Semi.LBVal.wchart_pull_le L₀ φ h j))).hom
        (c.s j).val :=
  (res_val_lemma _ _ _).trans (pull_val_lemma _ _ _ _)

private lemma charGen_val_lemma {S₀ : Scheme.{0}} (X₁ : Type) [AddCommGroup X₁] (G₀ : Over S₀)
    {Z₀ : Scheme.{0}} (L₀ : LB Z₀) (χ₀ : X₁) (j : PEmpty → L₀.ι)
    {W₀ : (splitTorus S₀ X₁ ⊗ G₀).left.Opens}
    (hW : W₀ ≤ LB.wchart L₀ (Y := (splitTorus S₀ X₁ ⊗ G₀).left) (K := PEmpty) PEmpty.elim j) :
    ((splitTorus S₀ X₁ ⊗ G₀).left.presheaf.map (homOfLE hW).op).hom
        ((charGen X₁ G₀ L₀ χ₀).s j).val =
      ((splitTorus S₀ X₁ ⊗ G₀).left.presheaf.map (homOfLE (le_top : W₀ ≤ ⊤)).op).hom
        (Semi.TorusInj.chiP X₁ G₀ χ₀) :=
  (res_val_lemma _ _ _).trans rfl

private lemma appLE_congr_lemma {X₀ Y₀ : Scheme.{0}} {f g : Y₀ ⟶ X₀} (hfg : f = g) {U₀ : X₀.Opens}
    {W₀ : Y₀.Opens} (h₁ : W₀ ≤ f ⁻¹ᵁ U₀) (h₂ : W₀ ≤ g ⁻¹ᵁ U₀) (x : Γ(X₀, U₀)) :
    (f.appLE U₀ W₀ h₁).hom x = (g.appLE U₀ W₀ h₂).hom x := by
  subst hfg
  rfl

private lemma snd_cancel_lemma {Z₀ : Scheme.{0}} (x y : (thickObj R I e G).left ⟶ Z₀)
    (h : (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ x =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ y) : x = y := by
  have h2 := congrArg ((lift (toUnit (thickObj R I e G) ≫ η[WeightPf.Te D.toPre I e])
    (𝟙 (thickObj R I e G))).left ≫ ·) h
  simpa only [← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp] using h2

theorem lhs_act (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) jA)
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)
    (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) :
    ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom ((lhs U ιD e a χ u).s jA).val =
      ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) *
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hs).hom
        ((lhs U ιD e a χ u).s jA).val := by
  simp only [lhs]
  rw [appLE_mulGen, appLE_mulGen, ← _root_.mul_assoc]
  congr 1
  · have hact : ∀ k : Fin 4, (WeightPf.act (U.gt e)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k =
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
          D.toPre.Oφ (U.gt e).pG (star a • χ) k :=
      fun k => hA_act (U := U) (ιD := ιD) (e := e) (a := a) (χ := χ) (Sum.inl k)
    have key : ∀ k₁ k₂ : Fin 4,
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
            D.toPre.Oφ (U.gt e).pG (star a • χ) k₁ =
          (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫
            D.toPre.Oφ (U.gt e).pG (star a • χ) k₂ →
        jA (Sum.inl k₁) = jA (Sum.inl k₂) :=
      fun k₁ k₂ h => cA (Sum.inl k₁) (Sum.inl k₂) (snd_cancel_lemma (e := e) _ _ h)
    have E := (U.gt e).t_weight (star a • χ) (jA ∘ Sum.inl)
      (Sum.elim (fun x => x.elim) (jA ∘ Sum.inl))
      (fun k₁ k₂ h => key k₁ k₂ ((hact k₁).symm.trans (h.trans (hact k₂))))
      (by
        rintro (k₁ | k₁) (k₂ | k₂) h <;>
          first | exact k₁.elim | exact k₂.elim | exact key k₁ k₂ h)
      (by
        rintro k (k' | k') h <;>
          first | exact k'.elim | exact key k k' ((hact k).symm.trans h))
    have h1 : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (star a • χ)) (jA ∘ Sum.inl) :=
      fun _ hz => wchart_inl_le D.toPre.P.L _ _ jA (ha hz)
    have h2 : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (star a • χ)) (jA ∘ Sum.inl) :=
      fun _ hz => wchart_inl_le D.toPre.P.L _ _ jA (hs hz)
    have hWa : W' ≤ LB.wchart D.toPre.P.L
        (fun k => (WeightPf.act (U.gt e)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k)
        (jA ∘ Sum.inl) :=
      fun _ hz => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (h1 hz) k
    have hWb : W' ≤ LB.wchart D.toPre.P.L
        (Sum.elim (PEmpty.elim : PEmpty → _) (fun k => (snd (WeightPf.Te D.toPre I e)
          (thickObj R I e G)).left ≫ D.toPre.Oφ (U.gt e).pG (star a • χ) k))
        (Sum.elim (fun x => x.elim) (jA ∘ Sum.inl)) := by
      intro z hz
      refine Set.mem_iInter.2 ?_
      rintro (k | k)
      · exact k.elim
      · exact Set.mem_iInter.1 (h2 hz) k
    have E' := corr_val_lemma _ _ _ _ E hWa hWb (le_inf hWa hWb)
    exact (pullGen_val_lemma ..).symm.trans (E'.trans ((mulGen_val_lemma ..).trans
      (congrArg₂ (· * ·) (charGen_val_lemma ..) (pullGen_val_lemma ..))))
  · exact (appLE_pullGen ..).trans ((appLE_congr_lemma (act_lift_xc (U := U) (e := e) (χ := χ)) ..).trans
      (appLE_pullGen ..).symm)

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
