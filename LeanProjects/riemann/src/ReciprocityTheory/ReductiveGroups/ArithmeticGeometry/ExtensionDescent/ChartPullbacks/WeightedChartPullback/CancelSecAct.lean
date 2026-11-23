import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WchartPullLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.WeightPf

open Semi

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

abbrev Te (D : DegPre R) (I : Ideal R) (e : ℕ) := splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X

def act : Te D I e ⊗ thickObj R I e G ⟶ thickObj R I e G :=
  lift (fst (Te D I e) (thickObj R I e G) ≫ g.i) (snd _ _) ≫ μ[thickObj R I e G]

def sec : thickObj R I e G ⟶ Te D I e ⊗ thickObj R I e G :=
  lift (toUnit _ ≫ η[Te D I e]) (𝟙 _)

lemma i_q : g.i ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := g.isKernel.w

lemma act_q : act g ≫ g.q = snd (Te D I e) (thickObj R I e G) ≫ g.q := by
  haveI : IsMonHom g.q := g.q_hom
  have hq : g.i ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := i_q g
  have hf : fst (Te D I e) (thickObj R I e G) ≫ toUnit (Te D I e) =
      toUnit (Te D I e ⊗ thickObj R I e G) := toUnit_unique _ _
  simp only [act, Category.assoc, IsMonHom.mul_hom, CartesianMonoidalCategory.lift_map_assoc, hq,
    reassoc_of% hq, reassoc_of% hf, MonObj.lift_comp_one_left]

lemma sec_act : sec (D := D) (G := G) (I := I) (e := e) ≫ act g = 𝟙 _ := by
  haveI : IsMonHom g.i := g.i_hom
  have h1 : sec (D := D) (G := G) (I := I) (e := e) ≫
      lift (fst (Te D I e) (thickObj R I e G) ≫ g.i) (snd (Te D I e) (thickObj R I e G)) =
      lift (toUnit (thickObj R I e G) ≫ η[thickObj R I e G]) (𝟙 _) := by
    simp only [sec, CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.lift_fst_assoc,
      CartesianMonoidalCategory.lift_snd, Category.assoc, IsMonHom.one_hom]
  rw [act, ← Category.assoc, h1, MonObj.lift_comp_one_left]

lemma sec_snd : sec (D := D) (G := G) (I := I) (e := e) ≫ snd (Te D I e) (thickObj R I e G) = 𝟙 _ := by simp [sec]

lemma act_left_pG : (act g).left ≫ g.pG.left = (snd (Te D I e) (thickObj R I e G)).left ≫ g.pG.left := by
  have h : (act g).left ≫ g.q.left = (snd (Te D I e) (thickObj R I e G)).left ≫ g.q.left :=
    congrArg (fun f => f.left) (act_q g)
  simp only [GtCoord.pG, Over.comp_left, Over.map_map_left]
  rw [reassoc_of% h]

omit [IsCommMonObj G] in
lemma Oφ_comp {T T' : Over (Spec (CommRingCat.of R))} (h : T' ⟶ T) (p : T ⟶ D.P.A) (χ : D.X)
    (k : Fin 4) : h.left ≫ D.Oφ p χ k = D.Oφ (h ≫ p) χ k := by
  have hu : h ≫ toUnit T = toUnit T' := toUnit_unique _ _
  fin_cases k
  · change h.left ≫ (padd D.P.A p (toUnit T ≫ D.c χ)).left = (padd D.P.A (h ≫ p) (toUnit T' ≫ D.c χ)).left
    rw [← Over.comp_left]
    congr 1
    simp only [padd]
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, reassoc_of% hu]
  · change h.left ≫ (toUnit T ≫ D.c χ).left = (toUnit T' ≫ D.c χ).left
    rw [← Over.comp_left, ← Category.assoc, hu]
  · change h.left ≫ p.left = (h ≫ p).left
    rw [Over.comp_left]
  · change h.left ≫ (toUnit T ≫ η[D.P.A]).left = (toUnit T' ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, hu]

lemma map_act_pG : (Over.map (thick R I e)).map (act g) ≫ g.pG =
    (Over.map (thick R I e)).map (snd (Te D I e) (thickObj R I e G)) ≫ g.pG := by
  ext
  simp only [Over.comp_left, Over.map_map_left]
  exact act_left_pG g

lemma act_Oφ (χ : D.X) (k : Fin 4) :
    (act g).left ≫ D.Oφ g.pG χ k = (snd (Te D I e) (thickObj R I e G)).left ≫ D.Oφ g.pG χ k := by
  calc (act g).left ≫ D.Oφ g.pG χ k
      = D.Oφ ((Over.map (thick R I e)).map (act g) ≫ g.pG) χ k :=
        Oφ_comp (D := D) ((Over.map (thick R I e)).map (act g)) g.pG χ k
    _ = D.Oφ ((Over.map (thick R I e)).map (snd (Te D I e) (thickObj R I e G)) ≫ g.pG) χ k := by
        rw [map_act_pG g]
    _ = (snd (Te D I e) (thickObj R I e G)).left ≫ D.Oφ g.pG χ k :=
        (Oφ_comp (D := D) ((Over.map (thick R I e)).map (snd (Te D I e) (thickObj R I e G))) g.pG χ k).symm

lemma sec_left_act : (sec (D := D) (G := G) (I := I) (e := e)).left ≫ (act g).left = 𝟙 _ := congrArg (fun f => f.left) (sec_act g)

lemma sec_left_snd : (sec (D := D) (G := G) (I := I) (e := e)).left ≫
    (snd (Te D I e) (thickObj R I e G)).left = 𝟙 _ := congrArg (fun f => f.left) (sec_snd (D := D) (G := G) (I := I) (e := e))

lemma cancel_sec_act {Z : Scheme.{0}} {a b : (thickObj R I e G).left ⟶ Z}
    (h : (act g).left ≫ a = (act g).left ≫ b) : a = b := by
  calc a = ((sec (D := D) (G := G) (I := I) (e := e)).left ≫ (act g).left) ≫ a := by
        rw [sec_left_act g, Category.id_comp]
    _ = (sec (D := D) (G := G) (I := I) (e := e)).left ≫ ((act g).left ≫ a) := Category.assoc _ _ _
    _ = (sec (D := D) (G := G) (I := I) (e := e)).left ≫ ((act g).left ≫ b) := by rw [h]
    _ = b := by rw [← Category.assoc, sec_left_act g, Category.id_comp]

lemma cancel_sec_snd {Z : Scheme.{0}} {a b : (thickObj R I e G).left ⟶ Z}
    (h : (snd (Te D I e) (thickObj R I e G)).left ≫ a = (snd (Te D I e) (thickObj R I e G)).left ≫ b) :
    a = b := by
  calc a = ((sec (D := D) (G := G) (I := I) (e := e)).left ≫
          (snd (Te D I e) (thickObj R I e G)).left) ≫ a := by
        rw [sec_left_snd, Category.id_comp]
    _ = (sec (D := D) (G := G) (I := I) (e := e)).left ≫
          ((snd (Te D I e) (thickObj R I e G)).left ≫ a) := Category.assoc _ _ _
    _ = (sec (D := D) (G := G) (I := I) (e := e)).left ≫
          ((snd (Te D I e) (thickObj R I e G)).left ≫ b) := by rw [h]
    _ = b := by rw [← Category.assoc, sec_left_snd, Category.id_comp]

lemma res_val {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((res h u : Γ(X, V)ˣ) : Γ(X, V)) = (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := rfl

lemma pullU_val {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    ((pullU f U u : Γ(Y, f ⁻¹ᵁ U)ˣ) : Γ(Y, f ⁻¹ᵁ U)) = (f.app U).hom (u : Γ(X, U)) := rfl

lemma rres {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  change (X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op).hom x = _
  rw [← Functor.map_comp]
  rfl

private lemma sres_val_lemma_2 {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    ((ReciprocityTheory.ChartRestriction.G.Semi.res h u : Γ(X, V)ˣ) : Γ(X, V)) =
      (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := rfl

private lemma corr_val_lemma_3 {Y : Scheme.{0}} {OA OC OS A B C PS W : Y.Opens}
    {pA : A ≤ OA} {c1 : C ≤ OC} {m1 : B ≤ C} {pS : PS ≤ OS} {m2 : B ≤ PS}
    (xa : Γ(Y, OA)ˣ) (xc : Γ(Y, OC)ˣ) (xs : Γ(Y, OS)ˣ) (hW : W ≤ A ⊓ B)
    (h : ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_left : A ⊓ B ≤ A) (ReciprocityTheory.ChartRestriction.G.Semi.res pA xa) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (inf_le_right : A ⊓ B ≤ B)
        (ReciprocityTheory.ChartRestriction.G.Semi.res m1 (ReciprocityTheory.ChartRestriction.G.Semi.res c1 xc) *
          ReciprocityTheory.ChartRestriction.G.Semi.res m2 (ReciprocityTheory.ChartRestriction.G.Semi.res pS xs))) :
    (Y.presheaf.map (homOfLE (hW.trans (inf_le_left.trans pA))).op).hom (xa : Γ(Y, OA)) =
      (Y.presheaf.map (homOfLE ((hW.trans inf_le_right).trans (m1.trans c1))).op).hom (xc : Γ(Y, OC)) *
      (Y.presheaf.map (homOfLE ((hW.trans inf_le_right).trans (m2.trans pS))).op).hom
        (xs : Γ(Y, OS)) := by
  have h2 := congrArg (fun u => ((ReciprocityTheory.ChartRestriction.G.Semi.res hW u : Γ(Y, W)ˣ) : Γ(Y, W))) h
  simp only [map_mul, Units.val_mul, sres_val_lemma_2, rres] at h2
  exact h2

lemma t_act (χ : D.X) (jt : Fin 4 → D.P.L.ι) (hjt : LB.Coh D.P.L (D.Oφ g.pG χ) jt)
    (W' : (Te D I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (Te D I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG χ) jt)
    (ha : W' ≤ (act g).left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG χ) jt) :
    ((act g).left.appLE _ W' ha).hom ((g.t χ).s jt).val =
      ((Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom
        (Semi.TorusInj.chiP D.X (thickObj R I e G) χ) *
      ((snd (Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom ((g.t χ).s jt).val := by
  have key := g.t_weight χ jt (Sum.elim PEmpty.elim jt)
    (fun k₁ k₂ h => hjt k₁ k₂ (cancel_sec_act g h))
    (by
      rintro (s₁ | k₁) (s₂ | k₂) h
      · exact s₁.elim
      · exact s₁.elim
      · exact s₂.elim
      · exact hjt k₁ k₂ (cancel_sec_snd h))
    (by
      rintro k (s | k') h
      · exact s.elim
      · exact hjt k k' (cancel_sec_snd ((act_Oφ g χ k).symm.trans h)))
  simp only [LB.pullGen, LB.mulGen, charGen] at key
  have hW1 : W' ≤ LB.wchart D.P.L (fun k => (lift (fst (Te D I e) (thickObj R I e G) ≫ g.i)
      (snd (Te D I e) (thickObj R I e G)) ≫ μ[thickObj R I e G]).left ≫ D.Oφ g.pG χ k) jt := by
    intro x hx
    have h1 : (act g).left.base x ∈ ⋂ k, (D.Oφ g.pG χ k).base ⁻¹' (D.P.L.U (jt k) : Set _) := ha hx
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 h1 k
  have hW2 : W' ≤ LB.wchart D.P.L
      (Sum.elim PEmpty.elim fun k => (snd (Te D I e) (thickObj R I e G)).left ≫ D.Oφ g.pG χ k)
      (Sum.elim PEmpty.elim jt) := by
    intro x hx
    have h1 : (snd (Te D I e) (thickObj R I e G)).left.base x ∈
        ⋂ k, (D.Oφ g.pG χ k).base ⁻¹' (D.P.L.U (jt k) : Set _) := hs hx
    refine Set.mem_iInter.2 ?_
    rintro (s | k)
    · exact s.elim
    · exact Set.mem_iInter.1 h1 k
  have hG := corr_val_lemma_3 _ _ _ (le_inf hW1 hW2) key
  exact hG

end ReciprocityTheory.ChartRestriction.G.Out.WeightPf
