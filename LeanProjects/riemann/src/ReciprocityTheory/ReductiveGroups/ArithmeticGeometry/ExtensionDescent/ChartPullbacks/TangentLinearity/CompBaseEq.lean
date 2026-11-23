import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.PairProp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.WchartInlLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ActActA

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

lemma appLE_res {A B : Scheme.{0}} (f : A ⟶ B) {U V : B.Opens} (hVU : V ≤ U) {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ V) (x : Γ(B, U)) :
    (f.appLE V W e).hom ((B.presheaf.map (homOfLE hVU).op).hom x) =
      (f.appLE U W (e.trans (f.preimage_mono hVU))).hom x :=
  congrArg (fun φ => φ.hom x) (Scheme.Hom.map_appLE f e (homOfLE hVU).op)

lemma res_appTop {A B : Scheme.{0}} (f : A ⟶ B) {W : A.Opens} (hW : W ≤ f ⁻¹ᵁ ⊤) (x : Γ(B, ⊤)) :
    (A.presheaf.map (homOfLE hW).op).hom (f.appTop.hom x) = (f.appLE ⊤ W hW).hom x := by
  have : f.app ⊤ ≫ A.presheaf.map (homOfLE hW).op = f.appLE ⊤ W hW := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  exact congrArg (fun φ => φ.hom x) this

theorem comp_base_eq' {A B C : Scheme.{0}} {a b : A ⟶ B} {ψ : B ⟶ C} (h : a ≫ ψ = b ≫ ψ) (z : A) :
    ψ (a z) = ψ (b z) := by
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

lemma act_mem_of {K : Type} [Fintype K] (φ : K → ((thickObj R I e G).left ⟶ D.toPre.P.A.left))
    (hφ : ∀ k, (WeightPf.act (U.gt e)).left ≫ φ k =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ k) (j : K → D.toPre.P.L.ι)
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hs : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      LB.wchart D.toPre.P.L φ j) :
    W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L φ j := by
  intro z hz
  refine Set.mem_iInter.2 fun k => ?_
  have h1 := Set.mem_iInter.1 (hs hz) k
  simp only [Set.mem_preimage] at h1 ⊢
  rw [comp_base_eq' (hφ k) z]
  exact h1

include hO in

theorem rho_inv_loc
    (hi : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
        (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i)
    (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) (hρ : PairProp U ιD ιG e a χ u ρ)
    (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (jB : Fin 4 → D.toPre.P.L.ι)
    (cA : LB.Coh D.toPre.P.L (φA U ιD e a χ) jA) (cB : LB.Coh D.toPre.P.L (φB U ιG e a χ) jB)
    (cAB : ∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB k = jA k')
    (W' : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens)
    (hsV : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ⊓ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA))
    (ht1 : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ ⊤)
    (ht2 : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ ⊤) :
    ((WeightPf.act (U.gt e)).left.appLE ⊤ W' ht1).hom ρ.val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE ⊤ W' ht2).hom ρ.val := by
  have hsA : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) := hsV.trans ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.preimage_mono inf_le_right)
  have hsB : W' ≤ (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) := hsV.trans ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.preimage_mono inf_le_left)
  have haA : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) := act_mem_of U e _ (hA_act U ιD e a χ) jA W' hsA
  have haB : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) := act_mem_of U e _ (hB_act U ιD ιG e a χ hO) jB W' hsB
  have haV : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ ((LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)) := fun z hz => ⟨haB hz, haA hz⟩
  have hP : (res (inf_le_right : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)) ((lhs U ιD e a χ u).s jA)).val =
      (res (le_top : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ ⊤) ρ).val * (res (inf_le_left : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB)) ((rhs U ιG e a χ).s jB)).val := by
    rw [← Units.val_mul]
    exact congrArg Units.val (hρ jA jB cA cB cAB)

  have hA1 := congrArg ((WeightPf.act (U.gt e)).left.appLE _ W' haV).hom hP
  rw [map_mul] at hA1
  have e1 : ((WeightPf.act (U.gt e)).left.appLE _ W' haV).hom (res (inf_le_right : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)) ((lhs U ιD e a χ u).s jA)).val =
      ((WeightPf.act (U.gt e)).left.appLE (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) W' haA).hom ((lhs U ιD e a χ u).s jA).val :=
    appLE_res (WeightPf.act (U.gt e)).left inf_le_right haV _
  have e2 : ((WeightPf.act (U.gt e)).left.appLE _ W' haV).hom (res (le_top : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ ⊤) ρ).val =
      ((WeightPf.act (U.gt e)).left.appLE ⊤ W' ht1).hom ρ.val :=
    appLE_res (WeightPf.act (U.gt e)).left le_top haV _
  have e3 : ((WeightPf.act (U.gt e)).left.appLE _ W' haV).hom (res (inf_le_left : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB)) ((rhs U ιG e a χ).s jB)).val =
      ((WeightPf.act (U.gt e)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' haB).hom ((rhs U ιG e a χ).s jB).val :=
    appLE_res (WeightPf.act (U.gt e)).left inf_le_left haV _
  rw [e1, e2, e3, lhs_act U ιD e a χ u jA cA W' hsA haA,
    rhs_act U ιD ιG e a χ hO hi jB cB W' hsB haB] at hA1

  have hS1 := congrArg ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hsV).hom hP
  rw [map_mul] at hS1
  have f1 : ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hsV).hom (res (inf_le_right : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)) ((lhs U ιD e a χ u).s jA)).val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) W' hsA).hom ((lhs U ιD e a χ u).s jA).val :=
    appLE_res (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left inf_le_right hsV _
  have f2 : ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hsV).hom (res (le_top : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ ⊤) ρ).val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE ⊤ W' ht2).hom ρ.val :=
    appLE_res (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left le_top hsV _
  have f3 : ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE _ W' hsV).hom (res (inf_le_left : (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) ⊓ (LB.wchart D.toPre.P.L (φA U ιD e a χ) jA) ≤ (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB)) ((rhs U ιG e a χ).s jB)).val =
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' hsB).hom ((rhs U ιG e a χ).s jB).val :=
    appLE_res (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left inf_le_left hsV _
  rw [f1, f2, f3] at hS1

  have hchi : IsUnit (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom
      (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ))) := by
    unfold Semi.TorusInj.chiP
    exact ((charUnit _ _ _).isUnit.map _).map _
  have hR : IsUnit (((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' hsB).hom ((rhs U ιG e a χ).s jB).val) :=
    ((rhs U ιG e a χ).s jB).isUnit.map _
  rw [hS1] at hA1
  have key : ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE ⊤ W' ht2).hom ρ.val * (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom
      (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) * ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' hsB).hom ((rhs U ιG e a χ).s jB).val) =
      ((WeightPf.act (U.gt e)).left.appLE ⊤ W' ht1).hom ρ.val * (((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom
      (Semi.TorusInj.chiP D.toPre.X (thickObj R I e G) (star a • χ)) * ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appLE (LB.wchart D.toPre.P.L (φB U ιG e a χ) jB) W' hsB).hom ((rhs U ιG e a χ).s jB).val) := by
    rw [← hA1]; ring
  exact ((hchi.mul hR).mul_right_cancel key).symm

include hO in

theorem rho_inv
    (hi : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
        (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i)
    (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) (hρ : PairProp U ιD ιG e a χ u ρ) :
    (WeightPf.act (U.gt e)).left.appTop.hom ρ.val =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop.hom ρ.val := by
  classical
  choose idx hidx using fun w : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left =>
    idx_exists D.toPre.P.L D.toPre.P.isLB
      ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w)
  let W : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left →
      (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left.Opens := fun w =>
    (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ⁻¹ᵁ
      (LB.wchart D.toPre.P.L (φB U ιG e a χ) (fun k => idx w (φB U ιG e a χ k)) ⊓
        LB.wchart D.toPre.P.L (φA U ιD e a χ) (fun k => idx w (φA U ιD e a χ k)))
  have hc : ⨆ w, W w = ⊤ := by
    refine eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, ?_⟩
    exact ⟨Set.mem_iInter.2 fun k => hidx z _, Set.mem_iInter.2 fun k => hidx z _⟩
  refine eq_local W hc _ _ (fun w => ?_)
  have r1 := res_appTop (WeightPf.act (U.gt e)).left (W := W w) (fun _ _ => trivial) ρ.val
  have r2 := res_appTop (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left (W := W w)
    (fun _ _ => trivial) ρ.val
  exact r1.trans ((rho_inv_loc U ιD ιG e a χ hO u hi ρ hρ _ _ (fun k1 k2 h => congrArg (idx w) h)
    (fun k1 k2 h => congrArg (idx w) h) (fun k k' h => congrArg (idx w) h) (W w) le_rfl
    (fun _ _ => trivial) (fun _ _ => trivial)).trans r2.symm)

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
