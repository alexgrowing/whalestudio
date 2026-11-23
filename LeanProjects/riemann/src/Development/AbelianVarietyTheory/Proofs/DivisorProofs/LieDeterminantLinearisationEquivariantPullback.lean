import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTransportEquivariantCartesianPreservesComStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameTransportCartesianAutomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkMapIdentityModMaximalOfFixedPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.EqvTrans

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLin

open GlobalTheory.ShFam

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Zm : Model Xo c β}

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem spMap_dualMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [← spMap_comp']
  congr 1
  exact RingHom.ext fun z => by ext <;> simp [dualMap]

theorem frame_ext {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Zm.X} {f g : EigFrame Zm φ x}
    (h : ∀ τ i, f.v τ i = g.v τ i) : f = g := by
  cases f; cases g
  simp only [EigFrame.mk.injEq]
  funext τ i
  exact h τ i

theorem ffMap_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) (k : X ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant k] (h : a ≫ b = k) :
    functionFieldMap k = (functionFieldMap a).comp (functionFieldMap b) := by
  subst h
  have e : Spec.map (CommRingCat.ofHom (functionFieldMap (a ≫ b))) ≫ genericFieldPoint Z =
      Spec.map (CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b))) ≫
        genericFieldPoint Z := by
    rw [specMap_functionFieldMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      specMap_functionFieldMap, ← Category.assoc, ← Category.assoc, specMap_functionFieldMap]
  haveI : Mono (genericFieldPoint Z) := inferInstanceAs (Mono (Z.fromSpecStalk _))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp e))

theorem unitAt_ffMap {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W) [IsDominant q] (x : X)
    {f : W.functionField} (h : UnitAt (q x) f) : UnitAt x (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap x a, ha.map _, (functionFieldMap_algebraMap q x a).symm⟩

theorem field_rearr {K : Type} [Field K] (s a w g c : K) (hg : g ≠ 0) (hc : c ≠ 0) :
    s * a⁻¹ * w = s * (g * w * c) * c⁻¹ * (a⁻¹ * g⁻¹) := by
  field_simp

end Frames

theorem ratLin_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (φ₀ : c.F →+* (X₀ TF.Y Z).functionField) (f₀ : GlobalTheory.ShFam.EigFrame TF.Y φ₀ ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι)) (a : (E →+* ℂ) → ℤ) (D : CartierDiv (X₀ TF.Y Z)), (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ s₀ TF.Y Z = spMap φ₀ → GlobalTheory.HodgeLin.DetEqns TF Z φ₀ f₀ a D → ∀ (Γ : Type) [Group Γ] (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ρ' : Γ →* Aut X'), IsDominant φ → (∀ γ, (ρ' γ).hom ≫ φ ≫ s₀ TF.Y Z = φ ≫ s₀ TF.Y Z) → ∀ (G' : Over X') [GrpObj G'] (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m → RatLin ρ' ((toLB D).pull φ) (LB.isLB_pull (isLB_toLB D) φ) := by
  intro E _ _ _ H Dw l Xo c TF Z _ φ₀ f₀ a D hφ₀ hD Γ _ X' _ φ ρ' hd hρ G' _ ψ act' m hE
  obtain ⟨hG, hact, hm, hmact, hmul, hfix⟩ := hE
  haveI := hd
  have hdom : ∀ γ, IsDominant (ρ' γ).hom := fun γ => by
    haveI : IsIso (ρ' γ).hom := Iso.isIso_hom (ρ' γ)
    infer_instance
  obtain ⟨D', hcls, hD'⟩ := GlobalTheory.T.exists_cartierDivisor_dominant_pullback_with_class (X₀ TF.Y Z) X' φ D

  have hη : genericFieldPoint X' ≫ φ ≫ (barComp TF.Y Z).ι = spMap (functionFieldMap φ) ≫
      ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
        (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) := by
    rw [← Category.assoc, ← specMap_functionFieldMap φ, Category.assoc]; rfl
  obtain ⟨f₀', hf₀'⟩ := f₀.exists_isMap (functionFieldMap φ) rfl hη

  have hch : spMap ((functionFieldMap φ).comp φ₀) = genericFieldPoint X' ≫ φ ≫ s₀ TF.Y Z := by
    rw [spMap_comp', ← hφ₀, ← Category.assoc, ← Category.assoc]
    rw [show spMap (functionFieldMap φ) ≫ (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
        (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) = genericFieldPoint X' ≫ φ from
      specMap_functionFieldMap φ]
    simp only [Category.assoc]
  have hσ : ∀ γ, (functionFieldMap φ).comp φ₀ = (functionFieldMap (ρ' γ).hom).comp ((functionFieldMap φ).comp φ₀) := by
    intro γ
    refine spMap_inj ?_
    have e1 : spMap (functionFieldMap (ρ' γ).hom) ≫ genericFieldPoint X' = genericFieldPoint X' ≫ (ρ' γ).hom :=
      specMap_functionFieldMap _
    rw [spMap_comp' _ (functionFieldMap (ρ' γ).hom), hch, ← Category.assoc (spMap _) (genericFieldPoint X'), e1,
      Category.assoc, hρ]

  choose T hT using fun γ => GlobalTheory.T.eigenFrame_transport_cartesian_automorphism TF.Y (φ ≫ (barComp TF.Y Z).ι) G' ψ act' (ρ' γ) (m γ) hG hact (hm γ)
    (hmact γ) ((functionFieldMap φ).comp φ₀) (genericFieldPoint X') _ rfl f₀'
  have hSx : ∀ γ, (genericFieldPoint X' ≫ (ρ' γ).hom) ≫ φ ≫ (barComp TF.Y Z).ι =
      spMap (functionFieldMap (ρ' γ).hom) ≫ genericFieldPoint X' ≫ φ ≫ (barComp TF.Y Z).ι := by
    intro γ
    rw [← specMap_functionFieldMap (ρ' γ).hom]
    simp only [Category.assoc]
  choose S hS using fun γ => f₀'.exists_isMap (functionFieldMap (ρ' γ).hom) (hσ γ) (hSx γ)

  unfold DetEqns at hD
  choose φy fy A d hDx using fun x : X' => hD (φ x)
  have hxF : ∀ x : X', (show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ φ ≫ (barComp TF.Y Z).ι =
      spMap (φ.stalkMap x).hom ≫ ((show Sp ((X₀ TF.Y Z).presheaf.stalk (φ x)) ⟶ X₀ TF.Y Z from
        (X₀ TF.Y Z).fromSpecStalk (φ x)) ≫ (barComp TF.Y Z).ι) := fun x => by
    rw [← Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]; rfl
  choose F hF using fun x : X' => (fy x).exists_isMap (φ.stalkMap x).hom rfl (hxF x)
  have hχ : ∀ x : X', spMap ((φ.stalkMap x).hom.comp (φy x)) =
      (show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ φ ≫ s₀ TF.Y Z := fun x => by
    rw [spMap_comp', ← (hDx x).1, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ s₀ TF.Y Z) (Scheme.SpecMap_stalkMap_fromSpecStalk φ)
  have hφK : ∀ x : X', (functionFieldMap φ).comp φ₀ =
      (algebraMap (X'.presheaf.stalk x) X'.functionField).comp ((φ.stalkMap x).hom.comp (φy x)) := fun x => by
    refine spMap_inj ?_
    rw [hch, spMap_comp' _ (algebraMap (X'.presheaf.stalk x) X'.functionField), hχ x, ← Category.assoc]
    exact congrArg (· ≫ φ ≫ s₀ TF.Y Z) (specAlgebraMap_fromSpecStalk x).symm
  have hxK : ∀ x : X', genericFieldPoint X' ≫ φ ≫ (barComp TF.Y Z).ι =
      spMap (algebraMap (X'.presheaf.stalk x) X'.functionField) ≫
        ((show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ φ ≫ (barComp TF.Y Z).ι) := fun x => by
    rw [← Category.assoc]
    exact congrArg (· ≫ φ ≫ (barComp TF.Y Z).ι) (specAlgebraMap_fromSpecStalk x).symm
  choose FK hFK using fun x : X' => (F x).exists_isMap (algebraMap (X'.presheaf.stalk x) X'.functionField) (hφK x) (hxK x)

  have hdet : ∀ (x : X') τ, ((FK x).co f₀' τ).det = functionFieldMap φ (d x τ) := by
    intro x τ
    have hφy : φ₀ = (algebraMap ((X₀ TF.Y Z).presheaf.stalk (φ x)) (X₀ TF.Y Z).functionField).comp (φy x) := by
      refine spMap_inj ?_
      rw [← hφ₀, spMap_comp', ← (hDx x).1, ← Category.assoc]
      exact congrArg (· ≫ s₀ TF.Y Z) (specAlgebraMap_fromSpecStalk (φ x)).symm
    have hxy : (show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from
        (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι =
        spMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk (φ x)) (X₀ TF.Y Z).functionField) ≫
          ((show Sp ((X₀ TF.Y Z).presheaf.stalk (φ x)) ⟶ X₀ TF.Y Z from
            (X₀ TF.Y Z).fromSpecStalk (φ x)) ≫ (barComp TF.Y Z).ι) := by
      rw [← Category.assoc]
      exact congrArg (· ≫ (barComp TF.Y Z).ι) (specAlgebraMap_fromSpecStalk (φ x)).symm
    obtain ⟨FyK, hFyK⟩ := (fy x).exists_isMap _ hφy hxy
    have hA : FyK.co f₀ τ = (A x τ).transpose := EigFrame.co_eq fun i => by
      rw [funext (hFyK τ)]
      exact (hDx x).2.2.1 τ i
    obtain ⟨FyKK, hFyKK⟩ := FyK.exists_isMap (functionFieldMap φ) rfl hη
    have e : FyKK = FK x := frame_ext fun τ' i => by
      rw [hFyKK τ' i, hFyK τ' i, hFK x τ' i, hF x τ' i, ← Category.assoc, ← Category.assoc, spMap_dualMap_comp,
        spMap_dualMap_comp]
      congr 3
      exact RingHom.ext fun z => functionFieldMap_algebraMap φ x z
    rw [← e, EigFrame.IsMap.co τ hFyKK hf₀' hη, hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose,
      ← (hDx x).2.1 τ]

  have hgx : ∀ x : X', D'.IsEqn x (Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d x τ ^ (-a τ))) :=
    fun x => hD' x _ (hDx x).2.2.2
  let cc : Γ → X'.functionFieldˣ := fun γ => ∏ τ, ((S γ).isUnit_det_co (T γ) τ).unit ^ (a τ)

  have ratio : ∀ (γ : Γ) (x y : X') (st : X'.presheaf.stalk y →+* X'.presheaf.stalk x),
      (show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ (ρ' γ).hom = spMap st ≫ X'.fromSpecStalk y →
      (∀ z, functionFieldMap (ρ' γ).hom (algebraMap _ X'.functionField z) = algebraMap _ X'.functionField (st z)) →
      ∃ Fs Ft : EigFrame TF.Y ((φ.stalkMap x).hom.comp (φy x))
          (((show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ (ρ' γ).hom) ≫ φ ≫ (barComp TF.Y Z).ι),
        (F y).IsMap st Fs ∧
        (∀ τ i, Ft.v τ i = trv hG.1 (m γ) (X'.fromSpecStalk x) ((F x).v τ i)) ∧
        fnAct ρ' γ (Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d y τ ^ (-a τ))) * (cc γ)⁻¹ =
          Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d x τ ^ (-a τ)) *
            Units.map (algebraMap (X'.presheaf.stalk x) X'.functionField).toMonoidHom
              (∏ τ, (Fs.isUnit_det_co Ft τ).unit ^ (-a τ)) := by
    intro γ x y st hst hstK
    have hχst : (φ.stalkMap x).hom.comp (φy x) = st.comp ((φ.stalkMap y).hom.comp (φy y)) := by
      refine spMap_inj ?_
      calc spMap ((φ.stalkMap x).hom.comp (φy x))
          = (show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ φ ≫ s₀ TF.Y Z := hχ x
        _ = ((show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ (ρ' γ).hom) ≫ φ ≫ s₀ TF.Y Z := by
          rw [Category.assoc, hρ]
        _ = (spMap st ≫ X'.fromSpecStalk y) ≫ φ ≫ s₀ TF.Y Z := by rw [hst]
        _ = spMap st ≫ ((show Sp (X'.presheaf.stalk y) ⟶ X' from X'.fromSpecStalk y) ≫ φ ≫ s₀ TF.Y Z) :=
          Category.assoc _ _ _
        _ = spMap (st.comp ((φ.stalkMap y).hom.comp (φy y))) := by rw [spMap_comp', hχ y]
    have hxs : ((show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ (ρ' γ).hom) ≫ φ ≫
        (barComp TF.Y Z).ι = spMap st ≫ ((show Sp (X'.presheaf.stalk y) ⟶ X' from X'.fromSpecStalk y) ≫ φ ≫
          (barComp TF.Y Z).ι) := by
      rw [hst, Category.assoc]
    obtain ⟨Fs, hFs⟩ := (F y).exists_isMap st hχst hxs
    obtain ⟨Ft, hFt⟩ := GlobalTheory.T.eigenFrame_transport_cartesian_automorphism TF.Y (φ ≫ (barComp TF.Y Z).ι) G' ψ act' (ρ' γ) (m γ) hG hact (hm γ) (hmact γ)
      ((φ.stalkMap x).hom.comp (φy x)) (X'.fromSpecStalk x) _ rfl (F x)
    refine ⟨Fs, Ft, hFs, hFt, ?_⟩
    have hxK2 : (genericFieldPoint X' ≫ (ρ' γ).hom) ≫ φ ≫ (barComp TF.Y Z).ι =
        spMap (algebraMap (X'.presheaf.stalk x) X'.functionField) ≫
          (((show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ (ρ' γ).hom) ≫ φ ≫ (barComp TF.Y Z).ι) := by
      rw [← specAlgebraMap_fromSpecStalk x]
      simp only [Category.assoc]
    obtain ⟨FsK, hFsK⟩ := Fs.exists_isMap (algebraMap (X'.presheaf.stalk x) X'.functionField) (hφK x) hxK2
    obtain ⟨FtK, hFtK⟩ := Ft.exists_isMap (algebraMap (X'.presheaf.stalk x) X'.functionField) (hφK x) hxK2
    obtain ⟨TrK, hTrK⟩ := GlobalTheory.T.eigenFrame_transport_cartesian_automorphism TF.Y (φ ≫ (barComp TF.Y Z).ι) G' ψ act' (ρ' γ) (m γ) hG hact (hm γ) (hmact γ)
      ((functionFieldMap φ).comp φ₀) (genericFieldPoint X') _ rfl (FK x)
    have eT : FtK = TrK := frame_ext fun τ i => by
      rw [hFtK τ i, hFt τ i, hTrK τ i, hFK x τ i, ← trv_map hG.1 (m γ) _ _ ((F x).tan τ i).1]
      congr 1
      exact specAlgebraMap_fromSpecStalk x
    obtain ⟨MainNotions, hSK⟩ := (FK y).exists_isMap (functionFieldMap (ρ' γ).hom) (hσ γ) (hSx γ)
    have eS : FsK = MainNotions := frame_ext fun τ i => by
      rw [hFsK τ i, hFs τ i, hSK τ i, hFK y τ i,
        ← Category.assoc (spMap (dualMap (algebraMap (X'.presheaf.stalk x) X'.functionField))),
        ← Category.assoc (spMap (dualMap (functionFieldMap (ρ' γ).hom))), spMap_dualMap_comp, spMap_dualMap_comp]
      congr 3
      exact RingHom.ext fun z => (hstK z).symm
    have hmat : ∀ τ, (Fs.co Ft τ).map (algebraMap (X'.presheaf.stalk x) X'.functionField) * (FK x).co f₀' τ =
        ((FK y).co f₀' τ).map (functionFieldMap (ρ' γ).hom) * (S γ).co (T γ) τ := by
      intro τ
      have hTP : TrK.co (T γ) τ = (FK x).co f₀' τ := EigFrame.co_eq fun i => by
        have := GlobalTheory.T.tangentTransport_equivariant_cartesian_preserves_comb TF.Y.t (φ ≫ (barComp TF.Y Z).ι) G' ψ (ρ' γ).hom (m γ) hG (hm γ)
          (genericFieldPoint X') ((FK x).v τ) _ (f₀'.v τ i) ((FK x).tan τ) (f₀'.tan τ i) ((FK x).co_spec f₀' τ i)
        rw [funext (hTrK τ), hT γ τ i]
        exact this
      rw [← EigFrame.IsMap.co τ hFsK hFtK hxK2, ← hTP, ← eT, EigFrame.co_mul, eS,
        ← EigFrame.IsMap.co τ hSK (hS γ) (hSx γ), EigFrame.co_mul]
    have key : ∀ τ, Units.map (functionFieldMap (ρ' γ).hom).toMonoidHom (Units.map (functionFieldMap φ).toMonoidHom (d y τ)) *
        ((S γ).isUnit_det_co (T γ) τ).unit = Units.map (functionFieldMap φ).toMonoidHom (d x τ) *
          Units.map (algebraMap (X'.presheaf.stalk x) X'.functionField).toMonoidHom (Fs.isUnit_det_co Ft τ).unit := by
      intro τ
      have e := congrArg Matrix.det (hmat τ)
      rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det, hdet, hdet] at e
      refine Units.ext ?_
      simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, IsUnit.unit_spec]
      rw [mul_comm (functionFieldMap φ (d x τ : (X₀ TF.Y Z).functionField)), ← e]
    simp only [fnAct, cc, map_prod, map_zpow]
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_neg, ← mul_zpow, ← mul_zpow, key τ]
  refine ⟨D', cc, hcls, ?_, ?_, ?_⟩
  · intro γ δ
    have hc : (ρ' (γ * δ)).hom = (ρ' δ).hom ≫ (ρ' γ).hom := by rw [map_mul, Aut.Aut_mul_def]; rfl
    have hσc : functionFieldMap (ρ' (γ * δ)).hom =
        (functionFieldMap (ρ' δ).hom).comp (functionFieldMap (ρ' γ).hom) := ffMap_comp _ _ _ hc.symm
    have hx1 : (genericFieldPoint X' ≫ (ρ' (γ * δ)).hom) ≫ φ ≫ (barComp TF.Y Z).ι =
        spMap (functionFieldMap (ρ' δ).hom) ≫ (genericFieldPoint X' ≫ (ρ' γ).hom) ≫ φ ≫ (barComp TF.Y Z).ι := by
      rw [hc, ← Category.assoc (genericFieldPoint X') (ρ' δ).hom, ← specMap_functionFieldMap (ρ' δ).hom]
      simp only [Category.assoc]
    have hx3 : (genericFieldPoint X' ≫ (ρ' (γ * δ)).hom) ≫ φ ≫ (barComp TF.Y Z).ι =
        ((genericFieldPoint X' ≫ (ρ' δ).hom) ≫ (ρ' γ).hom) ≫ φ ≫ (barComp TF.Y Z).ι := by
      rw [hc]; simp only [Category.assoc]
    obtain ⟨F1, hF1⟩ := (S γ).exists_isMap (functionFieldMap (ρ' δ).hom) (hσ δ) hx1
    obtain ⟨F2, hF2⟩ := (T γ).exists_isMap (functionFieldMap (ρ' δ).hom) (hσ δ) hx1
    obtain ⟨F3, hF3⟩ := GlobalTheory.T.eigenFrame_transport_cartesian_automorphism TF.Y (φ ≫ (barComp TF.Y Z).ι) G' ψ act' (ρ' γ) (m γ) hG hact (hm γ) (hmact γ)
      ((functionFieldMap φ).comp φ₀) (genericFieldPoint X' ≫ (ρ' δ).hom) _ hx3 (T δ)
    obtain ⟨F4, hF4⟩ := GlobalTheory.T.eigenFrame_transport_cartesian_automorphism TF.Y (φ ≫ (barComp TF.Y Z).ι) G' ψ act' (ρ' γ) (m γ) hG hact (hm γ) (hmact γ)
      ((functionFieldMap φ).comp φ₀) (genericFieldPoint X' ≫ (ρ' δ).hom) _ hx3 (S δ)
    have hq : genericFieldPoint X' ≫ (ρ' δ).hom = spMap (functionFieldMap (ρ' δ).hom) ≫ genericFieldPoint X' :=
      (specMap_functionFieldMap _).symm
    have e1 : S (γ * δ) = F1 := frame_ext fun τ i => by
      rw [hS (γ * δ) τ i, hF1 τ i, hS γ τ i, ← Category.assoc (spMap (dualMap (functionFieldMap (ρ' δ).hom))),
        spMap_dualMap_comp, hσc]
    have e3 : T (γ * δ) = F3 := frame_ext fun τ i => by
      rw [hT (γ * δ) τ i, hF3 τ i, hT δ τ i, hmul, trv_comp hG.1 (m δ) (m γ) (hm δ).1.w _ (f₀'.tan τ i).1]
    have e4 : F4 = F2 := frame_ext fun τ i => by
      rw [hF4 τ i, hF2 τ i, hT γ τ i, hS δ τ i, hq, trv_map hG.1 (m γ) _ _ (f₀'.tan τ i).1]
    have hB : ∀ τ, (S (γ * δ)).co (T (γ * δ)) τ =
        ((S γ).co (T γ) τ).map (functionFieldMap (ρ' δ).hom) * (S δ).co (T δ) τ := by
      intro τ
      have h34 : F4.co F3 τ = (S δ).co (T δ) τ := EigFrame.co_eq fun i => by
        have := GlobalTheory.T.tangentTransport_equivariant_cartesian_preserves_comb TF.Y.t (φ ≫ (barComp TF.Y Z).ι) G' ψ (ρ' γ).hom (m γ) hG (hm γ)
          (genericFieldPoint X' ≫ (ρ' δ).hom) ((S δ).v τ) _ ((T δ).v τ i) ((S δ).tan τ) ((T δ).tan τ i)
          ((S δ).co_spec (T δ) τ i)
        rw [← hx3] at this
        rw [funext (hF4 τ), hF3 τ i]
        exact this
      rw [e1, e3, ← EigFrame.co_mul F1 F2 F3, EigFrame.IsMap.co τ hF1 hF2 hx1, ← e4, h34]
    have hu : ∀ τ, ((S (γ * δ)).isUnit_det_co (T (γ * δ)) τ).unit =
        Units.map (functionFieldMap (ρ' δ).hom).toMonoidHom ((S γ).isUnit_det_co (T γ) τ).unit *
          ((S δ).isUnit_det_co (T δ) τ).unit := fun τ => Units.ext (by
      simp only [IsUnit.unit_spec, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [hB τ, Matrix.det_mul, RingHom.map_det]
      rfl)
    simp only [cc, fnAct, hu, mul_zpow, Finset.prod_mul_distrib, map_prod, map_zpow]
  · intro γ x g hg
    obtain ⟨Fs, Ft, -, -, hr⟩ := ratio γ x ((ρ' γ).hom x) ((ρ' γ).hom.stalkMap x).hom
      (Scheme.SpecMap_stalkMap_fromSpecStalk (ρ' γ).hom).symm (functionFieldMap_algebraMap (ρ' γ).hom x)
    have hu : UnitAt ((ρ' γ).hom x)
        ((g * (Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d ((ρ' γ).hom x) τ ^ (-a τ)))⁻¹ : X'.functionFieldˣ) :
          X'.functionField) := by
      have := (hgx ((ρ' γ).hom x)).iff_unitAt.1 hg
      rwa [div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
    refine (hgx x).iff_unitAt.2 ?_
    have hsplit : fnAct ρ' γ g * (cc γ)⁻¹ =
        fnAct ρ' γ (g * (Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d ((ρ' γ).hom x) τ ^ (-a τ)))⁻¹) *
          (fnAct ρ' γ (Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d ((ρ' γ).hom x) τ ^ (-a τ))) * (cc γ)⁻¹) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel_right]
    rw [hsplit, hr, Units.val_mul, Units.val_mul, mul_left_comm, mul_div_cancel_left₀ _ (Units.ne_zero _)]
    exact (unitAt_ffMap (ρ' γ).hom x hu).mul ⟨_, Units.isUnit _, rfl⟩
  · intro γ x g hfx hg
    obtain ⟨st, hst, hres, hstK⟩ := GlobalTheory.T.exists_stalk_map_identity_mod_maximal_of_fixed_point X' (ρ' γ) x hfx
    obtain ⟨Fs, Ft, hFs, hFt, hr⟩ := ratio γ x x st hst hstK

    have hdet1 : ∀ τ, IsLocalRing.residue (X'.presheaf.stalk x) (Fs.co Ft τ).det = 1 := by
      intro τ
      have hxR : (show Sp (IsLocalRing.ResidueField (X'.presheaf.stalk x)) ⟶ X' from X'.fromSpecResidueField x) ≫
          φ ≫ (barComp TF.Y Z).ι = spMap (IsLocalRing.residue (X'.presheaf.stalk x)) ≫
            (((show Sp (X'.presheaf.stalk x) ⟶ X' from X'.fromSpecStalk x) ≫ (ρ' γ).hom) ≫ φ ≫ (barComp TF.Y Z).ι) := by
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ φ ≫ (barComp TF.Y Z).ι) hfx.symm
      obtain ⟨FsR, hFsR⟩ := Fs.exists_isMap (IsLocalRing.residue (X'.presheaf.stalk x)) rfl hxR
      obtain ⟨FtR, hFtR⟩ := Ft.exists_isMap (IsLocalRing.residue (X'.presheaf.stalk x)) rfl hxR
      have hrs : (IsLocalRing.residue (X'.presheaf.stalk x)).comp st = IsLocalRing.residue (X'.presheaf.stalk x) :=
        RingHom.ext hres
      have eR : FsR = FtR := frame_ext fun τ' i => by
        have hv := GlobalTheory.LieMet.isTan_map (IsLocalRing.residue (X'.presheaf.stalk x)) rfl ((F x).tan τ' i)
        rw [hFsR τ' i, hFs τ' i, hFtR τ' i, hFt τ' i,
          ← Category.assoc (spMap (dualMap (IsLocalRing.residue (X'.presheaf.stalk x)))), spMap_dualMap_comp, hrs]
        refine Eq.trans ?_ (trv_map hG.1 (m γ) (IsLocalRing.residue (X'.presheaf.stalk x)) _ ((F x).tan τ' i).1)
        exact (trv_eq_self hG.1 (m γ) _ (fun w hw => hfix γ x hfx _ w _ hw) hv.1).symm
      have e := EigFrame.IsMap.co τ hFsR hFtR hxR
      rw [eR, EigFrame.co_self] at e
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← e, Matrix.det_one]

    obtain ⟨b, hb, hbv⟩ := (hgx x).iff_unitAt.1 hg
    have hWres : IsLocalRing.residue (X'.presheaf.stalk x)
        ((∏ τ, (Fs.isUnit_det_co Ft τ).unit ^ (-a τ) : (X'.presheaf.stalk x)ˣ) : X'.presheaf.stalk x) = 1 := by
      have e : Units.map (IsLocalRing.residue (X'.presheaf.stalk x)).toMonoidHom
          (∏ τ, (Fs.isUnit_det_co Ft τ).unit ^ (-a τ)) = 1 := by
        simp only [map_prod, map_zpow]
        refine Finset.prod_eq_one fun τ _ => ?_
        have e1 : Units.map (IsLocalRing.residue (X'.presheaf.stalk x)).toMonoidHom (Fs.isUnit_det_co Ft τ).unit = 1 :=
          Units.ext (by simp [hdet1 τ])
        rw [e1, one_zpow]
      exact congrArg Units.val e
    refine ⟨st b * ((hb.unit⁻¹ : (X'.presheaf.stalk x)ˣ) : X'.presheaf.stalk x) *
      ((∏ τ, (Fs.isUnit_det_co Ft τ).unit ^ (-a τ) : (X'.presheaf.stalk x)ˣ) : X'.presheaf.stalk x) - 1, ?_, ?_⟩
    · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, map_mul, hres, hWres, map_one, mul_one, ← map_mul,
        IsUnit.mul_val_inv, map_one, sub_self]
    · have hab : algebraMap (X'.presheaf.stalk x) X'.functionField b ≠ 0 := (hb.map _).ne_zero
      have hinv : algebraMap (X'.presheaf.stalk x) X'.functionField ((hb.unit⁻¹ : (X'.presheaf.stalk x)ˣ) :
          X'.presheaf.stalk x) = (algebraMap (X'.presheaf.stalk x) X'.functionField b)⁻¹ := by
        rw [map_units_inv, IsUnit.unit_spec]
      have e2 := congrArg Units.val hr
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe] at e2
      have eg : (g : X'.functionField) = algebraMap (X'.presheaf.stalk x) X'.functionField b *
          (Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d x τ ^ (-a τ)) : X'.functionFieldˣ) := by
        rw [hbv, div_mul_cancel₀ _ (Units.ne_zero _)]
      rw [map_sub, map_one, map_mul, map_mul, ← hstK b, hinv]
      congr 1
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      change _ = functionFieldMap (ρ' γ).hom (g : X'.functionField) * _ * _
      have hcc : ((cc γ : X'.functionFieldˣ) : X'.functionField) ≠ 0 := Units.ne_zero _
      have e2' : functionFieldMap (ρ' γ).hom ((Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d x τ ^ (-a τ)) :
          X'.functionFieldˣ) : X'.functionField) * ((cc γ : X'.functionFieldˣ) : X'.functionField)⁻¹ =
          ((Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d x τ ^ (-a τ)) : X'.functionFieldˣ) : X'.functionField) *
            algebraMap (X'.presheaf.stalk x) X'.functionField
              ((∏ τ, (Fs.isUnit_det_co Ft τ).unit ^ (-a τ) : (X'.presheaf.stalk x)ˣ) : X'.presheaf.stalk x) := e2
      have e3 : functionFieldMap (ρ' γ).hom ((Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d x τ ^ (-a τ)) :
          X'.functionFieldˣ) : X'.functionField) =
          ((Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d x τ ^ (-a τ)) : X'.functionFieldˣ) : X'.functionField) *
            algebraMap (X'.presheaf.stalk x) X'.functionField
              ((∏ τ, (Fs.isUnit_det_co Ft τ).unit ^ (-a τ) : (X'.presheaf.stalk x)ˣ) : X'.presheaf.stalk x) *
            ((cc γ : X'.functionFieldˣ) : X'.functionField) := by
        rw [← e2', inv_mul_cancel_right₀ hcc]
      have hgx0 : ((Units.map (functionFieldMap φ).toMonoidHom (∏ τ, d x τ ^ (-a τ)) : X'.functionFieldˣ) :
          X'.functionField) ≠ 0 := Units.ne_zero _
      rw [eg, map_mul, mul_inv, e3]
      exact field_rearr _ _ _ _ _ hgx0 hcc

end GlobalTheory.HodgeLin
