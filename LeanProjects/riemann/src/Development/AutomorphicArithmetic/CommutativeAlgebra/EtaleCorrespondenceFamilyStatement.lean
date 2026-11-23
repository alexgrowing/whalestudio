import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsSeparatedOfProj
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsComparisonFamilyNatural
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFunctionFieldStatementOne
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFunctionFieldStatementTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechIsCxOfMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosureProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamPullbackAlongSecondMapSmulIotaMultiKaehler
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteEtaleFunctionFieldIntegralClosureDifferentStatement

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option autoImplicit false

section Alg

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

private theorem left_union (I : Finset ι) (J : Finset κ) : lft (uni I J) = I := by
  ext i; simp [lft, uni]

private theorem right_union (I : Finset ι) (J : Finset κ) : rgt (uni I J) = J := by
  ext i; simp [rgt, uni]

private theorem uni_lr (s : Finset (ι ⊕ₗ κ)) : uni (lft s) (rgt s) = s := by
  unfold uni lft rgt
  rw [Finset.toLeft_disjSum_toRight, Finset.map_map]
  ext t; simp

private theorem card_uni_commutative_algebra (I : Finset ι) (J : Finset κ) : (uni I J).card = I.card + J.card := by
  simp [uni]

private def tr (ι : Type) {κ : Type} (j : κ) : ι ⊕ₗ κ := toLex (Sum.inr j)

private def tl {ι : Type} (κ : Type) (i : ι) : ι ⊕ₗ κ := toLex (Sum.inl i)

private theorem tr_mono : StrictMono (tr ι : κ → ι ⊕ₗ κ) := by
  intro a b h
  simp [tr, h]

private theorem tl_mono : StrictMono (tl κ : ι → ι ⊕ₗ κ) := by
  intro a b h
  simp [tl, h]

private theorem image_tr (J : Finset κ) : J.image (tr ι) = uni (∅ : Finset ι) J := by
  ext x
  simp only [tr, uni, Finset.mem_image, Finset.mem_map, Finset.empty_disjSum]
  simp

private theorem image_tl (I : Finset ι) : I.image (tl κ) = uni I (∅ : Finset κ) := by
  ext x
  simp only [tl, uni, Finset.mem_image, Finset.mem_map, Finset.disjSum_empty]
  simp

variable {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

private theorem pullC_mono {τ : κ → ι} (h : StrictMono τ) (φ : E →ₗ[ℂ] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = φ (c (s.image τ)) := by
  have hinj : Set.InjOn τ (s : Set κ) := h.injective.injOn
  have hsign : sortSign τ s = 1 := by
    unfold sortSign
    refine Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ => ?_
    rw [if_neg]
    rintro ⟨hab, hba⟩
    exact lt_asymm (h hab) hba
  simp [pullC, hinj, hsign]

private theorem pull_tr (c : Finset (ι ⊕ₗ κ) → E) (J : Finset κ) :
    pullC (tr ι) (LinearMap.id : E →ₗ[ℂ] E) c J = c (uni ∅ J) := by
  rw [pullC_mono tr_mono]
  exact congrArg c (image_tr J)

private theorem pull_tl (c : Finset (ι ⊕ₗ κ) → E) (I : Finset ι) :
    pullC (tl κ) (LinearMap.id : E →ₗ[ℂ] E) c I = c (uni I ∅) := by
  rw [pullC_mono tl_mono]
  exact congrArg c (image_tl I)

private theorem lift_cocycle (A : Finset (ι ⊕ₗ κ) → Submodule ℂ E) (A' : Finset κ → Submodule ℂ E)
    (hcx : (cech A).IsCx) (hA : ∀ J : Finset κ, J.Nonempty → A' J ≤ A (uni ∅ J)) (p : ℤ)
    (c0 : (cech A).Z p) (b : Finset κ → E)
    (h : pullC (tr ι) (LinearMap.id : E →ₗ[ℂ] E) c0.1 - b ∈ (cech A').B p) :
    ∃ c : (cech A).Z p, (∀ J, c.1 (uni ∅ J) = b J) ∧
      (Submodule.Quotient.mk c : (cech A).H p) = Submodule.Quotient.mk c0 := by
  classical
  have hB : pullC (tr ι) (LinearMap.id : E →ₗ[ℂ] E) c0.1 - b ∈ Submodule.map (deltaL ℂ κ E) (cechC A' (p - 1)) := h
  obtain ⟨e, he, hde⟩ := Submodule.mem_map.1 hB
  rw [UpperTheory.PullbackConnectingMap.mem_cechC] at he
  let et : Finset (ι ⊕ₗ κ) → E := fun s => if lft s = ∅ then e (rgt s) else 0
  have hpe : pullC (tr ι) (LinearMap.id : E →ₗ[ℂ] E) et = e := by
    funext J
    rw [pull_tr]
    simp [et, left_union, right_union]
  have hetC : et ∈ cechC A (p - 1) := by
    rw [UpperTheory.PullbackConnectingMap.mem_cechC]
    intro s
    by_cases hl : lft s = ∅
    · have hs : uni ∅ (rgt s) = s := by
        rw [← hl]
        exact uni_lr s
      have hcard : s.card = (rgt s).card := by
        have := card_uni_commutative_algebra (∅ : Finset ι) (rgt s)
        rw [hs] at this
        simpa using this
      have hne : s.Nonempty ↔ (rgt s).Nonempty := by
        rw [← Finset.card_pos, ← Finset.card_pos, hcard]
      simp only [et, hl, if_true]
      constructor
      · rintro ⟨hsn, hsc⟩
        have hrn := hne.1 hsn
        have hmem := (he (rgt s)).1 ⟨hrn, by rw [← hcard]; exact hsc⟩
        have := hA _ hrn hmem
        rw [hs] at this
        exact this
      · intro hno
        refine (he (rgt s)).2 ?_
        rintro ⟨hrn, hrc⟩
        exact hno ⟨hne.2 hrn, by rw [hcard]; exact hrc⟩
    · simp [et, hl]
  have hcxe := hcx (p - 1) et hetC
  rw [sub_add_cancel] at hcxe
  obtain ⟨hDC, hDD⟩ := hcxe
  have hc0 : c0.1 ∈ (cech A).C p ⊓ LinearMap.ker (cech A).D := c0.2
  rw [Submodule.mem_inf] at hc0
  have hmemZ : c0.1 - (cech A).D et ∈ (cech A).Z p := by
    show _ ∈ (cech A).C p ⊓ LinearMap.ker (cech A).D
    rw [Submodule.mem_inf]
    refine ⟨sub_mem hc0.1 hDC, ?_⟩
    rw [LinearMap.mem_ker, map_sub, hDD, sub_zero]
    exact hc0.2
  refine ⟨⟨_, hmemZ⟩, ?_, ?_⟩
  · intro J
    have h1 : (cech A).D et (uni ∅ J) = (deltaL ℂ κ E) e J := by
      have := congrFun (UpperTheory.PullbackConnectingMap.pullC_delta (tr ι) (LinearMap.id : E →ₗ[ℂ] E) et) J
      rw [pull_tr, hpe] at this
      exact this
    have h2 := congrFun hde J
    rw [Pi.sub_apply, pull_tr] at h2
    show (c0.1 - (cech A).D et) (uni ∅ J) = b J
    rw [Pi.sub_apply, h1, h2]
    abel
  · rw [Submodule.Quotient.eq]
    show c0.1 - (cech A).D et - c0.1 ∈ (cech A).B p
    rw [sub_sub_cancel_left, ← map_neg]
    exact Submodule.mem_map_of_mem (Submodule.neg_mem _ hetC)

end Alg

private theorem aff_mono {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type}
    {U : ι → X.Opens} {B : Finset ι → Subalgebra ℂ X.functionField} (hU : IsAffCover p U B) (s t : Finset ι)
    (hs : s.Nonempty) (h : s ⊆ t) : B s ≤ B t := by
  intro y hy
  obtain ⟨f, rfl⟩ := (hU.ring s hs y).1 hy
  have hle : t.inf U ≤ s.inf U := Finset.inf_mono h
  refine (hU.ring t (hs.mono h) _).2 ⟨X.presheaf.map (homOfLE hle).op f, ?_⟩
  exact X.presheaf.germ_res_apply (homOfLE hle) (genericPoint X) (hU.ne t) f

theorem UpperTheory.etaleCorrespondence_family_statement :
    ∀ (E : UpperTheory.A.EFam), UpperTheory.A.NatP E → UpperTheory.A.NatT E → ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (hY : IsAffCover s' (fun i => c1 ⁻¹ᵁ U i) (rB ℂ Y.functionField x)) (a p : ℕ) (b : Finset (Fin (d + 1)) → DR ℂ Z.functionField) (hb : b ∈ (cech fun I => omB ℂ Z.functionField (rB ℂ Z.functionField x I) a).Z p),
      ∃ bt ∈ (cech fun s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ Y.functionField (RY x j2 (lft s) (rgt s)) a).Z p,
        (∀ J, bt (uni ∅ J) = pr2L j2 (b J)) ∧
        ∃ h : trC (k := ℂ) (K := Z.functionField) (L := Y.functionField) (fun I => bt (uni I ∅)) ∈ (cech fun I => omB ℂ Z.functionField (rB ℂ Z.functionField x I) a).Z p,
          E d Z s _ U (rB ℂ Z.functionField x) hK hU a p (hodgeTrace h1 a p (hodgePull h2 a p ((E d Z s _ U (rB ℂ Z.functionField x) hK hU a p).symm (Submodule.Quotient.mk ⟨b, hb⟩)))) = Submodule.Quotient.mk ⟨_, h⟩ := by
  intro E hP hT d Z Y _ _ s s' _ _ hPr c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU hY a p b hb
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  haveI : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  have hU2 : IsAffCover s' (fun i => c2 ⁻¹ᵁ U i) (R2 x j2) :=
    UpperTheory.etaleCorrespondence_functionField_statement_one d Z Y s s' hPr c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  have hJ : IsAffCover s' (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S)) :=
    UpperTheory.etaleCorrespondence_functionField_statement_two d Z Y s s' hPr c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  have hdr2 : IsDRMap ℂ j2 (pr2L j2) := fun q b v => PullCoc.deRhamPullbackAlongSecondMap_smul_iotaMulti_kaehlerD j2 b q v
  have hdrid : IsDRMap ℂ (AlgHom.id ℂ Y.functionField) (LinearMap.id) := by
    intro q b v
    simp
  have hm1 := UpperTheory.PullbackConnectingMap.pullC_isMap hK hL hU hU2 c2 h2 j2 (pr2L j2) (id : Fin (d + 1) → Fin (d + 1)) hdr2 g2
    (fun i => le_rfl) a
  have hleR : ∀ k : Fin (d + 1), c2 ⁻¹ᵁ U k ≤ (𝟙 Y) ⁻¹ᵁ UpperTheory.A.joinCover c1 c2 U (tr (Fin (d + 1)) k) := by
    intro k
    simp [UpperTheory.A.joinCover, tr]
  have hleL : ∀ k : Fin (d + 1), c1 ⁻¹ᵁ U k ≤ (𝟙 Y) ⁻¹ᵁ UpperTheory.A.joinCover c1 c2 U (tl (Fin (d + 1)) k) := by
    intro k
    simp [UpperTheory.A.joinCover, tl]
  have hmR := UpperTheory.PullbackConnectingMap.pullC_isMap hL hL hJ hU2 (𝟙 Y) (Category.id_comp s') (AlgHom.id ℂ Y.functionField)
    LinearMap.id (tr (Fin (d + 1))) hdrid (Lef.germCompat_id Y) hleR a
  have hmL := UpperTheory.PullbackConnectingMap.pullC_isMap hL hL hJ hY (𝟙 Y) (Category.id_comp s') (AlgHom.id ℂ Y.functionField)
    LinearMap.id (tl (Fin (d + 1))) hdrid (Lef.germCompat_id Y) hleL a
  have hfin := (GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials Z Y s s' c1 h1 inferInstance inferInstance d hK hL g1).1
  have hmT := UpperTheory.PullbackConnectingMap.trL_isMap (ι := Fin (d + 1)) s' h1 hK hL hU hY (fun V hV hV' g => (g1 V hV hV' g).symm) hfin a
  set z := (E d Z s (Fin (d + 1)) U (rB ℂ Z.functionField x) hK hU a p).symm (Submodule.Quotient.mk ⟨b, hb⟩) with hz
  set w := hodgePull h2 a p z with hw
  have hN1 := hP d Z s (Fin (d + 1)) U (rB ℂ Z.functionField x) hK hU d Y s' (Fin (d + 1)) (fun i => c2 ⁻¹ᵁ U i)
    (R2 x j2) hL hU2 c2 h2 j2 (pr2L j2) id hdr2 g2 (fun i => le_rfl) a p hm1 z
  have hN2 := hP d Y s' (Fin (d + 1) ⊕ₗ Fin (d + 1)) (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S))
    hL hJ d Y s' (Fin (d + 1)) (fun i => c2 ⁻¹ᵁ U i) (R2 x j2) hL hU2 (𝟙 Y) (Category.id_comp s')
    (AlgHom.id ℂ Y.functionField) LinearMap.id (tr (Fin (d + 1))) hdrid (Lef.germCompat_id Y) hleR a p hmR w
  have hN3 := hP d Y s' (Fin (d + 1) ⊕ₗ Fin (d + 1)) (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S))
    hL hJ d Y s' (Fin (d + 1)) (fun i => c1 ⁻¹ᵁ U i) (rB ℂ Y.functionField x) hL hY (𝟙 Y) (Category.id_comp s')
    (AlgHom.id ℂ Y.functionField) LinearMap.id (tl (Fin (d + 1))) hdrid (Lef.germCompat_id Y) hleL a p hmL w
  have hT1 := hT d Z s Y s' c1 h1 (Fin (d + 1)) U (rB ℂ Z.functionField x) (rB ℂ Y.functionField x) hK hL hU hY g1 a p hmT w
  rw [hodgePull_id] at hN2 hN3
  rw [hz, LinearEquiv.apply_symm_apply] at hN1
  obtain ⟨c0, hc0⟩ := Submodule.Quotient.mk_surjective _
    (E d Y s' (Fin (d + 1) ⊕ₗ Fin (d + 1)) (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S)) hL hJ a p w)
  rw [← hc0] at hN2
  rw [hN1] at hN2
  simp only [Cx.hmap, Submodule.mapQ_apply] at hN2
  rw [Submodule.Quotient.eq] at hN2
  rw [← neg_sub, Submodule.neg_mem_iff] at hN2
  have hpb : pullC (id : Fin (d + 1) → Fin (d + 1)) (pr2L j2) b = fun J => pr2L j2 (b J) := by
    funext J
    rw [pullC_mono strictMono_id]
    simp
  have hdiff : pullC (tr (Fin (d + 1))) (LinearMap.id : DR ℂ Y.functionField →ₗ[ℂ] DR ℂ Y.functionField) c0.1
      - pullC (id : Fin (d + 1) → Fin (d + 1)) (pr2L j2) b
      ∈ (cech fun J => omB ℂ Y.functionField (R2 x j2 J) a).B p := hN2
  rw [hpb] at hdiff
  have hcx : (cech fun S : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ Y.functionField (RY x j2 (lft S) (rgt S)) a).IsCx :=
    cech_isCx_of_mono ℂ _ _ _ fun s t hs hst => omB_mono _ _ (aff_mono hJ s t hs hst) a
  have hA : ∀ J : Finset (Fin (d + 1)), J.Nonempty → omB ℂ Y.functionField (R2 x j2 J) a
      ≤ omB ℂ Y.functionField (RY x j2 (lft (uni (∅ : Finset (Fin (d + 1))) J)) (rgt (uni (∅ : Finset (Fin (d + 1))) J))) a := by
    intro J _
    rw [left_union, right_union]
    exact omB_mono _ _ le_sup_right a
  obtain ⟨c, hcJ, hcq⟩ := lift_cocycle _ (fun J => omB ℂ Y.functionField (R2 x j2 J) a) hcx hA p c0 _ hdiff
  refine ⟨c.1, c.2, hcJ, ?_⟩
  rw [← hc0, ← hcq] at hN3
  rw [hN3] at hT1
  simp only [Cx.hmap, Submodule.mapQ_apply] at hT1
  have hval : trC (k := ℂ) (K := Z.functionField) (L := Y.functionField) (fun I => c.1 (uni I ∅))
      = UpperTheory.PullbackConnectingMap.trL Z Y (Fin (d + 1)) (pullC (tl (Fin (d + 1))) (LinearMap.id : DR ℂ Y.functionField →ₗ[ℂ] DR ℂ Y.functionField) c.1) := by
    funext I
    show trDR ℂ Z.functionField Y.functionField (c.1 (uni I ∅))
      = trDR ℂ Z.functionField Y.functionField (pullC (tl (Fin (d + 1))) (LinearMap.id : DR ℂ Y.functionField →ₗ[ℂ] DR ℂ Y.functionField) c.1 I)
    rw [pull_tl]
  obtain ⟨m, hm1, hm2⟩ : ∃ m : (cech fun I => omB ℂ Z.functionField (rB ℂ Z.functionField x I) a).Z p,
      m.1 = UpperTheory.PullbackConnectingMap.trL Z Y (Fin (d + 1)) (pullC (tl (Fin (d + 1))) (LinearMap.id : DR ℂ Y.functionField →ₗ[ℂ] DR ℂ Y.functionField) c.1)
      ∧ E d Z s (Fin (d + 1)) U (rB ℂ Z.functionField x) hK hU a p (hodgeTrace h1 a p w) = Submodule.Quotient.mk m :=
    ⟨_, rfl, hT1⟩
  refine ⟨by rw [hval, ← hm1]; exact m.2, ?_⟩
  rw [hm2]
  congr 1
  exact Subtype.ext (hm1.trans hval.symm)
