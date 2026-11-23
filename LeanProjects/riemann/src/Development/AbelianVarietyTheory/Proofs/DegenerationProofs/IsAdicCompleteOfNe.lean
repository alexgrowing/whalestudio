import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

namespace GlobalTheory.GtDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

def scaleGen {M : LB X} (t : LB.Gen M) (c : Γ(X, ⊤)ˣ) : LB.Gen M := ⟨fun i => res le_top c * t.s i⟩

theorem gm_scaleGen {M : LB X} (t : LB.Gen M) (c : Γ(X, ⊤)ˣ) (r : Z ⟶ X) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scaleGen t c).s i) = gm r z ⊤ c * gm r z (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top h c) rfl)

theorem scaleGen_isGen {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
    (ht : t.IsGen) (c : Γ(Y, ⊤)ˣ) : (scaleGen t c).IsGen :=
  isGen_of_gm _ fun y j j' hj hj' => by
    have e1 : gm (𝟙 Y) y (LB.wchart M φ j) ((scaleGen t c).s j) =
        gm (𝟙 Y) y ⊤ c * gm (𝟙 Y) y (LB.wchart M φ j) (t.s j) :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y le_top hj c) rfl)
    have e2 : gm (𝟙 Y) y (LB.wchart M φ j') ((scaleGen t c).s j') =
        gm (𝟙 Y) y ⊤ c * gm (𝟙 Y) y (LB.wchart M φ j') (t.s j') :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y le_top hj' c) rfl)
    rw [e1, e2, gen_trans ht (𝟙 Y) y hj hj']
    exact mul_left_comm _ _ _

theorem corr_of_inj {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hL : L.IsLB)
    (h : FormEq φ' ε' φ ε) {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) {W : Scheme.{0}} (p : W ⟶ Y)
    (hi : Function.Injective p.appTop.hom) (hp : ∀ w J, Good L w J → val t p w J = val t' p w J) :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  obtain ⟨ρ, hρ⟩ := FormalPoint.exists_ratio hL h t t' ht ht'
  have h1 : p.appTop.hom ρ.val = 1 := FormalPoint.appTop_eq_one_of_gm p ρ fun w => by
    obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL w
    exact mul_eq_right.1 ((hρ W p w J hJ).symm.trans (hp w J hJ))
  have h2 : ρ = 1 := Units.ext (hi (h1.trans (map_one _).symm))
  exact corr_of_val hL fun y J hJ => by rw [hρ _ _ y J hJ, h2, map_one, _root_.one_mul]

theorem gm_transfer {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (hr : ∀ k, r ≫ φ k = r' ≫ φ' k) (z : Z) {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j)
    (hj' : r z ∈ LB.wchart L φ j')
    (h : gm r z (LB.wchart L φ j) (t.s j) = gm r' z (LB.wchart L φ' j) (t'.s j)) :
    gm r z (LB.wchart L φ j') (t.s j') = gm r' z (LB.wchart L φ' j') (t'.s j') := by
  have m : ∀ i : K → L.ι, r z ∈ LB.wchart L φ i → r' z ∈ LB.wchart L φ' i := fun i hi =>
    Set.mem_iInter.2 fun k => by
      have h1 : (r ≫ φ k) z ∈ L.U (i k) := Set.mem_iInter.1 hi k
      rw [hr k] at h1
      exact h1
  rw [gen_trans ht r z hj' hj, gen_trans ht' r' z (m _ hj') (m _ hj), h]
  simp only [trF, hr]

theorem mem_wchart_of_eq {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} (r : Z ⟶ Y) (r' : Z ⟶ Y')
    (hr : ∀ k, r ≫ φ k = r' ≫ φ' k) (z : Z) {i : K → L.ι} (hi : r z ∈ LB.wchart L φ i) :
    r' z ∈ LB.wchart L φ' i :=
  Set.mem_iInter.2 fun k => by
    have h1 : (r ≫ φ k) z ∈ L.U (i k) := Set.mem_iInter.1 hi k
    rw [hr k] at h1
    exact h1

theorem valR_transfer {A : Type} [CommRing A] [IsLocalRing A] (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε)} (ht : t.IsGen) (ht' : t'.IsGen) (r : Sp A ⟶ Y) (r' : Sp A ⟶ Y')
    (hr : ∀ k, r ≫ φ k = r' ≫ φ' k) (h : ∀ z J, Good L z J → val t r z J = val t' r' z J) {j : K → L.ι}
    (hj : ⊤ ≤ r ⁻¹ᵁ LB.wchart L φ j) :
    valR r (LB.wchart L φ j) (t.s j).val = valR r' (LB.wchart L φ' j) (t'.s j).val := by
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL (cpt A)
  have h1 := h _ J hJ
  rw [val_of t' r' _ J (fun k => J (r ≫ φ k)) (fun k => by rw [hr k])] at h1
  have hm := (top_le_iff_cpt r _).1 hj
  have h2 := gm_transfer ht ht' r r' hr (cpt A) (hJ.mem φ r) hm h1
  apply toStkA_injective
  exact (toStkA_valR r _ _ hj _).trans ((congrArg Units.val h2).trans
    (toStkA_valR r' _ _ ((top_le_iff_cpt r' _).2 (mem_wchart_of_eq r r' hr _ hm)) _).symm)

theorem valR_spMap_fn {A O : Type} [CommRing A] [CommRing O] (β : O →+* A) (a : O) :
    valR (spMap β) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) = β a := by
  have := (GlobalTheory.ZH.CrdCalc.valR_spMap β (𝟙 (Sp O)) ⊤ le_rfl).2 ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)
  rw [Category.comp_id] at this
  rw [this, GlobalTheory.ZH.CrdCalc.valR_eq (𝟙 (Sp O)) ⊤ le_top]
  congr 1
  have h : (𝟙 (Sp O) : Sp O ⟶ Sp O).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  change (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom
    (((𝟙 (Sp O) : Sp O ⟶ Sp O).appLE ⊤ ⊤ le_top).hom _) = a
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of O)).inv_hom_id_apply a

theorem exists_gen_extend {W F : Type} [CommRing W] [IsLocalRing W] [Field F] (hL : L.IsLB) (κ : W →+* F)
    {φ' : K → (Sp W ⟶ X)} {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} (hφ : ∀ k, spMap κ ≫ φ' k = φ k)
    (s : LB.Gen (LB.LinComb L φ ε)) (hs : s.IsGen) (j : K → L.ι) (hj : ⊤ ≤ LB.wchart L φ' j) (a : Wˣ)
    (ha : κ a = valR (𝟙 (Sp F)) (LB.wchart L φ j) (s.s j).val) :
    ∃ s' : LB.Gen (LB.LinComb L φ' ε), s'.IsGen ∧
      ∀ z J, Good L z J → val s' (spMap κ) z J = val s (𝟙 _) z J := by
  obtain ⟨t, ht⟩ := exists_gen_of_local L hL φ' ε
  let A : Γ(Sp W, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a
  let c : Γ(Sp W, ⊤)ˣ := res hj (t.s j)
  have hr : ∀ k, spMap κ ≫ φ' k = 𝟙 _ ≫ φ k := fun k => (hφ k).trans (Category.id_comp _).symm
  refine ⟨scaleGen t (A * c⁻¹), scaleGen_isGen t ht _, fun z J hJ => ?_⟩
  obtain rfl : z = cpt F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hm : spMap κ (cpt F) ∈ LB.wchart L φ' j := hj trivial
  rw [val_of s (𝟙 _) _ J (fun k => J (spMap κ ≫ φ' k)) (fun k => by rw [hr k])]
  refine gm_transfer (scaleGen_isGen t ht _) hs (spMap κ) (𝟙 _) hr _ hm (hJ.mem φ' _) ?_
  have e1 := gm_scaleGen (M := LB.LinComb L φ' ε) t (A * c⁻¹) (spMap κ) (cpt F) j hm
  have e2 : gm (spMap κ) (cpt F) ⊤ c = gm (spMap κ) (cpt F) (LB.wchart L φ' j) (t.s j) := gm_res _ _ hj trivial _
  refine e1.trans ?_
  rw [map_mul, map_inv, e2]
  refine (inv_mul_cancel_right _ _).trans (Units.ext ?_)
  exact (toStkA_valR (spMap κ) ⊤ (cpt F) le_top A).symm.trans ((congrArg _ ((valR_spMap_fn κ a).trans ha)).trans
    (toStkA_valR (𝟙 (Sp F)) _ (cpt F) ((top_le_iff_cpt _ _).2 (mem_wchart_of_eq _ _ hr _ hm)) (s.s j)))

theorem appTop_injective {W F : Type} [CommRing W] [CommRing F] (κ : W →+* F) (h : Function.Injective κ) :
    Function.Injective (spMap κ).appTop.hom := by
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ)
  intro a b hab
  have e : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((spMap κ).appTop.hom a) =
      κ ((Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom a) := fun a => congrArg (fun q => q.hom a) n
  have := (e a).symm.trans ((congrArg _ hab).trans (e b))
  exact (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.injective (h this)

end Gen

section Desc

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Spec (CommRingCat.of R))}

theorem prod_gtT (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (DegPre.gtφT D T b χ k) ^ DegPre.gtε k =
      (h (cP D T χ * b).left)⁻¹ * h (cP D T χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  have := FormalPoint.prod_gtφT (𝟙 T) b χ h
  simpa only [Over.id_left, Category.id_comp] using this

theorem exists_descend (ρ : T' ⟶ T) (hi : Function.Injective ρ.left.appTop.hom) (ξ' : GtPt D T') (b : T ⟶ D.P.A)
    (hb : ρ ≫ b = ξ'.b) (S : Set D.X) (hS : AddSubmonoid.closure S = ⊤)
    (h : ∀ χ ∈ S, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T b χ) DegPre.gtε), s.IsGen ∧
      ∀ z J, Good D.P.L z J → val s ρ.left z J = val (ξ'.s χ) (𝟙 _) z J) :
    ∃ ξ : GtPt D T, ξ.b = b ∧ ∀ χ z J, Good D.P.L z J → val (ξ.s χ) ρ.left z J = val (ξ'.s χ) (𝟙 _) z J := by
  have one : (LB.oneGen D.P.L (Y := T.left)).IsGen := fun i j =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  have F0 : FormEq (PEmpty.elim : PEmpty → (T.left ⟶ D.P.A.left)) PEmpty.elim (DegPre.gtφT D T b 0) DegPre.gtε :=
    fun U _ h => by rw [prod_gtT, cPoint_zero, _root_.one_mul]; simp
  have cg : ∀ χ χ' : D.X, (DegPre.cubAtT D T (cP D T χ) (cP D T χ') b).IsGen := fun χ χ' =>
    pullGen_isGen _ _ _ _ D.cub.isGen _
  have vm : ∀ χ χ' z J, Good D.P.L z J → val (ξ'.s (χ + χ')) (𝟙 _) z J *
      val (DegPre.cubAtT D T (cP D T χ) (cP D T χ') b) ρ.left z J =
        val (ξ'.s χ) (𝟙 _) z J * val (ξ'.s χ') (𝟙 _) z J := fun χ χ' z J hJ => by
    have e := FormalPoint.val_s_add ξ' (𝟙 T') hJ χ χ'
    have e' := val_cub D.cub ρ hJ (cP D T χ) (cP D T χ') b
    rw [comp_cP, comp_cP, hb] at e'
    rw [Category.id_comp] at e
    exact (congrArg₂ (· * ·) rfl e').trans e
  have all : ∀ χ, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T b χ) DegPre.gtε), s.IsGen ∧
      ∀ z J, Good D.P.L z J → val s ρ.left z J = val (ξ'.s χ) (𝟙 _) z J := fun χ => by
    have hχ : χ ∈ AddSubmonoid.closure S := hS ▸ AddSubmonoid.mem_top χ
    induction hχ using AddSubmonoid.closure_induction with
    | mem χ hχ => exact h χ hχ
    | zero =>
      obtain ⟨s, hs, hv⟩ := exists_gen D.P.isLB F0 _ one
      exact ⟨s, hs, fun z J hJ => (hv _ _ z J hJ).trans ((val_one _).trans
        ((val_corr hJ ξ'.s_zero _).trans (val_one _)).symm)⟩
    | add χ χ' _ _ h₁ h₂ =>
      obtain ⟨s₁, g₁, v₁⟩ := h₁
      obtain ⟨s₂, g₂, v₂⟩ := h₂
      obtain ⟨s, hs, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T b (χ + χ')) (ε' := DegPre.gtε) (fun U _ h => by
          refine (prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
            (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gtT b χ h) (prod_gtT b χ' h))
            (prod_neg _ _ (prod_cub (cP D _ χ) (cP D _ χ') b h))).trans ?_
          rw [prod_gtT, cPoint_add]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel)
        (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ s₁ s₂)
          (LB.invGen D.P.L _ _ (DegPre.cubAtT D T (cP D T χ) (cP D T χ') b)))
        (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) (invGen_isGen _ _ _ _ (cg χ χ')))
      refine ⟨s, hs, fun z J hJ => (hv _ _ z J hJ).trans ?_⟩
      refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        ((congrArg₂ (· * ·) (v₁ z J hJ) (v₂ z J hJ)).trans (vm χ χ' z J hJ).symm)) (val_inv _ _))).trans ?_
      exact mul_inv_cancel_right _ _
  choose s hs hv using all
  refine ⟨⟨b, s, hs, corr_of_inj D.P.isLB F0 (hs 0) one ρ.left hi fun z J hJ => ?_,
    fun χ χ' => corr_of_inj D.P.isLB (fun U _ h => ?_) (mulGen_isGen _ _ _ _ _ _ _ (hs _) (cg χ χ'))
      (mulGen_isGen _ _ _ _ _ _ _ (hs _) (hs _)) ρ.left hi fun z J hJ => ?_⟩, rfl, hv⟩
  · exact (hv 0 z J hJ).trans (((val_corr hJ ξ'.s_zero _).trans (val_one _)).trans (val_one _).symm)
  · refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_gtT b χ h) (prod_gtT b χ' h)).trans
      (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := thK) (U := U) _ (prod_gtT b (χ + χ') h)
        (prod_cub (cP D _ χ) (cP D _ χ') b h)).symm)
    rw [cPoint_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · exact (val_mul hJ _ _ _).trans (((congrArg₂ (· * ·) (hv _ z J hJ) rfl).trans ((vm χ χ' z J hJ).trans
      (congrArg₂ (· * ·) (hv _ z J hJ) (hv _ z J hJ)).symm)).trans (val_mul hJ _ _ _).symm)

end Desc

section Pts

theorem exists_factor {V O : Type} [CommRing V] [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (q : X ⟶ Sp V)
    [LocallyOfFiniteType q] (j : V →+* O) (y : Sp O ⟶ X) (hy : y ≫ q = spMap j) :
    ∃ s : Finset O, ∀ (W : Type) [CommRing W] (f : V →+* W) (κ : W →+* O), Function.Injective κ → κ.comp f = j →
      (∀ x ∈ s, x ∈ κ.range) → ∃ y' : Sp W ⟶ X, y' ≫ q = spMap f ∧ spMap κ ≫ y' = y := by
  classical
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y (cpt O)) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    exact (top_le_iff_cpt y U).2 hz (Set.mem_univ x)
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, U) ⟶ CommRingCat.of O, Spec.map φ ≫ hU.fromSpec = y :=
    ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec y hr), by rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of V ⟶ Γ(X, U), Spec.map ρ = hU.fromSpec ≫ q := ⟨_, Spec.map_preimage _⟩
  have hft : ρ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hρ]
    infer_instance
  have hj : ρ ≫ φ = CommRingCat.ofHom j := Spec.map_injective (by
    rw [Spec.map_comp, hρ, ← Category.assoc, hφ, hy])
  letI := ρ.hom.toAlgebra
  obtain ⟨s, hs⟩ := (hft : Algebra.FiniteType V Γ(X, U)).out
  refine ⟨s.image φ.hom, fun W _ f κ hκ hf hs' => ?_⟩
  have hmem : ∀ a, φ.hom a ∈ κ.range := by
    intro a
    have ha : a ∈ Algebra.adjoin V (s : Set Γ(X, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hs' _ (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact ⟨f r, (DFunLike.congr_fun hf r).trans (congrArg (fun q => q.hom r) hj).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let e : W ≃+* κ.range := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun a b h => hκ (congrArg Subtype.val h), κ.rangeRestrict_surjective⟩
  let ψ : Γ(X, U) →+* W := e.symm.toRingHom.comp (φ.hom.codRestrict κ.range hmem)
  have hψ : ∀ a, κ (ψ a) = φ.hom a := fun a => congrArg Subtype.val (e.apply_symm_apply ⟨_, hmem a⟩)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hρ, ← Spec.map_comp]
    congr 1
    ext r
    exact hκ ((hψ _).trans ((congrArg (fun q => q.hom r) hj).trans (DFunLike.congr_fun hf r).symm))
  · rw [← hφ, ← Category.assoc]
    congr 1
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact hψ a

theorem isAdicComplete_of_ne {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] {I : Ideal W} (h0 : I ≠ ⊥) (h1 : I ≠ ⊤) : IsAdicComplete I W := by
  have hle : I ≤ IsLocalRing.maximalIdeal W := IsLocalRing.le_maximalIdeal h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hϖ
  have he' : IsLocalRing.maximalIdeal W ^ e = I := by
    rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hm : ∀ n, I ^ n • (⊤ : Submodule W W) ≤ IsLocalRing.maximalIdeal W ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hle n)
  have : IsHausdorff I W := ⟨fun x hx => IsHausdorff.haus' (I := IsLocalRing.maximalIdeal W) x fun n => (hx n).mono (hm n)⟩
  have : IsPrecomplete I W := ⟨fun u hu => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal W) u fun {m n} hmn => (hu hmn).mono (hm m)
    refine ⟨L, fun n => (hu (Nat.le_mul_of_pos_left n e.succ_pos)).trans ((hL _).mono (Submodule.smul_mono_left ?_))⟩
    rw [pow_mul, ← he']
    exact Ideal.pow_right_mono (Ideal.pow_le_pow_right e.le_succ) n⟩
  exact ⟨⟩

end Pts

end GlobalTheory.GtDescent
