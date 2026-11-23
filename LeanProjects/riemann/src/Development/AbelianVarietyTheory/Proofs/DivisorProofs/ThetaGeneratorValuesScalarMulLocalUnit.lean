import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG.ThetaVal

open GlobalTheory.USep.EvG

theorem one_left' {S X : Scheme.{0}} (G : Over S) [GrpObj G] (t : X ⟶ S) :
    (1 : Over.mk t ⟶ G).left = t ≫ (η[G]).left := by
  rw [Hom.one_def]; rfl

theorem toUnit_eta_left {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    (toUnit G ≫ η[G]).left = G.hom ≫ (η[G]).left := by
  rfl

@[reassoc]
theorem spMap_two' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem eta_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) : (toUnit G' ≫ η[G']).left ≫ F = G'.hom ≫ f ≫ (η[G]).left := by
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hF G'.hom (G'.hom ≫ f) rfl
  have h1 := he 1
  rw [map_one, one_left', one_left'] at h1
  rw [toUnit_eta_left, ← h1, Category.assoc]

variable {V₁ : Type} [CommRing V₁] [IsDomain V₁]

theorem famφB_one (D : DegPre V₁) : D.famφB 0 1 = 𝟙 _ := by
  have h : padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c 0) = 𝟙 D.P.A := by
    rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
    exact mul_one (𝟙 D.P.A)
  show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
  rw [h]; rfl

theorem famφB_two (D : DegPre V₁) : D.famφB 0 2 = D.famφB 0 3 := by
  show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
  rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
  rfl

def chartPullCompPull {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) : ChartPull (LB.LinComb L (fun k => φ k ≫ F) ε) (LB.LinComb (L.pull F) φ ε) (𝟙 Y) :=
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart (L.pull F) φ (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun k => φ k ≫ F) ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L F (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).symm
      simp only [Category.assoc] }

theorem gm_linCombIso_pull' {A A₂ Y₂ : Scheme.{0}} {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A} (w : LB.Iso L₂ (L.pull φ))
    {K : Type} [Fintype K] (φ' : K → (Y₂ ⟶ A₂)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y₂) (z : Z) (p : K → L.ι) (q : K → L₂.ι)
    (hm : r z ∈ LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q) :
    gm r z (LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q)
      ((LB.linCombIso w φ' ε).s (fun k _ => p k, q)) = ∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ hm _).trans (gm_pull r (φ' k) z ((L.pull φ).U (fun _ => p k) ⊓ L₂.U (q k))
    ⟨Set.mem_iInter.1 hm.1 k, Set.mem_iInter.1 hm.2 k⟩ _)

theorem exists_conj_fibre_one {V₁ W₀ : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] (D : DegPre V₁) (ib : W₀ →+* V₁)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : D.P.A.left ⟶ B₀.left) (hβ : IsGrpPullback D.P.A B₀ (spMap ib) β)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ib a) ∈ k₀)
    (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) :
    ∃ σt : (Over.mk (spMap ev) ⊗ D.P.A).left ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left,
      σt ≫ (fst (Over.mk (spMap ev)) D.P.A).left = (fst (Over.mk (spMap ev)) D.P.A).left ≫ spMap σ.toRingHom ∧
      σt ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ β = (snd (Over.mk (spMap ev)) D.P.A).left ≫ β ∧
      ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left, x ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ →
        DefOver k₀ (x ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ β) → x ≫ σt = spMap σ.toRingHom ≫ x := by
  set E := Over.mk (spMap ev) with hE
  set fK := (fst E D.P.A).left with hfK
  set q := (snd E D.P.A).left with hq
  have hw : q ≫ D.P.A.hom = fK ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (fK ≫ spMap ev)
    (fK ≫ spMap (ev.comp ib)) (by rw [Category.assoc, spMap_two'])
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (fK ≫ spMap σ.toRingHom ≫ spMap ev)
    (fK ≫ spMap (ev.comp ib))
    (by rw [Category.assoc, Category.assoc, spMap_two', spMap_conj k₀ _ hf σ hσ])
  let qpt : Over.mk (fK ≫ spMap ev) ⟶ D.P.A := Over.homMk q hw
  let σD := Φ₁.symm (Φ₀ qpt)
  let a0 : Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev) ⟶ E :=
    Over.homMk (fK ≫ spMap σ.toRingHom) (Category.assoc _ _ _)
  let σt : (E ⊗ D.P.A).left ⟶ (E ⊗ D.P.A).left := (lift a0 σD).left
  have hfst : σt ≫ fK = fK ≫ spMap σ.toRingHom := congrArg (fun z => z.left) (lift_fst a0 σD)
  have hsnd : σt ≫ q = σD.left := congrArg (fun z => z.left) (lift_snd a0 σD)
  have hproj : σt ≫ q ≫ β = q ≫ β := by
    rw [reassoc_of% hsnd, ← hΦ₁ σD, MulEquiv.apply_symm_apply, hΦ₀]
    rfl
  refine ⟨σt, hfst, hproj, fun x hx hdef => ?_⟩
  have hEh : (E ⊗ D.P.A).hom = fK ≫ spMap ev := (Over.w (fst E D.P.A)).symm
  let T : Over (Sp V₁) := Over.mk (spMap σ.toRingHom ≫ spMap ev)
  let m1 : T ⟶ E ⊗ D.P.A := Over.homMk (x ≫ σt) (by
    show (x ≫ σt) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hfst, reassoc_of% hx])
  let m2 : T ⟶ E ⊗ D.P.A := Over.homMk (spMap σ.toRingHom ≫ x) (by
    show (spMap σ.toRingHom ≫ x) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hx])
  have hm : m1 = m2 := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      show (x ≫ σt) ≫ fK = (spMap σ.toRingHom ≫ x) ≫ fK
      rw [Category.assoc, hfst, reassoc_of% hx, Category.assoc, hx, Category.comp_id]
    · obtain ⟨Φ₂, hΦ₂⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ
        (spMap σ.toRingHom ≫ spMap ev) (spMap (ev.comp ib))
        (by rw [Category.assoc, spMap_two', spMap_conj k₀ _ hf σ hσ])
      apply Φ₂.injective
      apply Over.OverMorphism.ext
      rw [hΦ₂, hΦ₂]
      show (x ≫ σt) ≫ q ≫ β = (spMap σ.toRingHom ≫ x) ≫ q ≫ β
      obtain ⟨P₀, hP₀⟩ := hdef
      rw [Category.assoc, hproj, Category.assoc, ← hP₀, ← Category.assoc,
        spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  exact congrArg (fun m => m.left) hm

theorem gm_thetaIso {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) {B₀ : Scheme.{0}} {M₀ : LB B₀}
    (β : D.P.A.left ⟶ B₀) (w : LB.Iso D.P.L (M₀.pull β)) {K : Type} [Field K] (r : Sp K ⟶ D.P.A.left) (z : Sp K)
    (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀) → M₀.ι) (hJ : Good D.P.L z J) (hJ₀ : Good M₀ z J₀) :
    gm r z _ ((GlobalTheory.PolDeg.TautFrom.isoPull (chartPullId (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (chartPullCompPull M₀ β (D.famφB 0) (DegPre.famε 1)) (LB.linCombIso w (D.famφB 0) (DegPre.famε 1))).s
        (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β)), fun k => J (r ≫ D.famφB 0 k))) = gwx w z J J₀ r := by
  have hz : r z ∈ (LB.LinComb M₀ (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1)).U (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β))) ⊓
      (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U (fun k => J (r ≫ D.famφB 0 k)) :=
    ⟨hJ₀.mem (fun k => D.famφB 0 k ≫ β) r, hJ.mem (D.famφB 0) r⟩
  refine (GlobalTheory.PolDeg.TautFrom.gm_isoPull _ _ _ r z _ hz).trans ?_
  rw [Category.comp_id]
  have hm : r z ∈ LB.wchart (M₀.pull β) (D.famφB 0) (fun k _ => J₀ (r ≫ (D.famφB 0 k ≫ β))) ⊓
      LB.wchart D.P.L (D.famφB 0) (fun k => J (r ≫ D.famφB 0 k)) :=
    ⟨Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hz.1 k), hz.2⟩
  refine (gm_linCombIso_pull' w (D.famφB 0) (DegPre.famε 1) r z (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β)))
    (fun k => J (r ≫ D.famφB 0 k)) hm).trans ?_
  have h0 : D.famφB 0 0 = 𝟙 _ := rfl
  rw [Fin.prod_univ_four, h0, famφB_one D, famφB_two D]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_one, zpow_neg, one_mul,
    Category.comp_id, Category.id_comp, mul_inv_cancel_right]
  rw [_root_.one_mul, inv_mul_cancel_right]

theorem theta_values : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∃ κ : K, ∀ p : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, DefOver k₀ (spMap ev ≫ p.left ≫ β) → ∃ c ∈ k₀,
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J =
        ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ p.left))⁻¹).val * toStk z (κ * c) := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ θ hθ
  obtain ⟨-, hM₀, hβ, hw, -, -, -⟩ := hFB
  let u := GlobalTheory.PolDeg.TautFrom.isoPull (chartPullId (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (chartPullCompPull M₀ β (D.famφB 0) (DegPre.famε 1)) (LB.linCombIso w (D.famφB 0) (DegPre.famε 1))
  have hu : u.IsGen := GlobalTheory.PolDeg.TautFrom.isoPull_isGen _ _ _ (DVR.linCombIso_isGen w hw _ _)
  have hL : (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hM : (LB.LinComb M₀ (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ hM₀ _ _
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_isoRel hL hM hu
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
  let E := Over.mk (spMap ev)
  let q := (snd E D.P.A).left
  have hqw : q ≫ D.P.A.hom = (fst E D.P.A).left ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  let R : (Sp K ⟶ (E ⊗ D.P.A).left) → Prop := fun x => x ≫ (fst E D.P.A).left = 𝟙 _ ∧ DefOver k₀ (x ≫ q ≫ β)
  have hcases : ∀ k : Fin 4, D.famφB 0 k = 𝟙 _ ∨ D.famφB 0 k ≫ β = D.P.A.hom ≫ spMap ib ≫ (η[B₀]).left := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inl (by show D.famφB 0 1 = _; exact famφB_one D)
    · exact Or.inr (by show D.famφB 0 2 ≫ β = _; rw [famφB_two D]; exact eta_push hβ)
    · exact Or.inr (by show D.famφB 0 3 ≫ β = _; exact eta_push hβ)
  obtain ⟨κ, -, hval⟩ := galois_values k₀ hk₀ (fun k => q ≫ (D.famφB 0 k ≫ β)) (DegPre.famε 1)
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s q) R
    (fun t => by
      obtain ⟨c, hc⟩ := fibre_one_dim D ev (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (hθ K ev)
        (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1) hM₀ u hu s hs t
      exact ⟨c, fun x hR z J hJ => hc x hR.1 z J hJ⟩)
    (fun σ hσ => by
      obtain ⟨σt, hfst, hproj, hfix⟩ := exists_conj_fibre_one D ib B₀ β hβ K ev k₀ hk σ hσ
      refine ⟨σt, fun k => ?_, fun x hR => hfix x hR.1 hR.2⟩
      rcases hcases k with h | h
      · show σt ≫ q ≫ D.famφB 0 k ≫ β = q ≫ D.famφB 0 k ≫ β
        rw [h, Category.id_comp]
        exact hproj
      · show σt ≫ q ≫ D.famφB 0 k ≫ β = q ≫ D.famφB 0 k ≫ β
        have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
        rw [h, reassoc_of% hqw, reassoc_of% hfst, spMap_two'_assoc ib ev, reassoc_of% (spMap_conj k₀ _ hf σ hσ)])
  refine ⟨κ, fun p hdef => ?_⟩
  have hr : (spMap ev ≫ p.left) ≫ D.P.A.hom = spMap ev := by
    rw [Category.assoc, Over.w p]
    exact Category.comp_id _
  let a1 : Over.mk (spMap ev) ⟶ E := Over.homMk (𝟙 (Sp K)) (Category.id_comp _)
  let b1 : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk (spMap ev ≫ p.left) hr
  let x : Sp K ⟶ (E ⊗ D.P.A).left := (lift a1 b1).left
  have hxf : x ≫ (fst E D.P.A).left = 𝟙 _ :=
    congrArg (fun m : Over.mk (spMap ev) ⟶ E => m.left) (lift_fst a1 b1)
  have hxq : x ≫ q = spMap ev ≫ p.left := congrArg (fun m : Over.mk (spMap ev) ⟶ D.P.A => m.left) (lift_snd a1 b1)
  have hRx : R x := ⟨hxf, by
    show DefOver k₀ (x ≫ q ≫ β)
    rw [reassoc_of% hxq]
    exact hdef⟩
  obtain ⟨c, hc, he⟩ := hval x hRx z J₀ hJ₀
  refine ⟨c, hc, ?_⟩
  have e1 : sval s (spMap ev ≫ p.left) z J₀ = toStk z (κ * c) := by
    rw [← he, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s q x z hJ₀, hxq]
  have e2 := gs_isoRel_at hs _ _ (spMap ev ≫ p.left) z (hJ₀.mem (fun k => D.famφB 0 k ≫ β) (spMap ev ≫ p.left))
    (hJ.mem (D.famφB 0) (spMap ev ≫ p.left))
  rw [gm_thetaIso D β w (spMap ev ≫ p.left) z J J₀ hJ hJ₀] at e2
  have e4 : (gwx w z J J₀ (spMap ev ≫ p.left)).val *
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J = toStk z (κ * c) := by
    rw [← e1]; exact e2.symm
  rw [← e4, Units.inv_mul_cancel_left]

end GlobalTheory.USep.EvG.ThetaVal
