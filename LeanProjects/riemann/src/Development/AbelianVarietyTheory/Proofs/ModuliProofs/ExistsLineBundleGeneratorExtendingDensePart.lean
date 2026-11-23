import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericExtend

theorem coheight_apply_le_one {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] {y : Y}
    (h : Order.coheight y ≤ 1) : Order.coheight (p y) ≤ 1 := by
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun x₁ hx₁ ↦ ?_
  obtain ⟨y₁, hy₁, rfl⟩ := Flat.generalizingMap p (show x₁ ⤳ p y from hx₁.le)
  have hlt : y < y₁ := lt_of_le_not_ge hy₁ fun h' ↦
    hx₁.not_ge (show p y ⤳ p y₁ from (show y ⤳ y₁ from h').map p.continuous)
  have h0 := (Order.coheight_le_coe_iff (n := 1)).1 h y₁ hlt
  rw [Nat.cast_one, ENat.lt_one_iff_eq_zero, Order.coheight_eq_zero] at h0 ⊢
  intro x₂ hx₂
  obtain ⟨y₂, hy₂, rfl⟩ := Flat.generalizingMap p (show x₂ ⤳ p y₁ from hx₂)
  exact (show y₁ ⤳ y₂ from h0 hy₂).map p.continuous

theorem exists_lift {X U T : Scheme.{0}} (j : U ⟶ X) [IsPreimmersion j] [Flat j] (g : T ⟶ X)
    (h : Set.range g ⊆ Set.range j) : ∃ κ : T ⟶ U, κ ≫ j = g := by
  have hs : Surjective (pullback.fst g j) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun t ↦ h ⟨t, rfl⟩⟩
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst g j)
  have : IsOpenImmersion (pullback.fst g j) :=
    IsOpenImmersion.of_isIso_stalkMap _ ⟨(pullback.fst g j).isEmbedding, by
      rw [(pullback.fst g j).surjective.range_eq]; exact isOpen_univ⟩
  have : IsIso (pullback.fst g j) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact ⟨inv (pullback.fst g j) ≫ pullback.snd g j, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem exists_specializes_mem_range {X U : Scheme.{0}} (j : U ⟶ X) [IsDominant j] [QuasiCompact j]
    (x : X) : ∃ ξ ∈ Set.range j, ξ ⤳ x := by
  have hg := (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  refine ⟨_, genericPoints_subset_range_of_isDominant j ?_, hg.specializes mem_irreducibleComponent⟩
  change closure _ ∈ irreducibleComponents X
  rw [hg.def]
  exact irreducibleComponent_mem_irreducibleComponents x

def ExtAt {Q Y : Scheme.{0}} (J : Q ⟶ Y) (W : Y.Opens) (f : Γ(Q, J ⁻¹ᵁ W)) (y : Y) : Prop :=
  ∃ (V : Y.Opens) (h : V ≤ W) (s : Γ(Y, V)), y ∈ V ∧
    (J.appLE V (J ⁻¹ᵁ V) le_rfl).hom s = resG Q (J.preimage_mono h) f

theorem extAt_apply {Q Y : Scheme.{0}} (J : Q ⟶ Y) [IsPreimmersion J] (W : Y.Opens)
    (f : Γ(Q, J ⁻¹ᵁ W)) (q : Q) (hq : J q ∈ W) : ExtAt J W f (J q) := by
  obtain ⟨σ, hσ⟩ := J.stalkMap_surjective q (Q.presheaf.germ (J ⁻¹ᵁ W) q hq f)
  obtain ⟨V, hV, s, rfl⟩ := Y.presheaf.exists_germ_eq σ
  rw [Scheme.Hom.germ_stalkMap_apply] at hσ
  obtain ⟨O, hO, i₁, i₂, hh⟩ := Q.presheaf.germ_eq q _ _ _ _ hσ
  obtain ⟨A, hA, hAO⟩ := J.isEmbedding.isInducing.isOpen_iff.1 O.isOpen
  let V' : Y.Opens := ⟨A, hA⟩ ⊓ V ⊓ W
  have hle : J ⁻¹ᵁ V' ≤ O := fun z hz ↦ by
    rw [← SetLike.mem_coe, ← hAO]; exact hz.1.1
  refine ⟨V', inf_le_right, resG Y (inf_le_left.trans inf_le_right) s,
    ⟨⟨by rw [← SetLike.mem_coe, ← hAO] at hO; exact hO, hV⟩, hq⟩, ?_⟩
  have := congrArg (resG Q hle) hh
  rw [appLE_res_apply]
  refine Eq.trans ?_ (this.trans (resG_resG i₂.le hle f))
  exact (resG_resG i₁.le hle _).symm

theorem exists_app_eq {Q Y : Scheme.{0}} [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]
    (J : Q ⟶ Y) [IsPreimmersion J] (hJ : ∀ V, Function.Injective (J.app V).hom) (W : Y.Opens)
    (f : Γ(Q, J ⁻¹ᵁ W)) (h : ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range J → ExtAt J W f y) :
    ∃ s : Γ(Y, W), (J.app W).hom s = f := by
  have h' : ∀ y : {y : Y // ExtAt J W f y}, ExtAt J W f y := fun y ↦ y.2
  choose V hV s hy hs using h'
  have hm : ∀ y, ExtAt J W f y → y ∈ iSup V := fun y hy' ↦ Opens.mem_iSup.2 ⟨⟨y, hy'⟩, hy _⟩
  have hW : iSup V ≤ W := iSup_le hV
  obtain ⟨s', hs', -⟩ := Y.sheaf.existsUnique_gluing' V (iSup V) (fun i ↦ homOfLE (le_iSup V i))
    le_rfl s fun a b ↦ by
      apply injective_appLE_of_eq J (W := J ⁻¹ᵁ (V a ⊓ V b)) rfl (hJ _)
      have h₁ := congrArg (resG Q (J.preimage_mono (inf_le_left : V a ⊓ V b ≤ _))) (hs a)
      have h₂ := congrArg (resG Q (J.preimage_mono (inf_le_right : V a ⊓ V b ≤ _))) (hs b)
      rw [resG_resG, res_appLE_apply] at h₁ h₂
      exact (appLE_res_apply J inf_le_left _ _).trans
        ((h₁.trans h₂.symm).trans (appLE_res_apply J inf_le_right _ _).symm)
  obtain ⟨s₀, hs₀⟩ := (bijective_resG_of_coheight_le_one hW fun y hy h1 ↦ hm y (by
    by_cases hr : y ∈ Set.range J
    · obtain ⟨q, rfl⟩ := hr
      exact extAt_apply J W f q hy
    · exact h y hy h1 hr)).2 s'
  refine ⟨s₀, Q.sheaf.eq_of_locally_eq' (fun i ↦ J ⁻¹ᵁ V i) (J ⁻¹ᵁ W)
    (fun i ↦ homOfLE (J.preimage_mono (hV i)))
    (fun q hq ↦ Opens.mem_iSup.2 ⟨⟨_, extAt_apply J W f q hq⟩, hy _⟩) _ _ fun i ↦ ?_⟩
  refine Eq.trans ?_ (hs i)
  have e : s i = resG Y (hV i) s₀ := by
    rw [← hs' i, ← hs₀]
    exact resG_resG hW (le_iSup V i) s₀
  rw [e, appLE_res_apply]
  rfl

theorem extAt_of_generic {Q Y H Z : Scheme.{0}} [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]
    [IsReduced Q] (J : Q ⟶ Y) [IsPreimmersion J] (φ : H ⟶ Y) [IsPreimmersion φ] (k : Z ⟶ H)
    (ψ : Z ⟶ Q) (w : ψ ≫ J = k ≫ φ) (W : Y.Opens) (f : Γ(Q, J ⁻¹ᵁ W)) (s : Γ(H, φ ⁻¹ᵁ W))
    {O : Z.Opens} (h₁ : O ≤ k ⁻¹ᵁ φ ⁻¹ᵁ W) (h₂ : O ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ W)
    (hs : (k.appLE _ O h₁).hom s = (ψ.appLE _ O h₂).hom f) (z : Z) (hz : z ∈ O) (h : H)
    (hh : φ h ∈ W) (hg : ∀ y, y ⤳ φ h → φ (k z) ⤳ y) : ExtAt J W f (φ h) := by
  obtain ⟨V, hV, s₀, hhV, hs₀⟩ := extAt_apply φ W s h hh
  let C : irreducibleComponents Y := ⟨_, irreducibleComponent_mem_irreducibleComponents (φ h)⟩
  have hξ := (isIrreducible_irreducibleComponent (x := φ h)).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  have hw : J (ψ z) = φ (k z) := by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  let V' := V ⊓ IsNormalScheme.component C
  have hV' : φ h ∈ V' := ⟨hhV, mem_irreducibleComponent⟩
  refine ⟨V', inf_le_left.trans hV, resG Y inf_le_left s₀, hV', ?_⟩
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  intro q hq
  exfalso
  have hqV := Q.basicOpen_le _ hq
  obtain ⟨A, hA, hAO⟩ := J.isEmbedding.isInducing.isOpen_iff.1 (Q.basicOpen
    ((J.appLE V' (J ⁻¹ᵁ V') le_rfl).hom (resG Y inf_le_left s₀) -
      resG Q (J.preimage_mono (inf_le_left.trans hV)) f)).isOpen
  have hq' : J q ∈ A := by rw [← SetLike.mem_coe, ← hAO] at hq; exact hq
  have hzA : J (ψ z) ∈ A := by
    rw [hw]
    exact (hg _ (hξ.specializes mem_irreducibleComponent)).mem_open hA
      ((hξ.mem_open_set_iff hA).2 ⟨J q, hqV.2, hq'⟩)
  have hzV : φ (k z) ∈ V' := (hg _ specializes_rfl).mem_open V'.isOpen hV'
  let O' : Z.Opens := O ⊓ ψ ⁻¹ᵁ J ⁻¹ᵁ V'
  have hO' : O' ≤ k ⁻¹ᵁ φ ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← w]
    exact fun x hx ↦ hx.2.1
  have hz' : z ∈ Z.basicOpen ((ψ.appLE _ O' inf_le_right).hom
      ((J.appLE V' (J ⁻¹ᵁ V') le_rfl).hom (resG Y inf_le_left s₀) -
      resG Q (J.preimage_mono (inf_le_left.trans hV)) f)) := by
    rw [Scheme.basicOpen_appLE]
    refine ⟨⟨hz, show J (ψ z) ∈ V' from hw ▸ hzV⟩, ?_⟩
    change ψ z ∈ (Q.basicOpen _ : Set Q)
    rw [← hAO]
    exact hzA
  have e₁ := congrArg (resG Z (inf_le_left : O' ≤ O)) hs
  rw [res_appLE_apply, res_appLE_apply] at e₁
  have e₂ := congrArg (k.appLE _ O' hO').hom hs₀
  rw [appLE_res_apply, e₁, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE] at e₂
  have e₃ : ∀ (g : Z ⟶ Y) (_ : g = k ≫ φ) (hg), (g.appLE V O' hg).hom s₀ =
      ((k ≫ φ).appLE V O' hO').hom s₀ := by
    rintro _ rfl _; rfl
  rw [map_sub, appLE_res_apply, appLE_res_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, e₃ _ w, e₂, sub_self, Scheme.basicOpen_zero] at hz'
  exact hz'

theorem gm_res_pullU {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) {V : X.Opens}
    {A : Y.Opens} (h : A ≤ g ⁻¹ᵁ V) (hz : r z ∈ A) (a : Γ(X, V)ˣ) :
    gm r z A (res h (pullU g V a)) = gm (r ≫ g) z V a := by
  rw [gm_res r z h hz, gm_pull r g z V (h hz)]

def Compat {Q Y : Scheme.{0}} (N : LB Y) (J : Q ⟶ Y) (τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Q) (z : Z) (a b : N.ι), J (r z) ∈ N.U a → J (r z) ∈ N.U b →
    gm r z (J ⁻¹ᵁ N.U a) (τ a) =
      gm (r ≫ J) z (N.U a ⊓ N.U b) (N.g a b) * gm r z (J ⁻¹ᵁ N.U b) (τ b)

theorem exists_compat {Q Y : Scheme.{0}} {N : LB Y} {J : Q ⟶ Y} (t : (N.pull J).Gen)
    (ht : t.IsGen) : ∃ τ, Compat N J τ := by
  refine ⟨fun a ↦ res (DvrModel.pull_U N J fun _ ↦ a).ge (t.s fun _ ↦ a),
    fun Z r z a b ha hb ↦ ?_⟩
  have := gen_trans ht r z (j := fun _ ↦ a) (j' := fun _ ↦ b) (mem_pull.2 ha) (mem_pull.2 hb)
  rw [trF, Fintype.prod_unique, zpow_one] at this
  rw [gm_res r z _ ha, gm_res r z _ hb]
  exact this

theorem exists_normalised {X U P Q : Scheme.{0}} {N : LB P} (hN : N.IsLB) {j : U ⟶ X} {e : X ⟶ P}
    {J : Q ⟶ P} {π : Q ⟶ U} {eU : U ⟶ Q} (w : eU ≫ J = j ≫ e) (hπ : eU ≫ π = 𝟙 U)
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : Compat N e ρ) : ∃ τ', Compat N J τ' ∧ ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (J ⁻¹ᵁ N.U a) (τ' a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a) := by
  have hw : ∀ x, J (eU x) = e (j x) := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  have hle : ∀ a, j ⁻¹ᵁ e ⁻¹ᵁ N.U a ≤ eU ⁻¹ᵁ J ⁻¹ᵁ N.U a := fun a x hx ↦
    show J (eU x) ∈ N.U a from hw x ▸ hx
  let u : ∀ a, Γ(U, j ⁻¹ᵁ e ⁻¹ᵁ N.U a)ˣ := fun a ↦
    pullU j _ (ρ a) * (res (hle a) (pullU eU _ (τ a)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι), e (j (κ z)) ∈ N.U a →
      gm κ z _ (u a) = gm (κ ≫ j) z _ (ρ a) * (gm (κ ≫ eU) z _ (τ a))⁻¹ := fun Z κ z a ha ↦ by
    rw [map_mul, map_inv, gm_pull κ j z _ ha, gm_res_pullU κ eU z _ ha]
  obtain ⟨v, hv⟩ := glue_unit ⊤ (fun a ↦ j ⁻¹ᵁ e ⁻¹ᵁ N.U a) (fun _ ↦ le_top)
    (fun x _ ↦ Opens.mem_iSup.2 (exists_chart hN (e (j x)))) u fun a b x hx ↦ by
      rw [hu _ _ _ _ hx.1, hu _ _ _ _ hx.2, hρ _ (𝟙 U ≫ j) x a b hx.1 hx.2,
        hτ _ (𝟙 U ≫ eU) x a b (hle a hx.1) (hle b hx.2), Category.assoc, Category.assoc, w]
      rw [mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have ht : ∀ a, J ⁻¹ᵁ N.U a ≤ π ⁻¹ᵁ ⊤ := fun _ _ _ ↦ trivial
  refine ⟨fun a ↦ res (ht a) (pullU π ⊤ v) * τ a, fun Z r z a b ha hb ↦ ?_, fun Z κ z a ha ↦ ?_⟩
  · rw [map_mul, map_mul, gm_res_pullU r π z (ht a) ha, gm_res_pullU r π z (ht b) hb, hτ Z r z a b ha hb,
      mul_left_comm]
  · rw [map_mul, gm_res_pullU (κ ≫ eU) π z (ht a) (hle a ha), Category.assoc, hπ, Category.comp_id,
      ← gm_res κ z (le_top : j ⁻¹ᵁ e ⁻¹ᵁ N.U a ≤ ⊤) ha, hv, hu _ _ _ _ ha, inv_mul_cancel_right]

theorem Compat.res_pullU {Q Y H Z : Scheme.{0}} {N : LB Y} {J : Q ⟶ Y}
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {φ : H ⟶ Y} {k : Z ⟶ H} {ψ : Z ⟶ Q}
    (hψ : ψ ≫ J = k ≫ φ) (hW : ∀ A : Y.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A) (a b : N.ι) :
    res (inf_le_left : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ _)
      (res (hW _) (pullU ψ _ (τ a))) =
      res (le_rfl : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ k ⁻¹ᵁ φ ⁻¹ᵁ (N.U a ⊓ N.U b))
        (pullU k _ (pullU φ _ (N.g a b))) *
        res (inf_le_right : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤ _)
          (res (hW _) (pullU ψ _ (τ b))) := by
  refine unit_ext fun z hz ↦ ?_
  rw [map_mul, gm_res _ z inf_le_left hz, gm_res _ z inf_le_right hz,
    gm_res_pullU (𝟙 Z) ψ z (hW _) hz.1,
    gm_res_pullU (𝟙 Z) ψ z (hW _) hz.2, hτ _ (𝟙 Z ≫ ψ) z a b (hW _ hz.1) (hW _ hz.2)]
  have h₁ := gm_res_pullU (𝟙 Z) k z (le_rfl : k ⁻¹ᵁ φ ⁻¹ᵁ N.U a ⊓ k ⁻¹ᵁ φ ⁻¹ᵁ N.U b ≤
    k ⁻¹ᵁ φ ⁻¹ᵁ (N.U a ⊓ N.U b)) hz (pullU φ _ (N.g a b))
  rw [gm_pull (𝟙 Z ≫ k) φ z (N.U a ⊓ N.U b) hz, Category.assoc, ← hψ, ← Category.assoc] at h₁
  exact congrArg (· * _) h₁.symm

theorem exists_unit_dvr {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] {X P Q H Z : Scheme.{0}}
    {f : H ⟶ Spec (.of V)} [Smooth f] [GeometricallyIntegral f] {k : Z ⟶ H} {fK : Z ⟶ Spec (.of K)}
    (hK : IsPullback k fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    {N : LB P} (hN : N.IsLB) {J : Q ⟶ P} {φ : H ⟶ P} {ψ : Z ⟶ Q} (hψ : ψ ≫ J = k ≫ φ)
    (hW : ∀ A : P.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A)
    {e : X ⟶ P} {l : Spec (.of V) ⟶ X} {eV : Spec (.of V) ⟶ H} (heV : eV ≫ φ = l ≫ e)
    (heV' : eV ≫ f = 𝟙 _) {eK : Spec (.of K) ⟶ Z}
    (heK : eK ≫ k = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ eV)
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ z a, e (l (Spec.map (CommRingCat.ofHom (algebraMap V K)) z)) ∈ N.U a →
      gm (eK ≫ ψ) z (J ⁻¹ᵁ N.U a) (τ a) =
        gm (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) z (e ⁻¹ᵁ N.U a) (ρ a)) (a : N.ι) :
    ∃ s : Γ(H, φ ⁻¹ᵁ N.U a)ˣ, res le_rfl (pullU k _ s) = res (hW _) (pullU ψ _ (τ a)) := by
  have hs := IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  set n := Spec.map (CommRingCat.ofHom (algebraMap V K)) with hn
  obtain ⟨a₀, h₀⟩ := exists_chart hN (e (l (IsLocalRing.closedPoint V)))
  have hA : l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀ ≤ eV ⁻¹ᵁ φ ⁻¹ᵁ N.U a₀ := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, heV]
  have hA' : n ⁻¹ᵁ l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀ ≤ eK ⁻¹ᵁ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a₀ := by
    rw [← Scheme.Hom.comp_preimage eK, heK]
    exact n.preimage_mono hA
  have hu : res le_rfl (pullU n _ (pullU l _ (ρ a₀))) =
      res hA' (pullU eK _ (res (hW _) (pullU ψ _ (τ a₀)))) := by
    refine unit_ext fun z hz ↦ ?_
    rw [gm_res_pullU (𝟙 _) n z le_rfl hz, gm_res_pullU (𝟙 _) eK z hA' hz, Category.id_comp,
      Category.id_comp, gm_pull n l z _ hz, gm_res_pullU eK ψ z (hW _) (hA' hz), hρ z a₀ hz]
  obtain ⟨s, ⟨hsu, -, hsr⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs
    (U := fun a ↦ φ ⁻¹ᵁ N.U a) (g := fun a b ↦ (pullU φ _ (N.g a b)).val)
    (W := fun a ↦ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a) (fun _ ↦ rfl) (fun x ↦ exists_chart hN (φ x))
    (fun a b ↦ Units.isUnit _) (r := fun a ↦ (res (hW _) (pullU ψ _ (τ a))).val)
    (fun a b ↦ congrArg Units.val (hτ.res_pullU hψ hW a b))
    (fun a ↦ Units.isUnit _) heV' heK (a₀ := a₀) (A := l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀) h₀ hA rfl hA'
    (pullU l _ (ρ a₀)).isUnit (congrArg Units.val hu)
  exact ⟨(hsu a).unit, Units.ext (hsr a)⟩

theorem appLE_inv_eq {P Q H Z : Scheme.{0}} {J : Q ⟶ P} {φ : H ⟶ P} {k : Z ⟶ H} {ψ : Z ⟶ Q}
    {A : P.Opens} (hW : k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A) {s : Γ(H, φ ⁻¹ᵁ A)ˣ} {τ : Γ(Q, J ⁻¹ᵁ A)ˣ}
    (hu : res le_rfl (pullU k _ s) = res hW (pullU ψ _ τ)) :
    (k.appLE _ _ le_rfl).hom s.val = (ψ.appLE _ _ hW).hom τ.val ∧
      (k.appLE _ _ le_rfl).hom (s⁻¹).val = (ψ.appLE _ _ hW).hom (τ⁻¹).val := by
  have hu' : res le_rfl (pullU k _ s⁻¹) = res hW (pullU ψ _ τ⁻¹) := by
    rw [map_inv (pullU k _), map_inv (pullU ψ _), map_inv (res le_rfl), map_inv (res hW), hu]
  exact ⟨congrArg Units.val hu, congrArg Units.val hu'⟩

theorem extAt_of_coheight_eq_one {X U P : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {N : LB P}
    (hN : N.IsLB) {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e)
    (hπ : eU ≫ pullback.snd p j = 𝟙 U)
    {τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N _ τ)
    {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a))
    (y : P) (hx : Order.coheight (p y) = 1) (a : N.ι) (ha : y ∈ N.U a) :
    ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
      ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := by
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst p j)
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst p j)
  have := IsNormalScheme.isDiscreteValuationRing_stalk hx
  let V : Type := X.presheaf.stalk (p y)
  let K : Type := FractionRing V
  let l : Spec (.of V) ⟶ X := X.fromSpecStalk (p y)
  have : IsPreimmersion l := inferInstanceAs (IsPreimmersion (X.fromSpecStalk (p y)))
  have hl : Set.range l = {ξ | ξ ⤳ p y} := Scheme.range_fromSpecStalk
  let n : Spec (.of K) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨κ, hκ⟩ := exists_lift j (n ≫ l) (by
    rintro _ ⟨o, rfl⟩
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    obtain ⟨v, rfl⟩ : ξ ∈ Set.range l := hl ▸ hξy
    have hv : n o ⤳ v := (PrimeSpectrum.le_iff_specializes (n o) v).1 (by
      intro c hc
      have hc' : algebraMap V K c ∈ o.asIdeal := hc
      rw [Ideal.eq_bot_of_prime o.asIdeal, Ideal.mem_bot,
        map_eq_zero_iff _ (IsFractionRing.injective V K)] at hc'
      rw [hc']
      exact Ideal.zero_mem _)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range (hv.map l.continuous) hξ)
  let φ := pullback.fst p l
  let f := pullback.snd p l
  let k := pullback.fst f n
  let fK := pullback.snd f n
  have hK : IsPullback k fK f n := .of_hasPullback f n
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral hK
  have := DvrModel.isOpenImmersion_generic hK
  let ψ : pullback f n ⟶ pullback p j := pullback.lift (k ≫ φ) (fK ≫ κ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hK.w, Category.assoc, Category.assoc,
      hκ])
  have hψ : ψ ≫ pullback.fst p j = k ≫ φ := pullback.lift_fst _ _ _
  have hψ' : ψ ≫ pullback.snd p j = fK ≫ κ := pullback.lift_snd _ _ _
  let eV : Spec (.of V) ⟶ pullback p l := pullback.lift (l ≫ e) (𝟙 _) (by simp [he])
  have heV : eV ≫ φ = l ≫ e := pullback.lift_fst _ _ _
  have heV' : eV ≫ f = 𝟙 _ := pullback.lift_snd _ _ _
  let eK : Spec (.of K) ⟶ pullback f n := pullback.lift (n ≫ eV) (𝟙 _) (by simp [heV'])
  have heK : eK ≫ k = n ≫ eV := pullback.lift_fst _ _ _
  have heK' : eK ≫ fK = 𝟙 _ := pullback.lift_snd _ _ _
  have hek : eK ≫ ψ = κ ≫ eU := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hψ, reassoc_of% heK, heV, Category.assoc, w, reassoc_of% hκ]
    · rw [Category.assoc, hψ', reassoc_of% heK', Category.assoc, hπ, Category.comp_id]
  have hW : ∀ A : P.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ pullback.fst p j ⁻¹ᵁ A := fun A ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hψ]
  obtain ⟨s, hu⟩ := exists_unit_dvr hK hN hψ hW heV heV' heK hτ (ρ := ρ) (fun z a hz ↦ by
    rw [hek, hρ, hκ]
    rw [← Scheme.Hom.comp_apply κ, hκ]
    exact hz) a
  obtain ⟨h, hh⟩ : y ∈ Set.range φ := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hl]
    exact specializes_rfl
  obtain ⟨z, hz⟩ : genericPoint (pullback p l :) ∈ k.opensRange :=
    have : Nonempty k.opensRange := ⟨⟨k (Nonempty.some inferInstance), _, rfl⟩⟩
    genericPoint_mem_opens _
  have hg : ∀ y, y ⤳ φ h → φ (k z) ⤳ y := fun y hy ↦ by
    obtain ⟨h', rfl⟩ : y ∈ Set.range φ := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hl]
      exact (hh ▸ hy).map p.continuous
    rw [hz]
    exact (genericPoint_specializes h').map φ.continuous
  have ha' : φ h ∈ N.U a := by rw [hh]; exact ha
  have hza : z ∈ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a := (hg _ specializes_rfl).mem_open (N.U a).isOpen ha'
  suffices H : ExtAt (pullback.fst p j) (N.U a) (τ a).val (φ h) ∧
      ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val (φ h) by rwa [hh] at H
  exact ⟨extAt_of_generic _ φ k ψ hψ _ _ _ le_rfl (hW _) (appLE_inv_eq _ hu).1 z hza h ha' hg,
    extAt_of_generic _ φ k ψ hψ _ _ _ le_rfl (hW _) (appLE_inv_eq _ hu).2 z hza h ha' hg⟩

theorem exists_isGen_of_densePart : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (P : Over X) (e : X ⟶ P.left) (N : LB P.left), e ≫ P.hom = 𝟙 X → Smooth P.hom → GeometricallyIntegral P.hom → N.IsLB → (∃ r : (N.pull e).Gen, r.IsGen) → (∃ t : (N.pull (pullback.fst P.hom j)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X U _ j hX _ _ _ _ P e N he _ _ hN ⟨r, hr⟩ ⟨t, ht⟩
  have := IsNormalScheme.of_pred hX
  have := isNormalScheme_of_smooth P.hom
  have := LocallyOfFiniteType.isLocallyNoetherian P.hom
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst P.hom j).app_injective
  obtain ⟨τ₀, hτ₀⟩ := exists_compat t ht
  obtain ⟨ρ, hρ⟩ := exists_compat r hr
  let eU : U ⟶ pullback P.hom j := pullback.lift (j ≫ e) (𝟙 U) (by simp [he])
  have w : eU ≫ pullback.fst P.hom j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd P.hom j = 𝟙 U := pullback.lift_snd _ _ _
  obtain ⟨τ, hτ, hτρ⟩ := exists_normalised hN w hπ hτ₀ hρ
  have key : ∀ a, ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst P.hom j) →
      ExtAt (pullback.fst P.hom j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst P.hom j) (N.U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j P.hom he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one P.hom h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (P.hom y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show P.hom y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst P.hom j).app _).hom _ = ((pullback.fst P.hom j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  let σ : ∀ a, Γ(P.left, N.U a)ˣ := fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩
  have hσ : ∀ a, pullU (pullback.fst P.hom j) _ (σ a) = τ a := fun a ↦ Units.ext (hs a)
  refine ⟨⟨σ⟩, fun a b ↦ Units.map_injective
    (f := ((pullback.fst P.hom j).app (N.U a ⊓ N.U b)).hom.toMonoidHom) (hJ _) ?_⟩
  change pullU _ _ _ = pullU _ _ _
  refine unit_ext fun q hq ↦ ?_
  have := hτ _ (𝟙 _) q a b hq.1 hq.2
  rw [← hσ, ← hσ, gm_pull _ _ q _ hq.1, gm_pull _ _ q _ hq.2] at this
  rw [gm_pull _ _ q _ hq, gm_pull _ _ q _ hq, map_mul, gm_res _ q _ hq, gm_res _ q _ hq]
  exact this

end GlobalTheory.GenericExtend
