import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.PushInv

open GlobalTheory.AbLocusPull

variable {X Y Z : Scheme.{0}}

theorem gs_comp_stalkMap (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (f : Γ(X, U)) :
    gs (r ≫ q) z U f = (r.stalkMap z).hom (gs q (r z) U f) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z (q ⁻¹ᵁ U) h, gs_pull (𝟙 Y) q (r z) U h, Category.id_comp]

theorem gs_id (x : X) (U : X.Opens) (h : x ∈ U) (f : Γ(X, U)) :
    gs (𝟙 X) x U f = (X.presheaf.germ U x h).hom f := by
  rw [gs_eq (𝟙 X) x U h]; rfl

theorem gs_sub (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_specializes (r : Z ⟶ X) {y z : Z} (h : y ⤳ z) (U : X.Opens) (hz : r z ∈ U) (f : Γ(X, U)) :
    (Z.presheaf.stalkSpecializes h).hom (gs r z U f) = gs r y U f := by
  have hy : r y ∈ U := (h.map r.continuous).mem_open U.2 hz
  rw [gs_eq r z U hz, gs_eq r y U hy]
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

theorem stalkMap_injective_of_flat (r : Z ⟶ X) [Flat r] (z : Z) : Function.Injective (r.stalkMap z).hom := by
  refine (injective_iff_map_eq_zero _).2 fun b hb => ?_
  exact zero_dvd_iff.1 (dvd_descend r z (a := 0) (b := b) (by rw [hb, map_zero]))

theorem exists_frac {A : X.Opens} (hA : IsAffineOpen A) {y : X} (hy : y ∈ A) (κ : X.presheaf.stalk y) :
    ∃ a b : Γ(X, A), IsUnit (gs (𝟙 X) y A b) ∧ κ * gs (𝟙 X) y A b = gs (𝟙 X) y A a := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : A)
  have h := hA.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj (hA.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk ((⟨y, hy⟩ : A) : X)) κ
  refine ⟨a, b, ?_, ?_⟩
  · rw [gs_id y A hy]
    exact IsLocalization.map_units (X.presheaf.stalk ((⟨y, hy⟩ : A) : X)) b
  · rw [gs_id y A hy, gs_id y A hy]
    exact e

theorem stalkSpecializes_injective {x y : X} (h : y ⤳ x) [IsDomain (X.presheaf.stalk x)] :
    Function.Injective (X.presheaf.stalkSpecializes h).hom := by
  refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
  obtain ⟨A, hA, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  have hy : y ∈ A := h.mem_open A.2 hx
  obtain ⟨a, b, hb, e⟩ := exists_frac hA hx t
  have ha : gs (𝟙 X) y A a = 0 := by
    rw [← gs_specializes (𝟙 X) h A hx, ← e, map_mul, ht, zero_mul]
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : A)
  have hl := hA.isLocalization_stalk ⟨y, hy⟩
  rw [gs_id y A hy] at ha
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff (hA.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (X.presheaf.stalk ((⟨y, hy⟩ : A) : X)) a).1 ha
  have hu : IsUnit (gs (𝟙 X) y A c) := by
    rw [gs_id y A hy]
    exact IsLocalization.map_units (X.presheaf.stalk ((⟨y, hy⟩ : A) : X)) c
  have hne : gs (𝟙 X) x A c ≠ 0 := fun h0 => by
    rw [← gs_specializes (𝟙 X) h A hx, h0, map_zero] at hu
    exact not_isUnit_zero hu
  have h0 : gs (𝟙 X) x A c * gs (𝟙 X) x A a = 0 := by
    rw [← gs_mul _ _ _ hx, hc, gs_id x A hx, map_zero]
  rw [(mul_eq_zero.1 h0).resolve_left hne] at e
  exact (hb.mul_left_eq_zero).1 e

theorem exists_nhds_of_gs_eq {U₁ U₂ U₃ : X.Opens} {x : X} (h₁ : x ∈ U₁) (h₂ : x ∈ U₂) (h₃ : x ∈ U₃)
    (f₁ : Γ(X, U₁)) (f₂ : Γ(X, U₂)) (f₃ : Γ(X, U₃))
    (e : gs (𝟙 X) x U₁ f₁ = gs (𝟙 X) x U₂ f₂ * gs (𝟙 X) x U₃ f₃) :
    ∃ N : X.Opens, x ∈ N ∧ N ≤ U₁ ⊓ U₂ ⊓ U₃ ∧
      ∀ z ∈ N, gs (𝟙 X) z U₁ f₁ = gs (𝟙 X) z U₂ f₂ * gs (𝟙 X) z U₃ f₃ := by
  have h₂₃ : x ∈ U₂ ⊓ U₃ := ⟨h₂, h₃⟩
  have m : ∀ z ∈ U₂ ⊓ U₃, gs (𝟙 X) z (U₂ ⊓ U₃) (resG X inf_le_left f₂ * resG X inf_le_right f₃) =
      gs (𝟙 X) z U₂ f₂ * gs (𝟙 X) z U₃ f₃ := fun z hz => by
    rw [gs_mul _ z _ hz, gs_res _ z _ hz, gs_res _ z _ hz]
  rw [← m x h₂₃, gs_id x _ h₁, gs_id x _ h₂₃] at e
  obtain ⟨N, hN, i₁, i₂, e⟩ := X.presheaf.germ_eq x h₁ h₂₃ _ _ e
  refine ⟨N, hN, le_inf (le_inf i₁.le (i₂.le.trans inf_le_left)) (i₂.le.trans inf_le_right), fun z hz => ?_⟩
  rw [← m z (i₂.le hz), ← gs_res (𝟙 X) z i₁.le hz, ← gs_res (𝟙 X) z i₂.le hz]
  exact congrArg (gs (𝟙 X) z N) e

theorem exists_secOn_pull_germ {X' : Scheme.{0}} {F : X' ⟶ X} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) {W : X.Opens} {W' : X'.Opens} (hW : W' ≤ F ⁻¹ᵁ W)
    {θ : ∀ i, Γ(X, W ⊓ L.U i)} (hθ : θ ∈ secOn L W) :
    ∃ θ' ∈ secOn L' W', ∀ k x j, x ∈ W' → x ∈ L'.U k → F x ∈ L.U j →
      gs (𝟙 X') x _ (θ' k) = ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) := by
  have hw := (isGen_iff w).1 hw
  have rel : ∀ (x : X') j j' k k', x ∈ W' → F x ∈ L.U j → F x ∈ L.U j' → x ∈ L'.U k → x ∈ L'.U k' →
      ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) =
        (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k')).val * (((gw w (𝟙 X') x j' k')⁻¹).val * gs F x _ (θ j')) := by
    intro x j j' k k' hx hj hj' hk hk'
    have e := hw _ (𝟙 X') x j j' k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    rw [gs_secOn hθ F x j j' (hW hx) hj hj', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    rw [mul_inv, mul_inv, inv_inv, _root_.mul_comm, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  have ex : ∀ k, ∃ b : Γ(X', W' ⊓ L'.U k), ∀ x j, x ∈ W' → x ∈ L'.U k → F x ∈ L.U j →
      gs (𝟙 X') x _ b = ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) := by
    intro k
    let O : L.ι → X'.Opens := fun j => W' ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
    have le : ∀ j, O j ≤ F ⁻¹ᵁ (W ⊓ L.U j) := fun j x hx => ⟨hW hx.1, mem_pull.1 hx.2.1⟩
    let u : ∀ j, Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U k)ˣ := fun j => w.s (fun _ => j, k)
    let a : ∀ j, Γ(X', O j) := fun j => resG X' inf_le_right ((u j)⁻¹).val * resG X' (le j) ((F.app _).hom (θ j))
    have va : ∀ x j, x ∈ O j → gs (𝟙 X') x _ (a j) = ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) := by
      intro x j hx
      refine (gs_mul _ x _ hx _ _).trans ?_
      rw [gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx.2, map_inv, gs_pull _ F x _ (le j hx), Category.id_comp]
      rfl
    obtain ⟨b, hb⟩ := glue_fn (W' ⊓ L'.U k) O (fun j x hx => ⟨hx.1, hx.2.2⟩)
      (fun x hx => (exists_chart hL (F x)).imp fun j hj => ⟨hx.1, mem_pull.2 hj, hx.2⟩) a (fun j j' x hj hj' => by
        rw [va x j hj, va x j' hj', rel x j j' k k hj.1 (mem_pull.1 hj.2.1) (mem_pull.1 hj'.2.1) hj.2.2 hj.2.2,
          gm_self hL' (𝟙 X') x hj.2.2, Units.val_one, _root_.one_mul])
    refine ⟨b, fun x j hx hk hj => ?_⟩
    have hm : x ∈ O j := ⟨hx, mem_pull.2 hj, hk⟩
    exact (hb x j hm).trans (va x j hm)
  choose θ' hθ' using ex
  refine ⟨θ', fun k k' => fn_ext fun x hx => ?_, hθ'⟩
  obtain ⟨j, hj⟩ := exists_chart hL (F x)
  rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
    gs_unit (𝟙 X') x (L'.U k ⊓ L'.U k') ⟨hx.1.2, hx.2⟩, hθ' k x j hx.1.1 hx.1.2 hj, hθ' k' x j hx.1.1 hx.2 hj]
  exact rel x j j k k' hx.1.1 hj hj hx.1.2 hx.2

theorem exists_ratio_above {U : Scheme.{0}} {j : U ⟶ X} [IsPreimmersion j] {G : Over X} {G₀ : Over U}
    {φ : G₀.left ⟶ G.left} {L : LB G.left} {L₀ : LB G₀.left} (sq : φ ≫ G.hom = G₀.hom ≫ j) (hL : L.IsLB)
    (hL₀ : L₀.IsLB) (hw : LBIso L₀ (L.pull φ)) (h₀ : PushInvertible G₀ L₀) {V W A : X.Opens} (hA : IsAffineOpen A)
    {θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (G.hom ⁻¹ᵁ V))
    {s : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ L.U i)} (hs : s ∈ secOn L (G.hom ⁻¹ᵁ W))
    (z : G₀.left) (i : L.ι) (hzA : G.hom (φ z) ∈ A) (hzW : G.hom (φ z) ∈ W)
    (hz : φ z ∈ G.left.basicOpen (θ i)) :
    ∃ a b : Γ(X, A), IsUnit (gs (φ ≫ G.hom) z A b) ∧
      gs (φ ≫ G.hom) z A b * gs φ z _ (s i) = gs (φ ≫ G.hom) z A a * gs φ z _ (θ i) := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨V₀, hV₀, θ₀, -, gen, -⟩ := h₀ (G₀.hom z)
  obtain ⟨k, hk⟩ := exists_chart hL₀ z
  have hm : φ z ∈ G.hom ⁻¹ᵁ V ⊓ L.U i := G.left.basicOpen_le _ hz
  have pt : ∀ y, G.hom (φ y) = j (G₀.hom y) := fun y => by
    rw [← Scheme.Hom.comp_apply, sq, Scheme.Hom.comp_apply]
  have hjA : j (G₀.hom z) ∈ A := pt z ▸ hzA
  have key : ∀ (W : X.Opens) (s : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ L.U i)), s ∈ secOn L (G.hom ⁻¹ᵁ W) →
      G.hom (φ z) ∈ W → ∃ a b : Γ(X, A), IsUnit (gs (φ ≫ G.hom) z A b) ∧
        gs (φ ≫ G.hom) z A b * gs φ z _ (s i) =
          gs (φ ≫ G.hom) z A a * ((gw w (𝟙 _) z i k).val * gs (𝟙 _) z _ (θ₀ k)) := by
    intro W s hs hzW
    have hle : G₀.hom ⁻¹ᵁ (V₀ ⊓ j ⁻¹ᵁ W) ≤ φ ⁻¹ᵁ (G.hom ⁻¹ᵁ W) := fun y hy => by
      show G.hom (φ y) ∈ W
      rw [pt]; exact hy.2
    have hu : G₀.hom z ∈ V₀ ⊓ j ⁻¹ᵁ W := ⟨hV₀, show j (G₀.hom z) ∈ W from pt z ▸ hzW⟩
    obtain ⟨s', hs', es⟩ := exists_secOn_pull_germ hL hL₀ w hw hle hs
    obtain ⟨c, hc, -⟩ := gen _ inf_le_left s' hs'
    have hz' : z ∈ G₀.hom ⁻¹ᵁ (V₀ ⊓ j ⁻¹ᵁ W) ⊓ L₀.U k := ⟨hu, hk⟩
    have e := congrArg (gs (𝟙 _) z _) (hc k)
    rw [es k z i hu hk hm.2, gs_mul _ z _ hz', gs_appLE _ _ _ _ _ z hz', gs_res _ z _ hz', Category.id_comp] at e
    obtain ⟨κ, hκ⟩ := j.stalkMap_surjective (G₀.hom z) (gs (𝟙 U) (G₀.hom z) _ c)
    obtain ⟨a, b, hb, eab⟩ := exists_frac hA hjA κ
    have tr : ∀ f : Γ(X, A), gs (φ ≫ G.hom) z A f =
        (G₀.hom.stalkMap z).hom ((j.stalkMap (G₀.hom z)).hom (gs (𝟙 X) (j (G₀.hom z)) A f)) := fun f => by
      rw [sq, gs_comp_stalkMap _ _ z A hjA, gs_stalkMap j _ A hjA]
    have e' : gs G₀.hom z _ c * gs (φ ≫ G.hom) z A b = gs (φ ≫ G.hom) z A a := by
      rw [tr, tr, ← eab, map_mul, map_mul, gs_stalkMap G₀.hom z _ hu, ← hκ]
    refine ⟨a, b, ?_, ?_⟩
    · rw [tr]; exact (hb.map _).map _
    · rw [Units.inv_mul_eq_iff_eq_mul] at e
      rw [e, ← e']; ring
  obtain ⟨a, b, hb, e⟩ := key W s hs hzW
  obtain ⟨a', b', hb', e'⟩ := key V θ hθ hm.1
  have ha' : IsUnit (gs (φ ≫ G.hom) z A a') :=
    isUnit_of_mul_isUnit_left (e' ▸ hb'.mul ((isUnit_gs_iff φ z _ hm _).2 hz))
  have hzA' : (φ ≫ G.hom) z ∈ A := hzA
  refine ⟨a * b', b * a', ?_, ?_⟩
  · rw [gs_mul _ z _ hzA']; exact hb.mul ha'
  · rw [gs_mul _ z _ hzA', gs_mul _ z _ hzA']
    linear_combination gs (φ ≫ G.hom) z A a' * e - gs (φ ≫ G.hom) z A a * e'

theorem spread (π : Y ⟶ X) [GeometricallyIrreducible π] [IsReduced Y] (hπ : IsOpenMap π) {L : LB Y}
    {V W W' : X.Opens} {θ : ∀ i, Γ(Y, π ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (π ⁻¹ᵁ V))
    {s : ∀ i, Γ(Y, π ⁻¹ᵁ W ⊓ L.U i)} (hs : s ∈ secOn L (π ⁻¹ᵁ W)) (a : Γ(X, W')) (g : Y) (i : L.ι)
    (hV : π g ∈ V) (hW : π g ∈ W) (hW' : π g ∈ W') (hi : g ∈ L.U i)
    (e : gs (𝟙 Y) g _ (s i) = gs π g W' a * gs (𝟙 Y) g _ (θ i)) :
    ∃ O : X.Opens, π g ∈ O ∧ O ≤ W ∧ O ≤ W' ∧ ∀ k z, π z ∈ O → z ∈ L.U k →
      gs (𝟙 Y) z _ (s k) = gs π z W' a * gs (𝟙 Y) z _ (θ k) := by
  have pl : ∀ z, π z ∈ W' → gs (𝟙 Y) z (π ⁻¹ᵁ W') ((π.app W').hom a) = gs π z W' a := fun z hz => by
    rw [gs_pull (𝟙 Y) π z W' hz, Category.id_comp]
  rw [← pl g hW'] at e
  obtain ⟨N, hN, hle, eN⟩ := exists_nhds_of_gs_eq (U₁ := π ⁻¹ᵁ W ⊓ L.U i) (U₂ := π ⁻¹ᵁ W') (U₃ := π ⁻¹ᵁ V ⊓ L.U i)
    ⟨hW, hi⟩ hW' ⟨hV, hi⟩ _ _ _ e
  let O : X.Opens := ⟨π '' N, hπ _ N.2⟩
  have o₁ : O ≤ W := by rintro _ ⟨z, hz, rfl⟩; exact (hle hz).1.1.1
  have o₂ : O ≤ W' := by rintro _ ⟨z, hz, rfl⟩; exact (hle hz).1.2
  have o₃ : O ≤ V := by rintro _ ⟨z, hz, rfl⟩; exact (hle hz).2.1
  refine ⟨O, ⟨g, hN, rfl⟩, o₁, o₂, fun k z hz hk => ?_⟩
  let t : Γ(Y, π ⁻¹ᵁ O ⊓ L.U k) := resG Y (inf_le_inf_right _ (π.preimage_mono o₁)) (s k) -
    (π.appLE W' _ (inf_le_left.trans (π.preimage_mono o₂))).hom a *
      resG Y (inf_le_inf_right _ (π.preimage_mono o₃)) (θ k)
  have vt : ∀ z ∈ π ⁻¹ᵁ O ⊓ L.U k, gs (𝟙 Y) z _ t = gs (𝟙 Y) z _ (s k) - gs π z W' a * gs (𝟙 Y) z _ (θ k) :=
    fun z hz => by
      rw [gs_sub _ z _ hz, gs_mul _ z _ hz, gs_res _ z _ hz, gs_res _ z _ hz, gs_appLE _ _ _ _ _ z hz,
        Category.id_comp]
  have ht : t = 0 := by
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨y', hy', ey⟩ := (Y.basicOpen_le _ hy).1
    have irr : IsIrreducible (π ⁻¹' {π y}) := by
      rw [← π.range_fiberι, ← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ (π.fiberι _).continuous.continuousOn
    obtain ⟨q, -, hq, hq'⟩ := irr.2 N (Y.basicOpen t) N.2 (Y.basicOpen t).2 ⟨y', ey, hy'⟩ ⟨y, rfl, hy⟩
    have hm : q ∈ π ⁻¹ᵁ O ⊓ L.U k := Y.basicOpen_le _ hq'
    have hu := (isUnit_gs_iff (𝟙 Y) q _ hm t).2 hq'
    rw [vt q hm, gs_secOn hs (𝟙 Y) q k i (hle hq).1.1.1 hm.2 (hle hq).2.2,
      gs_secOn hθ (𝟙 Y) q k i (hle hq).2.1 hm.2 (hle hq).2.2, eN q hq, pl q (hle hq).1.2,
      mul_left_comm, sub_self] at hu
    exact (not_isUnit_zero hu).elim
  have hm : z ∈ π ⁻¹ᵁ O ⊓ L.U k := ⟨hz, hk⟩
  rw [← sub_eq_zero, ← vt z hm, ht, gs_id z _ hm, map_zero]

theorem gs_eq_of_mul_eq (π : Y ⟶ X) [Flat π] {O O' : X.Opens} (a : Γ(X, O)) (a' : Γ(X, O')) (g : Y)
    (h : π g ∈ O) (h' : π g ∈ O') {u : Y.presheaf.stalk g} (hu : IsUnit u)
    (e : gs π g O a * u = gs π g O' a' * u) : gs (𝟙 X) (π g) O a = gs (𝟙 X) (π g) O' a' := by
  apply stalkMap_injective_of_flat π g
  rw [← gs_stalkMap π g O h, ← gs_stalkMap π g O' h']
  exact hu.mul_right_cancel e

theorem pushInvertible_of_densePart : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G : Over X) (G₀ : Over U) (φ : G₀.left ⟶ G.left) (L : LB G.left) (L₀ : LB G₀.left), Smooth G.hom → GeometricallyIntegral G.hom → IsPullback φ G₀.hom G.hom j → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → PushInvertible G₀ L₀ → (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)) → PushInvertible G L := by
  intro X U _ j hX _ _ _ _ G G₀ φ L L₀ _ _ sq hL hL₀ hw h₀ H x
  obtain ⟨V, hx, θ, hθ, hne⟩ := H x
  refine ⟨V, hx, θ, hθ, fun W hW s hs => ?_, hne⟩
  have hG := forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX
  have : IsReduced G.left := by
    have : ∀ g : G.left, _root_.IsReduced (G.left.presheaf.stalk g) := fun g =>
      have := (hG g).1
      inferInstance
    exact isReduced_of_isReduced_stalk _
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) sq.flip ‹_›
  have loc : ∀ y : W, ∃ (O : X.Opens) (a : Γ(X, O)), y.1 ∈ O ∧ O ≤ W ∧ ∀ k z, G.hom z ∈ O → z ∈ L.U k →
      gs (𝟙 _) z _ (s k) = gs G.hom z O a * gs (𝟙 _) z _ (θ k) := by
    rintro ⟨y, hy⟩
    obtain ⟨g, i, rfl, hg⟩ := hne y (hW hy)
    have := (hG g).1
    have hm : g ∈ G.hom ⁻¹ᵁ V ⊓ L.U i := G.left.basicOpen_le _ hg
    have hm' : g ∈ G.hom ⁻¹ᵁ W ⊓ L.U i := ⟨hy, hm.2⟩
    have hu := (isUnit_gs_iff (𝟙 _) g _ hm _).2 hg
    obtain ⟨ξ, hξ, hsp⟩ : ∃ ξ ∈ genericPoints X, ξ ⤳ G.hom g := by
      let C : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents (G.hom g)⟩
      exact ⟨(genericPoints.ofComponent C).1, (genericPoints.ofComponent C).2,
        (genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent⟩
    obtain ⟨u, rfl⟩ := genericPoints_subset_range_of_isDominant j hξ
    obtain ⟨ν, hν, eν⟩ := Flat.generalizingMap G.hom hsp
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback sq ν u eν
    obtain ⟨A, hA, hgA, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := G.hom g) trivial
    have hsp' : G.hom (φ z) ⤳ G.hom g := hν.map G.hom.continuous
    have hzA : G.hom (φ z) ∈ A := hsp'.mem_open A.2 hgA
    obtain ⟨a, b, hb, e⟩ := exists_ratio_above sq.w hL hL₀ hw h₀ hA hθ hs z i hzA (hsp'.mem_open W.2 hy)
      (hν.mem_open (G.left.basicOpen _).2 hg)
    have tr : ∀ f : Γ(X, A), gs (φ ≫ G.hom) z A f =
        (φ.stalkMap z).hom ((G.left.presheaf.stalkSpecializes hν).hom (gs G.hom g A f)) := fun f => by
      rw [gs_comp_stalkMap _ _ z A hzA, gs_specializes G.hom hν A hgA]
    have tr' : ∀ (O : G.left.Opens) (f : Γ(G.left, O)), g ∈ O → gs φ z O f =
        (φ.stalkMap z).hom ((G.left.presheaf.stalkSpecializes hν).hom (gs (𝟙 _) g O f)) := fun O f hO => by
      rw [gs_stalkMap φ z O (hν.mem_open O.2 hO), gs_specializes (𝟙 _) hν O hO]
    have e' : gs G.hom g A b * gs (𝟙 _) g _ (s i) = gs G.hom g A a * gs (𝟙 _) g _ (θ i) := by
      apply stalkSpecializes_injective hν
      apply stalkMap_injective_of_flat φ z
      rw [map_mul, map_mul, map_mul, map_mul, ← tr, ← tr, ← tr' _ _ hm, ← tr' _ _ hm']
      exact e
    have hb0 : gs G.hom g A b ≠ 0 := fun h0 => by
      rw [tr, h0, map_zero, map_zero] at hb
      exact not_isUnit_zero hb
    have hd : gs G.hom g A b ∣ gs G.hom g A a := (hu.dvd_mul_right).1 ⟨_, e'.symm⟩
    have hd' := hd
    rw [gs_stalkMap G.hom g A hgA, gs_stalkMap G.hom g A hgA] at hd'
    obtain ⟨c, hc⟩ := dvd_descend G.hom g hd'
    obtain ⟨W', hW', c, rfl⟩ := X.presheaf.exists_germ_eq c
    rw [← gs_id _ W' hW'] at hc
    have ec : gs G.hom g A a = gs G.hom g A b * gs G.hom g W' c := by
      rw [gs_stalkMap G.hom g A hgA a, hc, map_mul, ← gs_stalkMap G.hom g A hgA, ← gs_stalkMap G.hom g W' hW']
    rw [ec, _root_.mul_assoc] at e'
    obtain ⟨O, hO, o₁, o₂, eO⟩ := spread G.hom G.hom.isOpenMap hθ hs c g i hm.1 hy hW' hm.2
      (mul_left_cancel₀ hb0 e')
    exact ⟨O, resG X o₂ c, hO, o₁, fun k z hz hk => by rw [gs_res _ z _ hz]; exact eO k z hz hk⟩
  choose O a hO hOW ea using loc
  obtain ⟨b, hb⟩ := glue_fn W O hOW (fun y hy => ⟨⟨y, hy⟩, hO _⟩) a (fun p q y hp hq => by
    obtain ⟨g, i, rfl, hg⟩ := hne y (hW (hOW p hp))
    have hm : g ∈ G.hom ⁻¹ᵁ V ⊓ L.U i := G.left.basicOpen_le _ hg
    exact gs_eq_of_mul_eq G.hom _ _ g hp hq ((isUnit_gs_iff (𝟙 _) g _ hm _).2 hg)
      ((ea p i g hp hm.2).symm.trans (ea q i g hq hm.2)))
  have val : ∀ (c : Γ(X, W)) i z (hz : z ∈ G.hom ⁻¹ᵁ W ⊓ L.U i), gs (𝟙 _) z _
      ((G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom c *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ i)) =
      gs G.hom z W c * gs (𝟙 _) z _ (θ i) := fun c i z hz => by
    rw [gs_mul _ z _ hz, gs_res _ z _ hz, gs_appLE _ _ _ _ _ z hz, Category.id_comp]
  refine existsUnique_of_exists_of_unique ⟨b, fun i => fn_ext fun z hz => ?_⟩ fun c c' hc hc' => fn_ext fun y hy => ?_
  · rw [val b i z hz, ea ⟨G.hom z, hz.1⟩ i z (hO _) hz.2, gs_stalkMap G.hom z W hz.1,
      hb _ ⟨G.hom z, hz.1⟩ (hO _), ← gs_stalkMap G.hom z _ (hO ⟨G.hom z, hz.1⟩)]
  · obtain ⟨g, i, rfl, hg⟩ := hne y (hW hy)
    have hm : g ∈ G.hom ⁻¹ᵁ V ⊓ L.U i := G.left.basicOpen_le _ hg
    have hm' : g ∈ G.hom ⁻¹ᵁ W ⊓ L.U i := ⟨hy, hm.2⟩
    refine gs_eq_of_mul_eq G.hom _ _ g hy hy ((isUnit_gs_iff (𝟙 _) g _ hm _).2 hg) ?_
    rw [← val c i g hm', ← val c' i g hm', ← hc i, ← hc' i]

end GlobalTheory.PushInv
