import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Y' Z : Scheme.{0}}

open Classical in

def gs (f : Y ⟶ X) (y : Y) (U : X.Opens) (a : Γ(X, U)) : Y.presheaf.stalk y :=
  if h : f y ∈ U then (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a) else 0

theorem gs_eq (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a) := by
  unfold gs
  exact dif_pos h

theorem gs_unit (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) : gs f y U a.val = (gm f y U a).val := by
  rw [gs_eq f y U h]
  unfold gm
  rw [dif_pos h]
  rfl

theorem gs_mul (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a * b) = gs f y U a * gs f y U b := by
  simp only [gs_eq f y U h, map_mul]

theorem gs_add (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a + b) = gs f y U a + gs f y U b := by
  simp only [gs_eq f y U h, map_add]

theorem gs_res (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)) :
    gs f y V ((X.presheaf.map (homOfLE hle).op).hom a) = gs f y U a := by
  rw [gs_eq f y V h, gs_eq f y U (hle h)]
  first
  | (rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
      Scheme.Hom.naturality_assoc]
     first
     | (erw [TopCat.Presheaf.germ_res]; done)
     | (simp only [TopCat.Presheaf.germ_res]; done))
  | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.naturality_assoc]
     erw [TopCat.Presheaf.germ_res])

theorem gs_pull (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)) :
    gs f z (g ⁻¹ᵁ U) ((g.app U).hom a) = gs (f ≫ g) z U a := by
  have h' : (f ≫ g) z ∈ U := h
  rw [gs_eq f z (g ⁻¹ᵁ U) h, gs_eq (f ≫ g) z U h']
  simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply]
  try rfl

theorem fn_ext {V : X.Opens} {a b : Γ(X, V)} (h : ∀ x ∈ V, gs (𝟙 X) x V a = gs (𝟙 X) x V b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf V a b
  intro x hx
  have e := h x hx
  rw [gs_eq (𝟙 X) x V hx, gs_eq (𝟙 X) x V hx] at e
  exact e

variable (L : LB X)

def Good (z : Z) (J : (Z ⟶ X) → L.ι) : Prop := ∀ ψ : Z ⟶ X, ψ z ∈ L.U (J ψ)

theorem exists_good (hL : L.IsLB) (z : Z) {K : Type} (ψ : K → (Z ⟶ X)) (j : K → L.ι)
    (hc : ∀ a b, ψ a = ψ b → j a = j b) (hj : ∀ k, ψ k z ∈ L.U (j k)) :
    ∃ J, Good L z J ∧ ∀ k, J (ψ k) = j k := by
  classical
  have hcov : ∀ x : X, ∃ i, x ∈ L.U i := fun x => by
    have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; simp
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨fun ψ' => if hk : ∃ k, ψ k = ψ' then j hk.choose else (hcov (ψ' z)).choose, ?_, ?_⟩
  · intro ψ'
    dsimp only
    split_ifs with hk
    · have hm := hj hk.choose
      rw [hk.choose_spec] at hm
      exact hm
    · exact (hcov _).choose_spec
  · intro k
    dsimp only
    rw [dif_pos ⟨k, rfl⟩]
    exact hc _ _ (Exists.choose_spec (⟨k, rfl⟩ : ∃ k', ψ k' = ψ k))

variable {L} {K K' : Type} [Fintype K] [Fintype K']

theorem Good.mem {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (φ : K → (Y ⟶ X)) (r : Z ⟶ Y) :
    r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ φ k)

def val {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    (Z.presheaf.stalk z)ˣ := gm r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (t.s (fun k => J (r ≫ φ k)))

def sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    Z.presheaf.stalk z := gs r z (LB.wchart L φ (fun k => J (r ≫ φ k))) (s.f (fun k => J (r ≫ φ k)))

theorem val_of {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    val t r z J = gm r z (LB.wchart L φ j) (t.s j) := by
  obtain rfl : (fun k => J (r ≫ φ k)) = j := funext h
  rfl

theorem sval_of {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    (J : (Z ⟶ X) → L.ι) (j : K → L.ι) (h : ∀ k, J (r ≫ φ k) = j k) :
    sval s r z J = gs r z (LB.wchart L φ j) (s.f j) := by
  obtain rfl : (fun k => J (r ≫ φ k)) = j := funext h
  rfl

section
variable {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
include hJ

theorem val_mul (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (r : Z ⟶ Y) :
    val (LB.mulGen L φ ε φ' ε' t t') r z J = val t r z J * val t' r z J := by
  simp only [val, LB.mulGen, map_mul]
  congr 1
  · exact gm_res r z _ (hJ.mem (Sum.elim φ φ') r) _
  · exact gm_res r z _ (hJ.mem (Sum.elim φ φ') r) _

omit hJ in
theorem val_inv (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) : val (LB.invGen L φ ε t) r z J = (val t r z J)⁻¹ := by
  simp only [val, LB.invGen]
  exact map_inv _ _

theorem val_pull (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') :
    val (LB.pullGen L φ ε t h) r z J = val t (r ≫ h) z J := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  simp only [val, LB.pullGen]
  have hm : h (r z) ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) := Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  exact (gm_res r z _ (hJ.mem (fun k => h ≫ φ k) r) _).trans (gm_pull r h z _ hm _)

omit hJ in
theorem val_one (r : Z ⟶ Y) : val (LB.oneGen L (Y := Y)) r z J = 1 := by
  simp only [val, LB.oneGen]
  exact map_one _

theorem val_corr {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') (r : Z ⟶ Y) : val t r z J = val t' r z J := by
  have hm : r z ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) ⊓ LB.wchart L φ' (fun k => J (r ≫ φ' k)) :=
    ⟨hJ.mem φ r, hJ.mem φ' r⟩
  have e := h (fun k => J (r ≫ φ k)) (fun k => J (r ≫ φ' k)) (fun a b hab => by simp only [hab])
    (fun a b hab => by simp only [hab]) (fun a b hab => by simp only [hab])
  have e2 := congrArg (gm r z (LB.wchart L φ (fun k => J (r ≫ φ k)) ⊓ LB.wchart L φ' (fun k => J (r ≫ φ' k)))) e
  exact (gm_res r z inf_le_left hm _).symm.trans (e2.trans (gm_res r z inf_le_right hm _))

end

theorem corr_of_val (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' hj hj' hjj'
  apply Units.ext
  apply fn_ext
  intro y hy
  have hyl : y ∈ LB.wchart L φ j := hy.1
  have hyr : y ∈ LB.wchart L φ' j' := hy.2
  have hc : ∀ a b, Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) a =
      Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) b → Sum.elim j j' a = Sum.elim j j' b := by
    rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr, Category.id_comp] at hab ⊢
    · exact hj a b hab
    · exact hjj' a b hab
    · exact (hjj' b a hab.symm).symm
    · exact hj' a b hab
  have hjv : ∀ k, Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k) k y ∈ L.U (Sum.elim j j' k) := by
    rintro (k | k)
    · exact Set.mem_iInter.1 hyl k
    · exact Set.mem_iInter.1 hyr k
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL y (Sum.elim (fun k => 𝟙 Y ≫ φ k) (fun k => 𝟙 Y ≫ φ' k)) (Sum.elim j j') hc hjv
  have e := h y J hJ
  rw [val_of t (𝟙 Y) y J j (fun k => hJj (Sum.inl k)), val_of t' (𝟙 Y) y J j' (fun k => hJj (Sum.inr k))] at e
  exact ((gs_res (𝟙 Y) y inf_le_left hy (t.s j).val).trans (gs_unit (𝟙 Y) y _ hyl _)).trans
    ((congrArg Units.val e).trans ((gs_res (𝟙 Y) y inf_le_right hy (t'.s j').val).trans
      (gs_unit (𝟙 Y) y _ hyr _)).symm)

def trF (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (j j' : K → L.ι) : (Z.presheaf.stalk z)ˣ :=
  ∏ k, gm (r ≫ φ k) z (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)) ^ ε k

theorem trF_trans (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {i j k : K → L.ι}
    (hi : r z ∈ LB.wchart L φ i) (hj : r z ∈ LB.wchart L φ j) (hk : r z ∈ LB.wchart L φ k) :
    trF φ ε r z i j * trF φ ε r z j k = trF φ ε r z i k := by
  unfold trF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [← mul_zpow]
  congr 1
  have hm : (r ≫ φ c) z ∈ L.U (i c) ⊓ L.U (j c) ⊓ L.U (k c) :=
    ⟨⟨Set.mem_iInter.1 hi c, Set.mem_iInter.1 hj c⟩, Set.mem_iInter.1 hk c⟩
  have c1 := congrArg (gm (r ≫ φ c) z (L.U (i c) ⊓ L.U (j c) ⊓ L.U (k c))) (hL.cocycle (i c) (j c) (k c))
  rw [map_mul] at c1
  exact (congrArg₂ (· * ·) (gm_res (r ≫ φ c) z _ hm _) (gm_res (r ≫ φ c) z _ hm _)).symm.trans
    (c1.trans (gm_res (r ≫ φ c) z _ hm _))

theorem gen_trans {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gm r z (LB.wchart L φ j) (t.s j) = trF φ ε r z j j' * gm r z (LB.wchart L φ j') (t.s j') := by
  have hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := ⟨hj, hj'⟩
  have e := congrArg (gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j')) (ht j j')
  have e1 : gm r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j') = trF φ ε r z j j' :=
    gm_linComb L φ ε r z j j' hj hj'
  exact (gm_res r z inf_le_left hm _).symm.trans
    (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) e1 (gm_res r z inf_le_right hm _))))

theorem sec_trans {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {j j' : K → L.ι} (hj : r z ∈ LB.wchart L φ j) (hj' : r z ∈ LB.wchart L φ j') :
    gs r z (LB.wchart L φ j) (s.f j) = (trF φ ε r z j j').val * gs r z (LB.wchart L φ j') (s.f j') := by
  have hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := ⟨hj, hj'⟩
  have e := congrArg (gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j')) (s.compat j j')
  have e1 := (gs_unit r z _ hm ((LB.LinComb L φ ε).g j j')).trans
    (congrArg Units.val (gm_linComb L φ ε r z j j' hj hj'))
  exact (gs_res r z inf_le_left hm _).symm.trans
    (e.trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) e1 (gs_res r z inf_le_right hm _))))

def FormEq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) : Prop :=
  ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = ∏ k, h (φ' k) ^ ε' k

theorem FormEq.trF {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε') (r : Z ⟶ Y)
    (z : Z) (I I' : (Y ⟶ X) → L.ι) :
    trF φ ε r z (fun k => I (φ k)) (fun k => I' (φ k)) = trF φ' ε' r z (fun k => I (φ' k)) (fun k => I' (φ' k)) := h _ fun ψ => gm (r ≫ ψ) z (L.U (I ψ) ⊓ L.U (I' ψ)) (L.g (I ψ) (I' ψ))

theorem exists_sec (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (s : LB.Sec (LB.LinComb L φ ε)) : ∃ s' : LB.Sec (LB.LinComb L φ' ε'),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval s' r z J = sval s r z J := by
  have glue : ∀ j : K' → L.ι, ∃ a : Γ(Y, LB.wchart L φ' j), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Y ⟶ X) → L.ι),
      r z ∈ LB.wchart L φ' j → r z ∈ LB.wchart L φ' (fun k => I (φ' k)) → r z ∈ LB.wchart L φ (fun k => I (φ k)) →
      gs r z _ a = (trF φ' ε' r z j (fun k => I (φ' k))).val * gs r z (LB.wchart L φ (fun k => I (φ k))) (s.f (fun k => I (φ k))) := by
    intro j
    let W : ((Y ⟶ X) → L.ι) → Y.Opens := fun I =>
      LB.wchart L φ' j ⊓ LB.wchart L φ' (fun k => I (φ' k)) ⊓ LB.wchart L φ (fun k => I (φ k))
    obtain ⟨u, hu⟩ : ∃ u : ∀ I, Γ(Y, W I), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) I, r z ∈ W I →
        gs r z (W I) (u I) = (trF φ' ε' r z j (fun k => I (φ' k))).val * gs r z (LB.wchart L φ (fun k => I (φ k))) (s.f (fun k => I (φ k))) :=
      ⟨fun I => (Y.presheaf.map (homOfLE (inf_le_left : W I ≤ LB.wchart L φ' j ⊓ LB.wchart L φ' (fun k => I (φ' k)))).op).hom
          ((LB.LinComb L φ' ε').g j (fun k => I (φ' k))).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W I ≤ LB.wchart L φ (fun k => I (φ k)))).op).hom (s.f (fun k => I (φ k))), fun Z r z I hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans ((gs_unit r z _ hz.1 _).trans
          (congrArg Units.val (gm_linComb L φ' ε' r z _ _ hz.1.1 hz.1.2)))) (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L φ' j)
      (fun I => homOfLE (inf_le_left.trans inf_le_left)) (fun y hy => by
        choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
        exact Opens.mem_iSup.2 ⟨I, ⟨hy, Set.mem_iInter.2 fun k => hI _⟩, Set.mem_iInter.2 fun k => hI _⟩) u
      (fun I I' => fn_ext (V := W I ⊓ W I') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y I hy.1, hu _ _ y I' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2, h.trF, ← mul_assoc, ← Units.val_mul,
          trF_trans hL φ' ε' (𝟙 Y) y hy.1.1.1 hy.1.1.2 hy.2.1.2])
    refine ⟨a, fun Z r z I h₁ h₂ h₃ => ?_⟩
    have hz : r z ∈ W I := ⟨⟨h₁, h₂⟩, h₃⟩
    exact (gs_res r z (inf_le_left.trans inf_le_left) hz a).symm.trans ((congrArg (gs r z (W I)) (ha I)).trans
      (hu Z r z I hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => ?_⟩
  · choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
    have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (fun k => I (φ' k)) := Set.mem_iInter.2 fun k => hI _
    have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ (fun k => I (φ k)) := Set.mem_iInter.2 fun k => hI _
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L φ' ε' (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y I hy.1 m₁ m₂).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y I hy.2 m₁ m₂)).symm)
    rw [← trF_trans hL φ' ε' (𝟙 Y) y hy.1 hy.2 m₁, Units.val_mul, mul_assoc]; rfl
  · have m := hJ.mem φ' r
    refine (ha _ Z r z (fun χ => J (r ≫ χ)) m m (hJ.mem φ r)).trans ?_
    rw [mul_eq_left.1 (trF_trans hL φ' ε' r z m m m), Units.val_one, one_mul]; rfl

def genSec {M : LB Y} (t : LB.Gen M) (ht : t.IsGen) : LB.Sec M := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩

theorem sval_genSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) : sval (genSec t ht) r z J = (val t r z J).val := by
  simp only [sval, val, genSec]
  exact gs_unit r z _ (hJ.mem φ r) _

theorem sval_trans (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (y : Y) (j : K → L.ι)
    (hy : y ∈ LB.wchart L φ j) : ∃ J, Good L y J ∧ gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL y (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim (fun a => a.elim)
    (fun k => k.elim)
  exact ⟨J, hJ, sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))⟩

theorem sec_ext_val (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)}
    (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = sval s' (𝟙 Y) y J) (j : K → L.ι) : s.f j = s'.f j := by
  apply fn_ext
  intro y hy
  obtain ⟨J, hJ, -⟩ := exists_good L hL y (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim (fun a => a.elim)
    (fun k => k.elim)
  exact (sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))).trans
    ((congrArg ((trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * ·) (h y J hJ)).trans
      (sec_trans s' (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))).symm)

theorem exists_gen (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : ∃ t' : LB.Gen (LB.LinComb L φ' ε'),
      t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J := by
  obtain ⟨s, hs⟩ := exists_sec hL h (genSec t ht)
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    rw [hs _ _ y J hJ, sval_genSec t ht _ y hJ, ← Units.val_mul] at e
    exact (congrArg IsUnit ((gs_eq (𝟙 Y) y (LB.wchart L φ' j) hy _).symm.trans e)).mpr (Units.isUnit _)
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j), fun Z r z J hJ => Units.ext ?_⟩
  exact (gs_unit r z _ (hJ.mem φ' r) _).symm.trans ((hs Z r z J hJ).trans (sval_genSec t ht r z hJ))

def pullMulSec {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) :
    LB.Sec (LB.LinComb L (Sum.elim (fun k => h ≫ φ k) φ₃) (Sum.elim ε ε₃)) :=
  have l₁ : ∀ j : K ⊕ K₃ → L.ι, LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j ≤ h ⁻¹ᵁ LB.wchart L φ (j ∘ Sum.inl) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have l₂ : ∀ j : K ⊕ K₃ → L.ι, LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j ≤ LB.wchart L φ₃ (j ∘ Sum.inr) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  { f := fun j => (Y'.presheaf.map (homOfLE (l₁ j)).op).hom ((h.app _).hom (s.f (j ∘ Sum.inl))) *
      (Y'.presheaf.map (homOfLE (l₂ j)).op).hom (u.s (j ∘ Sum.inr)).val
    compat := fun (j j' : K ⊕ K₃ → L.ι) => fn_ext fun y hy => by
      have v : ∀ j : K ⊕ K₃ → L.ι, y ∈ LB.wchart L (Sum.elim (fun k => h ≫ φ k) φ₃) j →
          gs (𝟙 Y') y _ ((Y'.presheaf.map (homOfLE (l₁ j)).op).hom ((h.app _).hom (s.f (j ∘ Sum.inl))) *
            (Y'.presheaf.map (homOfLE (l₂ j)).op).hom (u.s (j ∘ Sum.inr)).val) =
          gs (𝟙 Y' ≫ h) y (LB.wchart L φ (j ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) *
            (gm (𝟙 Y') y (LB.wchart L φ₃ (j ∘ Sum.inr)) (u.s (j ∘ Sum.inr))).val := fun j hj =>
        (gs_mul _ y _ hj _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hj _).trans (gs_pull _ h y _ (l₁ j hj) _))
          ((gs_res _ y _ hj _).trans (gs_unit _ y _ (l₂ j hj) _)))
      refine ((gs_res (𝟙 Y') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Y') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Y') y j j' hy.1 hy.2))) ((gs_res (𝟙 Y') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans s (𝟙 Y' ≫ h) y (l₁ j hy.1) (l₁ j' hy.2), gen_trans hu (𝟙 Y') y (l₂ j hy.1) (l₂ j' hy.2),
        Fintype.prod_sum_type, Units.val_mul, Units.val_mul, mul_mul_mul_comm]
      simp only [trF, Category.assoc, Sum.elim_inl, Sum.elim_inr, Function.comp_apply] }

theorem sval_pullMulSec {K₃ : Type} [Fintype K₃] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) {φ₃ : K₃ → (Y' ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen) (r : Z ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (pullMulSec s h u hu) r z J = sval s (r ≫ h) z J * (val u r z J).val := by
  have hm := hJ.mem (Sum.elim (fun k => h ≫ φ k) φ₃) r
  have hm1 : h (r z) ∈ LB.wchart L φ (fun k => J (r ≫ h ≫ φ k)) :=
    Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)
  have hm3 : r z ∈ LB.wchart L φ₃ (fun k => J (r ≫ φ₃ k)) := hJ.mem φ₃ r
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z _ hm _).trans (gs_pull r h z _ hm1 _))
    ((gs_res r z _ hm _).trans (gs_unit r z _ hm3 _)))

theorem secRel_iff (hL : L.IsLB) {K₃ : Type} [Fintype K₃] (φ₁ : K' → (Y' ⟶ X)) (ε₁ : K' → ℤ)
    (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (φ₃ : K₃ → (Y' ⟶ X)) (ε₃ : K₃ → ℤ) (u : LB.Gen (LB.LinComb L φ₃ ε₃)) :
    (Out.GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ ε s h φ₃ ε₃ u → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s₁ r z J = sval s (r ≫ h) z J * (val u r z J).val) ∧
    ((∀ y J, Good L y J → sval s₁ (𝟙 Y') y J = sval s (𝟙 Y' ≫ h) y J * (val u (𝟙 Y') y J).val) →
      Out.GeneratorPullback.SecRel L φ₁ ε₁ s₁ φ ε s h φ₃ ε₃ u) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j₁ : K' → L.ι) (j₂ : K → L.ι) (j₃ : K₃ → L.ι)
      (hm : r z ∈ LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ⊓ LB.wchart L φ₃ j₃)
      (a₁ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ LB.wchart L φ₁ j₁)
      (a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ h ⁻¹ᵁ LB.wchart L φ j₂)
      (a₃ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ k) j₂ ⊓ LB.wchart L φ₃ j₃ ≤ LB.wchart L φ₃ j₃),
      gs r z _ ((Y'.presheaf.map (homOfLE a₁).op).hom (s₁.f j₁)) = gs r z _ (s₁.f j₁) ∧
      gs r z _ ((Y'.presheaf.map (homOfLE a₂).op).hom ((h.app (LB.wchart L φ j₂)).hom (s.f j₂)) *
        (Y'.presheaf.map (homOfLE a₃).op).hom (u.s j₃).val) =
        gs (r ≫ h) z (LB.wchart L φ j₂) (s.f j₂) * (gm r z (LB.wchart L φ₃ j₃) (u.s j₃)).val :=
    fun Z r z j₁ j₂ j₃ hm a₁ a₂ a₃ => ⟨gs_res r z a₁ hm _, (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z a₂ hm _).trans (gs_pull r h z _ (a₂ hm) _)) ((gs_res r z a₃ hm _).trans (gs_unit r z _ (a₃ hm) _)))⟩
  constructor
  · intro H Z r z J hJ
    rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
    have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓ LB.wchart L (fun k => h ≫ φ k) (fun k => J (r ≫ h ≫ φ k)) ⊓
        LB.wchart L φ₃ (fun k => J (r ≫ φ₃ k)) := ⟨⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ k) r⟩, hJ.mem φ₃ r⟩
    have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ k)) (fun k => J (r ≫ φ₃ k)) (by
      rintro (a | a | a) (b | b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
    obtain ⟨k₁, k₂⟩ := key Z r z _ _ _ hm _ _ _
    exact k₁.symm.trans ((congrArg (gs r z _) e).trans k₂)
  · intro H j₁ j₂ j₃ hc
    refine fn_ext fun y hy => ?_
    obtain ⟨J, hJ, e⟩ := exists_good L hL y _ _ hc (by
      rintro (a | a | a)
      exacts [Set.mem_iInter.1 hy.1.1 a, Set.mem_iInter.1 hy.1.2 a, Set.mem_iInter.1 hy.2 a])
    have := H y J hJ
    rw [sval_of s₁ _ y J j₁ (fun k => by rw [Category.id_comp]; exact e (.inl k)),
      sval_of s _ y J j₂ (fun k => by rw [Category.id_comp]; exact e (.inr (.inl k))),
      val_of u _ y J j₃ (fun k => by rw [Category.id_comp]; exact e (.inr (.inr k)))] at this
    obtain ⟨k₁, k₂⟩ := key _ (𝟙 Y') y j₁ j₂ j₃ hy _ _ _
    exact k₁.trans (this.trans k₂.symm)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
