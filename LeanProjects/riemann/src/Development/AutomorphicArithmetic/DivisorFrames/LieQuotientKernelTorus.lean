import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusStableAffineOpenFunctionsWeightGraded
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

open GlobalTheory.Conormal GlobalTheory.DualPull in
private theorem isIso_map_open {S X X' : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} {π' : X' ⟶ S} {e' : S ⟶ X'}
    {φ : X' ⟶ X} [IsOpenImmersion φ] (he : e ≫ π = 𝟙 S) (he' : e' ≫ π' = 𝟙 S) (w : φ ≫ π = π')
    (we : e' ≫ φ = e) : IsIso (Conormal.map he' w we) := by
  have hle (W : X'.Opens) : W ≤ φ ⁻¹ᵁ φ ''ᵁ W := (φ.preimage_image_eq W).ge
  have hα (W : X'.Opens) (f : Γ(X', W)) : φ.appLE (φ ''ᵁ W) W (hle W) ((φ.appIso W).inv f) = f := by
    rw [← Scheme.Hom.appIso_hom']
    exact congr($((φ.appIso W).inv_hom_id) f)
  have hinj (W : X'.Opens) : Function.Injective (φ.appLE (φ ''ᵁ W) W (hle W)) := by
    rw [← Scheme.Hom.appIso_hom']
    exact (ConcreteCategory.bijective_of_isIso (φ.appIso W).hom).1
  have hV {W : X'.Opens} {V : S.Opens} (h : V ≤ e' ⁻¹ᵁ W) : V ≤ e ⁻¹ᵁ φ ''ᵁ W :=
    (le_preimage_of_comp we).1 (h.trans (e'.preimage_mono (hle W)))
  let D : Der π' e' (conormal e) :=
    { app := fun {W V} h => (d he (hV h)).comp (φ.appIso W).inv.hom.toAddMonoidHom
      res_app := fun h h' f => resM_d he (hV h) h' _
      app_res := fun {W W' V} h k f => by
        have : (φ.appIso W').inv (resG X' k f) = resG X (φ.image_mono k) ((φ.appIso W).inv f) := by
          apply hinj
          rw [hα, appLE_resG, ← resG_appLE φ k (hle W), hα]
        exact (congrArg (d he (hV h)) this).trans (d_resG he _ _ _)
      app_mul := fun {W V} h f g => by
        refine (congrArg (d he (hV h)) (map_mul (φ.appIso W).inv.hom f g)).trans ((d_mul he _ _ _).trans ?_)
        rw [← appLE_appLE we (hle W) h, ← appLE_appLE we (hle W) h]
        erw [hα, hα]
        rfl
      app_base := fun {W V U} h k a => by
        have k' : φ ''ᵁ W ≤ π ⁻¹ᵁ U := by
          rintro _ ⟨x, hx, rfl⟩
          exact (le_preimage_of_comp w).2 k hx
        have : (φ.appIso W).inv (π'.appLE U W k a) = π.appLE U _ k' a := by
          apply hinj
          rw [hα, appLE_appLE w]
        exact (congrArg (d he (hV h)) this).trans (d_base he _ _ _) }
  refine ⟨D.lift, Conormal.hom_ext he fun W f => ?_, Conormal.hom_ext he' fun W f => ?_⟩
  · have h' := (le_preimage_of_comp we).2 (le_refl (e ⁻¹ᵁ W))
    rw [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply, map_d he he' w we _ h' le_rfl, Der.lift_d]
    have : (φ.appIso (φ ⁻¹ᵁ W)).inv (φ.appLE W _ le_rfl f) = resG X (φ.image_preimage_le W) f := by
      apply hinj
      rw [hα, appLE_resG]
    exact (congrArg (d he (hV h')) this).trans (d_resG he _ _ _)
  · rw [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply, Der.lift_d]
    exact (map_d he he' w we (hV le_rfl) le_rfl (hle W) _).trans (congrArg _ (hα W f))

private theorem isIso_cotMap_open {S : Scheme.{0}} {T T' : Over S} {s : 𝟙_ (Over S) ⟶ T} {s' : 𝟙_ (Over S) ⟶ T'}
    (φ : T' ⟶ T) (h : s' ≫ φ = s) [IsOpenImmersion φ.left] : IsIso (cotMap φ h) :=
  isIso_map_open (sec_hom s) _ _ _

private def WG {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G)
    (V : G.left.Opens) : Prop :=
  (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V ∧
    ∃ u : Multiplicative X →* Γ(G.left, V)ˣ, ∀ χ, Wt i V (u (Multiplicative.ofAdd χ)).val χ

private theorem exists_tau {S : Scheme.{0}} {G Vo : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
    {u : splitTorus S X ⟶ G} {V : G.left.Opens} (hV : WG u V) (j : Vo ⟶ G) (hj : ⊤ ≤ j.left ⁻¹ᵁ V) :
    ∃ τ : Vo ⟶ splitTorus S X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (x y : Z ⟶ Vo),
      y ≫ j = (t ≫ u) * (x ≫ j) → y ≫ τ = t * (x ≫ τ) := by
  obtain ⟨-, w, hw⟩ := hV
  let τ : Vo ⟶ splitTorus S X := (splitTorusPointsEquiv S X Vo).symm
    ((Units.map (j.left.appLE V ⊤ hj).hom.toMonoidHom).comp w)
  have hτ (χ : X) : (chV τ χ).val = (j.left.appLE V ⊤ hj).hom (w (Multiplicative.ofAdd χ)).val := by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  refine ⟨τ, fun Z t x y h => ?_⟩
  refine (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => Units.ext ?_)
  change (chV (y ≫ τ) χ.toAdd).val = (chV (t * (x ≫ τ)) χ.toAdd).val
  have k₁ := TorusGrading.top_le_comp_left y hj
  have k₂ := TorusGrading.top_le_comp_left x hj
  rw [chV_mul, Units.val_mul, TorusGrading.chV_comp, TorusGrading.chV_comp, hτ,
    ← TorusGrading.val_comp y hj k₁, ← TorusGrading.val_comp x hj k₂,
    TorusGrading.val_congr h k₁ (h ▸ k₁), hw _ Z t (x ≫ j) _ k₂, chV_val]

private theorem free_etale_sheaf_zmod_exists_hom_sending_generator {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    [IsMonHom q] (hk : IsPullback u (toUnit _) q η[B]) {Z : Over S} (x y : Z ⟶ G) (h : x ≫ q = y ≫ q) :
    ∃ t : Z ⟶ T, y = (t ≫ u) * x := by
  have h1 : (y / x) ≫ q = toUnit Z ≫ η[B] := by
    rw [GrpObj.div_comp, h, div_self', Hom.one_def]
  exact ⟨hk.lift (y / x) (toUnit Z) h1, by rw [hk.lift_fst, div_mul_cancel]⟩

private theorem exists_open {S : Scheme.{0}} {G B : Over S} [GrpObj G] [GrpObj B] {X : Type} [AddCommGroup X]
    {u : splitTorus S X ⟶ G} {q : G ⟶ B} (hq : IsKer u q) {V : G.left.Opens} (hV : WG u V) :
    ∃ W : B.left.Opens, V = q.left ⁻¹ᵁ W := by
  obtain ⟨_, _, _, _, hk⟩ := hq
  have hsat : q.left ⁻¹' (q.left '' V) = V := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro y ⟨x, hx, e⟩
    obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback x y e
    let Z : Over S := Over.mk (pullback.fst q.left q.left ≫ G.hom)
    let a : Z ⟶ G := Over.homMk (pullback.fst q.left q.left) rfl
    let b : Z ⟶ G := Over.homMk (pullback.snd q.left q.left) (by
      rw [← Over.w q, ← pullback.condition_assoc, Over.w]; rfl)
    obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hk a b (Over.OverMorphism.ext pullback.condition)
    have h2 : (lift t a).left z ∈ (snd (splitTorus S X) G).left ⁻¹ᵁ V := by
      show (lift t a ≫ snd _ _).left z ∈ V
      rw [lift_snd]; exact hx
    have h3 : (lift t a ≫ ((fst (splitTorus S X) G ≫ u) * snd (splitTorus S X) G)).left z ∈ V := hV.1 h2
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, ← ht] at h3
    exact h3
  refine ⟨⟨q.left '' V, (Flat.isQuotientMap_of_surjective q.left).isOpen_preimage.1 (by rw [hsat]; exact V.2)⟩, ?_⟩
  ext1
  exact hsat.symm

private theorem selfDualLattice_projection_mem_of_unit_length {C : Type*} [Category C] [Preadditive C] {B G T V W : C} (a : B ⟶ G) (b : G ⟶ T)
    (J : G ⟶ V) (K : B ⟶ W) (σ : G ⟶ W) (τ : T ⟶ V) (u : V ⟶ T) (q : W ⟶ V) (hJ : IsIso J) (hK : IsIso K)
    (c₁ : a ≫ σ = K) (c₂ : J ≫ u = b) (c₃ : τ ≫ u = 𝟙 _) (c₄ : a ≫ J = K ≫ q) (c₅ : b ≫ τ + σ ≫ q = J) :
    ∃ (r : G ⟶ B) (s : T ⟶ G), a ≫ r = 𝟙 _ ∧ s ≫ b = 𝟙 _ ∧ b ≫ s + r ≫ a = 𝟙 _ := by
  refine ⟨σ ≫ inv K, τ ≫ inv J, by rw [reassoc_of% c₁, IsIso.hom_inv_id], by simp [← c₂, c₃], ?_⟩
  rw [← cancel_mono J]
  simp [c₄, c₅]

private theorem exists_split {S : Scheme.{0}} {G B : Over S} [GrpObj G] [GrpObj B] {X : Type} [AddCommGroup X]
    {u : splitTorus S X ⟶ G} {q : G ⟶ B} [IsMonHom u] [IsMonHom q] [QuasiSeparated G.hom] (hq : IsKer u q)
    {V : G.left.Opens} (hV : WG u V) (he : ⊤ ≤ η[G].left ⁻¹ᵁ V) :
    ∃ (r : omega G ⟶ omega B) (s : omega (splitTorus S X) ⟶ omega G), omegaMap q ≫ r = 𝟙 _ ∧
      s ≫ omegaMap u = 𝟙 _ ∧ omegaMap u ≫ s + r ≫ omegaMap q = 𝟙 _ := by
  obtain ⟨W, rfl⟩ := exists_open hq hV
  obtain ⟨_, _, _, _, hk⟩ := hq
  let Vo : Over S := Over.mk ((q.left ⁻¹ᵁ W).ι ≫ G.hom)
  let Wo : Over S := Over.mk (W.ι ≫ B.hom)
  let j : Vo ⟶ G := Over.homMk (q.left ⁻¹ᵁ W).ι rfl
  let k : Wo ⟶ B := Over.homMk W.ι rfl
  let q' : Vo ⟶ Wo := Over.homMk (q.left ∣_ W) (by
    change _ ≫ W.ι ≫ B.hom = _ ≫ G.hom
    rw [morphismRestrict_ι_assoc, Over.w])
  have hq' : q' ≫ k = j ≫ q := Over.OverMorphism.ext (morphismRestrict_ι _ _)
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (q.left ⁻¹ᵁ W).ι)
  have : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion W.ι)
  have : Flat q'.left := inferInstanceAs (Flat (q.left ∣_ W))
  have : Surjective q'.left := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹Surjective q.left› W
  have : QuasiCompact q'.left := MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_morphismRestrict q.left W).flip ‹QuasiCompact q.left›
  have : Mono j := Over.mono_of_mono_left j
  have hj : ⊤ ≤ j.left ⁻¹ᵁ q.left ⁻¹ᵁ W := fun y _ => y.2
  have hl {Z : Over S} (g : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ q.left ⁻¹ᵁ W) : ∃ g' : Z ⟶ Vo, g' ≫ j = g := by
    have hr : Set.range g.left ⊆ Set.range j.left := by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨_, h (x := z) trivial⟩, rfl⟩
    have hf := IsOpenImmersion.lift_fac j.left g.left hr
    exact ⟨Over.homMk (IsOpenImmersion.lift j.left g.left hr) (by
      rw [← Over.w j, reassoc_of% hf, Over.w]), Over.OverMorphism.ext hf⟩
  obtain ⟨τ₀, hτ₀⟩ := exists_tau hV j hj
  obtain ⟨e, hej⟩ := hl η[G] he
  let τ : Vo ⟶ splitTorus S X := τ₀ * (toUnit _ ≫ e ≫ τ₀)⁻¹
  have hτ (Z : Over S) (t : Z ⟶ splitTorus S X) (x y : Z ⟶ Vo) (h : y ≫ j = (t ≫ u) * (x ≫ j)) :
      y ≫ τ = t * (x ≫ τ) := by
    simp only [τ, MonObj.comp_mul, GrpObj.comp_inv, hτ₀ Z t x y h, comp_toUnit_assoc, _root_.mul_assoc]
  have heτ : e ≫ τ = η := by
    simp only [τ, MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc, toUnit_unit, Category.id_comp,
      mul_inv_cancel, Hom.one_def]
  have hu : (𝟙 _ ≫ u) * (toUnit _ ≫ η[G]) = u := by rw [← Hom.one_def, _root_.mul_one, Category.id_comp]
  obtain ⟨u', hu'⟩ := hl u (hu ▸ TorusGrading.top_le_act hV.1 (𝟙 _) (TorusGrading.top_le_comp_left _ he))
  have huτ : u' ≫ τ = 𝟙 _ := by
    rw [hτ _ (𝟙 _) (toUnit _ ≫ e) u' (by rw [Category.assoc, hej, hu, hu']), Category.assoc, heτ,
      ← Hom.one_def, _root_.mul_one]
  have heu : η ≫ u' = e := by rw [← cancel_mono j, Category.assoc, hu', hej, IsMonHom.one_hom]
  obtain ⟨σ, hσ⟩ := AbelianQuotient.exists_desc q' ((τ ≫ u)⁻¹ * j) fun Z x y h => by
    obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hk (x ≫ j) (y ≫ j) (by rw [Category.assoc, Category.assoc, ← hq', reassoc_of% h])
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hτ Z t x y ht, ht, MonObj.mul_comp]
    group
  have huq : u ≫ q = 1 := hk.w
  have hσq : σ ≫ q = k := by
    have := FlatQuotient.epi_of_flat_surjective q'
    rw [← cancel_epi q', reassoc_of% hσ, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, huq, MonObj.comp_one,
      inv_one, _root_.one_mul, hq']
  have heτu : e ≫ τ ≫ u = η := by rw [reassoc_of% heτ, IsMonHom.one_hom]
  have h1 : η[G] = 1 := by simp [Hom.one_def]
  have heσ : e ≫ q' ≫ σ = η := by
    rw [hσ, MonObj.comp_mul, GrpObj.comp_inv, heτu, hej, inv_mul_cancel, h1]
  have heσ' : (e ≫ q') ≫ σ = η := by rw [Category.assoc, heσ]
  have hek : (e ≫ q') ≫ k = η := by rw [Category.assoc, hq', reassoc_of% hej, IsMonHom.one_hom]
  have hjm : (τ ≫ u) * (q' ≫ σ) = j := by rw [hσ, mul_inv_cancel_left]
  have hq1 := IsMonHom.one_hom q
  have hu1 := IsMonHom.one_hom u
  refine selfDualLattice_projection_mem_of_unit_length (cotMap q hq1) (cotMap u hu1) (cotMap j hej) (cotMap k hek) (cotMap σ heσ') (cotMap τ heτ)
    (cotMap u' heu) (cotMap q' rfl) (isIso_cotMap_open j hej) (isIso_cotMap_open k hek) (cotMap_comp _ _ hσq _)
    (cotMap_comp _ _ hu' _) ((cotMap_comp _ _ huτ (Category.comp_id _)).trans (cotMap_id rfl _))
    ((cotMap_comp _ _ hq'.symm (by rw [← Category.assoc, hek])).trans (cotMap_comp _ _ rfl _).symm) ?_
  rw [cotMap_comp heσ' rfl rfl heσ, cotMap_comp hu1 heτ rfl heτu, ← cotMap_mul heτu heσ (hjm ▸ hej)]
  congr 1

private theorem key {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) {X : Type} [AddCommGroup X] {u : splitTorus S X ⟶ G}
    {u' : splitTorus S' X ⟶ G'} (h : TorusCompat f φ u' u) (Z : Over S') (t : Z ⟶ splitTorus S' X) (g : Z ⟶ G') :
    ∃ (t₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S X) (g₀ : Over.mk (Z.hom ≫ f) ⟶ G),
      (∀ χ, t₀.left.appTop.hom (charUnit S X χ).val = t.left.appTop.hom (charUnit S' X χ).val) ∧
      g₀.left = g.left ≫ φ ∧ ((t₀ ≫ u) * g₀).left = ((t ≫ u') * g).left ≫ φ := by
  obtain ⟨τ, hτ, hχ, e⟩ := h
  let t₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S X := Over.homMk (t.left ≫ τ) (by
    rw [Category.assoc, hτ, ← Category.assoc, Over.w]; rfl)
  let g₀ : Over.mk (Z.hom ≫ f) ⟶ G := Over.homMk (g.left ≫ φ) (by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w]; rfl)
  refine ⟨t₀, g₀, fun χ => ?_, rfl, ?_⟩
  · show (t.left ≫ τ).appTop.hom _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hχ]
  · refine hφ.2 Z (t ≫ u') g _ _ ?_ rfl
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← e, ← Category.assoc]; rfl

private theorem appLE_comp_exists {Z Y Y' : Scheme.{0}} (a : Z ⟶ Y') (φ : Y' ⟶ Y) (b : Z ⟶ Y) (e : b = a ≫ φ)
    (V : Y.Opens) (h : ⊤ ≤ a ⁻¹ᵁ φ ⁻¹ᵁ V) (s : Γ(Y, V)) :
    ∃ h' : ⊤ ≤ b ⁻¹ᵁ V, (b.appLE V ⊤ h').hom s = (a.appLE (φ ⁻¹ᵁ V) ⊤ h).hom ((φ.app V).hom s) := by
  subst e
  refine ⟨h, ?_⟩
  exact congrArg (fun q => q.hom s) (Scheme.Hom.comp_appLE a φ V ⊤ h)

private theorem wg_baseChange {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) {X : Type} [AddCommGroup X] {u : splitTorus S X ⟶ G}
    {u' : splitTorus S' X ⟶ G'} (h : TorusCompat f φ u' u) {V : G.left.Opens} (hV : WG u V) :
    WG u' (φ ⁻¹ᵁ V) := by
  obtain ⟨hst, w, hw⟩ := hV
  refine ⟨?_, (Units.map (φ.app V).hom.toMonoidHom).comp w, fun χ Z t g h₁ h₂ => ?_⟩
  · obtain ⟨t₀, g₀, -, e₁, e₂⟩ := key hφ h _ (fst (splitTorus S' X) G') (snd (splitTorus S' X) G')
    intro x hx
    have h1 : g₀.left x ∈ V := by rw [e₁]; exact hx
    have h2 : (lift t₀ g₀).left x ∈ (snd (splitTorus S X) G).left ⁻¹ᵁ V := by
      show (lift t₀ g₀ ≫ snd _ _).left x ∈ V
      rwa [lift_snd]
    have h3 : (lift t₀ g₀ ≫ ((fst (splitTorus S X) G ≫ u) * snd (splitTorus S X) G)).left x ∈ V := hst h2
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, e₂] at h3
    exact h3
  · obtain ⟨t₀, g₀, e₀, e₁, e₂⟩ := key hφ h Z t g
    obtain ⟨k₁, r₁⟩ := appLE_comp_exists _ φ _ e₂ V h₁ (w (Multiplicative.ofAdd χ)).val
    obtain ⟨k₂, r₂⟩ := appLE_comp_exists _ φ _ e₁ V h₂ (w (Multiplicative.ofAdd χ)).val
    have := hw χ _ t₀ g₀ k₁ k₂
    rw [r₁, r₂, e₀] at this
    exact this

open GlobalTheory.QCoh in
private theorem shortExact_of_local {X : Scheme.{0}} (S : ShortComplex X.Modules)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ (r : (Scheme.Modules.pullback U.ι).obj S.X₂ ⟶ (Scheme.Modules.pullback U.ι).obj S.X₁)
        (s : (Scheme.Modules.pullback U.ι).obj S.X₃ ⟶ (Scheme.Modules.pullback U.ι).obj S.X₂),
        (Scheme.Modules.pullback U.ι).map S.f ≫ r = 𝟙 _ ∧ s ≫ (Scheme.Modules.pullback U.ι).map S.g = 𝟙 _ ∧
        (Scheme.Modules.pullback U.ι).map S.g ≫ s + r ≫ (Scheme.Modules.pullback U.ι).map S.f = 𝟙 _) :
    S.ShortExact := by
  have hU (U V : X.Opens) : V ⊓ U ≤ U.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]; exact inf_le_right
  refine ShortComplex.ShortExact.mk' (DualExact.exact_of_locally _ fun V x hx => ?_)
    (mono_of_locally_app_injective _ fun V x hx => ?_) (epi_of_locally_app_surjective _ fun V x hx => ?_)
  · obtain ⟨U, hxU, r, s, -, -, h⟩ := H x
    refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, fun t ht => FlagLocal.mem_range_of_pullback U.ι S.f (hU U V) rfl t
      ⟨r.app _ (pullbackSections U.ι _ le_rfl t), ?_⟩⟩
    have := congr(($h).app _ (pullbackSections U.ι _ le_rfl t))
    refine Eq.trans ?_ this
    change _ = s.app _ (((Scheme.Modules.pullback U.ι).map S.g).app _ _) + _
    rw [pullback_map_app_pullbackSections, ht, map_zero, map_zero]
    exact (_root_.zero_add _).symm
  · obtain ⟨U, hxU, r, s, h, -, -⟩ := H x
    refine ⟨V ⊓ U, ⟨hx, hxU⟩, inf_le_left, fun a b e => ?_⟩
    apply (FlagLocal.bijective_pullbackSections U.ι S.X₁ (hU U V) rfl).1
    have ha := congr(($h).app _ (pullbackSections U.ι _ le_rfl a))
    have hb := congr(($h).app _ (pullbackSections U.ι _ le_rfl b))
    refine ha.symm.trans (Eq.trans ?_ hb)
    change r.app _ (((Scheme.Modules.pullback U.ι).map S.f).app _ _) =
      r.app _ (((Scheme.Modules.pullback U.ι).map S.f).app _ _)
    rw [pullback_map_app_pullbackSections, pullback_map_app_pullbackSections, e]
  · obtain ⟨U, hxU, r, s, -, h, -⟩ := H x
    exact ⟨V ⊓ U, ⟨hx, hxU⟩, inf_le_left, fun t => FlagLocal.mem_range_of_pullback U.ι S.g (hU U V) rfl t
      ⟨s.app _ (pullbackSections U.ι _ le_rfl t), congr(($h).app _ (pullbackSections U.ι _ le_rfl t))⟩⟩

private theorem transport {C : Type*} [Category C] [Preadditive C] {B G T B' G' T' : C} {a : B ⟶ G} {b : G ⟶ T}
    {a' : B' ⟶ G'} {b' : G' ⟶ T'} {β : B ⟶ B'} {g : G ⟶ G'} {θ : T ⟶ T'} (_ : IsIso β) (_ : IsIso g) (_ : IsIso θ)
    (h₁ : a ≫ g = β ≫ a') (h₂ : b ≫ θ = g ≫ b')
    (h : ∃ (r : G' ⟶ B') (s : T' ⟶ G'), a' ≫ r = 𝟙 _ ∧ s ≫ b' = 𝟙 _ ∧ b' ≫ s + r ≫ a' = 𝟙 _) :
    ∃ (r : G ⟶ B) (s : T ⟶ G), a ≫ r = 𝟙 _ ∧ s ≫ b = 𝟙 _ ∧ b ≫ s + r ≫ a = 𝟙 _ := by
  obtain ⟨r, s, e₁, e₂, e₃⟩ := h
  obtain rfl : a = β ≫ a' ≫ inv g := by simp [← reassoc_of% h₁]
  obtain rfl : b = g ≫ b' ≫ inv θ := by simp [← reassoc_of% h₂]
  refine ⟨g ≫ r ≫ inv β, θ ≫ s ≫ inv g, by simp [reassoc_of% e₁], by simp [reassoc_of% e₂], ?_⟩
  have := congr(g ≫ $e₃ ≫ inv g)
  simpa using this

theorem UpperTheory.lie_quotient_kernel_torus :
    ∀ (S : Scheme.{0}) (G B : Over S) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) (q : G ⟶ B) [IsMonHom u]
        [IsMonHom q], SmConn G → IsQuot u q → GoodCover u →
        Epi (lieMap q) ∧ Nonempty (kernel (lieMap q) ≅ Lie (splitTorus S X)) := by
  intro S G B _ _ X _ _ _ u q _ _ hG hq hc
  have hk := isKer_of_isQuot hq
  have := hG.2.2.1
  have := hq.2.2.2.2.2.2.2.2.1
  have huq : u ≫ q = 1 := hk.2.2.2.2.w
  have : IsMonHom (1 : splitTorus S X ⟶ B) := huq ▸ inferInstance
  have h0 : omegaMap q ≫ omegaMap u = 0 := by rw [← omegaMap_comp, omegaMap_congr huq, omegaMap_one]
  have hS : (ShortComplex.mk _ _ h0).ShortExact := shortExact_of_local _ fun x => by
    obtain ⟨V, hx, hV⟩ := hc (unitSec G x)
    refine ⟨unitSec G ⁻¹ᵁ V, hx, ?_⟩
    let f := (unitSec G ⁻¹ᵁ V).ι
    obtain ⟨G', _, φ, hφ⟩ : ∃ (G' : Over _) (_ : GrpObj G') (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ :=
      ⟨_, _, _, isGrpPullback_pullback G f⟩
    obtain ⟨B', _, ψ, hψ⟩ : ∃ (B' : Over _) (_ : GrpObj B') (ψ : B'.left ⟶ B.left), IsGrpPullback B' B f ψ :=
      ⟨_, _, _, isGrpPullback_pullback B f⟩
    obtain ⟨u', hu', -⟩ := existsUnique_torusCompat hφ.1 u
    have := hu'.isMonHom hφ
    obtain ⟨q', hq', sq⟩ := IsKer.baseChange hφ hψ hu' hk
    have := hq'.1
    have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback hφ.1 inferInstance
    have hT : IsGrpPullback (splitTorus _ X) (splitTorus S X) f (SplitTorus.bcMap f X) :=
      SplitTorus.isGrpPullback_bcMap f X
    have : QuasiSeparated (splitTorus S X).hom := inferInstance
    refine transport (isIso_omegaBase hψ) (isIso_omegaBase hφ) (isIso_omegaBase hT)
      (omegaBase_naturality hφ hψ q q' sq.w.symm) (omegaBase_naturality hT hφ u u' (torusCompat_iff.1 hu').symm)
      (exists_split hq' (wg_baseChange hφ hu' hV.2) fun y _ => ?_)
    change (unitSec _ ≫ _) y ∈ V
    rw [unitSec_comp hφ]
    exact y.2
  have hd := DualExact.shortExact_dual S _ _ hS (isFrame_dlogChar S (Module.Free.chooseBasis ℤ X)).isVB
  have := hd.mono_f
  exact ⟨hd.epi_g, ⟨IsLimit.conePointUniqueUpToIso (kernelIsKernel _) hd.exact.fIsKernel⟩⟩
