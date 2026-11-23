import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationRingStalk
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallPowDvdGerm
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

private theorem exists_pt {Y C : Scheme.{0}} (p : Y ⟶ C) [GeometricallyIntegral p] (s : C) :
    ∃ y : Y, p y = s ∧ (IsLocalRing.maximalIdeal (C.presheaf.stalk (p y))).map (p.stalkMap y).hom =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  have : IsIntegral (p.fiber s) := inferInstance
  refine ⟨p.fiberι s (genericPoint _), GlobalTheory.FibreStalk.image_eq C Y p s _, ?_⟩
  rw [← GlobalTheory.FibreStalk.ker_stalkMap_fiberι]
  letI : Field ((p.fiber s).presheaf.stalk (genericPoint _)) := inferInstanceAs (Field (p.fiber s).functionField)
  exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ ((p.fiberι s).stalkMap_surjective _))

private theorem exists_pow_unit {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] {ϖ : R}
    (h : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) {a : R} (ha : a ≠ 0) : ∃ (n : ℕ) (e : Rˣ), a = ϖ ^ n * e := by
  have hϖ : ¬ IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).1 (h ▸ Ideal.mem_span_singleton_self ϖ)
  obtain ⟨n, b, hb, e⟩ := WfDvdMonoid.max_power_factor' ha hϖ
  have : IsUnit b := by
    by_contra hu
    exact hb (Ideal.mem_span_singleton.1 (h ▸ (IsLocalRing.mem_maximalIdeal b).2 hu))
  exact ⟨n, this.unit, e⟩

open GlobalTheory.PrimeSection in

private theorem exists_unit_near {Y C : Scheme.{0}} (p : Y ⟶ C) [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y)
    (π : C.presheaf.stalk (p y))
    (hπ : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = Ideal.span {(p.stalkMap y).hom π})
    (U : Y.Opens) (f : Γ(Y, U)) (hU : (U : Set Y).Nonempty) (hf : IsUnit f) :
    ∃ (W : C.Opens) (c d : Γ(C, W)) (U₁ : Y.Opens) (f₁ : Γ(Y, U₁)) (V : Y.Opens) (h : V ≤ U) (h₁ : V ≤ U₁)
      (h₂ : V ≤ p ⁻¹ᵁ W), y ∈ U₁ ∧ IsUnit f₁ ∧ (V : Set Y).Nonempty ∧ IsUnit ((p.appLE W V h₂).hom d) ∧
      (Y.presheaf.map (homOfLE h).op).hom f * (p.appLE W V h₂).hom c =
        (Y.presheaf.map (homOfLE h₁).op).hom f₁ * (p.appLE W V h₂).hom d := by
  obtain ⟨x, hx⟩ := hU
  have hg : genericPoint Y ∈ U := PrimeSection.genericPoint_mem hx
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Y.presheaf.stalk y) (K := Y.functionField)
    (Y.presheaf.germ U _ hg f)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap _ Y.functionField b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact (hf.map (Y.presheaf.germ U _ hg).hom).ne_zero hab.symm
  obtain ⟨n, a₁, rfl⟩ := exists_pow_unit hπ ha0
  obtain ⟨m, b₁, rfl⟩ := exists_pow_unit hπ hb0
  obtain ⟨U₀, hy, f₀, hf₀⟩ := Y.presheaf.exists_germ_eq (a₁ * b₁⁻¹).val
  obtain ⟨W, hW, π₀, rfl⟩ := C.presheaf.exists_germ_eq π
  have hϖ : (p.stalkMap y).hom (C.presheaf.germ W _ hW π₀) = Y.presheaf.germ (p ⁻¹ᵁ W) y hW (p.app W π₀) :=
    Scheme.Hom.germ_stalkMap_apply ..
  rw [hϖ] at hab ha0 hb'
  have hy₁ : y ∈ Y.basicOpen f₀ := (Y.mem_basicOpen f₀ y hy).2 (hf₀ ▸ Units.isUnit _)
  have hd : p.app W (π₀ ^ n) ≠ 0 := fun h0 => by
    rw [← map_pow, ← map_pow, h0, map_zero, zero_mul] at ha0
    exact ha0 rfl
  refine ⟨W, π₀ ^ m, π₀ ^ n, Y.basicOpen f₀, Y.presheaf.map (homOfLE (Y.basicOpen_le f₀)).op f₀, U ⊓ Y.basicOpen f₀ ⊓ Y.basicOpen (p.app W (π₀ ^ n)),
    inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right, inf_le_right.trans (Y.basicOpen_le _), hy₁,
    Y.toRingedSpace.isUnit_res_basicOpen f₀, ⟨_, ⟨hg, PrimeSection.genericPoint_mem hy₁⟩, genericPoint_mem_basicOpen hd⟩, ?_, ?_⟩
  · have := (Y.toRingedSpace.isUnit_res_basicOpen (p.app W (π₀ ^ n))).map (Y.presheaf.map (homOfLE
      (inf_le_right : U ⊓ Y.basicOpen f₀ ⊓ Y.basicOpen (p.app W (π₀ ^ n)) ≤ _)).op).hom
    exact (res_res _ _ _).symm ▸ this
  · refine eq_of_germ_eq fun hV => ?_
    have e : ∀ (c : Γ(C, W)) h₂, Y.presheaf.germ _ _ hV ((p.appLE W _ h₂).hom c) =
        algebraMap _ Y.functionField (Y.presheaf.germ (p ⁻¹ᵁ W) y hW (p.app W c)) := fun c h₂ =>
      (germ_res h₂ hV (p.app W c)).trans (algebraMap_germ (W := p ⁻¹ᵁ W) (x := y) hW _).symm
    rw [map_mul, map_mul, e, e, germ_res, germ_res, germ_res]
    rw [← hab, ← algebraMap_germ hy, hf₀, div_mul_eq_mul_div, div_eq_iff hb']
    simp only [← map_mul, map_pow]
    simp only [← map_pow (algebraMap _ Y.functionField), ← map_mul]
    congr 1
    rw [Units.val_mul]
    linear_combination (-(Y.presheaf.germ (p ⁻¹ᵁ W) y hW (p.app W π₀)) ^ (n + m) * a₁.val) * b₁.inv_mul

private theorem wt_of_res (hW : WtGeneric) {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
    (u : splitTorus S X ⟶ G) [IsMonHom u] (hI : IsIntegral (splitTorus S X ⊗ G).left) {U V : G.left.Opens}
    (h : V ≤ U) (hV : (V : Set G.left).Nonempty) (f : Γ(G.left, U)) (χ : X)
    (hf : IsWt u V ((G.left.presheaf.map (homOfLE h).op).hom f) χ) : Wt u U f χ := by
  let T := splitTorus S X
  let O : (T ⊗ G).left.Opens := ((fst T G ≫ u) * snd T G).left ⁻¹ᵁ V ⊓ (snd T G).left ⁻¹ᵁ V
  have hO : Nonempty O := by
    obtain ⟨x, hx⟩ := hV
    let σ : G ⟶ T ⊗ G := lift 1 (𝟙 G)
    have e₁ : σ ≫ ((fst T G ≫ u) * snd T G) = 𝟙 G := by
      rw [MonObj.comp_mul, ← Category.assoc, lift_fst, lift_snd, MonObj.one_comp, _root_.one_mul]
    have e₂ : σ ≫ snd T G = 𝟙 G := lift_snd _ _
    have k : ∀ r : T ⊗ G ⟶ G, σ ≫ r = 𝟙 G → σ.left x ∈ r.left ⁻¹ᵁ V := fun r hr => by
      have : r.left (σ.left x) = x := by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hr]; rfl
      show r.left (σ.left x) ∈ V
      rw [this]; exact hx
    exact ⟨⟨σ.left x, k _ e₁, k _ e₂⟩⟩
  let Z : Over S := Over.mk (O.ι ≫ (T ⊗ G).hom)
  let j : Z ⟶ T ⊗ G := Over.homMk O.ι rfl
  have hj : lift (j ≫ fst T G) (j ≫ snd T G) = j := by rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have k : ∀ r : T ⊗ G ⟶ G, O ≤ r.left ⁻¹ᵁ V → ⊤ ≤ (j ≫ r).left ⁻¹ᵁ V := fun r hr z _ => hr z.2
  have k₁ : ⊤ ≤ (((j ≫ fst T G) ≫ u) * (j ≫ snd T G)).left ⁻¹ᵁ V := by
    rw [Category.assoc, ← MonObj.comp_mul]; exact k _ inf_le_left
  have k₂ : ⊤ ≤ (j ≫ snd T G).left ⁻¹ᵁ V := k _ inf_le_right
  have e : ∀ (r : Z.left ⟶ G.left) (k : ⊤ ≤ r ⁻¹ᵁ V), (r.appLE V ⊤ k).hom ((G.left.presheaf.map (homOfLE h).op).hom f) =
      (r.appLE U ⊤ (k.trans (r.preimage_mono h))).hom f := fun r k =>
    congrArg (fun q => q.hom f) (r.map_appLE k (homOfLE h).op)
  refine hW S G X u hI U f χ Z (j ≫ fst T G) (j ≫ snd T G) ?_ (k₁.trans (Scheme.Hom.preimage_mono _ h))
    (k₂.trans (Scheme.Hom.preimage_mono _ h)) ?_
  · rw [hj]
    show IsDominant O.ι
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Opens.range_ι]
    exact O.isOpen.dense (by obtain ⟨z⟩ := hO; exact ⟨z.1, z.2⟩)
  · rw [← e _ k₁, ← e _ k₂]
    exact hf Z _ _ k₁ k₂

private theorem isWt_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
    (u : splitTorus S X ⟶ G) {V : G.left.Opens} (W : S.Opens) (h : V ≤ G.hom ⁻¹ᵁ W) (c : Γ(S, W)) :
    IsWt u V ((G.hom.appLE W V h).hom c) 0 := fun Z t g h₁ h₂ => by
  rw [← chV_val, chV_zero, Units.val_one, _root_.one_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [Over.w]

theorem UpperTheory.torus_weight_unit_local :
    WtGeneric → ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
        ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus C X ⟶ G), IsMonHom u →
        ∀ (χ : X) (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty → IsUnit f → Wt u U f χ →
        ∀ s : C, ∃ (U₁ : G.left.Opens) (f₁ : Γ(G.left, U₁)), (∃ y ∈ U₁, G.hom y = s) ∧ IsUnit f₁ ∧ Wt u U₁ f₁ χ := by
  intro hW k _ _ C _ hC G _ hG X _ _ _ u hu χ U f hU hf hw s
  have : IsIntegral C := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have := hC.1
  have : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  have := hG.smooth
  have := hG.geomConnected
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsIntegral G.left := isIntegral_left_of_isSemiAbelian G
  have := geometricallyIntegral_of_isSemiAbelian G
  have hI : IsIntegral (splitTorus C X ⊗ G).left := by
    have : IsIntegral (splitTorus C X).left :=
      isIntegral_left_of_isSemiAbelian (splitTorus C X) (h := Diag.isSemiAbelian C X)
    have : Smooth (fst (splitTorus C X) G).left := inferInstanceAs (Smooth (pullback.fst _ G.hom))
    have : GeometricallyConnected (fst (splitTorus C X) G).left :=
      inferInstanceAs (GeometricallyConnected (pullback.fst _ G.hom))
    exact isIntegral_of_smooth_of_geometricallyConnected (fst (splitTorus C X) G).left
  obtain ⟨y, hy, hm⟩ := exists_pt G.hom s
  have := GlobalTheory.ProjHol.valuationRing_stalk (strHom k C) (G.hom y)
  have : IsPrincipalIdealRing (C.presheaf.stalk (G.hom y)) := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal (C.presheaf.stalk (G.hom y)))).principal
  rw [hπ, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton] at hm
  obtain ⟨W, c, d, U₁, f₁, V, h, h₁, h₂, hy₁, hf₁, hV, hd, e⟩ := exists_unit_near G.hom y π hm.symm U f hU hf
  refine ⟨U₁, f₁, ⟨y, hy₁, hy⟩, hf₁, wt_of_res hW u hI h₁ hV f₁ χ ?_⟩
  have w₁ := ((IsWt.res (i := u) hw h).mul (isWt_base u W h₂ c)).mul
    (IsWt.inv (u := hd.unit) (isWt_base u W h₂ d))
  rw [e, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one] at w₁
  simpa using w₁
