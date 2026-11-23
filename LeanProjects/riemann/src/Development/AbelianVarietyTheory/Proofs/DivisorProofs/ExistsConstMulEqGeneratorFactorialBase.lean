import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnitOnOpen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulUnitAtCodimOneOfFactorialBaseStatement

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.MBX
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GlobalVerticalUnit
open GlobalTheory.VerticalUnit

theorem exists_const_mul_eq_gen : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K) (M : LB X.left) (c : LB.Gen (M.pull φ)), Smooth X.hom → QuasiCompact X.hom → GeometricallyConnected X.hom → IsPullback φ p X.hom (spMap (algebraMap R K)) → M.IsLB → c.IsGen → ∃ (a : Kˣ) (u : LB.Gen M), u.IsGen ∧ ∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val := by
  intro R K _ _ _ _ _ _ _ X Y φ p M c hsm hqc hgc H hM hc
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ X.hom hsm hgc
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian X.hom
  have : IsIntegral Y := DvrModel.isIntegral_of_geometricallyIntegral H
  have := isNormalScheme_of_smooth X.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : AlgebraicGeometry.IsNoetherian X.left := {}
  have hinj := IsFractionRing.injective R K
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) H.flip
    (Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip
    (IsPreimmersion.of_isLocalization (nonZeroDivisors R))
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks φ
  have lift : ∀ x : X.left, (X.hom x).asIdeal = ⊥ → ∃ y, φ y = x := fun x hx => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum K)
      (PrimeSpectrum.ext (hx.trans (Ideal.comap_bot_of_injective _ hinj).symm))
    exact ⟨y, hy⟩
  have hφ : φ (genericPoint Y) ⤳ genericPoint X.left := by
    obtain ⟨y, hy⟩ := (Flat.generalizingMap φ).stableUnderGeneralization_range
      (genericPoint_specializes (φ (genericPoint Y))) ⟨_, rfl⟩
    exact hy ▸ (genericPoint_specializes y).map φ.continuous
  have hne : ∀ (V : X.left.Opens) [Nonempty V], Nonempty (φ ⁻¹ᵁ V) := fun V _ =>
    ⟨⟨_, hφ.mem_open V.isOpen (genericPoint_mem_opens V)⟩⟩
  have hne' : ∀ i [Nonempty (M.U i)], Nonempty ((M.pull φ).U fun _ => i) := fun i _ => by
    rw [DvrModel.pull_U]; exact hne _
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  have hb := ffMap_bijective φ hφ
  obtain ⟨r, hr⟩ : ∃ r : M.ι → X.left.functionField, ∀ i [Nonempty ((M.pull φ).U fun _ => i)],
      ffMap φ hφ (r i) = Y.germToFunctionField _ (c.s fun _ => i).val := by
    have : ∀ i, ∃ t : X.left.functionField, ∀ [Nonempty ((M.pull φ).U fun _ => i)],
        ffMap φ hφ t = Y.germToFunctionField _ (c.s fun _ => i).val := fun i => by
      by_cases h : Nonempty ((M.pull φ).U fun _ => i)
      · exact (hb.2 (Y.germToFunctionField _ (c.s fun _ => i).val)).imp fun _ h => h
      · exact ⟨0, @fun h' => (h h').elim⟩
    exact ⟨fun i => (this i).choose, fun i => (this i).choose_spec⟩
  let k : K →+* Γ(Y, ⊤) := (p.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let κ : K →+* X.left.functionField := (RingEquiv.ofBijective (ffMap φ hφ).hom hb).symm.toRingHom.comp
    ((Y.germToFunctionField ⊤).hom.comp k)
  have hκ : ∀ a, ffMap φ hφ (κ a) = Y.germToFunctionField ⊤ (constFn p ⊤ a) := fun a =>
    (RingEquiv.ofBijective (ffMap φ hφ).hom hb).apply_symm_apply _
  have hr0 : ∀ i x, x ∈ M.U i → r i ≠ 0 := fun i x hx h => by
    have : Nonempty (M.U i) := ⟨⟨x, hx⟩⟩
    have := hne' i
    have e := hr i
    rw [h, map_zero] at e
    exact ((Units.isUnit _).map _).ne_zero e.symm
  have hg : ∀ i j (x : X.left) (hi : x ∈ M.U i) (hj : x ∈ M.U j),
      haveI : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      r i = X.left.germToFunctionField (M.U i ⊓ M.U j) (M.g i j).val * r j := by
    intro i j x hi hj
    have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
    have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
    have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
    have := hne' i
    have := hne' j
    have := nonempty_inf_of_isIntegral ((M.pull φ).U fun _ => i) ((M.pull φ).U fun _ => j)
    refine hb.1 ?_
    have e := congrArg (Y.germToFunctionField _) (congrArg Units.val (hc (fun _ => i) fun _ => j))
    rw [Units.val_mul, map_mul, DvrModel.coe_pull_g, ← ffMap_germ φ hφ] at e
    rw [map_mul, hr, hr]
    exact (germToFunctionField_res _ _).symm.trans (e.trans (congrArg _ (germToFunctionField_res _ _)))
  have htr : ∀ i j x t, x ∈ M.U i → x ∈ M.U j → UnitAt x (t * r j) → UnitAt x (t * r i) := by
    intro i j x t hi hj h
    rw [hg i j x hi hj, mul_left_comm]
    exact UnitAt.mul ⟨Units.map (X.left.presheaf.germ (M.U i ⊓ M.U j) x ⟨hi, hj⟩).hom (M.g i j),
      X.left.presheaf.germ_stalkSpecializes_apply _ _ _⟩ h
  have hκR : ∀ b : R, κ (algebraMap R K b) = X.left.presheaf.germ ⊤ (genericPoint X.left) trivial (constFn X.hom ⊤ b) := fun b => hb.1 (by
    rw [hκ, ← app_constFn H.w, ← φ.appLE_eq_app]
    exact (ffMap_germ φ hφ ⊤ ⊤ le_top _).symm)
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_const_mul_unitAt_codimOne_of_factorialBase R K X.left X.hom κ hκR M.ι M.U r (LB.mem_of_cover hM) (fun i x hx => hr0 i x hx) htr (fun x hx => by
    obtain ⟨y, rfl⟩ := lift x hx
    obtain ⟨i, hi⟩ := LB.mem_of_cover hM (φ y)
    have : Nonempty (M.U i) := ⟨⟨_, hi⟩⟩
    have := hne' i
    exact ⟨i, hi, unitAt_of_isUnit φ hφ (Units.isUnit _) ((DvrModel.pull_U M φ _).ge hi) (hr i)⟩)
  have hu : ∀ i, ∃ v : Γ(X.left, M.U i)ˣ, ∀ [Nonempty (M.U i)],
      X.left.germToFunctionField (M.U i) v.val = κ a * r i := fun i => by
    by_cases h : Nonempty (M.U i)
    · obtain ⟨v, hv⟩ := exists_unit_eq (M.U i) (κ a * r i)
        (mul_ne_zero ((map_ne_zero κ).2 a.ne_zero) (hr0 i _ h.some.2)) (ha i)
      exact ⟨v, @fun _ => hv⟩
    · exact ⟨1, @fun h' => (h h').elim⟩
  choose u hu using hu
  refine ⟨a, ⟨u⟩, fun i j => ?_, fun i Z rr z hz => ?_⟩
  · by_cases h : Nonempty (M.U i ⊓ M.U j : X.left.Opens)
    · obtain ⟨⟨x, hi, hj⟩⟩ := h
      have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
      have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
      have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      refine Units.ext (X.left.germToFunctionField_injective (M.U i ⊓ M.U j) ?_)
      show X.left.germToFunctionField _ (X.left.presheaf.map (homOfLE _).op (u i).val) =
        X.left.germToFunctionField _ ((M.g i j).val * X.left.presheaf.map (homOfLE _).op (u j).val)
      rw [map_mul, germToFunctionField_res, germToFunctionField_res, hu, hu, hg i j x hi hj]
      ring
    · exact unit_ext fun x hx => (h ⟨⟨x, hx⟩⟩).elim
  · have hm : rr z ∈ (M.pull φ).U fun _ => i := mem_pull.2 hz
    have h₂ : ((M.pull φ).U fun _ => i) ≤ φ ⁻¹ᵁ M.U i := fun y hy => mem_pull.1 hy
    have : Nonempty ((M.pull φ).U fun _ => i) := ⟨⟨_, hm⟩⟩
    have : Nonempty (M.U i) := ⟨⟨_, hz⟩⟩
    have hW : (φ.appLE (M.U i) _ h₂).hom (u i).val = constFn p _ (a : K) * (c.s fun _ => i).val := by
      refine Y.germToFunctionField_injective _ ((ffMap_germ φ hφ _ _ h₂ _).symm.trans ?_)
      rw [hu, map_mul, map_mul, hκ, hr]
      refine congrArg₂ (· * ·) ?_ rfl
      exact (germToFunctionField_res (le_top : ((M.pull φ).U fun _ => i) ≤ ⊤) _).symm.trans
        (congrArg _ (res_appLE_apply p _ _ _))
    show (gm (rr ≫ φ) z (M.U i) (u i)).val = _
    rw [← gs_unit (rr ≫ φ) z _ hz, ← gs_unit rr z _ hm, ← GlobalTheory.OpenPartUnit.gs_appLE rr φ z _ _ h₂ hm, hW,
      gs_mul rr z _ hm]
    refine congrArg (· * _) ?_
    exact GlobalTheory.OpenPartUnit.gs_appLE rr p z ⊤ _ _ hm _

end GlobalTheory.GlobalVerticalUnit
