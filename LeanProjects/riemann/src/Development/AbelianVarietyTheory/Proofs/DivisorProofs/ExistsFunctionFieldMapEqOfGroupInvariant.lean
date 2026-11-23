import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep

theorem functionFieldMap_germToFunctionField {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (f : X ⟶ X') [IsDominant f] (V : X'.Opens) (U : X.Opens) (e : U ≤ f ⁻¹ᵁ V) [Nonempty U]
    [Nonempty V] (s : Γ(X', V)) :
    functionFieldMap f (X'.germToFunctionField V s) = X.germToFunctionField U (f.appLE V U e s) := by
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hfx : f (genericPoint X) ∈ V := e hx
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X') hfx, functionFieldMap_algebraMap,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx]
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply f V _ hfx s).trans
    (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE e) _ hx (f.app V s)).symm

theorem exists_functionFieldMap_eq_of_invariant (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W]
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q]
    (h : IsAffineQuotient ρ q) (u : X.functionFieldˣ) (hu : ∀ γ, fnAct ρ γ u = u) :
    ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  classical
  have := Fintype.ofFinite Γ
  have := h.isAffineHom
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  haveI : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := (show IsAffineOpen V from hV).preimage q
  obtain ⟨x, hx⟩ := q.denseRange.exists_mem_open V.isOpen ⟨_, hyV⟩
  haveI : Nonempty (q ⁻¹ᵁ V) := ⟨⟨x, hx⟩⟩
  have hst := h.preimage_le V
  haveI (γ : Γ) : IsIso (ρ γ).hom := Iso.isIso_hom (ρ γ)
  haveI := functionField_isFractionRing_of_isAffineOpen X _ hU
  let σ : Γ → Γ(X, q ⁻¹ᵁ V) →+* Γ(X, q ⁻¹ᵁ V) := fun γ ↦ ((ρ γ).hom.appLE _ _ (hst γ)).hom
  have hσ (γ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) :
      functionFieldMap (ρ γ).hom (algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField s) =
        algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField (σ γ s) :=
    functionFieldMap_germToFunctionField _ _ _ (hst γ) s
  have hσ1 (s : Γ(X, q ⁻¹ᵁ V)) : σ 1 s = s := by
    have e1 : (ρ 1).hom = 𝟙 X := by rw [map_one]; rfl
    change (ρ 1).hom.appLE _ _ (hst 1) s = s
    simp only [e1]
    exact congr($(X.presheaf.map_id (Opposite.op (q ⁻¹ᵁ V))) s)
  have hσmul (γ δ : Γ) (s : Γ(X, q ⁻¹ᵁ V)) : σ δ (σ γ s) = σ (γ * δ) s := by
    have e2 : (ρ (γ * δ)).hom = (ρ δ).hom ≫ (ρ γ).hom := by rw [map_mul]; rfl
    change (ρ δ).hom.appLE _ _ (hst δ) ((ρ γ).hom.appLE _ _ (hst γ) s) =
      (ρ (γ * δ)).hom.appLE _ _ (hst (γ * δ)) s
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, e2]
  set e := algebraMap Γ(X, q ⁻¹ᵁ V) X.functionField with he_def
  have einj : Function.Injective e := IsFractionRing.injective _ _
  have hfu (δ : Γ) : functionFieldMap (ρ δ).hom (u : X.functionField) = u :=
    congrArg Units.val (hu δ)
  obtain ⟨a, t, ht, hat⟩ := IsFractionRing.div_surjective (A := Γ(X, q ⁻¹ᵁ V)) (u : X.functionField)
  have ht0 : e t ≠ 0 := by
    rw [Ne, ← map_zero e]
    exact fun h0 ↦ nonZeroDivisors.ne_zero ht (einj h0)
  let N := ∏ γ, σ γ t
  have hN (δ : Γ) : σ δ N = N := by
    simp only [N, map_prod, hσmul]
    exact Fintype.prod_equiv (Equiv.mulRight δ) _ _ (fun _ ↦ rfl)
  have hNe : e N ≠ 0 := by
    simp only [N, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun γ _ ↦ ?_
    rw [← hσ]
    exact (map_ne_zero _).mpr ht0
  let c := a * ∏ γ ∈ Finset.univ.erase 1, σ γ t
  have hc : e c = u * e N := by
    have hsplit : N = t * ∏ γ ∈ Finset.univ.erase 1, σ γ t := by
      simp only [N]
      rw [← Finset.mul_prod_erase Finset.univ (fun γ ↦ σ γ t) (Finset.mem_univ 1), hσ1]
    rw [← he_def] at hat
    rw [hsplit]
    simp only [c, map_mul]
    rw [← hat]
    field_simp
  have hcinv (δ : Γ) : σ δ c = c := by
    apply einj
    rw [← hσ, hc, map_mul, hfu, hσ, hN]
  obtain ⟨bc, hbc⟩ := h.mem_range_app V c fun δ ↦ ⟨hst δ, hcinv δ⟩
  obtain ⟨bN, hbN⟩ := h.mem_range_app V N fun δ ↦ ⟨hst δ, hN δ⟩
  have hq (b : Γ(W, V)) : functionFieldMap q (W.germToFunctionField V b) = e (q.app V b) := by
    rw [Scheme.Hom.app_eq_appLE]
    exact functionFieldMap_germToFunctionField q V (q ⁻¹ᵁ V) le_rfl b
  have hbN0 : W.germToFunctionField V bN ≠ 0 := by
    intro h0
    apply hNe
    rw [← hbN, ← hq, h0, map_zero]
  have hbc0 : W.germToFunctionField V bc ≠ 0 := by
    intro h0
    apply mul_ne_zero u.ne_zero hNe
    rw [← hc, ← hbc, ← hq, h0, map_zero]
  refine ⟨Units.mk0 (W.germToFunctionField V bc / W.germToFunctionField V bN)
    (div_ne_zero hbc0 hbN0), Units.ext ?_⟩
  simp only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_div₀, hq, hbc, hbN, hc]
  field_simp

end GlobalTheory.OrbitSep
