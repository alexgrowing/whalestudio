import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Semi MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolAdjoint

section Chern

open GlobalTheory.Cris.ChernExists

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X Y : Scheme.{0}} {s : X ⟶ Sp R}
  {s' : Y ⟶ Sp R}

def expU (T : Thick κ s) : T.J →+ Additive T.Bˣ :=
  AddMonoidHom.mk' (fun a ↦ Additive.ofMul ⟨dpExp T.δ a.1, dpExp T.δ (-a.1),
      by rw [← exp_add T a.2 (T.J.neg_mem a.2), add_neg_cancel, dpExp_zero],
      by rw [← exp_add T (T.J.neg_mem a.2) a.2, neg_add_cancel, dpExp_zero]⟩)
    fun a b ↦ congrArg Additive.ofMul (Units.ext (exp_add T a.2 b.2))

theorem exp_sum (T : Thick κ s) {K : Type} [Fintype K] (ε : K → ℤ) (a : K → T.B) (ha : ∀ k, a k ∈ T.J)
    (p q : K → T.Bˣ) (h : ∀ k, dpExp T.δ (a k) * (p k).val = (q k).val) :
    dpExp T.δ (∑ k, ε k • a k) * (∏ k, p k ^ ε k).val = (∏ k, q k ^ ε k).val := by
  have e1 : ∀ k, q k = Additive.toMul (expU T ⟨a k, ha k⟩) * p k := fun k ↦ Units.ext (h k).symm
  have e2 : dpExp T.δ (∑ k, ε k • a k) =
      (Additive.toMul (expU T (∑ k, ε k • (⟨a k, ha k⟩ : T.J)))).val := by
    change _ = dpExp T.δ (Subtype.val _)
    congr 1
    simp
  rw [e2, map_sum, toMul_sum, ← Units.val_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [e1, mul_zpow, map_zsmul, toMul_zsmul]

theorem isChern_linComb {L : LB X} {z : Cris.H2 κ s} (hz : IsChern κ s L z) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : ∀ k, IsMor κ s κ s' (RingHom.id R) (φ k)) :
    IsChern κ s' (LB.LinComb L φ ε) (∑ k, ε k • (m k).pull2 z) := by
  obtain ⟨i, hi, u, ℓ, h1, h2, h3⟩ := hz
  let G : K → (IsSmall κ s' (LB.LinComb L φ ε).U).FullSubcategory ⥤ (IsSmall κ s L.U).FullSubcategory :=
    fun k ↦ ObjectProperty.lift _ ((IsSmall κ s' (LB.LinComb L φ ε).U).ι ⋙ (m k).functor) fun T ↦
      T.property.elim fun j hj ↦ ⟨j k, fun p _ ↦ LB.wchart_le L φ j k (hj (Set.mem_univ p))⟩
  let n : K → CoefMap (RingHom.id R) ((IsSmall κ s L.U).ι ⋙ O κ s)
      ((IsSmall κ s' (LB.LinComb L φ ε).U).ι ⋙ O κ s') := fun k ↦
    { G := G k
      α := fun T ↦ RingHom.id T.obj.B
      naturality := fun _ _ ↦ rfl
      smul := fun T r b ↦ (m k).coef.smul T.obj r b }
  have hu : ∀ k T T' (ψ : T ⟶ T'), IsUnit (M := T'.obj.B) (u _ _ ((G k).map ψ)) := fun k T T' ψ ↦
    isUnit_of_π T'.obj ((h1 _ _ ((G k).map ψ)).symm ▸ (Units.isUnit _).map _)
  choose U hU using hu
  have hi' : ∀ T : (IsSmall κ s' (LB.LinComb L φ ε).U).FullSubcategory,
      ⊤ ≤ T.obj.x ⁻¹ᵁ (LB.LinComb L φ ε).U (fun k ↦ i ((G k).obj T)) :=
    fun T p _ ↦ Set.mem_iInter.2 fun k ↦ hi ((G k).obj T) (Set.mem_univ p)
  refine ⟨fun T k ↦ i ((G k).obj T), hi', fun T T' ψ ↦ (∏ k, U k T T' ψ ^ ε k).val,
    ∑ k, ε k • (n k).pullbackTwoCocycle ℓ, fun T T' ψ ↦ ?_, fun T T' T'' ψ χ ↦ ?_, ?_⟩
  · refine congrArg Units.val (show Units.map (T'.obj.π : T'.obj.B →* T'.obj.B₀) (∏ k, U k T T' ψ ^ ε k) =
      evU T'.obj.x ((LB.LinComb L φ ε).U (fun k ↦ i ((G k).obj T')) ⊓ (LB.LinComb L φ ε).U (fun k ↦ i ((G k).obj T)))
        (le_inf (hi' T') (ψ.hom.le_preimage (hi' T))) ((LB.LinComb L φ ε).g _ _) from ?_)
    refine (map_prod _ _ _).trans (Eq.trans (Finset.prod_congr rfl fun k _ ↦ ?_) (map_prod _ _ _).symm)
    refine (map_zpow _ _ _).trans (Eq.trans (congrArg (· ^ ε k) ?_) (map_zpow _ _ _).symm)
    refine Units.ext ?_
    refine ((congrArg T'.obj.π (hU k T T' ψ)).trans (h1 _ _ ((G k).map ψ))).trans ?_
    exact evalAt_pull (φ k) T'.obj.x _ _ _ _
  · have e : ((∑ k, ε k • (n k).pullbackTwoCocycle ℓ).1 T T' T'' ψ χ : T''.obj.B) =
        ∑ k, ε k • (show T''.obj.B from ℓ.1 _ _ _ ((G k).map ψ) ((G k).map χ)) := by
      rw [Submodule.coe_sum]
      simp only [Finset.sum_apply]
      rfl
    have hm : ∀ k, (show T''.obj.B from ℓ.1 _ _ _ ((G k).map ψ) ((G k).map χ)) ∈ T''.obj.J :=
      fun k ↦ (h2 _ _ _ ((G k).map ψ) ((G k).map χ)).1
    rw [e]
    refine ⟨Submodule.sum_mem _ fun k _ ↦ zsmul_mem (hm k) _, ?_⟩
    refine (exp_sum T''.obj ε _ hm _
      (fun k ↦ Units.map (χ.hom.φ : T'.obj.B →* T''.obj.B) (U k T T' ψ) * U k T' T'' χ) fun k ↦ ?_).trans ?_
    · rw [hU, Units.val_mul, hU, Units.coe_map, hU]
      exact (h2 _ _ _ ((G k).map ψ) ((G k).map χ)).2
    · refine Eq.trans ?_ (Units.val_mul (Units.map (χ.hom.φ : T'.obj.B →* T''.obj.B) (∏ k, U k T T' ψ ^ ε k)) _)
      rw [map_prod, ← Finset.prod_mul_distrib]
      simp only [mul_zpow, map_zpow]
  · rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_zsmul, map_zsmul, ← (n k).pullCohomologyTwo_class, ← h3]
    obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective _ z
    rfl

end Chern

section Cube

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem pullOver_one {T : Over S} (c : prim κ t A) : pullOver κ t (1 : T ⟶ A) c.1 = 0 := by
  have h := c.2 T 1 1
  rw [_root_.mul_one] at h
  exact left_eq_add.1 h

theorem pullOver_psum {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) (J : Finset (Fin n)) (c : prim κ t A) :
    pullOver κ t (psum A x J) c.1 = ∑ i ∈ J, pullOver κ t (x i) c.1 := by
  have key : ∀ l : List (Fin n), pullOver κ t (l.foldr (fun k acc ↦ padd A (x k) acc) (pzero A T)) c.1 =
      (l.map fun i ↦ pullOver κ t (x i) c.1).sum := fun l ↦ by
    induction l with
    | nil => exact pullOver_one c
    | cons k l ih => exact (c.2 T (x k) _).trans (by rw [ih, List.map_cons, List.sum_cons])
  rw [psum, key, ← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

theorem isMor_psum {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ A)) (J : ULift.{0} (Finset (Fin n))) :
    IsMor κ (A.hom ≫ t) κ (T.hom ≫ t) (RingHom.id R) (psum A x J.down).left :=
  IsMor.of_over κ (by rw [← Category.assoc, Over.w])

theorem isChern_cube {L : LB A.left} {n : ℕ} {a b : Fin n → prim κ t A}
    (h : IsChern κ (A.hom ≫ t) L (∑ k, cup _ (a k).1 (b k).1)) {T : Over S} (u v : T ⟶ A) :
    IsChern κ (T.hom ≫ t) (cubeLB A ![u, v] L)
      (∑ k, (cup _ (pullOver κ t u (a k).1) (pullOver κ t v (b k).1) +
        cup _ (pullOver κ t v (a k).1) (pullOver κ t u (b k).1))) := by
  have H := isChern_linComb h _ (fun J : ULift.{0} (Finset (Fin 2)) ↦ (-1 : ℤ) ^ (2 - J.down.card))
    (isMor_psum ![u, v])
  have e : ∀ J : ULift.{0} (Finset (Fin 2)), (isMor_psum ![u, v] J).pull2 (∑ k, cup _ (a k).1 (b k).1) =
      ∑ k, cup _ (∑ i ∈ J.down, pullOver κ t (![u, v] i) (a k).1)
        (∑ i ∈ J.down, pullOver κ t (![u, v] i) (b k).1) := fun J ↦ by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [IsMor.pullCohomologyTwo_cup, ← pullOver_psum, ← pullOver_psum]
    rfl
  simp only [e, Finset.smul_sum] at H
  rw [Finset.sum_comm] at H
  refine (congrArg (IsChern κ (T.hom ≫ t) (cubeLB A ![u, v] L)) ?_).mpr H
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Equiv.ulift.symm.sum_comp,
    show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp only [Equiv.ulift_symm_down, Finset.sum_empty, Finset.sum_singleton,
    Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide), Finset.card_pair (show (0 : Fin 2) ≠ 1 by decide),
    Finset.card_singleton, map_zero, smul_zero, map_add, LinearMap.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num
  abel

end Cube

theorem lbIso_cube {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A]
    [IsCommMonObj A] {f : S' ⟶ S} {π : A.left ⟶ G.left} (h : IsGrpPullback A G f π) (L : LB G.left)
    {α β : G ⟶ G} {α' β' : A ⟶ A} (hα : α'.left ≫ π = π ≫ α.left) (hβ : β'.left ≫ π = π ≫ β.left)
    (H : LBIso (cubeLB G ![fst G G ≫ α, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ β] L)) :
    LBIso (cubeLB A ![fst A A ≫ α', snd A A] (L.pull π)) (cubeLB A ![fst A A, snd A A ≫ β'] (L.pull π)) := by
  let U : Over.mk ((A ⊗ A).hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst A A)) (pushPt h.1.w (snd A A))
  have e : ∀ {ρ : G ⟶ G} {ρ' : A ⟶ A}, ρ'.left ≫ π = π ≫ ρ.left → ∀ p : A ⊗ A ⟶ A,
      pushPt h.1.w (p ≫ ρ') = pushPt h.1.w p ≫ ρ := fun hρ p ↦ Over.OverMorphism.ext (by
    change (p.left ≫ _) ≫ π = (p.left ≫ π) ≫ _
    rw [Category.assoc, Category.assoc, hρ])
  refine LBIso.chartPull (chartPullLinComb L π _ _ _ U.left fun J ↦ psum_push h _ _ U (fun i ↦ ?_) _)
    (chartPullLinComb L π _ _ _ U.left fun J ↦ psum_push h _ _ U (fun i ↦ ?_) _) H
  · fin_cases i
    · exact (e hα _).trans (lift_fst_assoc _ _ _).symm
    · exact (lift_snd _ _).symm
  · fin_cases i
    · exact (lift_fst _ _).symm
    · exact (e hβ _).trans (lift_snd_assoc _ _ _).symm

theorem exists_wedge {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (X Y : M →ₗ[R] R) :
    ∃ Λ : ⋀[R]^2 M →ₗ[R] R, ∀ c d, Λ (exteriorPower.ιMulti R 2 ![c, d]) = X c * Y d - X d * Y c := by
  refine ⟨exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating.compLinearMap (LinearMap.pi ![X, Y])), fun c d ↦ ?_⟩
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change Matrix.det (Matrix.of fun i j ↦ (![X, Y] j) (![c, d] i)) = _
  rw [Matrix.det_fin_two]
  simp [mul_comm]

theorem exists_wedge_functional (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)}
    [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (X Y : FirstDeRham (A.hom ≫ 𝟙 _) →ₗ[R] R) :
    ∃ Λ : SecondDeRham (A.hom ≫ 𝟙 _) →ₗ[R] R, ∀ c d, Λ (cup _ c d) = X c * Y d - X d * Y c := by
  obtain ⟨-, -, -, -, e, he⟩ := P R A g hA hg
  obtain ⟨Λ, hΛ⟩ := exists_wedge X Y
  exact ⟨Λ ∘ₗ e.symm.toLinearMap, fun c d ↦ by
    rw [← he, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply, hΛ]⟩

theorem isAbelianScheme_sq {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) :
    IsAbelianScheme (A ⊗ A) := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    exact GeometricallyConnected.comp _ _

theorem adjoint_of_lbIso (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)}
    [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left}
    (hL : L.IsLB) {ψ : LinearMap.BilinForm R (HdR A)} (hψ : IsPolForm (dp0 R) (𝟙 _) A L ψ)
    (α β : A ⟶ A) [IsMonHom α] [IsMonHom β]
    (H : LBIso (cubeLB A ![fst A A ≫ α, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ β] L)) (x y : HdR A) :
    ψ (push (dp0 R) (𝟙 _) α x) y = ψ x (push (dp0 R) (𝟙 _) β y) := by
  obtain ⟨n, a, b, hc, rfl⟩ := hψ
  have h0 := (P R A g hA hg).1
  have hg2 : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom A.hom).flip hg
    rw [Over.tensorObj_hom]
    exact smoothOfRelativeDimension_comp g g _ _
  let E : primDR A ≃ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) := LinearEquiv.ofTop _ h0
  obtain ⟨Λ, hΛ⟩ := exists_wedge_functional P (isAbelianScheme_sq hA) hg2
    (x ∘ₗ E.symm.toLinearMap ∘ₗ pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1))
    (y ∘ₗ E.symm.toLinearMap ∘ₗ pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)))
  have C := isChern_existsUnique_and_iso R _ (dp0 R) _ ((A ⊗ A).hom ≫ 𝟙 _)
  have l₁ : (cubeLB A ![fst A A ≫ α, snd A A] L).IsLB := DVR.linComb_isLB _ hL _ _
  have l₂ : (cubeLB A ![fst A A, snd A A ≫ β] L).IsLB := DVR.linComb_isLB _ hL _ _
  have e := congrArg Λ ((C.1 _ l₂).unique (C.2 _ _ l₁ l₂ H _ (isChern_cube hc _ _)) (isChern_cube hc _ _))
  have v : ∀ (ρ : A ⟶ A) [IsMonHom ρ] (c : primDR A),
      E.symm (pullOver (dp0 R) (𝟙 _) ρ c.1) = primPull (dp0 R) (𝟙 _) ρ c := fun _ _ _ ↦ Subtype.ext rfl
  have v₁ : ∀ c : primDR A, primPull (dp0 R) (𝟙 _) (𝟙 A) c = c := fun c ↦
    Subtype.ext (IsMor.pullCohomologyOne_id _ _)
  simp only [map_sum, map_add, hΛ, LinearMap.comp_apply, LinearEquiv.coe_coe, pullOver_pullOver,
    lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd, Category.id_comp, MonObj.one_comp, pullOver_one,
    map_zero, v, v₁, mul_zero, zero_mul, sub_zero, zero_sub] at e
  simp only [wedgeForm_apply, push_apply, sub_eq_add_neg]
  exact e

theorem polForm_adjoint : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∀ (a : OAct (𝓞 E) A), (∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) → ∀ {ψ : LinearMap.BilinForm K (HdR A)}, IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → IsAdjointFor a (fun z => H.bar z) ψ := by
  intro P E _ _ _ H Dw l Xo K _ x A _ π hπ a ha ψ hψ z u v
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have := hA.comm
  have := a.hom
  exact adjoint_of_lbIso P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hψ (a.act z) (a.act (H.bar z))
    (lbIso_cube hπ _ (ha z) (ha (H.bar z)) (Xo.univ.t.adj z)) u v

end GlobalTheory.PolAdjoint
