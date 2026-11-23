import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase

noncomputable section

namespace GlobalTheory.CubeNoeth

section Cube

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen GlobalTheory.Biadditive
attribute [local instance] Over.cartesianMonoidalCategory

section Fibres

variable {X Y T : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem fibTriv_clopen [IsLocallyNoetherian T] (p : Y ⟶ T)
    (h : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (j : Spec (CommRingCat.of R) ⟶ T), ∃ (W : Scheme.{0}) (q : W ⟶ Y)
      (f : W ⟶ Spec (CommRingCat.of R)), IsPullback q f p j ∧
      IsClosed {x : PrimeSpectrum R | ∃ (F : Type) (_ : Field F) (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W)
        (f' : Z ⟶ Spec (CommRingCat.of F)), RingHom.ker g = x.asIdeal ∧
        IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧
        Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π)} ∧
      ∀ (F : Type) [Field F] (g : R →+* F) (Z : Scheme.{0}) (π : Z ⟶ W) (f' : Z ⟶ Spec (CommRingCat.of F)),
        IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) →
        ∃ r : R, g r ≠ 0 ∧
          Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull (f ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι)) :
    fibTriv L φ ε p ⊆ locTriv L φ ε p ∧ IsClosed (fibTriv L φ ε p) := by
  have chart : ∀ t : T, ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R)
      (j : Spec (CommRingCat.of R) ⟶ T) (_ : IsOpenImmersion j)
      (x : PrimeSpectrum R), j x = t := fun t => by
    obtain ⟨_, ⟨U, hU, rfl⟩, ht, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ t) isOpen_univ
    obtain ⟨x, hx⟩ := hU.range_fromSpec.ge ht
    exact ⟨Γ(T, U), inferInstance, IsLocallyNoetherian.component_noetherian ⟨U, hU⟩, hU.fromSpec,
      hU.isOpenImmersion_fromSpec, x, hx⟩
  constructor
  · intro t ht
    obtain ⟨R, _, _, j, _, x, rfl⟩ := chart t
    obtain ⟨W, q, f, H, -, ho⟩ := h R j
    obtain ⟨F, _, g, Z, π, f', hk, hp, ht⟩ := (mem_fibTriv_iff L φ ε H x).1 ht
    obtain ⟨r, hr, hT⟩ := ho F g Z π f' hp ht
    rw [triv_pull_comp_iff] at hT
    have : IsOpenImmersion q := MorphismProperty.of_isPullback H.flip ‹_›
    refine ⟨j ''ᵁ (PrimeSpectrum.basicOpen r), ⟨x, ?_, rfl⟩, ?_⟩
    · show r ∉ x.asIdeal
      rw [← hk]; exact hr
    · have := hT.comp (IsOpenImmersion.lift ((f ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι ≫ q)
        (p ⁻¹ᵁ (j ''ᵁ (PrimeSpectrum.basicOpen r))).ι (by
          rintro _ ⟨y, rfl⟩
          obtain ⟨x', hx', e⟩ := y.2
          obtain ⟨w, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback H y.1 x' e.symm
          exact ⟨⟨w, (congrArg (· ∈ PrimeSpectrum.basicOpen r) h₂).mpr hx'⟩, h₁⟩))
      exact (congrArg (TrivAt L φ ε) (IsOpenImmersion.lift_fac _ _ _)).mp this
  · refine ⟨isOpen_iff_forall_mem_open.2 fun t ht => ?_⟩
    obtain ⟨R, _, _, j, _, x, rfl⟩ := chart t
    obtain ⟨W, q, f, H, hc, -⟩ := h R j
    refine ⟨j '' _, ?_, j.isOpenEmbedding.isOpenMap _ hc.isOpen_compl, x,
      fun hx => ht ((mem_fibTriv_iff L φ ε H x).2 hx), rfl⟩
    rintro _ ⟨y, hy, rfl⟩ hy'
    exact hy ((mem_fibTriv_iff L φ ε H y).1 hy')

end Fibres

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A]

theorem triv_of_faces (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    (φ : K → ((G3 A).left ⟶ X)) (ε : K → ℤ)
    (face : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S),
      r ≫ (x3 A i).left = b ≫ η[A].left → TrivAt M φ ε r)
    (formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (b : Z ⟶ S),
      r ≫ (x3 A 0).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
        ∏ i, k (r ≫ φ i) ^ ε i = 1) :
    Triv (LB.LinComb M φ ε) := by
  have := hA.geomConnected
  have := hA.smooth
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have H := CubeNoeth.fibTriv_clopen M φ ε (x3 A 2).left (fun R _ _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ φ k) ε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf : ∀ N : LB (B ⊗ B).left, N.IsLB → Nonempty (Perf (B ⊗ B).hom N) := fun N hN' =>
      ProperFinite.nonempty_perf_of_isProper (R := R) (B ⊗ B).hom hN'
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' => CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine face _ 1 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine face _ 0 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M φ ε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M φ ε (x3 A 2).left := fun t => by
    have hr : Set.range (S.fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := S.fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = S.fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec (S.residueField (A.hom t)) ⟶ S => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨S.residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      face _ 2 (pullback.snd _ g ≫ S.fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm)⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM φ ε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => formal _ (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

variable {B : Over S} (F : A ⊗ A ⟶ B)

theorem triv_add (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    {M : LB B.left} (hM : M.IsLB)
    (h₁ : Triv (M.pull (lift (1 : A ⟶ A) (𝟙 A) ≫ F).left))
    (h₂ : Triv (M.pull (lift (𝟙 A) (1 : A ⟶ A) ≫ F).left)) {T : Over S} (x x' y : T ⟶ A) :
    Triv (LB.LinComb M (K := Fin 3)
      ![(lift (x * x') y ≫ F).left, (lift x y ≫ F).left, (lift x' y ≫ F).left] ![1, -1, -1]) := by
  have a₁ : ∀ {T : Over S} (y : T ⟶ A), Triv (M.pull (lift 1 y ≫ F).left) := fun y => by
    have := triv_pull_comp h₁ y.left
    rwa [← Over.comp_left, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have a₂ : ∀ {T : Over S} (y : T ⟶ A), Triv (M.pull (lift y 1 ≫ F).left) := fun y => by
    have := triv_pull_comp h₂ y.left
    rwa [← Over.comp_left, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S), i = 0 ∨ i = 1 →
      r ≫ (x3 A i).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ B.left) → U),
        ∏ i, k (r ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
    intro Z r i b hi h U _ k
    obtain ⟨w, hw, h'⟩ := exists_over r i b h
    have := prod_fourPts F (x := w ≫ x3 A 0) (x' := w ≫ x3 A 1) (w ≫ x3 A 2)
      (hi.imp (fun e => e ▸ h') (fun e => e ▸ h')) U k
    simp only [← comp_fourPts, hw] at this
    exact this
  have cube := CubeNoeth.triv_of_faces hG hA hM (fourPts F (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, 1]
    (fun r i b h => by
      by_cases hi : i = 0 ∨ i = 1
      · exact trivAt_of_formal hM r (formal r i b hi h)
      · obtain rfl : i = 2 := by omega
        obtain ⟨w, hw, h'⟩ := exists_over r 2 b h
        have e : (fun k => r ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) k) =
            fourPts F (w ≫ x3 A 0) (w ≫ x3 A 1) 1 := funext fun k => by
          rw [← h', ← comp_fourPts, hw]
        unfold TrivAt
        rw [e]
        refine triv_of_formal hM (triv_mul (triv_mul (a₂ (w ≫ x3 A 0 * w ≫ x3 A 1)) (triv_inv (a₂ (w ≫ x3 A 0))))
          (triv_mul (triv_inv (a₂ (w ≫ x3 A 1))) (a₂ (T := Over.mk (r ≫ (G3 A).hom)) 1))) fun U _ k => ?_
        simp [Fin.prod_univ_four, fourPts, -Over.comp_left, Fintype.prod_sum_type, _root_.mul_assoc])
    (fun r b h => formal r 0 b (Or.inl rfl) h)
  have c₀ : TrivAt M (fourPts F (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, 1] (lift x (lift x' y)).left := by
    obtain ⟨t, ht⟩ := cube
    exact ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  have e : (fun k => (lift x (lift x' y)).left ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) k) =
      fourPts F x x' y := funext fun k => by
    rw [comp_fourPts]
    simp [x3]
  unfold TrivAt at c₀
  rw [e] at c₀
  refine triv_of_formal hM (triv_mul c₀ (triv_inv (a₁ y))) fun U _ k => ?_
  simp [Fin.prod_univ_four, Fin.prod_univ_three, fourPts, -Over.comp_left, Fintype.prod_sum_type]

end Cube

section Additive

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {A B : Over S} [GrpObj A] [GrpObj B]

theorem isAdditive_of_triv_axes (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (h0l : Triv (ev P (1 : B ⟶ A) (𝟙 B))) (h0r : Triv (ev P (𝟙 A) (1 : A ⟶ B))) : IsAdditive P := by
  have hG := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  let F : (A ⊗ B) ⊗ (A ⊗ B) ⟶ A ⊗ B :=
    lift (fst (A ⊗ B) (A ⊗ B) ≫ fst A B) (snd (A ⊗ B) (A ⊗ B) ≫ snd A B)
  have h₁ : Triv (P.pull (lift (1 : A ⊗ B ⟶ A ⊗ B) (𝟙 _) ≫ F).left) := by
    have e : lift (1 : A ⊗ B ⟶ A ⊗ B) (𝟙 _) ≫ F = snd A B ≫ lift (1 : B ⟶ A) (𝟙 B) := by
      ext <;> simp [F]
    rw [e, Over.comp_left]
    exact GlobalTheory.Biadditive.triv_pull_comp h0l _
  have h₂ : Triv (P.pull (lift (𝟙 _) (1 : A ⊗ B ⟶ A ⊗ B) ≫ F).left) := by
    have e : lift (𝟙 _) (1 : A ⊗ B ⟶ A ⊗ B) ≫ F = fst A B ≫ lift (𝟙 A) (1 : A ⟶ B) := by
      ext <;> simp [F]
    rw [e, Over.comp_left]
    exact GlobalTheory.Biadditive.triv_pull_comp h0r _
  refine (isAdditive_iff hP).2 fun Y a a' t => ?_
  have T := CubeNoeth.triv_add F GlobalTheory.laws_without_cohomology.1 hG hP h₁ h₂
    (lift a (1 : Y ⟶ B)) (lift a' 1) (lift (1 : Y ⟶ A) t)
  have e₀ : lift (lift a (1 : Y ⟶ B) * lift a' 1) (lift (1 : Y ⟶ A) t) ≫ F = lift (a * a') t := by
    ext <;> simp [F, MonObj.mul_comp]
  have e₁ : lift (lift a (1 : Y ⟶ B)) (lift (1 : Y ⟶ A) t) ≫ F = lift a t := by
    ext <;> simp [F]
  have e₂ : lift (lift a' (1 : Y ⟶ B)) (lift (1 : Y ⟶ A) t) ≫ F = lift a' t := by
    ext <;> simp [F]
  rw [e₀, e₁, e₂] at T
  have z := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 T
  rw [cls_linComb hP, Fin.sum_univ_three] at z
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
  simp only [evc]
  rw [← sub_eq_zero, ← z]
  abel

theorem isAdditive_swap_of_triv_axes (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (h0l : Triv (ev P (1 : B ⟶ A) (𝟙 B))) (h0r : Triv (ev P (𝟙 A) (1 : A ⟶ B))) : IsAdditive (swap P) := by
  have hG := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have hs : (swap P).IsLB := pull_isLB hP _
  let F : (A ⊗ B) ⊗ (A ⊗ B) ⟶ A ⊗ B :=
    lift (snd (A ⊗ B) (A ⊗ B) ≫ fst A B) (fst (A ⊗ B) (A ⊗ B) ≫ snd A B)
  have h₁ : Triv (P.pull (lift (1 : A ⊗ B ⟶ A ⊗ B) (𝟙 _) ≫ F).left) := by
    have e : lift (1 : A ⊗ B ⟶ A ⊗ B) (𝟙 _) ≫ F = fst A B ≫ lift (𝟙 A) (1 : A ⟶ B) := by
      ext <;> simp [F]
    rw [e, Over.comp_left]
    exact GlobalTheory.Biadditive.triv_pull_comp h0r _
  have h₂ : Triv (P.pull (lift (𝟙 _) (1 : A ⊗ B ⟶ A ⊗ B) ≫ F).left) := by
    have e : lift (𝟙 _) (1 : A ⊗ B ⟶ A ⊗ B) ≫ F = snd A B ≫ lift (1 : B ⟶ A) (𝟙 B) := by
      ext <;> simp [F]
    rw [e, Over.comp_left]
    exact GlobalTheory.Biadditive.triv_pull_comp h0l _
  refine (isAdditive_iff hs).2 fun Y b b' a => ?_
  rw [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]
  have T := CubeNoeth.triv_add F GlobalTheory.laws_without_cohomology.1 hG hP h₁ h₂
    (lift (1 : Y ⟶ A) b) (lift 1 b') (lift a (1 : Y ⟶ B))
  have e₀ : lift (lift (1 : Y ⟶ A) b * lift 1 b') (lift a (1 : Y ⟶ B)) ≫ F = lift a (b * b') := by
    ext <;> simp [F, MonObj.mul_comp]
  have e₁ : lift (lift (1 : Y ⟶ A) b) (lift a (1 : Y ⟶ B)) ≫ F = lift a b := by
    ext <;> simp [F]
  have e₂ : lift (lift (1 : Y ⟶ A) b') (lift a (1 : Y ⟶ B)) ≫ F = lift a b' := by
    ext <;> simp [F]
  rw [e₀, e₁, e₂] at T
  have z := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 T
  rw [cls_linComb hP, Fin.sum_univ_three] at z
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at z
  simp only [evc]
  rw [← sub_eq_zero, ← z]
  abel

end Additive

end GlobalTheory.CubeNoeth
