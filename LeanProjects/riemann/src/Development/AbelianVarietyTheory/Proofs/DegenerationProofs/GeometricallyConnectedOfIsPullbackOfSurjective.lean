import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitOnProductEqOne

section

open TensorProduct

namespace GlobalTheory.UnitRigidity

theorem exists_normalised {K L B ι : Type*} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    (b : Module.Basis ι K B) (O : ValuationSubring L) [Algebra K O] [IsScalarTower K O L]
    (w : L ⊗[K] B) (hw : w ≠ 0) :
    ∃ (a : L) (w' : O ⊗[K] B), a ≠ 0 ∧
      w = a • Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O L) (AlgHom.id K B) w' ∧
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
        (AlgHom.id K B) w' ≠ 0 ∧
      ∀ i, ∃ c : O, (Algebra.TensorProduct.basis L b).repr w i = a * c := by
  classical
  set c := (Algebra.TensorProduct.basis L b).repr w with hc
  have hne : c.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    simpa [hc] using hw
  obtain ⟨i₀, hi₀, hmax⟩ := c.support.exists_max_image (fun i => O.valuation (c i)) hne
  have h0 : c i₀ ≠ 0 := Finsupp.mem_support_iff.mp hi₀
  have hmem : ∀ i, c i / c i₀ ∈ O := by
    intro i
    rw [← O.valuation_le_one_iff, map_div₀, div_le_one₀ (by simpa [pos_iff_ne_zero] using h0)]
    by_cases hi : i ∈ c.support
    · exact hmax i hi
    · simp [Finsupp.notMem_support_iff.mp hi]
  refine ⟨c i₀, ∑ i ∈ c.support, (⟨_, hmem i⟩ : O) ⊗ₜ b i, h0, ?_, ?_, fun i => ⟨⟨_, hmem i⟩, ?_⟩⟩
  · rw [map_sum, Finset.smul_sum]
    conv_lhs => rw [← (Algebra.TensorProduct.basis L b).linearCombination_repr w, ← hc,
      Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', mul_div_cancel₀ _ h0]
  · intro h
    have := congrArg (fun z => (Algebra.TensorProduct.basis (IsLocalRing.ResidueField O) b).repr z i₀) h
    simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.coe_finset_sum, Finset.sum_apply, map_zero,
      Module.Basis.repr_self, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i₀] at this
    · have e : (⟨_, hmem i₀⟩ : O) = 1 := Subtype.ext (div_self h0)
      rw [e] at this
      simp at this
    · intro i _ hi
      simp [hi]
    · exact fun h => (h hi₀).elim
  · simp [mul_div_cancel₀ _ h0]

theorem coeff_mem {K L B ι : Type*} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]
    (b : Module.Basis ι K B) (O : ValuationSubring L) [Algebra K O] [IsScalarTower K O L]
    [NoZeroDivisors (IsLocalRing.ResidueField O ⊗[K] B)] (ψ : B →ₐ[K] K)
    (u : L ⊗[K] B) (hu : IsUnit u)
    (h1 : Algebra.TensorProduct.lift (AlgHom.id K L) ((Algebra.ofId K L).comp ψ)
      (fun _ _ => Commute.all _ _) u = 1) (i : ι) :
    (Algebra.TensorProduct.basis L b).repr u i ∈ O := by
  have : Nontrivial B := ψ.toRingHom.domain_nontrivial
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  obtain ⟨a, u', ha, eu, hu', hcu⟩ := exists_normalised b O u hu.ne_zero
  obtain ⟨c, w', hc, ew, hw', -⟩ := exists_normalised b O w (right_ne_zero_of_mul_eq_one hw)
  set j := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O L) (AlgHom.id K B) with hj
  set r := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O))
    (AlgHom.id K B) with hr
  set e := Algebra.TensorProduct.lift (AlgHom.id K L) ((Algebra.ofId K L).comp ψ)
      (fun _ _ => Commute.all _ _) with he
  set e' := Algebra.TensorProduct.lift (AlgHom.id K O) ((Algebra.ofId K O).comp ψ)
      (fun _ _ => Commute.all _ _) with he'
  have hjinj : Function.Injective j :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := B)
      (IsScalarTower.toAlgHom K O L).toLinearMap Subtype.val_injective
  have hej : ∀ z, e (j z) = (e' z : L) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y =>
      simp [he, he', hj, Algebra.ofId_apply]
      left
      exact IsScalarTower.algebraMap_apply K O L _
    | add x y hx hy => simp [hx, hy]
  have hes : ∀ (x : L) z, e (x • z) = x * e z := by
    intro x z
    rw [Algebra.smul_def, map_mul]
    simp [he]
  have hprod : (a * c) • j (u' * w') = 1 := by
    rw [← hw, eu, ew, map_mul, smul_mul_smul_comm]
  have hac : a * c ≠ 0 := mul_ne_zero ha hc
  have hunit : IsUnit (e' u') := by
    refine isUnit_of_mul_isUnit_left (y := e' w') ?_
    have h2 : a * c * ((e' u' * e' w' : O) : L) = 1 := by
      rw [← map_mul, ← hej, ← hes, hprod, map_one]
    rcases O.mem_or_inv_mem (a * c) with h | h
    · exact IsUnit.of_mul_eq_one_right (⟨_, h⟩ : O) (Subtype.ext h2)
    · have h3 : u' * w' = (⟨_, h⟩ : O) ⊗ₜ 1 := by
        apply hjinj
        rw [← inv_smul_smul₀ hac (j (u' * w')), hprod]
        simp [hj, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
      have h4 : r (u' * w') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hu' hw'
      have h5 : e' u' * e' w' = ⟨_, h⟩ := by
        rw [← map_mul, h3]; simp [he']
      rw [h5, ← IsLocalRing.residue_ne_zero_iff_isUnit]
      intro h6
      apply h4
      rw [h3, hr, Algebra.TensorProduct.map_tmul]
      change (IsLocalRing.residue O _) ⊗ₜ _ = 0
      rw [h6, TensorProduct.zero_tmul]
  have h7 : a * (e' u' : L) = 1 := by rw [← hej, ← hes, ← eu, h1]
  obtain ⟨t, ht⟩ := hunit.exists_right_inv
  have hat : a = t := by
    have : (e' u' : L) * t = 1 := by exact_mod_cast congrArg Subtype.val ht
    calc a = a * (e' u' * t) := by rw [this, mul_one]
      _ = t := by rw [← mul_assoc, h7, one_mul]
  obtain ⟨d, hd⟩ := hcu i
  rw [hd, hat]
  exact mul_mem t.2 d.2

theorem mem_range_of_forall_valuationSubring {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    (x : L) (h : ∀ O : ValuationSubring L, (∀ k, algebraMap K L k ∈ O) → x ∈ O) :
    x ∈ Set.range (algebraMap K L) := by
  have h1 : x ∈ (integralClosure (Subring.closure (Set.range (algebraMap K L))) L).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    exact fun V => h V.1 fun k => V.2 ⟨k, rfl⟩
  have e : Subring.closure (Set.range (algebraMap K L)) = (algebraMap K L).range :=
    Subring.closure_eq (algebraMap K L).range
  rw [e] at h1
  have h2 : IsIntegral (algebraMap K L).range x := h1
  have h3 : IsIntegral K x := by
    obtain ⟨p, hp, hpx⟩ := h2
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (algebraMap K L).rangeRestrict_surjective p) hp
    refine ⟨q, hqm, ?_⟩
    rw [← hq, Polynomial.eval₂_map] at hpx
    exact hpx
  exact minpoly.mem_range_of_degree_eq_one K x
    (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h3))

theorem tensor_unit_eq_one {K A B : Type} [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A] [Algebra K A]
    [CommRing B] [Algebra K B]
    (hB : ∀ (F : Type) [Field F] [Algebra K F], NoZeroDivisors (F ⊗[K] B))
    (φ : A →ₐ[K] K) (ψ : B →ₐ[K] K) (u : A ⊗[K] B) (hu : IsUnit u)
    (h1 : Algebra.TensorProduct.lift (AlgHom.id K A) ((Algebra.ofId K A).comp ψ)
      (fun _ _ => Commute.all _ _) u = 1)
    (h2 : Algebra.TensorProduct.lift ((Algebra.ofId K B).comp φ) (AlgHom.id K B)
      (fun _ _ => Commute.all _ _) u = 1) : u = 1 := by
  classical
  let L := FractionRing A
  let b := Module.Basis.ofVectorSpace K B
  set j := Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A L) (AlgHom.id K B) with hj
  have hrepr : ∀ z i, (Algebra.TensorProduct.basis L b).repr (j z) i =
      algebraMap A L ((Algebra.TensorProduct.basis A b).repr z i) := by
    intro z i
    induction z with
    | zero => simp
    | tmul x y => simp [hj, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
    | add x y hx hy => simp [hx, hy]
  have hev : ∀ z, Algebra.TensorProduct.lift (AlgHom.id K L) ((Algebra.ofId K L).comp ψ)
      (fun _ _ => Commute.all _ _) (j z) = algebraMap A L
        (Algebra.TensorProduct.lift (AlgHom.id K A) ((Algebra.ofId K A).comp ψ)
          (fun _ _ => Commute.all _ _) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [hj, Algebra.ofId_apply, ← IsScalarTower.algebraMap_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hco : ∀ i, ∃ k : K, (Algebra.TensorProduct.basis A b).repr u i = algebraMap K A k := by
    intro i
    obtain ⟨k, hk⟩ := mem_range_of_forall_valuationSubring (K := K)
      ((Algebra.TensorProduct.basis L b).repr (j u) i) (fun O hO => by
        letI : Algebra K O := ((algebraMap K L).codRestrict O.toSubring hO).toAlgebra
        haveI : IsScalarTower K O L := IsScalarTower.of_algebraMap_eq fun _ => rfl
        haveI := hB (IsLocalRing.ResidueField O)
        exact coeff_mem b O ψ (j u) (hu.map j) (by rw [hev, h1, map_one]) i)
    refine ⟨k, IsFractionRing.injective A L ?_⟩
    rw [← hrepr, ← hk, ← IsScalarTower.algebraMap_apply]
  choose k hk using hco
  have hu' : u = 1 ⊗ₜ ∑ i ∈ ((Algebra.TensorProduct.basis A b).repr u).support, k i • b i := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis A b).linearCombination_repr u,
      Finsupp.linearCombination_apply, Finsupp.sum]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk, Algebra.TensorProduct.basis_apply, algebraMap_smul, TensorProduct.tmul_smul]
  rw [hu'] at h2
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.id_apply] at h2
  rw [hu', h2, Algebra.TensorProduct.one_def]

end GlobalTheory.UnitRigidity

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnitRigidity

theorem geometricallyConnected_of_isPullback_of_surjective {P X Y Z : Scheme.{0}} {a : P ⟶ X}
    {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) [Surjective g]
    [GeometricallyConnected b] : GeometricallyConnected f := by
  refine ⟨fun k _ y W fst snd hW => ?_⟩
  obtain ⟨z, -⟩ := (pullback.snd g y).surjective (Classical.arbitrary _)
  let p := (pullback g y).fromSpecResidueField z
  have : Surjective (p ≫ pullback.snd g y) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have h1 := (IsPullback.of_hasPullback snd (p ≫ pullback.snd g y)).paste_horiz hW
  rw [Category.assoc, ← pullback.condition, ← Category.assoc] at h1
  have h2 := IsPullback.of_right (by rwa [h.lift_fst]) (h.lift_snd _ _ h1.w) h
  have : ConnectedSpace ↥(pullback snd (p ≫ pullback.snd g y)) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h2
  exact (pullback.fst snd (p ≫ pullback.snd g y)).surjective.connectedSpace
    (pullback.fst snd (p ≫ pullback.snd g y)).continuous

theorem isPullback_act {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) :
    IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  refine ⟨⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.one_mul]
  · have hW := ex (W.fst / W.snd) (by rw [GrpObj.div_comp, W.condition, div_self'])
    refine ⟨lift hW.choose W.snd, ?_, lift_snd _ _, ?_⟩
    · change lift _ _ ≫ (_ * _) = _
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, hW.choose_spec, div_mul_cancel]
    · intro (m : W.pt ⟶ T ⊗ G) (h1 : m ≫ (_ * _) = W.fst) (h2 : m ≫ snd T G = W.snd)
      change m = _
      refine CartesianMonoidalCategory.hom_ext _ _ (inj ?_) (by rw [lift_snd, h2])
      rw [lift_fst, hW.choose_spec, ← h1, ← h2, MonObj.comp_mul, mul_div_cancel_right,
        Category.assoc]

theorem smooth_geometricallyConnected_of_isGt {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G]
    (h : E.IsGt G) : Smooth G.hom ∧ GeometricallyConnected G.hom := by
  obtain ⟨D⟩ := h
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have := E.isAbelian.smooth
  have := E.isAbelian.geomConnected
  obtain ⟨-, -, -, -, h1, -, -, h2, -⟩ := (splitTorus_properties S).1 E.X
  have : Smooth (splitTorus S E.X).hom := SmoothOfRelativeDimension.smooth (Module.finrank ℤ E.X) _
  have H := (isPullback_act D.i D.q D.isKernel).map (Over.forget S)
  have a1 : Smooth (snd (splitTorus S E.X) G).left :=
    inferInstanceAs (Smooth (pullback.snd (splitTorus S E.X).hom G.hom))
  have a2 : GeometricallyConnected (snd (splitTorus S E.X) G).left :=
    inferInstanceAs (GeometricallyConnected (pullback.snd (splitTorus S E.X).hom G.hom))
  have b1 : Smooth D.q.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip ⟨⟨‹_›, ‹_›⟩, (inferInstance : QuasiCompact D.q.left)⟩ a1
  have b2 : GeometricallyConnected D.q.left :=
    @geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _ H D.q_surjective a2
  rw [← Over.w D.q]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

open scoped TensorProduct

theorem appTop_SpecMap_apply {R S : CommRingCat.{0}} (φ : R ⟶ S) {X : Scheme.{0}} (g : Spec R ⟶ X)
    (u : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso S).hom.hom ((Spec.map φ ≫ g).appTop.hom u) =
      φ.hom ((Scheme.ΓSpecIso R).hom.hom (g.appTop.hom u)) := by
  rw [Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

theorem appTop_injective {U X : Scheme.{0}} [IsIntegral X] [Nonempty U] (m : U ⟶ X)
    [IsOpenImmersion m] : Function.Injective m.appTop.hom := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra h
  rw [← basicOpen_eq_bot_iff] at h
  obtain ⟨_, hx, x, rfl⟩ := nonempty_preirreducible_inter (X.basicOpen v).isOpen
    m.isOpenEmbedding.isOpen_range (TopologicalSpace.Opens.ne_bot_iff_nonempty _ |>.mp h)
    (Set.range_nonempty _)
  have hx' : x ∈ m ⁻¹ᵁ X.basicOpen v := hx
  rw [Scheme.preimage_basicOpen_top, hv, Scheme.basicOpen_zero] at hx'
  exact hx'

theorem noZeroDivisors_tensor {K A : Type} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (g : Spec (.of A) ⟶ X) [IsOpenImmersion g]
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (F : Type) [Field F] [Algebra K F] : NoZeroDivisors (F ⊗[K] A) := by
  let y := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : IsIntegral (pullback y f) :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F y
  let m : Spec (.of (F ⊗[K] A)) ⟶ pullback y f := (pullbackSpecIso K F A).inv ≫
    pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by simp [y]) (by simp [hg])
  have : IsIntegral (Spec (.of (F ⊗[K] A))) := isIntegral_of_isOpenImmersion m
  have : IsDomain (F ⊗[K] A) := (affine_isIntegral_iff (.of (F ⊗[K] A))).mp this
  infer_instance

theorem unit_eq_one_of_axes {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] (e : Spec (.of K) ⟶ X) (he : e ≫ f = 𝟙 _)
    (a₁ a₂ : X ⟶ pullback f f) (h₁ : a₁ ≫ pullback.fst f f = 𝟙 X) (h₁' : a₁ ≫ pullback.snd f f = f ≫ e)
    (h₂ : a₂ ≫ pullback.fst f f = f ≫ e) (h₂' : a₂ ≫ pullback.snd f f = 𝟙 X)
    (u : Γ(pullback f f, ⊤)) (hu : IsUnit u) (u₁ : a₁.appTop.hom u = 1) (u₂ : a₂.appTop.hom u = 1) :
    u = 1 := by
  first
  | exact @_root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
  | exact _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
  | (apply _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one ..)

end GlobalTheory.UnitRigidity

namespace GlobalTheory

open UnitRigidity in

theorem unit_eq_one_of_axes_of_isGt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ u : Γ((G ⊗ G).left, ⊤), IsUnit u → (lift (𝟙 G) (1 : G ⟶ G)).left.appTop.hom u = 1 → (lift (1 : G ⟶ G) (𝟙 G)).left.appTop.hom u = 1 → u = 1 := by
  intro K _ _ E G _ h u hu u₁ u₂
  obtain ⟨_, _⟩ := smooth_geometricallyConnected_of_isGt E G h
  have := geometricallyIntegral_of_smooth G.hom
  have h1 : (1 : G ⟶ G).left = G.hom ≫ (η[G] : 𝟙_ _ ⟶ G).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  refine unit_eq_one_of_axes G.hom (η[G] : 𝟙_ _ ⟶ G).left (Over.w _) _ _ ?_ ?_ ?_ ?_ u hu u₁ u₂
  · exact congrArg (·.left) (lift_fst (𝟙 G) (1 : G ⟶ G))
  · exact (congrArg (·.left) (lift_snd (𝟙 G) (1 : G ⟶ G))).trans h1
  · exact (congrArg (·.left) (lift_fst (1 : G ⟶ G) (𝟙 G))).trans h1
  · exact congrArg (·.left) (lift_snd (1 : G ⟶ G) (𝟙 G))

end GlobalTheory
