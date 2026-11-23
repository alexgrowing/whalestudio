import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanScalIffOfLeftEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionsOfComaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineGaloisCoverDualNumberEpiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LieGalDesc

section Help
variable {S : Scheme.{0}} {R₁ : Type} [CommRing R₁]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem fst_comp_alg : (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom.comp (algebraMap R₁ (DualNumber R₁)) = RingHom.id R₁ :=
  RingHom.ext fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem es_comp_alg (r : R₁) : (epsScaleR r).comp (algebraMap R₁ (DualNumber R₁)) = algebraMap R₁ (DualNumber R₁) :=
  RingHom.ext fun a => by ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_es (r : R₁) : (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom.comp (epsScaleR r) =
    (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom :=
  RingHom.ext fun a => by simp [epsScaleR]

theorem es_comp_es (r s : R₁) : (epsScaleR r).comp (epsScaleR s) = epsScaleR (r * s) :=
  RingHom.ext fun a => by ext <;> simp [epsScaleR] <;> ring

theorem es_one : epsScaleR (1 : R₁) = RingHom.id _ :=
  RingHom.ext fun a => by ext <;> simp [epsScaleR]

theorem es_zero : epsScaleR (0 : R₁) = (algebraMap R₁ (DualNumber R₁)).comp (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom :=
  RingHom.ext fun a => by ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

def zeroAt (y : Sp R₁ ⟶ S) : Over.mk y ⟶ epsPtR y :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom) (by
    show _ ≫ spMap _ ≫ y = y
    rw [← Category.assoc, spMap_comp', fst_comp_alg, spMap_id', Category.id_comp])

def baseAt (y : Sp R₁ ⟶ S) : epsPtR y ⟶ Over.mk y :=
  Over.homMk (spMap (algebraMap R₁ (DualNumber R₁))) rfl

def scaleAt (y : Sp R₁ ⟶ S) (r : R₁) : epsPtR y ⟶ epsPtR y :=
  Over.homMk (spMap (epsScaleR r)) (by
    show _ ≫ spMap _ ≫ y = spMap _ ≫ y
    rw [← Category.assoc, spMap_comp', es_comp_alg])

theorem zeroAt_scaleAt (y : Sp R₁ ⟶ S) (r : R₁) : zeroAt y ≫ scaleAt y r = zeroAt y :=
  Over.OverMorphism.ext (by
    show spMap _ ≫ spMap _ = spMap _
    rw [spMap_comp', fst_comp_es])

theorem scaleAt_mul (y : Sp R₁ ⟶ S) (r s : R₁) : scaleAt y r ≫ scaleAt y s = scaleAt y (r * s) :=
  Over.OverMorphism.ext (by
    show spMap _ ≫ spMap _ = spMap _
    rw [spMap_comp', es_comp_es])

theorem scaleAt_one (y : Sp R₁ ⟶ S) : scaleAt y 1 = 𝟙 _ :=
  Over.OverMorphism.ext (by
    show spMap _ = 𝟙 _
    rw [es_one, spMap_id'])

theorem scaleAt_zero (y : Sp R₁ ⟶ S) : scaleAt y 0 = baseAt y ≫ zeroAt y :=
  Over.OverMorphism.ext (by
    show spMap _ = spMap _ ≫ spMap _
    rw [spMap_comp', es_zero])

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

def tan (y : Sp R₁ ⟶ S) : Subgroup (epsPtR y ⟶ G) where
  carrier := {u | zeroAt y ≫ u = 1}
  one_mem' := comp_one _
  mul_mem' {u u'} hu hu' := by
    simp only [Set.mem_setOf_eq] at *
    rw [comp_mul, hu, hu', _root_.one_mul]
  inv_mem' {u} hu := by
    simp only [Set.mem_setOf_eq] at *
    rw [GrpObj.comp_inv, hu, inv_one]

abbrev TM (y : Sp R₁ ⟶ S) := Additive (tan G y)

def scM (y : Sp R₁ ⟶ S) (r : R₁) : AddMonoid.End (TM G y) where
  toFun u := Additive.ofMul ⟨scaleAt y r ≫ (Additive.toMul u).1, by
    show zeroAt y ≫ scaleAt y r ≫ _ = 1
    rw [← Category.assoc, zeroAt_scaleAt]; exact (Additive.toMul u).2⟩
  map_zero' := Subtype.ext (comp_one _)
  map_add' u u' := Subtype.ext (comp_mul _ _ _)

def acM (y : Sp R₁ ⟶ S) (f : G ⟶ G) (hf : IsMonHom f) : AddMonoid.End (TM G y) where
  toFun u := Additive.ofMul ⟨(Additive.toMul u).1 ≫ f, by
    show zeroAt y ≫ _ ≫ f = 1
    rw [← Category.assoc, (Additive.toMul u).2, one_comp]⟩
  map_zero' := Subtype.ext (one_comp _)
  map_add' u u' := Subtype.ext (mul_comp _ _ _)

end Help

section Theta
variable {S : Scheme.{0}} {R₁ : Type} [CommRing R₁] (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem isTanScal_iff' {O : Type} [Ring O] (act : OActN O G) (y : Sp R₁ ⟶ S) (c : O) (r : R₁)
    (u : epsPtR y ⟶ G) : IsTanScal act y c r u ↔ zeroAt y ≫ u = 1 ∧ u ≫ act.act c = scaleAt y r ≫ u :=
  and_congr ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg Over.Hom.left h⟩
    ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg Over.Hom.left h⟩

theorem tan_left (y : Sp R₁ ⟶ S) (u : tan G y) :
    spMap (TrivSqZeroExt.fstHom R₁ R₁ R₁).toRingHom ≫ u.1.left = (1 : Over.mk y ⟶ G).left :=
  congrArg Over.Hom.left u.2

def phiR (y : Sp R₁ ⟶ S) : R₁ →+* AddMonoid.End (TM G y) where
  toFun := scM G y
  map_one' := AddMonoidHom.ext fun u => Subtype.ext (by
    show scaleAt y 1 ≫ _ = _
    rw [scaleAt_one, Category.id_comp]; rfl)
  map_mul' r s := AddMonoidHom.ext fun u => Subtype.ext (by
    show scaleAt y (r * s) ≫ _ = scaleAt y r ≫ scaleAt y s ≫ _
    rw [← Category.assoc, scaleAt_mul])
  map_zero' := AddMonoidHom.ext fun u => Subtype.ext (by
    show scaleAt y 0 ≫ _ = 1
    rw [scaleAt_zero, Category.assoc, (Additive.toMul u).2, comp_one])
  map_add' r s := AddMonoidHom.ext fun u => Subtype.ext (by
    show scaleAt y (r + s) ≫ _ = (scaleAt y r ≫ _) * (scaleAt y s ≫ _)
    exact Over.OverMorphism.ext ((GlobalTheory.T.grpObj_tangentVector_add_at_point G y _ (tan_left G y _) r s _ _ rfl rfl).symm))

def psiR {O : Type} [Ring O] (F : Type) [CommRing F] [Algebra F O] (act : OActN O G) (y : Sp R₁ ⟶ S) :
    F →+* AddMonoid.End (TM G y) where
  toFun c := acM G y (act.act (algebraMap F O c)) (act.hom _)
  map_one' := AddMonoidHom.ext fun u => Subtype.ext (by
    show _ ≫ act.act (algebraMap F O 1) = _
    rw [map_one, act.one, Category.comp_id]; rfl)
  map_mul' c d := AddMonoidHom.ext fun u => Subtype.ext (by
    show _ ≫ act.act (algebraMap F O (c * d)) = (_ ≫ act.act (algebraMap F O d)) ≫ act.act (algebraMap F O c)
    rw [map_mul, act.mul, Category.assoc])
  map_zero' := AddMonoidHom.ext fun u => Subtype.ext (by
    show _ ≫ act.act (algebraMap F O 0) = 1
    have h0 : act.act 0 = 1 := by
      have h := act.add 0 0
      rw [add_zero] at h
      exact (mul_left_cancel (a := act.act 0) (by rw [_root_.mul_one]; exact h)).symm
    rw [map_zero, h0, comp_one])
  map_add' c d := AddMonoidHom.ext fun u => Subtype.ext (by
    show _ ≫ act.act (algebraMap F O (c + d)) = (_ ≫ act.act (algebraMap F O c)) * (_ ≫ act.act (algebraMap F O d))
    rw [map_add, act.add, comp_mul])

def theta {O : Type} [Ring O] (F : Type) [CommRing F] [Algebra F O] (act : OActN O G) {R : Type} [CommRing R]
    (β₁ : R →+* R₁) (y : Sp R₁ ⟶ S) : R ⊗[ℤ] F →+* AddMonoid.End (TM G y) :=
  (Algebra.TensorProduct.lift ((phiR G y).comp β₁).toIntAlgHom (psiR G F act y).toIntAlgHom
    (fun r c => AddMonoidHom.ext fun u => Subtype.ext (by
      show scaleAt y (β₁ r) ≫ (_ ≫ _) = (scaleAt y (β₁ r) ≫ _) ≫ _
      exact (Category.assoc _ _ _).symm))).toRingHom

theorem theta_tmul {O : Type} [Ring O] (F : Type) [CommRing F] [Algebra F O] (act : OActN O G) {R : Type}
    [CommRing R] (β₁ : R →+* R₁) (y : Sp R₁ ⟶ S) (r : R) (c : F) :
    theta G F act β₁ y (r ⊗ₜ c) = phiR G y (β₁ r) * psiR G F act y c :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

def pullM {R₂ : Type} [CommRing R₂] (y : Sp R₁ ⟶ S) (y' : Sp R₂ ⟶ S) (j : epsPtR y' ⟶ epsPtR y)
    (g₀ : Over.mk y' ⟶ Over.mk y) (hj : zeroAt y' ≫ j = g₀ ≫ zeroAt y) : TM G y →+ TM G y' where
  toFun u := Additive.ofMul ⟨j ≫ (Additive.toMul u).1, by
    show zeroAt y' ≫ j ≫ _ = 1
    rw [← Category.assoc, hj, Category.assoc, (Additive.toMul u).2, comp_one]⟩
  map_zero' := Subtype.ext (comp_one _)
  map_add' u u' := Subtype.ext (comp_mul _ _ _)

theorem pullM_theta {O : Type} [Ring O] (F : Type) [CommRing F] [Algebra F O] (act : OActN O G) {R : Type}
    [CommRing R] (β₁ : R →+* R₁) {R₂ : Type} [CommRing R₂] (g₁ : R₁ →+* R₂) (y : Sp R₁ ⟶ S) (y' : Sp R₂ ⟶ S)
    (j : epsPtR y' ⟶ epsPtR y) (g₀ : Over.mk y' ⟶ Over.mk y) (hj : zeroAt y' ≫ j = g₀ ≫ zeroAt y)
    (hs : ∀ r, j ≫ scaleAt y r = scaleAt y' (g₁ r) ≫ j) (z : R ⊗[ℤ] F) (u : TM G y) :
    pullM G y y' j g₀ hj (theta G F act β₁ y z u) = theta G F act (g₁.comp β₁) y' z (pullM G y y' j g₀ hj u) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact map_zero _
  | tmul r c =>
    rw [theta_tmul, theta_tmul]
    apply Subtype.ext
    show j ≫ scaleAt y (β₁ r) ≫ (_ ≫ _) = scaleAt y' (g₁ (β₁ r)) ≫ (j ≫ _) ≫ _
    rw [← Category.assoc, hs, Category.assoc, Category.assoc]
  | add z z' hz hz' =>
    rw [map_add, map_add]
    show pullM G y y' j g₀ hj (theta G F act β₁ y z u + theta G F act β₁ y z' u) =
      theta G F act (g₁.comp β₁) y' z (pullM G y y' j g₀ hj u) + theta G F act (g₁.comp β₁) y' z' (pullM G y y' j g₀ hj u)
    rw [map_add, hz, hz']

end Theta

theorem lie_descends : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ X), x ≫ (π ≫ sY) = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ sY = spMap β → ∀ v : epsPtR x ⟶ A₀, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A₀), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act₀ x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ hG _ _ hpb hact H R' _ β x hx v hv
  classical
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_eigen_projections_tensor_of_comaximal R (𝓞 D.F) D.a b.t b.comax
  obtain ⟨R'', _, g₁, x'', d₁, hsq, hdalg, hdfst, hdes, hepi⟩ := GlobalTheory.T.exists_affine_galois_cover_dual_number_epi X Y π Ga ρ hG R' x

  let j : epsPtR (x'' ≫ π) ⟶ epsPtR x := Over.homMk (spMap d₁) (by
    show spMap d₁ ≫ spMap _ ≫ x = spMap _ ≫ x'' ≫ π
    rw [hsq, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', hdalg])
  let g₀ : Over.mk (x'' ≫ π) ⟶ Over.mk x := Over.homMk (spMap g₁) hsq.symm
  have hj : zeroAt (x'' ≫ π) ≫ j = g₀ ≫ zeroAt x := Over.OverMorphism.ext (by
    show spMap _ ≫ spMap d₁ = spMap g₁ ≫ spMap _
    rw [spMap_comp', spMap_comp', hdfst])
  have hs : ∀ r, j ≫ scaleAt x r = scaleAt (x'' ≫ π) (g₁ r) ≫ j := fun r => Over.OverMorphism.ext (by
    show spMap d₁ ≫ spMap _ = spMap _ ≫ spMap d₁
    rw [spMap_comp', spMap_comp', hdes])
  have jinj : ∀ u u' : epsPtR x ⟶ A₀, j ≫ u = j ≫ u' → u = u' := fun u u' h =>
    Over.OverMorphism.ext ((cancel_epi (spMap d₁)).1 (congrArg Over.Hom.left h))
  let pj : (epsPtR x ⟶ A₀) →* (epsPtR (x'' ≫ π) ⟶ A₀) :=
    { toFun := fun u => j ≫ u, map_one' := comp_one _, map_mul' := fun u u' => comp_mul _ _ _ }

  have hv' := (isTanScal_iff' A₀ act₀ x _ _ v).1 hv
  let m : TM A₀ x := Additive.ofMul ⟨v, hv'.1⟩
  let Θ := theta A₀ (𝓞 D.F) act₀ β x
  let Θ' := theta A₀ (𝓞 D.F) act₀ (g₁.comp β) (x'' ≫ π)
  let P := pullM A₀ x (x'' ≫ π) j g₀ hj
  have hP : ∀ z u, P (Θ z u) = Θ' z (P u) := pullM_theta A₀ (𝓞 D.F) act₀ β g₁ x (x'' ≫ π) j g₀ hj hs
  let w : Fin D.a → (epsPtR x ⟶ A₀) := fun i => (Additive.toMul (Θ (e i) m)).1

  have hx'' : x'' ≫ (π ≫ sY) = spMap (g₁.comp β) := by
    rw [← Category.assoc, hsq, Category.assoc, hx, spMap_comp']
  obtain ⟨E, hE⟩ := GlobalTheory.LiePull.exists_pushEquiv hpb (epsPtR x'')
    (spMap (algebraMap R'' (DualNumber R'')) ≫ (x'' ≫ π)) (Category.assoc _ _ _).symm
  have key : ∀ (u : epsPtR x'' ⟶ A) (c : D.O) (r : R''), IsTanScal act x'' c r u ↔
      IsTanScal act₀ (x'' ≫ π) c r (E u) := fun u c r =>
    GlobalTheory.HTPullTan.isTanScal_iff_of_left_eq π φ act₀ act hpb hact x'' c r u (E u) (hE u)
  have hvj : IsTanScal act₀ (x'' ≫ π) (algebraMap (𝓞 D.F) D.O D.ω) ((g₁.comp β) b.ρ) (j ≫ v) := by
    refine (isTanScal_iff' A₀ act₀ _ _ _ _).2 ⟨(Additive.toMul (P m)).2, ?_⟩
    rw [Category.assoc, hv'.2, ← Category.assoc, hs, Category.assoc]
    rfl
  obtain ⟨w₃, hw₃, hprod⟩ := H R'' (g₁.comp β) x'' hx'' (E.symm (j ≫ v))
    ((key _ _ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hvj))
  have eig : ∀ l c, E (w₃ l) ≫ act₀.act (algebraMap (𝓞 D.F) D.O c) =
      scaleAt (x'' ≫ π) (g₁ (β (b.t l c))) ≫ E (w₃ l) := fun l c =>
    ((isTanScal_iff' A₀ act₀ _ _ _ _).1 ((key _ _ _).1 (hw₃ l c))).2
  let m₃ : Fin D.a → TM A₀ (x'' ≫ π) := fun l =>
    Additive.ofMul ⟨E (w₃ l), ((isTanScal_iff' A₀ act₀ _ _ _ _).1 ((key _ _ _).1 (hw₃ l 1))).1⟩
  have hjv : j ≫ v = ∏ l, E (w₃ l) := by
    rw [← List.prod_ofFn]
    have h2 := congrArg E hprod
    rw [MulEquiv.apply_symm_apply, map_list_prod, List.map_ofFn] at h2
    exact h2
  have hPm : P m = ∑ l, m₃ l := by
    apply Additive.toMul.injective
    rw [toMul_sum]
    apply Subtype.ext
    rw [SubmonoidClass.coe_finset_prod]
    exact hjv
  have eig₃ : ∀ l (c : 𝓞 D.F), Θ' (1 ⊗ₜ c) (m₃ l) = Θ' (b.t l c ⊗ₜ 1) (m₃ l) := fun l c => by
    rw [theta_tmul, theta_tmul]
    apply Subtype.ext
    show scaleAt (x'' ≫ π) ((g₁.comp β) 1) ≫ (E (w₃ l) ≫ act₀.act (algebraMap (𝓞 D.F) D.O c)) =
      scaleAt (x'' ≫ π) ((g₁.comp β) (b.t l c)) ≫ (E (w₃ l) ≫ act₀.act (algebraMap (𝓞 D.F) D.O 1))
    rw [map_one, scaleAt_one, Category.id_comp, map_one, act₀.one, Category.comp_id, eig]
    rfl
  have hw : ∀ i, j ≫ w i = E (w₃ i) := fun i => by
    have h1 : P (Θ (e i) m) = m₃ i := by
      rw [hP, hPm, map_sum]
      simp only [he _ _ i _ _ (eig₃ _), Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact congrArg (fun z : TM A₀ (x'' ≫ π) => (Additive.toMul z).1) h1
  refine ⟨w, fun i c => ?_, ?_⟩
  · refine (isTanScal_iff' A₀ act₀ _ _ _ _).2 ⟨(Additive.toMul (Θ (e i) m)).2, jinj _ _ ?_⟩
    rw [← Category.assoc j (w i), hw, eig, ← Category.assoc j (scaleAt x _) (w i), hs, Category.assoc, hw]
  · refine jinj _ _ ?_
    show pj v = pj (List.ofFn w).prod
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
    exact hjv.trans (Finset.prod_congr rfl fun i _ => (hw i).symm)

end GlobalTheory.LieGalDesc
