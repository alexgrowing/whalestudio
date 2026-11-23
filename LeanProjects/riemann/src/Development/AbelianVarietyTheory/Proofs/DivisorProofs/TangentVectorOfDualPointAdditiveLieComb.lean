import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieBasisOfHolUnif
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.TanLinComb

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]

abbrev TP (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (P : Type) [CommRing P] [Algebra ℂ P] :
    Over (Sp R) :=
  Over.mk (spMap (algebraMap ℂ P) ≫ (TF (R := R) ℂ).hom)

def mapP {P P' : Type} [CommRing P] [Algebra ℂ P] [CommRing P'] [Algebra ℂ P'] (φ : P →ₐ[ℂ] P') :
    TP R P' ⟶ TP R P :=
  Over.homMk (spMap φ.toRingHom) (by
    show spMap _ ≫ spMap _ ≫ _ = spMap _ ≫ _
    rw [← Category.assoc, spMap_comp']
    congr 2
    exact RingHom.ext fun x => φ.commutes x)

def toTF (P : Type) [CommRing P] [Algebra ℂ P] : TP R P ⟶ TF (R := R) ℂ :=
  Over.homMk (spMap (algebraMap ℂ P)) rfl

def homF {P : Type} [CommRing P] [Algebra ℂ P] (a : P →ₐ[ℂ] ℂ) : TF (R := R) ℂ ⟶ TP R P :=
  Over.homMk (spMap a.toRingHom) (by
    show spMap _ ≫ spMap _ ≫ _ = _
    rw [← Category.assoc, spMap_comp']
    have : a.toRingHom.comp (algebraMap ℂ P) = RingHom.id ℂ := RingHom.ext fun x => a.commutes x
    rw [this, spMap_id', Category.id_comp])

variable {P P' P'' : Type} [CommRing P] [Algebra ℂ P] [CommRing P'] [Algebra ℂ P'] [CommRing P''] [Algebra ℂ P'']

theorem specMap_comp₃ (f : P →ₐ[ℂ] P') (g : P' →ₐ[ℂ] P'') :
    mapP (R := R) g ≫ mapP f = mapP (g.comp f) := by
  apply Over.OverMorphism.ext
  exact spMap_comp' _ _

theorem specMap_id₃ : mapP (R := R) (AlgHom.id ℂ P) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact spMap_id' _

theorem specMap_comp_toTF (f : P →ₐ[ℂ] P') : mapP (R := R) f ≫ toTF P = toTF P' := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  rw [spMap_comp']
  congr 1
  exact RingHom.ext fun x => f.commutes x

theorem homF_mapP (a : P' →ₐ[ℂ] ℂ) (f : P →ₐ[ℂ] P') : homF (R := R) a ≫ mapP f = homF (a.comp f) := by
  apply Over.OverMorphism.ext
  exact spMap_comp' _ _

theorem homF_toTF (a : P →ₐ[ℂ] ℂ) : homF (R := R) a ≫ toTF P = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = 𝟙 _
  rw [spMap_comp']
  have : a.toRingHom.comp (algebraMap ℂ P) = RingHom.id ℂ := RingHom.ext fun x => a.commutes x
  rw [this, spMap_id']

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
variable {G : Over (Sp R)} [GrpObj G]

def IsT (x : TP R (DualNumber ℂ) ⟶ G) : Prop := homF (Chart.fstD ℂ) ≫ x = 1

abbrev L {P : Type} [CommRing P] [Algebra ℂ P] (z : TP R P ⟶ G) : TP R P ⟶ TF (R := R) ℂ ⊗ G := lift (toTF P) z

abbrev x0 (G : Over (Sp R)) [GrpObj G] : Sp ℂ ⟶ (TF (R := R) ℂ ⊗ G).left := (lift (𝟙 (TF (R := R) ℂ)) (1 : TF (R := R) ℂ ⟶ G)).left

theorem isT_one : IsT (1 : TP R (DualNumber ℂ) ⟶ G) := MonObj.comp_one _

theorem isT_mul {x y : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) (hy : IsT y) : IsT (x * y) := by
  unfold IsT at *
  rw [MonObj.comp_mul, hx, hy, _root_.mul_one]

theorem isT_scale (c : ℂ) {x : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) : IsT (mapP (Chart.scaleD c) ≫ x) := by
  unfold IsT at *
  have : (Chart.fstD ℂ).comp (Chart.scaleD c) = Chart.fstD ℂ := by
    ext
    exact TrivSqZeroExt.fst_map _ _
  rw [← Category.assoc, homF_mapP, this, hx]

theorem specMap_scaleD_zero : mapP (R := R) (Chart.scaleD (0 : ℂ)) = toTF (DualNumber ℂ) ≫ homF (Chart.fstD ℂ) := by
  apply Over.OverMorphism.ext
  show spMap _ = spMap _ ≫ spMap _
  rw [spMap_comp', Chart.scaleD_zero]
  rfl

theorem scale_zero_comp {x : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) : mapP (Chart.scaleD (0 : ℂ)) ≫ x = 1 := by
  rw [specMap_scaleD_zero, Category.assoc, hx, MonObj.comp_one]

theorem scale_one_comp (x : TP R (DualNumber ℂ) ⟶ G) : mapP (Chart.scaleD (1 : ℂ)) ≫ x = x := by
  rw [Chart.scaleD_one, specMap_id₃, Category.id_comp]

theorem homF_L {P : Type} [CommRing P] [Algebra ℂ P] (a : P →ₐ[ℂ] ℂ) (z : TP R P ⟶ G) :
    homF a ≫ L z = lift (𝟙 _) (homF a ≫ z) := by
  rw [comp_lift, homF_toTF]

theorem mapP_L {P P' : Type} [CommRing P] [Algebra ℂ P] [CommRing P'] [Algebra ℂ P'] (φ : P →ₐ[ℂ] P') (z : TP R P ⟶ G) :
    mapP φ ≫ L z = L (mapP φ ≫ z) := by
  rw [comp_lift, specMap_comp_toTF]

theorem valR_spMap_comp {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (φ : A →+* B) (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR (spMap φ ≫ x) U f = φ (TangentOrigin.evalPt x U h f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ => h (Set.mem_univ _)
  rw [valR, dif_pos h']
  exact TangentOrigin.evalPt_spMap_comp φ x U h h' f

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
variable {G : Over (Sp R)} [GrpObj G]

theorem val_comb {x y : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) (hy : IsT y) (U : (TF (R := R) ℂ ⊗ G).left.Opens)
    (f : Γ((TF (R := R) ℂ ⊗ G).left, U)) (h0 : ⊤ ≤ x0 G ⁻¹ᵁ U) :
    ∃ t : TrivSqZeroExt ℂ (ℂ × ℂ), ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ,
      valR (L ((mapP (Chart.scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ x) * (mapP (Chart.scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ y))).left U f =
        TrivSqZeroExt.map l t := by
  let P : TP R (Chart.JetR ℂ (Fin 2) 1) ⟶ G := (mapP (Chart.qD 0) ≫ x) * (mapP (Chart.qD 1) ≫ y)
  have hP : homF (Chart.jetAug ℂ (Fin 2) 1) ≫ P = 1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homF_mapP, homF_mapP, Chart.jetAug_comp_qD,
      Chart.jetAug_comp_qD]
    unfold IsT at hx hy
    rw [hx, hy, _root_.mul_one]
  have hred : spMap (Chart.jetAug ℂ (Fin 2) 1).toRingHom ≫ (L P).left = x0 G := by
    have := congrArg CommaMorphism.left (homF_L (Chart.jetAug ℂ (Fin 2) 1) P)
    rw [hP] at this
    exact this
  have hPU : ⊤ ≤ (L P).left ⁻¹ᵁ U := fun p _ => by
    obtain ⟨q, rfl⟩ := UnifLieBasis.spMap_jetAug_surjective p
    rw [← hred] at h0
    exact h0 (Set.mem_univ q)
  refine ⟨Chart.deltaJ (TangentOrigin.evalPt (L P).left U hPU f), fun l => ?_⟩
  have hval : mapP (Chart.rD l) ≫ P =
      (mapP (Chart.scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ x) * (mapP (Chart.scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ y) := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specMap_comp₃, specMap_comp₃, Chart.restrictDiag_comp_incl_fst, Chart.restrictDiag_comp_incl_snd]
  rw [← hval, ← mapP_L]
  exact valR_spMap_comp (Chart.rD l).toRingHom (L P).left U hPU f

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
variable {G : Over (Sp R)} [GrpObj G]

def Dg (z : TP R (DualNumber ℂ) ⟶ G) (δ : ∀ U : (TF (R := R) ℂ ⊗ G).left.Opens, Γ((TF (R := R) ℂ ⊗ G).left, U) → ℂ) :
    Prop :=
  IsT z ∧ ∀ U f, ⊤ ≤ x0 G ⁻¹ᵁ U → valR (L z).left U f = TrivSqZeroExt.inl (valF (x0 G) U f) + TrivSqZeroExt.inr (δ U f)

theorem val_one (U : (TF (R := R) ℂ ⊗ G).left.Opens) (f : Γ((TF (R := R) ℂ ⊗ G).left, U)) (h0 : ⊤ ≤ x0 G ⁻¹ᵁ U) :
    valR (L (1 : TP R (DualNumber ℂ) ⟶ G)).left U f = TrivSqZeroExt.inl (valF (x0 G) U f) := by
  have e : L (1 : TP R (DualNumber ℂ) ⟶ G) = toTF (DualNumber ℂ) ≫ lift (𝟙 _) (1 : TF (R := R) ℂ ⟶ G) := by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  rw [e, Over.comp_left]
  show valR (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x0 G) U f = _
  rw [valR_spMap_comp _ _ U h0, valF, dif_pos h0, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

theorem dg_one : Dg (1 : TP R (DualNumber ℂ) ⟶ G) (fun _ _ => 0) := by
  refine ⟨isT_one, fun U f h0 => ?_⟩
  rw [val_one U f h0, TrivSqZeroExt.inr_zero, add_zero]

theorem fst_comb {x y : TP R (DualNumber ℂ) ⟶ G} (hx : IsT x) (hy : IsT y) (U : (TF (R := R) ℂ ⊗ G).left.Opens)
    (f : Γ((TF (R := R) ℂ ⊗ G).left, U)) (h0 : ⊤ ≤ x0 G ⁻¹ᵁ U) (t : TrivSqZeroExt ℂ (ℂ × ℂ))
    (ht : ∀ l : ℂ × ℂ →ₗ[ℂ] ℂ,
      valR (L ((mapP (Chart.scaleD (l ((1 : ℂ), (0 : ℂ)))) ≫ x) * (mapP (Chart.scaleD (l ((0 : ℂ), (1 : ℂ)))) ≫ y))).left U f =
        TrivSqZeroExt.map l t) : t.fst = valF (x0 G) U f := by
  have := ht 0
  simp only [LinearMap.zero_apply] at this
  rw [scale_zero_comp hx, scale_zero_comp hy, _root_.mul_one, val_one U f h0] at this
  have := congrArg TrivSqZeroExt.fst this
  rw [TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_map] at this
  exact this.symm

theorem dg_mul {x y : TP R (DualNumber ℂ) ⟶ G} {δ δ'} (hx : Dg x δ) (hy : Dg y δ') : Dg (x * y) (δ + δ') := by
  refine ⟨isT_mul hx.1 hy.1, fun U f h0 => ?_⟩
  obtain ⟨t, ht⟩ := val_comb hx.1 hy.1 U f h0
  have h1 := fst_comb hx.1 hy.1 U f h0 t ht
  have ha := ht (LinearMap.fst ℂ ℂ ℂ)
  have hb := ht (LinearMap.snd ℂ ℂ ℂ)
  have hc := ht (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ)
  simp only [LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply, add_zero, zero_add] at ha hb hc
  rw [scale_one_comp, scale_zero_comp hy.1, _root_.mul_one, hx.2 U f h0] at ha
  rw [scale_one_comp, scale_zero_comp hx.1, _root_.one_mul, hy.2 U f h0] at hb
  rw [scale_one_comp, scale_one_comp] at hc
  rw [hc]
  have ha2 := congrArg TrivSqZeroExt.snd ha
  have hb2 := congrArg TrivSqZeroExt.snd hb
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_map,
    LinearMap.fst_apply, LinearMap.snd_apply, zero_add] at ha2 hb2
  ext
  · simp [TrivSqZeroExt.fst_map, h1]
  · simp [TrivSqZeroExt.snd_map, ha2, hb2]

theorem dg_scale (c : ℂ) {x : TP R (DualNumber ℂ) ⟶ G} {δ} (hx : Dg x δ) :
    Dg (mapP (Chart.scaleD c) ≫ x) (c • δ) := by
  refine ⟨isT_scale c hx.1, fun U f h0 => ?_⟩
  obtain ⟨t, ht⟩ := val_comb hx.1 isT_one U f h0
  have h1 := fst_comb hx.1 isT_one U f h0 t ht
  have ha := ht (LinearMap.fst ℂ ℂ ℂ)
  have hc := ht (c • LinearMap.fst ℂ ℂ ℂ)
  simp only [LinearMap.fst_apply, LinearMap.smul_apply, smul_eq_mul, _root_.mul_one, MulZeroClass.mul_zero] at ha hc
  rw [scale_one_comp, scale_zero_comp isT_one, _root_.mul_one, hx.2 U f h0] at ha
  rw [scale_zero_comp isT_one, _root_.mul_one] at hc
  rw [hc]
  have ha2 := congrArg TrivSqZeroExt.snd ha
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_map,
    LinearMap.fst_apply, zero_add] at ha2
  ext
  · simp [TrivSqZeroExt.fst_map, h1]
  · simp [TrivSqZeroExt.snd_map, ha2]

theorem dg_prod : ∀ {n : ℕ} (z : Fin n → (TP R (DualNumber ℂ) ⟶ G)) (δ : Fin n → ∀ U : (TF (R := R) ℂ ⊗ G).left.Opens,
    Γ((TF (R := R) ℂ ⊗ G).left, U) → ℂ), (∀ i, Dg (z i) (δ i)) → Dg (List.ofFn z).prod (∑ i, δ i)
  | 0, z, δ, _ => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
    exact dg_one
  | n + 1, z, δ, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact dg_mul (h 0) (dg_prod (fun i => z i.succ) (fun i => δ i.succ) fun i => h i.succ)

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]

theorem toUnit_left' (T : Over (Sp R)) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

abbrev fC (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] : R →+* ℂ :=
  (algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))

theorem tf_hom : (TF (R := R) ℂ).hom = spMap (fC R) := by
  show spMap _ ≫ spMap _ = _
  rw [spMap_comp']

def dm (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] : TP R (DualNumber ℂ) ⟶ epsR R :=
  Over.homMk (spMap (dualMap (fC R))) (by
    show spMap _ ≫ spMap _ = spMap _ ≫ (TF (R := R) ℂ).hom
    rw [tf_hom, spMap_comp', spMap_comp']
    congr 1
    refine RingHom.ext fun a => ?_
    ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

variable {G : Over (Sp R)} [GrpObj G]

theorem comp_prod {T T' : Over (Sp R)} (h : T' ⟶ T) : ∀ {n : ℕ} (u : Fin n → (T ⟶ G)),
    h ≫ (List.ofFn u).prod = (List.ofFn fun i => h ≫ u i).prod
  | 0, u => by simp only [List.ofFn_zero, List.prod_nil]; exact MonObj.comp_one _
  | n + 1, u => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_prod h]

theorem isT_of_tangent {v : epsR R ⟶ G} (hv : IsTangent v) {b : TP R (DualNumber ℂ) ⟶ G}
    (hb : b.left = spMap (dualMap (fC R)) ≫ v.left) : IsT b := by
  unfold IsT
  apply Over.OverMorphism.ext
  rw [Over.comp_left, hb, Hom.one_def, Over.comp_left, toUnit_left', tf_hom]
  show spMap _ ≫ spMap _ ≫ _ = _
  rw [← Category.assoc, spMap_comp']
  have e : (Chart.fstD ℂ).toRingHom.comp (dualMap (fC R)) = (fC R).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp [dualMap, Chart.fstD]
  rw [e, ← spMap_comp', Category.assoc]
  unfold IsTangent at hv
  rw [hv]

end GlobalTheory.TanLinComb

namespace GlobalTheory.TanLinComb

variable {R : Type} [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ]
variable {G : Over (Sp R)} [GrpObj G]

theorem dm_scale (c : R) {v u : epsR R ⟶ G} (hu : u.left = spMap (epsScaleR c) ≫ v.left) {b : TP R (DualNumber ℂ) ⟶ G}
    (hb : b.left = spMap (dualMap (fC R)) ≫ v.left) : dm R ≫ u = mapP (Chart.scaleD (fC R c)) ≫ b := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, hu, hb]
  show spMap _ ≫ spMap _ ≫ _ = spMap _ ≫ spMap _ ≫ _
  rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp']
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [epsScaleR, dualMap, Chart.scaleD, smul_smul, _root_.mul_comm]

end GlobalTheory.TanLinComb

namespace GlobalTheory

open GlobalTheory.TanLinComb in

theorem isD_lieComb : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (n : ℕ) (c : Fin n → R) (v : Fin n → (epsR R ⟶ D.P.A)) (w : epsR R ⟶ D.P.A) (W : Fin n → Fin g → ℂ) (b : Fin n → (TE R ℂ ⟶ D.P.A)) (bw : TE R ℂ ⟶ D.P.A), (∀ j, IsTangent (v j)) → IsLieComb c v w → (∀ j, (b j).left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (v j).left) → bw.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ w.left → (∀ j, IsD ν d (W j) (b j)) → IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (c j)) • W j) bw := by
  intro R _ _ D _ N ν g d n c v w W b bw hv hc hb hbw hD
  have hx0 : ptB ν d 0 = x0 D.P.A := by
    have e1 : ν.eA (d.ex 0) = 1 := by
      have h1 := d.ex_add 0 0
      rw [add_zero] at h1
      have h2 := congrArg ν.eA h1
      rw [map_mul] at h2
      exact mul_eq_left.1 h2.symm
    unfold ptB
    rw [e1]
  let δW : (Fin g → ℂ) → ∀ U : (TF (R := R) ℂ ⊗ D.P.A).left.Opens, Γ((TF (R := R) ℂ ⊗ D.P.A).left, U) → ℂ :=
    fun W U f => fderiv ℂ (fun z => valF (ptB ν d z) U f) 0 W
  have hDg : ∀ j, Dg (b j) (δW (W j)) := fun j => ⟨isT_of_tangent (hv j) (hb j), fun U f h0 => by
    rw [← hx0] at h0 ⊢
    exact hD j U f h0⟩
  obtain ⟨u, hu, rfl⟩ := hc
  have hbw' : bw = (List.ofFn fun i => mapP (Chart.scaleD (fC R (c i))) ≫ b i).prod := by
    have e : bw = dm R ≫ (List.ofFn u).prod := Over.OverMorphism.ext hbw
    rw [e, comp_prod]
    exact congrArg (fun F : Fin n → (TE R ℂ ⟶ D.P.A) => (List.ofFn F).prod) (funext fun i => dm_scale (c i) (hu i) (hb i))
  have key := dg_prod _ _ (fun i => dg_scale (fC R (c i)) (hDg i))
  rw [← hbw'] at key
  intro U f h0
  rw [hx0] at h0 ⊢
  refine (key.2 U f h0).trans ?_
  congr 2
  simp only [δW, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul]
  rfl

end GlobalTheory
