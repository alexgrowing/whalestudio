import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ZH

namespace GlobalTheory.FieldPts

theorem comp_closedPoint {K L : Type} [Field K] [Field L] (ι : K →+* L) {X : Scheme.{0}} (p : Sp K ⟶ X) :
    (spMap ι ≫ p) (IsLocalRing.closedPoint L) = p (IsLocalRing.closedPoint K) := by
  exact congrArg p (Subsingleton.elim (α := PrimeSpectrum K) _ _)

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem spMap_comp_ofField {L L' : Type} [Field L] [Field L'] (g : L →+* L') {X : Scheme.{0}} (y : X)
    (ψ : X.residueField y ⟶ CommRingCat.of L) :
    spMap g ≫ (Scheme.SpecToEquivOfField L X).symm ⟨y, ψ⟩ =
      (Scheme.SpecToEquivOfField L' X).symm ⟨y, ψ ≫ CommRingCat.ofHom g⟩ := by
  simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]

theorem exists_of_fixed {K : Type} [Field K] [PerfectField K] {X : Scheme.{0}} (q : Sp (AlgebraicClosure K) ⟶ X)
    (hq : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      spMap (σ : AlgebraicClosure K →+* AlgebraicClosure K) ≫ q = q) :
    ∃ p : Sp K ⟶ X, spMap (algebraMap K (AlgebraicClosure K)) ≫ p = q := by
  obtain ⟨⟨y, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField (AlgebraicClosure K) X).symm.surjective q
  have hfix : ∀ a, ψ.hom a ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
    intro a
    rw [InfiniteGalois.mem_bot_iff_fixed]
    intro σ
    have h1 := hq σ
    rw [spMap_comp_ofField] at h1
    have h2 := (Scheme.SpecToEquivOfField _ X).symm.injective h1
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at h2
    have := congrArg (fun f => f.hom a) h2
    simpa using this
  have hbot : ∀ z : (⊥ : IntermediateField K (AlgebraicClosure K)),
      algebraMap K (AlgebraicClosure K) (IntermediateField.botEquiv K (AlgebraicClosure K) z) = z := by
    intro z
    conv_rhs => rw [← (IntermediateField.botEquiv K (AlgebraicClosure K)).symm_apply_apply z]
    rw [IntermediateField.botEquiv_symm]
    rfl
  let ψ' : X.residueField y →+* K := (IntermediateField.botEquiv K (AlgebraicClosure K)).toRingHom.comp
    (ψ.hom.codRestrict (⊥ : IntermediateField K (AlgebraicClosure K)) hfix)
  refine ⟨(Scheme.SpecToEquivOfField K X).symm ⟨y, CommRingCat.ofHom ψ'⟩, ?_⟩
  refine (spMap_comp_ofField (algebraMap K (AlgebraicClosure K)) y (CommRingCat.ofHom ψ')).trans ?_
  congr 2
  ext a
  exact hbot _

theorem val_spMap {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {K L : Type} [Field K]
    [Field L] (ι : K →+* L) (p : Sp K ⟶ M.Z) (x : Ω) : M.val (spMap ι ≫ p) x = ι (M.val p x) := by
  by_cases hx : x ∈ M.O (p (IsLocalRing.closedPoint K))
  · have h1 := RatModel.val_spMap_comp (M := M) ι p (specializes_rfl) ⟨x, hx⟩
    rw [RatModel.valLoc_eq_val] at h1
    exact h1
  · rw [RatModel.val_of_notMem (IsLocalRing.closedPoint K) hx, map_zero]
    exact RatModel.val_of_notMem (IsLocalRing.closedPoint L) (by rwa [comp_closedPoint])

theorem par_map_iff {ι' : Type} {m k : ι' → ℕ} {K L : Type} [Field K] [Field L] (ι : K →+* L) (G : Mat m K) :
    Par k ⊤ (G.map ι) ↔ Par k ⊤ G := by
  refine ⟨fun hG τ => ⟨fun _ _ => trivial, fun h0 => (hG τ).2.1 ?_, trivial, fun i j hi hij => ?_⟩,
    fun hG => hG.map ι fun _ _ => trivial⟩
  · rw [Mat.det_map, h0, map_zero]
  · exact ι.injective (((hG τ).2.2.2 i j hi hij).trans (map_zero ι).symm)

theorem bears_spMap_iff {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    {ι' : Type} {m k' : ι' → ℕ} {M' : RatModel F Ω'} (S' : Fr M' m k') (φ : Ω →ₐ[F] Ω') (A : Mat m Ω)
    {K L : Type} [Field K] [Field L] (ι : K →+* L) (h : Mat m K) (p : Sp K ⟶ M'.Z) :
    Bears S' φ A (h.map ι) (spMap ι ≫ p) ↔ Bears S' φ A h p := by
  unfold Bears
  rw [comp_closedPoint]
  refine exists_congr fun A' => and_congr_right fun _ => ?_
  have e : (A' * (A.map φ)⁻¹).map (M'.val (spMap ι ≫ p)) = ((A' * (A.map φ)⁻¹).map (M'.val p)).map ι := by
    funext τ
    ext i j
    exact val_spMap M' ι p _
  rw [e, ← Mat.map_inv, ← Mat.map_mul, par_map_iff]

end GlobalTheory.FieldPts

namespace GlobalTheory.ShFam.FieldLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F]

section Lifts

variable (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
  (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn)
  (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X)

theorem coord_iff_of_hom (hπ : C.π = f ≫ j) (hT : Tied e B j f₀ S A₀) (hT' : Tied e C.Y C.π C.f0 S' A₁)
    (hC : f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹)) (hφ : (ratOf B).IsHom (ratOf C.Y) φ f)
    {K : Type} [Field K] {χ : c.F →+* K} {x : Sp K ⟶ Z.X} (p : Sp K ⟶ C.Y.X) (hx : (p ≫ f) ≫ j ≫ genι Z = x)
    (g : EigFrame Z χ x)
    {A : Mat Dw.mult B.Fn} (_hA : A ∈ S.S (f (p (IsLocalRing.closedPoint K))))
    {φA : c.F →+* B.X.presheaf.stalk (f (p (IsLocalRing.closedPoint K)))}
    {fA : EigFrame Z φA (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z)}
    (hfA : fA.Coord (algebraMap _ B.X.functionField) f₀ (A₀ * A⁻¹))
    {h : Mat Dw.mult K} (hh : fA.Coord (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom g h)
    {A' : Mat Dw.mult C.Y.Fn} (hA' : A' ∈ S'.S (p (IsLocalRing.closedPoint K)))
    {φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))}
    {f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)}
    (hf₁ : f₁.Coord (algebraMap _ C.Y.X.functionField) C.f0 (A₁ * A'⁻¹)) :
    (∀ τ, (((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p)) τ).det ≠ 0) ∧
    ∀ h' : Mat Dw.mult K, f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' ↔
      h = h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) := by
  rw [← AlgHom.coe_toRingHom φ] at hC ⊢
  have hA₀ : A₀ ∈ S.S (genericPoint B.X) := hT.1
  have hA₁ : A₁ ∈ S'.S (genericPoint C.Y.X) := hT'.1
  have hxK : (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom =
      (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom := by
    rw [Scheme.stalkClosedPointTo_comp]; rfl

  have hφ₁ : φ₁ = (f.stalkMap (p (IsLocalRing.closedPoint K))).hom.comp φA := by
    ext a
    apply IsFractionRing.injective (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField
    have e1 : algebraMap _ C.Y.X.functionField (φ₁ a) = constF e C.Y a := by rw [hf₁.2.1]; rfl
    have e2 : algebraMap _ C.Y.X.functionField ((f.stalkMap (p (IsLocalRing.closedPoint K))).hom (φA a)) =
        constF e C.Y a := by
      rw [← map_algebraMap_stalk hφ (p (IsLocalRing.closedPoint K)) (φA a)]
      have e3 : algebraMap _ B.X.functionField (φA a) = constF e B a := by rw [hfA.2.1]; rfl
      rw [e3]
      exact φ.commutes (e.symm a)
    exact e1.trans e2.symm
  have hSA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ φA _ fA inferInstance
  have hS₁ : f₁.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ φ₁ _ f₁ inferInstance
  have e0 : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ f =
      spMap (f.stalkMap (p (IsLocalRing.closedPoint K))).hom ≫ stalkPt B (f (p (IsLocalRing.closedPoint K))) :=
    (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  have hst : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (f.stalkMap (p (IsLocalRing.closedPoint K))).hom ≫
        (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z) := by
    rw [hπ]
    simp only [← Category.assoc]
    rw [e0]

  have hU := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φA _ fA _ φ₁ _ (f.stalkMap (p (IsLocalRing.closedPoint K))).hom
    inferInstance hSA hst hφ₁).1 f₁
  obtain ⟨G, hG⟩ := hU.1.exists
  have hGdet : ∀ τ, IsUnit (G τ).det := hU.2 G hG

  have c1 : fA.Coord ((algebraMap _ C.Y.X.functionField).comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom) C.f0
      ((A₁ * A'⁻¹) * G.map (algebraMap _ C.Y.X.functionField)) :=
    GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₁ _ _ _ C.f0 _ _ _ _ inferInstance hG hf₁
  have c2 : fA.Coord ((φ : B.Fn →+* C.Y.Fn).comp (algebraMap _ B.X.functionField)) C.f0
      ((A₁ * (A₀.map (φ : B.Fn →+* C.Y.Fn))⁻¹) * (A₀ * A⁻¹).map (φ : B.Fn →+* C.Y.Fn)) :=
    GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ C.f0 _ _ _ _ inferInstance hfA hC
  have hcomp : (algebraMap _ C.Y.X.functionField).comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom =
      (φ : B.Fn →+* C.Y.Fn).comp (algebraMap _ B.X.functionField) :=
    RingHom.ext fun a => (map_algebraMap_stalk hφ (p (IsLocalRing.closedPoint K)) a).symm
  rw [← hcomp] at c2
  have e4 := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φA _ fA _ _ _ _ inferInstance hSA c1.1 c1.2.1).1 C.f0).1.unique c1 c2
  have dA₀ : ∀ τ, ((A₀.map (φ : B.Fn →+* C.Y.Fn)) τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (Fr.det_ne hA₀ τ)
  have dA₁ : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁
  have dA' : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  have e5 : G.map (algebraMap _ C.Y.X.functionField) = A' * (A.map (φ : B.Fn →+* C.Y.Fn))⁻¹ := by
    have e6 : (A₁ * (A₀.map (φ : B.Fn →+* C.Y.Fn))⁻¹) * (A₀ * A⁻¹).map (φ : B.Fn →+* C.Y.Fn) =
        A₁ * (A.map (φ : B.Fn →+* C.Y.Fn))⁻¹ := by
      rw [Mat.map_mul, Mat.map_inv, mul_assoc, ← mul_assoc _ (A₀.map _), Mat.inv_mul dA₀, one_mul]
    calc G.map (algebraMap _ C.Y.X.functionField)
        = (A' * A₁⁻¹) * ((A₁ * A'⁻¹) * G.map (algebraMap _ C.Y.X.functionField)) := by
          rw [← mul_assoc, mul_assoc A', ← mul_assoc A₁⁻¹, Mat.inv_mul dA₁, one_mul, Mat.mul_inv dA', one_mul]
      _ = A' * (A.map (φ : B.Fn →+* C.Y.Fn))⁻¹ := by
          rw [e4, e6, ← mul_assoc, mul_assoc A', Mat.inv_mul dA₁, mul_one]

  have hpt : spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ stalkPt C.Y (p (IsLocalRing.closedPoint K)) = p :=
    spMap_stalkClosedPointTo p
  have e7 : (A' * (A.map (φ : B.Fn →+* C.Y.Fn))⁻¹).map ((ratOf C.Y).val p) =
      G.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    rw [← e5]
    funext τ
    show ((G τ).map _).map _ = (G τ).map _
    rw [Matrix.map_map]
    congr 1
    funext a
    show (ratOf C.Y).val p (algebraMap _ C.Y.X.functionField a) = _
    exact ((congrArg (fun q => (ratOf C.Y).val q (algebraMap _ C.Y.X.functionField a)) hpt).symm.trans
      (val_ratOf (Scheme.stalkClosedPointTo (R := .of K) p).hom a))
  have hGK : ∀ τ, ((G.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det ≠ 0 := fun τ => by
    show ((G τ).map (Scheme.stalkClosedPointTo (R := .of K) p).hom).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((hGdet τ).map _).ne_zero
  have fwd : ∀ h', f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' →
      h = h' * G.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := fun h' hh' => by
    have c3 := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₁ _ _ _ g _ _ _ _ inferInstance hG hh'
    rw [← hxK] at c3
    exact ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φA _ fA _ χ _ _ inferInstance hSA hh.1 hh.2.1).1 g).1.unique hh c3
  have hx₁ : x = spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫
      (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z) := by
    rw [← hx, hπ]
    simp only [← Category.assoc]
    rw [hpt]
  have hχ₁ : χ = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp φ₁ := by
    rw [hh.2.1, hxK, hφ₁, RingHom.comp_assoc]
  have bwd : ∀ h', h = h' * G.map (Scheme.stalkClosedPointTo (R := .of K) p).hom →
      f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' := fun h' hh' => by
    obtain ⟨h'', hh''⟩ := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φ₁ _ f₁ K χ _ _ inferInstance hS₁ hx₁ hχ₁).1 g).1.exists
    have e10 : h' * G.map (Scheme.stalkClosedPointTo (R := .of K) p).hom =
        h'' * G.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := hh'.symm.trans (fwd h'' hh'')
    have e9 : h' = h'' := by
      calc h' = h' * G.map (Scheme.stalkClosedPointTo (R := .of K) p).hom *
            (G.map (Scheme.stalkClosedPointTo (R := .of K) p).hom)⁻¹ := by rw [mul_assoc, Mat.mul_inv hGK, mul_one]
        _ = h'' := by rw [e10, mul_assoc, Mat.mul_inv hGK, mul_one]
    rw [e9]; exact hh''
  rw [e7]
  exact ⟨hGK, fun h' => ⟨fwd h', bwd h'⟩⟩

theorem lifts_closed (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (hπ : C.π = f ≫ j)
    (hT : Tied e B j f₀ S A₀) (hT' : Tied e C.Y C.π C.f0 S' A₁)
    (hC : f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹)) (hφ : (ratOf B).IsHom (ratOf C.Y) φ f)
    (hL : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ B.X), x ≫ j ≫ genStr Z = spMap χ →
      ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ B.X) (A : Mat Dw.mult B.Fn)
    (hA : A ∈ S.S (x (IsLocalRing.closedPoint K))) (h : Mat Dw.mult K) (hh : Par 0 ⊤ h) :
    ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ Bears S' φ A h p := by
  obtain ⟨φA, fA, hfA⟩ := hT.2 _ A hA
  have hst : stalkPt B _ ≫ j ≫ genStr Z = spMap φA := stalkPt_genStr B e j hj _ φA hfA.2.1
  have hx'' : spMap (Scheme.stalkClosedPointTo (R := .of K) x).hom ≫ stalkPt B (x (IsLocalRing.closedPoint K)) = x :=
    spMap_stalkClosedPointTo x
  obtain ⟨χ, hχ⟩ : ∃ χ : c.F →+* K, x ≫ j ≫ genStr Z = spMap χ := ⟨_, (Spec.map_preimage _).symm⟩
  have hχ' : χ = (Scheme.stalkClosedPointTo (R := .of K) x).hom.comp φA := by
    apply spMap_inj'
    rw [← hχ]
    conv_lhs => rw [← hx'']
    simp only [Category.assoc]
    rw [hst]
    exact (Spec.map_comp _ _).symm
  have hSA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ φA _ fA inferInstance
  have hxg : x ≫ j ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) x).hom ≫
      (stalkPt B (x (IsLocalRing.closedPoint K)) ≫ j ≫ genι Z) := by
    conv_lhs => rw [← hx'']
    simp only [Category.assoc]
  obtain ⟨g, hg⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φA _ fA K χ _ _ inferInstance hSA hxg hχ').2 h
    fun τ => (hh τ).2.1.isUnit
  refine (existsUnique_congr fun p => and_congr_right fun hp => ?_).2 (hL K χ x hχ g)
  subst hp
  rw [GlobalTheory.T.carriesFlags_iff_adaptedFrame_at_image E H Dw l Xo c O β Z F e C S' A₁ K χ _ g p hT']
  constructor
  · rintro ⟨A', hA', hP⟩
    obtain ⟨φ₁, f₁, hf₁⟩ := hT'.2 _ A' hA'
    obtain ⟨hM, key⟩ := coord_iff_of_hom e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hφ p rfl g hA hfA hg hA' hf₁
    refine ⟨A', hA', φ₁, f₁, h * ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹, hf₁, (key _).2 ?_, hP⟩
    rw [mul_assoc, Mat.inv_mul hM, mul_one]
  · rintro ⟨A', hA', φ₁, f₁, h', hf₁, hh', hP⟩
    obtain ⟨hM, key⟩ := coord_iff_of_hom e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hφ p rfl g hA hfA hg hA' hf₁
    refine ⟨A', hA', ?_⟩
    rw [(key h').1 hh', mul_assoc, Mat.mul_inv hM, mul_one]
    exact hP

end Lifts

end GlobalTheory.ShFam.FieldLift

namespace GlobalTheory.ShFam.FieldLift

open MvPolynomial GlobalTheory.ProjVar GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem lifts_of_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → (∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), ∀ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat Dw.mult K, Par 0 ⊤ h → ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ Bears E' φ A h p := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j _ hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC _ K _ x A hA h hh
  haveI : CharZero F := (RingHom.charZero_iff e.toRingHom.injective).2 inferInstance
  obtain ⟨ρ, -⟩ : ∃ ρ : F →+* K, x ≫ X.str = spMap ρ := ⟨_, (Spec.map_preimage _).symm⟩
  haveI : CharZero K := (RingHom.charZero_iff ρ.injective).1 inferInstance
  have hcl := lifts_closed e C X j f₀ Eb A₀ E' A₁ φ f hj hπ.symm hT hT' hC hφ hL (AlgebraicClosure K)
    (spMap (algebraMap K (AlgebraicClosure K)) ≫ x) A (by rwa [GlobalTheory.FieldPts.comp_closedPoint])
    (h.map (algebraMap K (AlgebraicClosure K))) (hh.map _ fun _ _ => trivial)
  obtain ⟨q, ⟨hq1, hq2⟩, hqu⟩ := hcl
  have hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      spMap (σ : AlgebraicClosure K →+* AlgebraicClosure K) ≫ q = q := by
    intro σ
    have hσι : (σ : AlgebraicClosure K →+* AlgebraicClosure K).comp (algebraMap K (AlgebraicClosure K)) =
        algebraMap K (AlgebraicClosure K) := RingHom.ext fun a => σ.commutes a
    refine hqu _ ⟨?_, ?_⟩
    · rw [Category.assoc, hq1, ← Category.assoc, GlobalTheory.FieldPts.spMap_comp', hσι]
    · have e1 : (h.map (algebraMap K (AlgebraicClosure K))).map (σ : AlgebraicClosure K →+* AlgebraicClosure K) =
          h.map (algebraMap K (AlgebraicClosure K)) := by
        funext τ
        ext i k
        exact σ.commutes _
      rw [← e1]
      exact (GlobalTheory.FieldPts.bears_spMap_iff E' φ A (σ : AlgebraicClosure K →+* AlgebraicClosure K) _ q).2 hq2
  obtain ⟨p, hp⟩ := GlobalTheory.FieldPts.exists_of_fixed q hfix
  refine ⟨p, ⟨GlobalTheory.spec_map_field_cancel (algebraMap K (AlgebraicClosure K)) _ _ ?_,
    (GlobalTheory.FieldPts.bears_spMap_iff E' φ A (algebraMap K (AlgebraicClosure K)) h p).1 (hp ▸ hq2)⟩, ?_⟩
  · rw [← Category.assoc, hp, hq1]
  · rintro p' ⟨h1, h2⟩
    refine GlobalTheory.spec_map_field_cancel (algebraMap K (AlgebraicClosure K)) _ _ ?_
    rw [hp]
    exact hqu _ ⟨by rw [Category.assoc, h1], (GlobalTheory.FieldPts.bears_spMap_iff E' φ A _ h p').2 h2⟩

end GlobalTheory.ShFam.FieldLift
