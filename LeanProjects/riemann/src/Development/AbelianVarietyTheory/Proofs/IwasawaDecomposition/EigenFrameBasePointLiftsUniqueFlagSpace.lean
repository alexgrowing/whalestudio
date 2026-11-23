import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriesFlagsIffAdaptedFrameAtImageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesCompStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F]

theorem spMap_inj' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have h1 : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h1

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem stalkPt_genStr (B : GlobalTheory.ProjVar.Var F) (e : F ≃+* c.F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (z : B.X) (φA : c.F →+* B.X.presheaf.stalk z)
    (hφ : constF e B = (algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp φA) :
    stalkPt B z ≫ j ≫ genStr Z = spMap φA := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (stalkPt B z ≫ j ≫ genStr Z)
  have hgen : spMap (algebraMap (B.X.presheaf.stalk z) B.X.functionField) ≫ stalkPt B z = genericPt B :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec B.X).specializes trivial)
  have hpt : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := (ratOf B).pt_s
  have key : ((algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ.hom).comp e.toRingHom =
      algebraMap F B.Fn := by
    apply spMap_inj'
    rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, ← hpt, ← hj, ← hgen,
      show spMap ψ.hom = stalkPt B z ≫ j ≫ genStr Z from hψ]
    simp only [Category.assoc]
  have hψeq : ψ.hom = φA := by
    ext a
    apply IsFractionRing.injective (B.X.presheaf.stalk z) B.X.functionField
    have e1 := RingHom.congr_fun key (e.symm a)
    have e2 := RingHom.congr_fun hφ a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at e1
    simp only [constF, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at e2
    exact e1.trans e2
  rw [← hψ, ← hψeq]
  try rfl

private theorem coord_unique' {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x}
    {ψ₁ ψ₂ : R →+* R'} {g : EigFrame Z φ' x'} {M₁ M₂ : Mat Dw.mult R'} (hψ : ψ₁ = ψ₂)
    (h₁ : f.Coord ψ₁ g M₁) (h₂ : f.Coord ψ₂ g M₂) : M₁ = M₂ := by
  subst hψ
  obtain ⟨hx, hφ, -⟩ := id h₁
  exact ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ ψ₁ inferInstance
    (GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing _ _ _ _ _ _ _ _ _ _ _ _ f inferInstance) hx hφ).1 g).1.unique h₁ h₂

private theorem coord_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [IsLocalRing R'']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X}
    {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} {k : EigFrame Z φ'' x''}
    {ψ : R →+* R'} {ψ' : R' →+* R''} {M : Mat Dw.mult R'} {M' : Mat Dw.mult R''}
    (h₁ : f.Coord ψ g M) (h₂ : g.Coord ψ' k M') : f.Coord (ψ'.comp ψ) k (M' * M.map ψ') :=
  GlobalTheory.T.lie_eigenspace_frame_coordinates_comp _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ g _ _ _ k ψ ψ' M M' inferInstance h₁ h₂

private theorem exists_coord_unit_det_of_baseChange {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} (f : EigFrame Z φ x)
    (ψ : R →+* R') (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (g : EigFrame Z φ' x') :
    ∃ M : Mat Dw.mult R', f.Coord ψ g M ∧ ∀ τ, IsUnit (M τ).det := by
  have H := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible _ _ _ _ _ _ _ _ _ _ _ _ f _ _ _ ψ inferInstance
    (GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing _ _ _ _ _ _ _ _ _ _ _ _ f inferInstance) hx hφ).1 g
  obtain ⟨M, hM, -⟩ := H.1
  exact ⟨M, hM, H.2 M hM⟩

section Lifts

variable (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
  (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn)
  (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X)

theorem coord_iff (hπ : C.π = f ≫ j) (hT : Tied e B j f₀ S A₀) (hT' : Tied e C.Y C.π C.f0 S' A₁)
    (hC : f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹)) (hR : Refines S S' φ f)
    {K : Type} [Field K] {χ : c.F →+* K} {x : Sp K ⟶ gen Z} (p : Sp K ⟶ C.Y.X) (hx : (p ≫ f) ≫ j = x)
    (g : EigFrame Z χ (x ≫ genι Z))
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
  obtain ⟨hA₀g, -⟩ := id hT
  obtain ⟨hA₁g, -⟩ := id hT'
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hA₁g
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := by
    intro τ
    have e0 : ((A₀.map φ) τ).det = (φ : B.Fn →+* C.Y.Fn) (A₀ τ).det :=
      (RingHom.map_det (φ : B.Fn →+* C.Y.Fn) (A₀ τ)).symm
    rw [e0]
    exact (map_ne_zero _).2 (Fr.det_ne hA₀g τ)
  have hσ : (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField).comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom =
      (φ : B.Fn →+* C.Y.Fn).comp (algebraMap (B.X.presheaf.stalk (f (p (IsLocalRing.closedPoint K)))) B.X.functionField) := by
    ext a
    exact (map_algebraMap_stalk hR.hom _ a).symm
  have hxC : stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z =
      spMap (f.stalkMap (p (IsLocalRing.closedPoint K))).hom ≫ (stalkPt B (f (p (IsLocalRing.closedPoint K))) ≫ j ≫ genι Z) := by
    rw [hπ]
    show C.Y.X.fromSpecStalk _ ≫ (f ≫ j) ≫ genι Z =
      Spec.map (f.stalkMap _) ≫ B.X.fromSpecStalk _ ≫ j ≫ genι Z
    simp only [Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  obtain ⟨-, hφf₁, -⟩ := id hf₁
  obtain ⟨-, hφfA, -⟩ := id hfA
  have hφ₁ : φ₁ = (f.stalkMap (p (IsLocalRing.closedPoint K))).hom.comp φA := by
    ext a
    apply IsFractionRing.injective (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField
    have e1 := RingHom.congr_fun hφf₁ a
    have e2 := RingHom.congr_fun hφfA a
    have e3 := RingHom.congr_fun hσ (φA a)
    simp only [RingHom.comp_apply] at e1 e2 e3 ⊢
    rw [← e1, e3, ← e2]
    simp [constF]
  obtain ⟨N, hN, hNu⟩ := exists_coord_unit_det_of_baseChange fA (f.stalkMap (p (IsLocalRing.closedPoint K))).hom hxC hφ₁ f₁
  have h2 := coord_comp' hfA hC
  have h4 := coord_comp' hN hf₁
  have h5 := coord_unique' hσ h4 h2
  rw [Mat.map_mul, Mat.map_inv] at h5
  try simp only [AlgHom.coe_toRingHom] at h5
  have hNeq : N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = A' * (A.map φ)⁻¹ := by
    calc N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) = (A' * A₁⁻¹) * (A₁ * A'⁻¹ * N.map (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField)) := by
          simp only [← mul_assoc]
          rw [mul_assoc A' A₁⁻¹ A₁, Mat.inv_mul hA₁d, mul_one, Mat.mul_inv hA'd, one_mul]
      _ = (A' * A₁⁻¹) * (A₁ * (A₀.map φ)⁻¹ * (A₀.map φ * (A.map φ)⁻¹)) := by rw [h5]
      _ = A' * (A.map φ)⁻¹ := by
          simp only [← mul_assoc]
          rw [mul_assoc A' A₁⁻¹ A₁, Mat.inv_mul hA₁d, mul_one, mul_assoc A' (A₀.map φ)⁻¹ (A₀.map φ),
            Mat.inv_mul hA₀φ, mul_one]
  have hval : ∀ n : C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K)),
      (ratOf C.Y).val p ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n) = (Scheme.stalkClosedPointTo (R := .of K) p).hom n := by
    intro n
    calc (ratOf C.Y).val p ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n)
        = (ratOf C.Y).val (spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ C.Y.X.fromSpecStalk (p (IsLocalRing.closedPoint K))) ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n) := by
          exact congrArg (fun q : Sp K ⟶ C.Y.X => (ratOf C.Y).val q ((algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) n))
            (spMap_stalkClosedPointTo p).symm
      _ = (Scheme.stalkClosedPointTo (R := .of K) p).hom n := val_ratOf _ _
  have hM : (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) = N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    rw [← hNeq]
    funext τ
    ext a b
    exact hval (N τ a b)
  have hdetN : ∀ τ, ((N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det ≠ 0 := by
    intro τ
    have e0 : ((N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom) τ).det = (Scheme.stalkClosedPointTo (R := .of K) p).hom (N τ).det := (RingHom.map_det (Scheme.stalkClosedPointTo (R := .of K) p).hom (N τ)).symm
    rw [e0]
    exact ((hNu τ).map _).ne_zero
  have hdetM : ∀ τ, (((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p)) τ).det ≠ 0 := by
    rw [hM]; exact hdetN
  have hev : (Scheme.stalkClosedPointTo (R := .of K) (p ≫ f)).hom = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp (f.stalkMap (p (IsLocalRing.closedPoint K))).hom := by
    rw [Scheme.stalkClosedPointTo_comp]; try rfl
  have fwd : ∀ h' : Mat Dw.mult K, f₁.Coord (Scheme.stalkClosedPointTo (R := .of K) p).hom g h' → h = h' * N.map (Scheme.stalkClosedPointTo (R := .of K) p).hom := by
    intro h' hh'
    exact coord_unique' hev hh (coord_comp' hN hh')
  obtain ⟨hxg, hχ, -⟩ := id hh
  have hxg' : x ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) p).hom ≫ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z) := by
    rw [hxC, hxg, hev, spMap_comp_moduli_spaces, Category.assoc]
  have hχ' : χ = (Scheme.stalkClosedPointTo (R := .of K) p).hom.comp φ₁ := by
    rw [hχ, hev, hφ₁, RingHom.comp_assoc]
  obtain ⟨h'', hh'', -⟩ := exists_coord_unit_det_of_baseChange f₁ (Scheme.stalkClosedPointTo (R := .of K) p).hom hxg' hχ' g
  refine ⟨hdetM, fun h' => ⟨fun hh' => ?_, fun heq => ?_⟩⟩
  · rw [fwd h' hh', hM]
  · have e1 := fwd h'' hh''
    rw [← hM] at e1
    have e2 : h'' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) =
        h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) := e1.symm.trans heq
    have e3 : h'' = h' := by
      calc h'' = h'' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) *
            ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹ := by rw [mul_assoc, Mat.mul_inv hdetM, mul_one]
        _ = h' * (A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p) *
            ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val p))⁻¹ := by rw [e2]
        _ = h' := by rw [mul_assoc, Mat.mul_inv hdetM, mul_one]
    rw [← e3]
    exact hh''

end Lifts

theorem flagex_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn) (S' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn) (φ : B.Fn →ₐ[F] C.Y.Fn) (f : C.Y.X ⟶ B.X), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → C.π = f ≫ j → Tied e B j f₀ S A₀ → Tied e C.Y C.π C.f0 S' A₁ → f₀.Coord (φ : B.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → Refines S S' φ f → ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x → x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C B j f₀ S A₀ S' A₁ φ f hj hπ hT hT' hC hR K _ χ x x' hx' hxs g
  obtain ⟨A, hA⟩ := S.nonempty (x' (IsLocalRing.closedPoint K))
  obtain ⟨-, hTie⟩ := id hT
  obtain ⟨φA, fA, hfA⟩ := hTie _ A hA
  have hx'f : spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K)) = x' := spMap_stalkClosedPointTo x'
  obtain ⟨-, hφA, -⟩ := id hfA
  have hsg := stalkPt_genStr B e j hj (x' (IsLocalRing.closedPoint K)) φA hφA
  have hχ : χ = (Scheme.stalkClosedPointTo (R := .of K) x').hom.comp φA := by
    apply spMap_inj'
    calc spMap χ = x ≫ genStr Z := hxs.symm
      _ = (x' ≫ j) ≫ genStr Z := by rw [hx']
      _ = ((spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K))) ≫ j) ≫ genStr Z := by rw [hx'f]
      _ = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ (stalkPt B (x' (IsLocalRing.closedPoint K)) ≫ j ≫ genStr Z) := by simp only [Category.assoc]
      _ = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ spMap φA := by rw [hsg]
      _ = spMap ((Scheme.stalkClosedPointTo (R := .of K) x').hom.comp φA) := (spMap_comp_moduli_spaces _ _).symm
  have hxg : x ≫ genι Z = spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ (stalkPt B (x' (IsLocalRing.closedPoint K)) ≫ j ≫ genι Z) := by
    calc x ≫ genι Z = (x' ≫ j) ≫ genι Z := by rw [hx']
      _ = ((spMap (Scheme.stalkClosedPointTo (R := .of K) x').hom ≫ stalkPt B (x' (IsLocalRing.closedPoint K))) ≫ j) ≫ genι Z := by rw [hx'f]
      _ = _ := by simp only [Category.assoc]
  obtain ⟨h, hh, hu⟩ := exists_coord_unit_det_of_baseChange fA (Scheme.stalkClosedPointTo (R := .of K) x').hom hxg hχ g
  have hPar : Par (0 : (E →+* ℂ) → ℕ) ⊤ h := fun τ =>
    ⟨fun _ _ => Subring.mem_top _, (hu τ).ne_zero, Subring.mem_top _, fun i _ hi => by simp at hi⟩
  obtain ⟨p, ⟨hp1, hp2⟩, huniq⟩ := hR.lifts K x' A hA h hPar
  obtain ⟨-, hTie'⟩ := id hT'
  have key : ∀ q : Sp K ⟶ C.Y.X, q ≫ f = x' → (Bears S' φ A h q ↔ C.Carries q g) := by
    intro q hq
    subst hq
    rw [GlobalTheory.T.carriesFlags_iff_adaptedFrame_at_image _ _ _ _ _ _ _ _ _ _ e C S' A₁ K χ (x ≫ genι Z) g q hT']
    constructor
    · rintro ⟨A', hA', hPar'⟩
      obtain ⟨φ₁, f₁, hf₁⟩ := hTie' _ A' hA'
      have hci := coord_iff e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hR q hx' g hA hfA hh hA' hf₁
      refine ⟨A', hA', φ₁, f₁, h * ((A' * (A.map φ)⁻¹).map ((ratOf C.Y).val q))⁻¹, hf₁, ?_, hPar'⟩
      rw [hci.2, mul_assoc, Mat.inv_mul hci.1, mul_one]
    · rintro ⟨A', hA', φ₁, f₁, h', hf₁, hh', hPar'⟩
      have hci := coord_iff e C B j f₀ S A₀ S' A₁ φ f hπ hT hT' hC hR q hx' g hA hfA hh hA' hf₁
      refine ⟨A', hA', ?_⟩
      rw [(hci.2 h').1 hh', mul_assoc, Mat.mul_inv hci.1, mul_one]
      exact hPar'
  exact ⟨p, ⟨hp1, (key p hp1).1 hp2⟩, fun q hq => huniq q ⟨hq.1, (key q hq.1).2 hq.2⟩⟩

end GlobalTheory.ShFam
