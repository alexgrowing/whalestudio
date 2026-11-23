import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesCompStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.TieBase

theorem spMap_trans {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_affine_factor {Y : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (h : x (IsLocalRing.closedPoint R) ∈ U) :
    ∃ ψ : Γ(Y, U) →+* R, spMap ψ ≫ hU.fromSpec = x := by
  obtain ⟨ψ, hψ⟩ := EigLoc.exists_stalk_factor x _ (specializes_refl _)
  refine ⟨ψ.comp (Y.presheaf.germ U _ h).hom, ?_⟩
  have hg : spMap (Y.presheaf.germ U _ h).hom ≫ hU.fromSpec = Y.fromSpecStalk _ := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk h]; rfl
  rw [spMap_trans, Category.assoc, hg, hψ]

theorem par_zero_iff {ι : Type} {m : ι → ℕ} {R K : Type} [CommRing R] [Field K] (a : R →+* K)
    (ha : Function.Injective a) (O : Subring K) (hO : ∀ x, x ∈ O ↔ ∃ r, a r = x) (P : Mat m K) :
    Par 0 O P ↔ ∃ G : Mat m R, (∀ τ, IsUnit (G τ).det) ∧ P = G.map a := by
  constructor
  · intro hP
    have hent : ∀ τ i j, ∃ r, a r = P τ i j := fun τ i j => (hO _).1 ((hP τ).1 i j)
    choose G₀ hG using hent
    let G : Mat m R := fun τ => Matrix.of (G₀ τ)
    have hGP : P = G.map a := by
      funext τ i j
      exact (hG τ i j).symm
    refine ⟨G, fun τ => ?_, hGP⟩
    obtain ⟨s, hs⟩ := (hO _).1 (hP τ).2.2.1
    have hdet : a (G τ).det = (P τ).det := by
      rw [hGP]
      exact RingHom.map_det a (G τ)
    refine isUnit_iff_exists_inv.2 ⟨s, ha ?_⟩
    rw [map_mul, hdet, hs, map_one, mul_inv_cancel₀ (hP τ).2.1]
  · rintro ⟨G, hG, rfl⟩ τ
    have hdet : (G.map a τ).det = a (G τ).det := (RingHom.map_det a (G τ)).symm
    obtain ⟨u, hu⟩ := hG τ
    refine ⟨fun i j => (hO _).2 ⟨G τ i j, rfl⟩, ?_, ?_, fun i j hi _ => absurd hi (Nat.not_lt_zero _)⟩
    · rw [hdet, ← hu]
      exact (u.isUnit.map a).ne_zero
    · rw [hdet, ← hu]
      exact (hO _).2 ⟨((u⁻¹ : Rˣ) : R), by rw [map_units_inv]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem frames_iff {R R₁ K : Type} [CommRing R] [CommRing R₁] [IsLocalRing R₁] [Field K] {φ : c.F →+* R}
    {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x) (hf : f.Stable) (ψ : R →+* R₁) (a : R₁ →+* K) (ha : Function.Injective a)
    {x₁ : Sp R₁ ⟶ Z.X} (hx : x₁ = spMap ψ ≫ x) {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} (f₀ : EigFrame Z φ₀ x₀)
    {T : Mat Dw.mult K} (hT : f.Coord (a.comp ψ) f₀ T) (A : Mat Dw.mult K) :
    ((∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ₁ : c.F →+* R₁) (g : EigFrame Z φ₁ x₁), g.Coord a f₀ A⁻¹) ↔
      ∃ G : Mat Dw.mult R₁, (∀ τ, IsUnit (G τ).det) ∧ A * T = G.map a := by
  have hU := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f K φ₀ x₀ (a.comp ψ) inferInstance hf hT.1 hT.2.1).1 f₀
  have huniq : ∀ B, f.Coord (a.comp ψ) f₀ B → B = T := fun B hB => hU.1.unique hB hT
  constructor
  · rintro ⟨hA, φ₁, g, hg⟩
    have hφ₁ : φ₁ = ψ.comp φ := by
      apply RingHom.ext
      intro r
      apply ha
      have h := RingHom.congr_fun (hg.2.1.symm.trans hT.2.1) r
      simpa using h
    subst hφ₁
    obtain ⟨hE, hunits⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ ψ inferInstance hf hx rfl).1 g
    obtain ⟨G, hG, -⟩ := hE
    refine ⟨G, hunits G hG, ?_⟩
    have hc := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ g K φ₀ x₀ f₀ ψ a G A⁻¹ inferInstance hG hg
    rw [← huniq _ hc, ← mul_assoc, Mat.mul_inv hA, one_mul]
  · rintro ⟨G, hG, hAT⟩
    obtain ⟨g, hfg⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ ψ inferInstance hf hx rfl).2 G hG
    have hgs : g.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z R₁ (ψ.comp φ) x₁ g inferInstance
    have hx₀ : x₀ = spMap a ≫ x₁ := by rw [hT.1, hx, spMap_trans, Category.assoc]
    have hφ₀ : φ₀ = a.comp (ψ.comp φ) := hT.2.1.trans (RingHom.comp_assoc _ _ _)
    obtain ⟨⟨B, hB, -⟩, -⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z R₁ (ψ.comp φ) x₁ g K φ₀ x₀ a inferInstance hgs hx₀ hφ₀).1 f₀
    have hc := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z R φ x f R₁ (ψ.comp φ) x₁ g K φ₀ x₀ f₀ ψ a G B inferInstance hfg hB
    have hTB : B * G.map a = T := huniq _ hc
    have hGd : ∀ τ, (G.map a τ).det ≠ 0 := fun τ => by
      have h := ((hG τ).map a).ne_zero
      rw [RingHom.map_det] at h
      exact h
    have hAB : A * B = 1 := by
      calc A * B = A * B * (G.map a * (G.map a)⁻¹) := by rw [Mat.mul_inv hGd, mul_one]
      _ = A * (B * G.map a) * (G.map a)⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hTB, hAT, Mat.mul_inv hGd]
    have hAτ : ∀ τ, A τ * B τ = 1 := fun τ => congrFun hAB τ
    have hAd : ∀ τ, (A τ).det ≠ 0 := fun τ hd => by
      have h := congrArg Matrix.det (hAτ τ)
      rw [Matrix.det_mul, hd, zero_mul, Matrix.det_one] at h
      exact zero_ne_one h
    have hAi : A⁻¹ = B := funext fun τ => Matrix.inv_eq_right_inv (hAτ τ)
    refine ⟨hAd, ψ.comp φ, g, ?_⟩
    rw [hAi]
    exact hB

variable {F : Type} [Field F]

theorem genericPt_eq (B : GlobalTheory.ProjVar.Var F) (y : B.X) :
    genericPt B = spMap (algebraMap (B.X.presheaf.stalk y) B.X.functionField) ≫ stalkPt B y := by
  unfold genericPt stalkPt
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)]
  rfl

theorem genericPt_str (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) : (genericPt B ≫ j) ≫ genStr Z = spMap (constF e B) := by
  have hs : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := by
    apply ext_of_isAffine
    unfold genericPt spMap
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_mono (Scheme.ΓSpecIso _).hom,
      Scheme.ΓSpecIso_naturality]
    ext a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [IsScalarTower.algebraMap_apply F Γ(B.X, ⊤) B.Fn, GlobalTheory.ProjVar.Var.algebraMap_Γ,
      GlobalTheory.Cartier.CartierDiv.algebraMap_top, CommRingCat.inv_hom_apply]
    have hmap : (Spec (B.X.presheaf.stalk (genericPoint B.X))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (B.X.presheaf.stalk (genericPoint B.X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : (Spec (B.X.presheaf.stalk (genericPoint B.X))).Opens) ≤ ⊤)) = 𝟙 _ from rfl]
      exact CategoryTheory.Functor.map_id _ _
    rw [hmap, CommRingCat.hom_id, RingHom.id_apply]
    exact CommRingCat.hom_inv_apply _ _
  have hid : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← spMap_trans, RingEquiv.toRingHom_comp_symm_toRingHom]
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
  unfold constF
  rw [spMap_trans, ← hs, ← hj]
  simp only [Category.assoc, hid, Category.comp_id]

def fam (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) :
    Fr (ratOf B) Dw.mult 0 where
  S (y : B.X) := {A | (∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk y)
    (f : EigFrame Z φ (stalkPt B y ≫ j ≫ genι Z)),
    f.Coord (algebraMap (B.X.presheaf.stalk y) B.X.functionField) f₀ A⁻¹}
  loc (z : B.X) := by
    obtain ⟨U, hU, φ, f, hz, hφ, hf⟩ := GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame E H Dw l Xo c O β Z (j z)
    have key : ∀ y : B.X, j y ∈ U → ∃ ψ : Γ(gen Z, U) →+* B.X.presheaf.stalk y,
        spMap ψ ≫ hU.fromSpec = stalkPt B y ≫ j := fun y hy =>
      exists_affine_factor _ hU (by
        show j (B.X.fromSpecStalk y (IsLocalRing.closedPoint _)) ∈ U
        rw [Scheme.fromSpecStalk_closedPoint]; exact hy)
    have key' : ∀ (y : B.X) (ψ : Γ(gen Z, U) →+* B.X.presheaf.stalk y), spMap ψ ≫ hU.fromSpec = stalkPt B y ≫ j →
        spMap ((algebraMap (B.X.presheaf.stalk y) B.X.functionField).comp ψ) ≫ hU.fromSpec = genericPt B ≫ j :=
      fun y ψ h => by rw [spMap_trans, Category.assoc, h, genericPt_eq B y, Category.assoc]
    obtain ⟨ψ₀, hψ₀⟩ := key z hz
    have h₀ := key' z ψ₀ hψ₀
    obtain ⟨⟨T, hT, -⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ φ _ f B.Fn (constF e B) (genericPt B ≫ j ≫ genι Z)
      ((algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ₀) inferInstance hf
      (by rw [← Category.assoc, ← h₀, Category.assoc])
      (EigLoc.spMap_inj (by rw [← genericPt_str e B j hj, ← h₀, Category.assoc, hφ, ← spMap_trans]))).1 f₀
    have hTd : ∀ τ, (T τ).det ≠ 0 := fun τ => (hu T hT τ).ne_zero
    refine ⟨j ⁻¹ᵁ U, T⁻¹, hz, fun τ => ?_, fun (y : B.X) hy A => ?_⟩
    · exact (Matrix.isUnit_det_of_right_inverse (congrFun (Mat.inv_mul hTd) τ)).ne_zero
    · obtain ⟨ψ, hψ⟩ := key y hy
      have e1 : (algebraMap (B.X.presheaf.stalk z) B.X.functionField).comp ψ₀ =
          (algebraMap (B.X.presheaf.stalk y) B.X.functionField).comp ψ :=
        EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 (h₀.trans (key' y ψ hψ).symm))
      rw [e1] at hT
      have ha : Function.Injective (algebraMap (B.X.presheaf.stalk y) B.X.functionField) :=
        IsFractionRing.injective _ _
      rw [Mat.inv_inv hTd]
      refine (frames_iff f hf ψ _ ha (by rw [← Category.assoc, ← hψ, Category.assoc]) f₀ hT A).trans
        (par_zero_iff _ ha _ (fun x => mem_O_ratOf (Y := B) (y := y) (g := x)) _).symm

end GlobalTheory.ShFam.TieBase

open GlobalTheory.ShFam.TieBase in

theorem GlobalTheory.ShFam.TieBase.exists_tied : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∃ (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn), Tied e B j f₀ S A₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e B j hj
  have hx : (genericPt B ≫ j) ≫ genι Z = genericPt B ≫ j ≫ genι Z := Category.assoc _ _ _
  obtain ⟨f₀⟩ : Nonempty (EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) := by
    rw [← hx]
    exact EigLoc.exists_eigFrame E H Dw l Xo c O β Z B.Fn (constF e B) (genericPt B ≫ j) (genericPt_str e B j hj)
  refine ⟨f₀, fam e B j hj f₀, 1, ?_⟩
  unfold GlobalTheory.ShFam.Tied
  refine ⟨?_, ?_⟩
  · have hst : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ inferInstance
    have hsp : spMap (RingHom.id B.Fn) = 𝟙 _ := by simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    obtain ⟨⟨A₁, hA₁, huq⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ B.Fn (constF e B) _
      (RingHom.id B.Fn) inferInstance hst (by rw [hsp, Category.id_comp]) (RingHom.id_comp _).symm).1 f₀
    have h2 := GlobalTheory.T.lie_eigenspace_frame_coordinates_comp E H Dw l Xo c O β Z B.Fn (constF e B) _ f₀ B.Fn (constF e B) _ f₀ B.Fn (constF e B) _ f₀
      (RingHom.id B.Fn) (RingHom.id B.Fn) A₁ A₁ inferInstance hA₁ hA₁
    have hm : A₁.map (RingHom.id B.Fn) = A₁ := by
      funext τ i j
      rfl
    rw [RingHom.id_comp, hm] at h2
    have hsq : A₁ * A₁ = A₁ := huq _ h2
    have hdet : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => (hu A₁ hA₁ τ).ne_zero
    have h1 : A₁ = 1 := by
      calc A₁ = A₁⁻¹ * (A₁ * A₁) := by rw [← mul_assoc, Mat.inv_mul hdet, one_mul]
      _ = 1 := by rw [hsq, Mat.inv_mul hdet]
    have hinv : (1 : Mat Dw.mult B.Fn)⁻¹ = 1 := funext fun τ => by simp
    have halg : @algebraMap (B.X.presheaf.stalk (genericPoint B.X)) B.X.functionField _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra (X := B.X) (genericPoint B.X)) = RingHom.id _ := by
      ext r
      show (B.X.presheaf.stalkSpecializes _).hom r = r
      rw [TopCat.Presheaf.stalkSpecializes_refl]
      rfl
    show (∀ τ, ((1 : Mat Dw.mult B.Fn) τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk (genericPoint B.X))
      (f : EigFrame Z φ (stalkPt B (genericPoint B.X) ≫ j ≫ genι Z)),
      f.Coord (@algebraMap (B.X.presheaf.stalk (genericPoint B.X)) B.X.functionField _ _
        (AlgebraicGeometry.stalkFunctionFieldAlgebra (X := B.X) (genericPoint B.X))) f₀ (1 : Mat Dw.mult B.Fn)⁻¹
    refine ⟨fun τ => by simp, constF e B, f₀, ?_⟩
    rw [halg, hinv, ← h1]
    exact hA₁
  · intro y A hA
    have hA' : (∀ τ, (A τ).det ≠ 0) ∧ ∃ (φ : c.F →+* B.X.presheaf.stalk y)
        (f : EigFrame Z φ (stalkPt B y ≫ j ≫ genι Z)),
        f.Coord (algebraMap (B.X.presheaf.stalk y) B.X.functionField) f₀ A⁻¹ := hA
    obtain ⟨-, φ, f, hf⟩ := hA'
    exact ⟨φ, f, by rw [one_mul]; exact hf⟩

end
