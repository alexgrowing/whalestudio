import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.PicSpec

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  Eq.symm (NatTrans.naturality_apply φ.hom g.op x)

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (ψ : F ⟶ G) (φ : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map φ (Sec.map ψ x) = Sec.map (ψ ≫ φ) x := rfl

theorem sec_eq_zero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  simpa [Sec.map] using this

theorem res_isZero {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs

theorem resι_d {R : Type} [CommRing R] (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  unfold resι res
  rw [Category.assoc, (injectiveResolution F).ι'.comm 0 1]
  simp

theorem unitSec_mul {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec ofRings.sec
  exact map_add (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom)
    (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

theorem unitSec_res {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  unfold unitSec ofRings.sec
  have := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).naturality g.op
  have h2 := congrArg (fun f => f.hom (show (Scheme.Γ ⋙ unitsF).obj (op U) from ULift.up (Additive.ofMul u))) this
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2.symm

theorem glMat_map {U V : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) =
      Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem generalLinearGroup_det_map_fin_one {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : GL (Fin 1) A) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f M) =
      Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det M) := by
  ext
  simp [RingHom.map_det]

theorem glMat_δ1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (((ofCat (glCat 1)).δ 1).app (op U) y) =
      glMat (((ofCat (glCat 1)).δ 0).app (op U) y) * glMat (((ofCat (glCat 1)).δ 2).app (op U) y) := by
  have h : ((show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 2) =
      (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 0 1 ≫
        (show ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 from y).map' 1 2 :=
    ComposableArrows.map'_comp _ 0 1 2
  exact h

theorem face_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) (i : Fin 3) :
    (L.app (op (SimplexCategory.mk 1))).app (op U) ((E.δ i).app (op U) x) =
      ((ofCat (glCat 1)).δ i).app (op U) ((L.app (op (SimplexCategory.mk 2))).app (op U) x) := by
  have := ConcreteCategory.congr_hom (NatTrans.congr_app (SimplicialObject.δ_naturality L i) (op U)) x
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  exact this

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  rw [NatTrans.naturality_apply (L.app (op (SimplexCategory.mk 1))) g.op x, glMat_map, generalLinearGroup_det_map_fin_one]

theorem lineUnit_face {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.face 0) * lineUnit L (x.face 2) := by
  unfold lineUnit Sx.face
  rw [face_nat, face_nat, face_nat, glMat_δ1, map_mul]

def fam {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res ℤ Gm).X s) U
  | 1, s, h, _, x => Sec.map ((res ℤ Gm).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
  | _, _, _, _, _ => 0

theorem fam_zero {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0})
    (x : Sx E 0 U) : fam L 0 s h U x = 0 := rfl

theorem fam_add_two {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -((p + 2 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E (p + 2) U) : fam L (p + 2) s h U x = 0 := rfl

theorem fam_one {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : fam L 1 0 h U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  simp [fam, Sec.map]

theorem fam_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0})
    (g : V ⟶ U) (x : Sx E p U) : Sec.res g (fam L p s h U x) = fam L p s h V (x.res g) := by
  match p with
  | 0 => simp [fam_zero]
  | 1 =>
    simp only [fam]
    rw [sec_map_res, sec_map_res, unitSec_res, lineUnit_res]
  | p + 2 => simp [fam_add_two]

theorem sec_map_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add _ _ _

theorem ev_zero_cochain {E : Spc} {I : Cx ℤ} {n : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (0 : Cochain ((chains ℤ).obj E) I n) p s h U x = 0 :=
  ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).1 0 0 p s h U x).2.2.1

theorem fam_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) (α : Cochain ((chains ℤ).obj E) (res ℤ Gm) 1)
    (hα : ∀ p s h U x, ev α p s h U x = fam L p s h U x) : δ 1 2 α = 0 := by
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).2.2.1
  intro p t ht U x
  rw [ev_zero_cochain]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values ℤ (by norm_num) α U).1 x, hα, fam_zero, sec_map_zero]
  | 1 =>
    obtain rfl : t = 1 := by omega
    have key : ev (δ 1 2 α) 1 1 ht U x = Sec.map ((res ℤ Gm).d 0 1) (ev α 1 0 (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ev α 0 1 (by simp) U (x.face i) :=
      (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values ℤ (by norm_num) α U).2 0 0 1 (by simp) ht x
    rw [key]
    simp only [hα, fam_zero, fam_one, smul_zero, Finset.sum_const_zero, add_zero, sec_map_comp, resι_d]
    rfl
  | 2 =>
    obtain rfl : t = 0 := by omega
    have key : ev (δ 1 2 α) 2 0 ht U x = Sec.map ((res ℤ Gm).d (-1) 0) (ev α 2 (-1) (by simp) U x) +
        (2 : ℤ).negOnePow • ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ev α 1 0 (by simp) U (x.face i) :=
      (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values ℤ (by norm_num) α U).2 1 (-1) 0 (by simp) ht x
    rw [key]
    simp only [hα, fam_one]
    rw [show fam L 2 (-1) (by simp) U x = 0 from rfl, sec_map_zero, zero_add, Fin.sum_univ_three, lineUnit_face,
      unitSec_mul, sec_map_add]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    simp
  | p + 3 =>
    have key := (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values ℤ (by norm_num) α U).2 (p + 2) (t - 1) t (by omega) ht x
    rw [key]
    simp only [hα, fam_add_two, sec_map_zero, zero_add, smul_zero, Finset.sum_const_zero]

theorem exists_cocycle {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  obtain ⟨α, hα⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' ℤ (fam L) (fam_nat L)
  refine ⟨Cocycle.mk α 2 (by norm_num) (fam_cocycle L α hα), fun U x => ?_, fun U x => ?_⟩
  · exact (hα 0 1 _ U x).trans (fam_zero L 1 _ U x)
  · exact (hα 1 0 _ U x).trans (fam_one L _ U x)

theorem spec {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = picClass L ∧
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)) := by
  obtain ⟨γ, h0, h1⟩ := exists_cocycle L
  exact pick_spec (P := fun c => ∃ γ : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x)))
    ⟨_, γ, rfl, h0, h1⟩

theorem cocycle_ext {E : Spc} (γ γ' : Cocycle ((chains ℤ).obj E) (res ℤ Gm) 1)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 1 (by simp) U x = ev γ'.1 0 1 (by simp) U x)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 0 (by simp) U x = ev γ'.1 1 0 (by simp) U x) : γ = γ' := by
  refine Cocycle.ext ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties ℤ).2.2.1 _ _ fun p s h U x => ?_)
  match p with
  | 0 =>
    obtain rfl : s = 1 := by omega
    exact h0 U x
  | 1 =>
    obtain rfl : s = 0 := by omega
    exact h1 U x
  | p + 2 =>
    have hZ := res_isZero Gm s (by omega)
    exact (sec_eq_zero hZ _).trans (sec_eq_zero hZ _).symm

end GlobalTheory.EtC.PicSpec
