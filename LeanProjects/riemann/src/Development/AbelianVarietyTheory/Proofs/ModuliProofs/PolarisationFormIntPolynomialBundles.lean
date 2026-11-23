import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.FormPoly

open GlobalTheory.CechPic Polynomial

theorem poly_induction {p : ℤ[X] → Prop} (h1 : p 1) (hadd : ∀ F G, p F → p G → p (F + G))
    (hneg : ∀ F, p F → p (-F)) (hX : ∀ F, p F → p (X * F)) (F : ℤ[X]) : p F := by
  have h0 : p 0 := by simpa using hadd 1 (-1) h1 (hneg 1 h1)
  have hC : ∀ a : ℤ, p (Polynomial.C a) := by
    intro a
    induction a using Int.induction_on with
    | zero => simpa using h0
    | succ i ih => simpa using hadd _ _ ih h1
    | pred i ih => simpa [sub_eq_add_neg] using hadd _ _ ih (hneg 1 h1)
  have hmono : ∀ (n : ℕ) (a : ℤ), p (Polynomial.monomial n a) := by
    intro n a
    induction n with
    | zero => simpa using hC a
    | succ n ih => rw [← Polynomial.X_mul_monomial]; exact hX _ ih
  induction F using Polynomial.induction_on' with
  | add F G hF hG => exact hadd _ _ hF hG
  | monomial n a => exact hmono n a

theorem exists_apply {V : Type} [CommGroup V] (c : V → V) (hc : ∀ a b, c (a * b) = c a * c b) (v : V) :
    ∃ ev : ℤ[X] → V, ev 1 = v ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (X * F) = c (ev F) := by
  let φ : Module.End ℤ (Additive V) :=
    (AddMonoidHom.mk' (fun a => Additive.ofMul (c a.toMul)) (fun a b => by simp [hc])).toIntLinearMap
  refine ⟨fun F => (Polynomial.aeval φ F (Additive.ofMul v)).toMul, by simp, fun F G => by simp, fun F => by simp [φ]⟩

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem exists_ev (s : A ⟶ A) [IsMonHom s] : ∃ ev : ℤ[X] → (A ⟶ A), ev 1 = 𝟙 A ∧
    (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (X * F) = ev F ≫ s := by
  exact exists_apply (fun f => f ≫ s) (fun a b => MonObj.mul_comp a b s) (𝟙 A)

section Ev

variable {s : A ⟶ A} [IsMonHom s] {ev : ℤ[X] → (A ⟶ A)} (h1 : ev 1 = 𝟙 A)
  (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (X * F) = ev F ≫ s)

include hadd in
theorem ev_neg (F : ℤ[X]) : ev (-F) = (ev F)⁻¹ := by
  have h0 : ev 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  have e := hadd F (-F)
  rw [add_neg_cancel, h0] at e
  exact eq_inv_of_mul_eq_one_right e.symm

include h1 hadd hX

theorem ev_isMonHom (F : ℤ[X]) : IsMonHom (ev F) := by
  refine poly_induction (p := fun F => IsMonHom (ev F)) ?_ ?_ ?_ ?_ F
  · rw [h1]; infer_instance
  · intro F G hF hG; rw [hadd, Hom.mul_def]; infer_instance
  · intro F hF; rw [ev_neg hadd]; infer_instance
  · intro F hF; rw [hX]; infer_instance

omit [IsMonHom s] in
theorem ev_mul (F G : ℤ[X]) : ev (F * G) = ev F ≫ ev G := by
  refine poly_induction (p := fun G => ev (F * G) = ev F ≫ ev G) ?_ ?_ ?_ ?_ G
  · rw [_root_.mul_one, h1, Category.comp_id]
  · intro G H hG hH; rw [mul_add, hadd, hadd, hG, hH, MonObj.comp_mul]
  · intro G hG; rw [mul_neg, ev_neg hadd, ev_neg hadd, hG, GrpObj.comp_inv]
  · intro G hG; rw [mul_left_comm F X G, hX, hX, hG, Category.assoc]

omit [IsMonHom s] hadd in
theorem ev_X : ev X = s := by
  have e := hX 1
  rwa [_root_.mul_one, h1, Category.id_comp] at e

end Ev

variable {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)

include hΘ in
theorem lam_inv_left {T : Over S} (x y : T ⟶ A) : lam (cls L hL) x⁻¹ y = -lam (cls L hL) x y := by
  have e := lam_mul_left hL hΘ x x⁻¹ y
  rw [mul_inv_cancel, lam_one_left] at e
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact e.symm

include hΘ in
theorem lam_inv_right {T : Over S} (x y : T ⟶ A) : lam (cls L hL) x y⁻¹ = -lam (cls L hL) x y := by
  rw [lam_comm, lam_inv_left hL hΘ, lam_comm]

include hΘ in

theorem lam_ev_adj {s : A ⟶ A} {ev : ℤ[X] → (A ⟶ A)} (h1 : ev 1 = 𝟙 A)
    (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (X * F) = ev F ≫ s) {T : Over S}
    (hs : ∀ x y : T ⟶ A, lam (cls L hL) (x ≫ s) y = lam (cls L hL) x (y ≫ s)) (F : ℤ[X]) :
    ∀ x y : T ⟶ A, lam (cls L hL) (x ≫ ev F) y = lam (cls L hL) x (y ≫ ev F) := by
  have hcomm : ∀ G : ℤ[X], s ≫ ev G = ev G ≫ s := by
    intro G
    have e := ev_mul h1 hadd hX X G
    rw [ev_X h1 hX, hX] at e
    exact e.symm
  refine poly_induction (p := fun F => ∀ x y : T ⟶ A,
    lam (cls L hL) (x ≫ ev F) y = lam (cls L hL) x (y ≫ ev F)) ?_ ?_ ?_ ?_ F
  · intro x y; simp only [h1, Category.comp_id]
  · intro F G hF hG x y
    rw [hadd, MonObj.comp_mul, MonObj.comp_mul, lam_mul_left hL hΘ,
      GlobalTheory.HermTensorLB.lam_mul_right hL hΘ, hF, hG]
  · intro F hF x y
    rw [ev_neg hadd, GrpObj.comp_inv, GrpObj.comp_inv, lam_inv_left hL hΘ, lam_inv_right hL hΘ, hF]
  · intro F hF x y
    rw [hX, ← Category.assoc, hs, hF, Category.assoc, ← hcomm F]

theorem pull_one {K : Type} [Field K] {B T : Over (Sp K)} [GrpObj B] (c : Pic B.left) :
    pull (1 : T ⟶ B).left c = 0 := by
  rw [Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨N, hN, hc⟩ := cls_surj (pull η[B].left c)
  rw [← hc, (cls_eq_zero_iff hN).2 (ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local N hN), map_zero]

private theorem isLB_cube_lemma {S : Scheme.{0}} {A T : Over S} [GrpObj A] {n : ℕ} (x : Fin n → (T ⟶ A))
    {N : LB A.left} (hN : N.IsLB) : (cubeLB A x N).IsLB :=
  ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hN _ _

private theorem lam_id_lemma_2 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (c : Pic A.left)
    (hadd : ∀ x y z : A ⟶ A, lam c x (y * z) = lam c x y + lam c x z) :
    lam c (𝟙 A) (𝟙 A) = c + pull (GrpObj.inv : A ⟶ A).left c := by
  have e := hadd (𝟙 A) (𝟙 A) (𝟙 A)⁻¹
  rw [_root_.mul_inv_cancel, lam_one_right] at e
  have e2 : lam c (𝟙 A) (𝟙 A)⁻¹ = -c - pull (GrpObj.inv : A ⟶ A).left c := by
    unfold lam
    rw [_root_.mul_inv_cancel, pull_one, ← GrpObj.inv_eq_inv, Over.id_left, pull_id]
    abel
  rw [e2, eq_comm, add_eq_zero_iff_eq_neg] at e
  rw [e]
  abel

private theorem pull_inv_lemma_3 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (h : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, t, ht⟩ := h (IsLocalRing.closedPoint K)
  have hV : A.hom ⁻¹ᵁ U = ⊤ := by
    rw [ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem U hU]
    simp
  have h0 := (cls_eq_zero_iff (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL, Fin.sum_univ_two] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
    ← sub_eq_add_neg, sub_eq_zero, pull_comp] at h0
  have hf : (A.left.topIso.inv ≫ (A.left.isoOfEq hV.symm).hom) ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 A.left := by
    rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]
  have e := congrArg (pull (A.left.topIso.inv ≫ (A.left.isoOfEq hV.symm).hom)) h0
  rw [← pull_comp _ (A.hom ⁻¹ᵁ U).ι, ← pull_comp _ (A.hom ⁻¹ᵁ U).ι, hf, pull_id, pull_id] at e
  exact e

end GlobalTheory.FormPoly

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.FormPoly

theorem formPoly_bundles : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → (∃ ev : Polynomial ℤ → (P.A ⟶ P.A), ev 1 = 𝟙 P.A ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (Polynomial.X * F) = ev F ≫ s) ∧ ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → (∀ F, IsMonHom (ev F)) ∧ (∀ F G, ev (F * G) = ev F ≫ ev G) ∧ (∀ F, FormIs P (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) (ev (2 * F))) ∧ (∀ F G, LBIso (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ((cubeLB P.A ![𝟙 P.A, ev (F)] P.L).pull (ev G).left)) ∧ (∀ F G, LBIso (LB.div (cubeLB P.A ![𝟙 P.A, ev (F + G)] P.L) (cubeLB P.A ![𝟙 P.A, ev (F)] P.L)) (cubeLB P.A ![𝟙 P.A, ev (G)] P.L)) ∧ LBIso (cubeLB P.A ![𝟙 P.A, ev (1)] P.L) (lbPow P.L 2) ∧ (SymB M → LBIso (cubeLB P.A ![𝟙 P.A, ev (Polynomial.X)] P.L) (lbPow M 2)) := by
  intro laws _ K _ _ P M s hM hF
  obtain ⟨hsM, hFi⟩ := hF
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
    obtain ⟨r, hr⟩ := P.rigid
    obtain ⟨cs⟩ := (laws.cube (Sp K) P { L := P.L, rig := r, isLB := P.isLB, rigGen := hr } rfl).1
    exact ⟨cs.t, cs.isGen⟩
  have hc : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A) (N : LB P.A.left) (hN : N.IsLB),
      cls (cubeLB P.A ![x, y] N) (isLB_cube_lemma _ hN) = lam (cls N hN) x y :=
    fun x y N hN => cls_cube_two hN x y _
  have eF : lam (cls M hM) (fst P.A P.A) (snd P.A P.A) =
      lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A ≫ s) := by
    rw [← hc _ _ M hM, ← hc _ _ P.L P.isLB]
    exact (cls_eq_iff (isLB_cube_lemma _ hM) (isLB_cube_lemma _ P.isLB)).2 hFi
  have eF' : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls M hM) x y = lam (cls P.L P.isLB) x (y ≫ s) := by
    intro T x y
    have e := congrArg (pull (lift x y).left) eF
    rwa [pull_lam, pull_lam, lift_fst, lift_snd, lift_snd_assoc] at e
  have hsa : ∀ (T : Over (Sp K)) (x y : T ⟶ P.A),
      lam (cls P.L P.isLB) (x ≫ s) y = lam (cls P.L P.isLB) x (y ≫ s) := by
    intro T x y
    rw [lam_comm (cls P.L P.isLB) (x ≫ s) y, ← eF' y x, lam_comm (cls M hM) y x, eF' x y]
  have hMadd : ∀ x y z : P.A ⟶ P.A,
      lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [eF', eF', eF', MonObj.mul_comp, GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ]
  have hι := pull_inv_lemma_3 P.isLB P.sym
  refine ⟨exists_ev s, fun ev h1 hadd hX => ?_⟩
  have adj : ∀ (F : Polynomial ℤ) (T : Over (Sp K)) (x y : T ⟶ P.A),
      lam (cls P.L P.isLB) (x ≫ ev F) y = lam (cls P.L P.isLB) x (y ≫ ev F) :=
    fun F T => lam_ev_adj P.isLB hΘ h1 hadd hX (hsa T) F
  refine ⟨ev_isMonHom h1 hadd hX, ev_mul h1 hadd hX, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    have := ev_isMonHom h1 hadd hX F
    unfold FormIs
    refine ⟨ev_isMonHom h1 hadd hX (2 * F), ?_⟩
    show LBIso (cubeLB P.A ![fst P.A P.A, snd P.A P.A] (cubeLB P.A ![𝟙 P.A, ev F] P.L)) _
    rw [← cls_eq_iff (isLB_cube_lemma _ (isLB_cube_lemma _ P.isLB)) (isLB_cube_lemma _ P.isLB), hc, hc, hc,
      GlobalTheory.HermTensorLB.lam_lam P.isLB hΘ, two_mul, hadd, MonObj.comp_mul,
      GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ, Category.comp_id, Category.comp_id,
      lam_comm (cls P.L P.isLB) (snd P.A P.A), adj]
    all_goals first | exact P.isLB | exact isLB_cube_lemma _ P.isLB
  · intro F G
    rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (pull_isLB (isLB_cube_lemma _ P.isLB) _),
      cls_pull (isLB_cube_lemma _ P.isLB), hc, hc, pull_lam, Category.comp_id]
    have e := adj G P.A (𝟙 P.A) (ev G ≫ ev F)
    rw [Category.id_comp] at e
    rw [e, show G ^ 2 * F = G * F * G by ring, ev_mul h1 hadd hX, ev_mul h1 hadd hX, Category.assoc]
    all_goals exact P.isLB
  · intro F G
    rw [← cls_eq_iff (LB.isLB_div (isLB_cube_lemma _ P.isLB) (isLB_cube_lemma _ P.isLB)) (isLB_cube_lemma _ P.isLB),
      cls_div (isLB_cube_lemma _ P.isLB) (isLB_cube_lemma _ P.isLB), hc, hc, hc, hadd,
      GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ, add_sub_cancel_left]
    all_goals exact P.isLB
  · rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ P.isLB _ _), hc,
      cls_lbPow P.isLB, h1, lam_id_lemma_2 _ (fun x y z => GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ x y z), hι,
      two_nsmul]
    all_goals exact P.isLB
  · intro hsym
    have hιM : pull (GrpObj.inv : P.A ⟶ P.A).left (cls M hM) = cls M hM := by
      rw [← cls_pull hM _ (pull_isLB hM _)]
      exact ((cls_eq_iff hM (pull_isLB hM _)).2 hsym).symm
    have e := eF' (𝟙 P.A) (𝟙 P.A)
    rw [Category.id_comp] at e
    rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _), hc, cls_lbPow hM,
      ev_X h1 hX, ← e, lam_id_lemma_2 _ hMadd, hιM, two_nsmul]
    all_goals exact P.isLB

end GlobalTheory
