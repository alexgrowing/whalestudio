import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

section
variable {F : Type} [Field F] [NumberField F]

private lemma nU_val (b : A F) : (nU b).1 = !![1, b; 0, 1] := rfl
private lemma mD_val (a : (A F)ˣ) : (mD a).1 = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl
private lemma wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

private lemma sl_ext {g h : G1 F} (e : g.1 = h.1) : g = h := Subtype.ext e

private lemma sl_of {g h : G1 F} {p q r s : A F} (e : h.1 = !![p, q; r, s])
    (h00 : g.1 0 0 = p) (h01 : g.1 0 1 = q) (h10 : g.1 1 0 = r) (h11 : g.1 1 1 = s) : g = h := by
  apply sl_ext
  rw [e, Matrix.eta_fin_two g.1, h00, h01, h10, h11]

private lemma det_eq (g : G1 F) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private lemma nm_val (b : A F) (a : (A F)ˣ) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, mD_val, Matrix.mul_fin_two]
  simp

private lemma cell_val (b b' : A F) (a : (A F)ˣ) :
    (nU b * mD a * wW F * nU b').1 =
      !![-(b * ((a⁻¹ : (A F)ˣ) : A F)), (a : A F) - b * ((a⁻¹ : (A F)ˣ) : A F) * b';
        -((a⁻¹ : (A F)ˣ) : A F), -(((a⁻¹ : (A F)ˣ) : A F) * b')] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, nm_val, wW_val, nU_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  simp
  ring_nf

private lemma rel_part : Rel (nU (F := F)) mD (wW F) where
  N_zero := by
    apply sl_ext
    simp [nU_val, Matrix.one_fin_two]
  N_add b c := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, nU_val, nU_val, nU_val, Matrix.mul_fin_two]
    simp [add_comm]
  M_one := by
    apply sl_ext
    simp [mD_val, Matrix.one_fin_two]
  M_mul a a' := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, mD_val, mD_val, mD_val, Matrix.mul_fin_two]
    simp [mul_comm]
  MN a b := by
    apply sl_ext
    have he : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1 := a.mul_inv
    rw [Matrix.SpecialLinearGroup.coe_mul, nm_val, mD_val, nU_val, Matrix.mul_fin_two]
    have hq : (a : A F) ^ 2 * b * ((a⁻¹ : (A F)ˣ) : A F) = (a : A F) * b := by
      linear_combination ((a : A F) * b) * he
    simp [hq]
  WM a := by
    apply sl_ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, mD_val, mD_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp
  W_unit := Group.isUnit _

private lemma gauss_part : Gauss (nU (F := F)) mD (wW F) := by
  intro t
  apply sl_ext
  have he : (t : A F) * ((t⁻¹ : (A F)ˣ) : A F) = 1 := t.mul_inv
  rw [cell_val, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, wW_val, nU_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [he]

private lemma tri_part (g : G1 F) : g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a := by
  constructor
  · intro h
    have h' : g.1 1 0 = 0 := h
    have hd := det_eq g
    rw [h', mul_zero, sub_zero] at hd
    have hd' : g.1 1 1 * g.1 0 0 = 1 := by rw [mul_comm]; exact hd
    refine ⟨g.1 0 1 * g.1 0 0, ⟨g.1 0 0, g.1 1 1, hd, hd'⟩, ?_⟩
    refine sl_of (nm_val _ _) rfl ?_ h' rfl
    show g.1 0 1 = g.1 0 1 * g.1 0 0 * g.1 1 1
    linear_combination (-g.1 0 1) * hd
  · rintro ⟨b, a, rfl⟩
    show (nU b * mD a).1 1 0 = 0
    rw [nm_val]
    simp

private lemma tri_uniq (b b' : A F) (a a' : (A F)ˣ) (e : nU b * mD a = nU b' * mD a') : b = b' ∧ a = a' := by
  have h := congrArg Subtype.val e
  rw [nm_val, nm_val] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp at h00 h01
  have ha : a = a' := Units.ext h00
  subst ha
  exact ⟨(Units.mul_left_inj _).1 h01, rfl⟩

private lemma cell_part (g : G1 F) : IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  constructor
  · rintro ⟨c, hc⟩
    have hc' : g.1 1 0 = (c : A F) := hc.symm
    have he : (c : A F) * ((c⁻¹ : (A F)ˣ) : A F) = 1 := c.mul_inv
    have hd := det_eq g
    rw [hc'] at hd
    refine ⟨g.1 0 0 * ((c⁻¹ : (A F)ˣ) : A F), -c⁻¹, g.1 1 1 * ((c⁻¹ : (A F)ˣ) : A F), ?_⟩
    refine sl_of (cell_val _ _ _) ?_ ?_ ?_ ?_
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 0 0) * he
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) ^ 2)) * hd +
        (-((c⁻¹ : (A F)ˣ) : A F) - g.1 0 1 * ((c : A F) * ((c⁻¹ : (A F)ˣ) : A F) + 1)) * he
    · simp only [inv_neg, inv_inv, Units.val_neg, neg_neg]
      exact hc'
    · simp only [inv_neg, inv_inv, Units.val_neg]
      linear_combination (-g.1 1 1) * he
  · rintro ⟨b, a, b', rfl⟩
    show IsUnit ((nU b * mD a * wW F * nU b').1 1 0)
    rw [cell_val]
    simp
end

theorem UpperTheory.ConvolutionTheory.R2.C.grpRel :
    ∀ (F : Type) [Field F] [NumberField F], Rel (nU (F := F)) mD (wW F) ∧ Gauss (nU (F := F)) mD (wW F) ∧
    (∀ g : G1 F, g 1 0 = 0 ↔ ∃ b a, g = nU b * mD a) ∧ (∀ (b b' : A F) a a', nU b * mD a = nU b' * mD a' → b = b' ∧ a = a') ∧
    ∀ g : G1 F, IsUnit (g 1 0) ↔ ∃ b a b', g = nU b * mD a * wW F * nU b' := by
  intro F _ _
  exact ⟨rel_part, gauss_part, tri_part, tri_uniq, cell_part⟩
