import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem mem_bor_iff {F : Type} [Field F] [NumberField F] (g : G1 F) :
    g ∈ M.Bor F ↔ g 1 0 = 0 := by
  constructor
  · intro h
    exact h (show (id (0 : Fin 2)) < id (1 : Fin 2) by decide)
  · intro h i j hij
    have hij' : j < i := hij
    have hi : i = 1 := by omega
    have hj : j = 0 := by omega
    subst hi hj
    exact h

private theorem nm_val {F : Type} [Field F] [NumberField F] (a : (A F)ˣ) (b : A F) :
    (nU b * mD a).1 = !![(a : A F), b * ((a⁻¹ : (A F)ˣ) : A F); 0, ((a⁻¹ : (A F)ˣ) : A F)] := by
  rw [M.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperTriangular_diagonal_product {F : Type} [Field F] [NumberField F] (g : G1 F) (h : g 1 0 = 0) :
    g 0 0 * g 1 1 = 1 := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two] at hd
  have h' : g.1 1 0 = 0 := h
  rw [h', mul_zero, sub_zero] at hd
  exact hd

private def dg {F : Type} [Field F] [NumberField F] (g : M.Bor F) : IdeleGroup F :=
  ⟨g.1 0 0, g.1 1 1, upperTriangular_diagonal_product g.1 ((mem_bor_iff g.1).1 g.2),
    (mul_comm _ _).trans (upperTriangular_diagonal_product g.1 ((mem_bor_iff g.1).1 g.2))⟩

theorem UpperTheory.ConvolutionTheory.R2.M.borHomeo :
    ∀ (F : Type) [Field F] [NumberField F], IsClosed (M.Bor F : Set (G1 F)) ∧ ∃ e : IdeleGroup F × A F ≃ₜ M.Bor F, ∀ p, (e p : G1 F) = nU p.2 * mD p.1 := by
  intro F _ _
  refine ⟨?_, ?_⟩
  · have : (M.Bor F : Set (G1 F)) = {g | g 1 0 = 0} := Set.ext mem_bor_iff
    rw [this]
    exact isClosed_eq (M.continuous_entry 1 0) continuous_const
  · have hmem : ∀ p : IdeleGroup F × A F, nU p.2 * mD p.1 ∈ M.Bor F := fun p => by
      rw [mem_bor_iff]
      show (nU p.2 * mD p.1).1 1 0 = 0
      rw [nm_val]
      simp
    refine ⟨{ toFun := fun p => ⟨nU p.2 * mD p.1, hmem p⟩
              invFun := fun g => (dg g, g.1 0 1 * g.1 0 0)
              left_inv := ?_
              right_inv := ?_
              continuous_toFun := ?_
              continuous_invFun := ?_ }, fun p => rfl⟩
    · rintro ⟨a, b⟩
      have e00 : (nU b * mD a) 0 0 = (a : A F) := by
        show (nU b * mD a).1 0 0 = _
        rw [nm_val]; simp
      have e01 : (nU b * mD a) 0 1 = b * ((a⁻¹ : (A F)ˣ) : A F) := by
        show (nU b * mD a).1 0 1 = _
        rw [nm_val]; simp
      refine Prod.ext (Units.ext e00) ?_
      show (nU b * mD a) 0 1 * (nU b * mD a) 0 0 = b
      rw [e00, e01, mul_assoc, Units.inv_mul, mul_one]
    · rintro ⟨g, hg⟩
      have h10 := (mem_bor_iff g).1 hg
      have hd := upperTriangular_diagonal_product g h10
      refine Subtype.ext (Subtype.ext ?_)
      show (nU (g 0 1 * g 0 0) * mD (dg ⟨g, hg⟩)).1 = g.1
      rw [nm_val]
      have hinv : (((dg ⟨g, hg⟩)⁻¹ : (A F)ˣ) : A F) = g 1 1 := rfl
      have hval : ((dg ⟨g, hg⟩ : (A F)ˣ) : A F) = g 0 0 := rfl
      rw [hinv, hval]
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · show g 0 1 * g 0 0 * g 1 1 = g 0 1
        rw [mul_assoc, hd, mul_one]
      · exact h10.symm
      · rfl
    · exact Continuous.subtype_mk
        ((M.continuous_nU.comp continuous_snd).mul (M.continuous_mD.comp continuous_fst)) _
    · have c : ∀ i j, Continuous fun g : M.Bor F => g.1 i j := fun i j =>
        (M.continuous_entry i j).comp continuous_subtype_val
      exact (Units.continuous_iff.2 ⟨c 0 0, c 1 1⟩).prodMk ((c 0 1).mul (c 0 0))
