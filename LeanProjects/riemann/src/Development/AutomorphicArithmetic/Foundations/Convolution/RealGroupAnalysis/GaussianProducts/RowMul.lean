import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.rowMul :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (p : (Fin 2 → A F) → ℂ) (φ φ' : S4 F), (∀ v, hat φ'.1 v = p ![v 0, v 1] * hat φ.1 v) →
    ∀ (g : G1 F) v, hat (W.Om g φ').1 v = p (![v 0, v 1] ᵥ* g.1) * hat (W.Om g φ).1 v := by
  intro F E _ _ _ _ _ _ _ D W
  have hS := hatSt F E D W
  let P : G1 F → Prop := fun g => ∀ (p : (Fin 2 → A F) → ℂ) (φ φ' : S4 F),
    (∀ v, hat φ'.1 v = p ![v 0, v 1] * hat φ.1 v) →
      ∀ v, hat (W.Om g φ').1 v = p (![v 0, v 1] ᵥ* g.1) * hat (W.Om g φ).1 v
  have hone : P 1 := by
    intro p φ φ' h v
    simpa using h v
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb p φ φ' h v
    have h1 := ha (fun r => p (r ᵥ* b.1)) (W.Om b φ) (W.Om b φ') (hb p φ φ' h) v
    simp only [map_mul, Module.End.mul_apply, Matrix.SpecialLinearGroup.coe_mul]
    rw [h1, Matrix.vecMul_vecMul]
  have hn : ∀ b, P (nU b) := by
    intro b p φ φ' h v
    rw [hS.n, hS.n, h]
    have e : ![Function.update v 1 (v 1 + b * v 0) 0, Function.update v 1 (v 1 + b * v 0) 1] =
        ![v 0, v 1] ᵥ* (nU b).1 := by
      ext i
      fin_cases i <;> simp [nU, Matrix.vecMul, dotProduct, Fin.sum_univ_two, add_comm, mul_comm]
    rw [e]
    ring
  have hw : P (wW F) := by
    intro p φ φ' h v
    rw [hS.w, hS.w]
    have e : ![-v 1, v 0] = ![v 0, v 1] ᵥ* (wW F).1 := by
      ext i
      fin_cases i <;> simp [wW, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [← e, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [h]
    simp [mul_assoc]
  have hninv : ∀ b : A F, (nU b)⁻¹ = nU (-b) := by
    intro b
    refine inv_eq_of_mul_eq_one_right ?_
    refine Subtype.ext ?_
    show (nU b).1 * (nU (-b)).1 = 1
    simp [nU, Matrix.one_fin_two, Matrix.mul_fin_two]
  have hwinv : (wW F)⁻¹ = wW F * wW F * wW F := by
    refine inv_eq_of_mul_eq_one_right ?_
    refine Subtype.ext ?_
    show (wW F).1 * ((wW F).1 * (wW F).1 * (wW F).1) = 1
    simp [wW, Matrix.one_fin_two, Matrix.mul_fin_two]
  let T : Subgroup (G1 F) :=
    { carrier := {g | P g ∧ P g⁻¹}
      mul_mem' := fun {a b} ha hb => ⟨hmul a b ha.1 hb.1, by
        rw [_root_.mul_inv_rev]; exact hmul _ _ hb.2 ha.2⟩
      one_mem' := ⟨hone, by rw [inv_one]; exact hone⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  have hle : Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) ≤ T := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨b, rfl⟩ | rfl)
    · exact ⟨hn b, by rw [hninv]; exact hn _⟩
    · exact ⟨hw, by rw [hwinv]; exact hmul _ _ (hmul _ _ hw hw) hw⟩
  intro p φ φ' h g v
  have hg : g ∈ T := hle (by rw [(gen F).1]; exact Subgroup.mem_top g)
  exact hg.1 p φ φ' h v
