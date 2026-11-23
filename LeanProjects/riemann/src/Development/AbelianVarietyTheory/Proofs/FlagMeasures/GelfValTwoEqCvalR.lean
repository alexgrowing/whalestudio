import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CasimirEigen

variable {n : ℕ}

theorem gelfVal_two_eq (χ : Fin n → ℂ) :
    gelfVal χ 2 = ∑ a, χ a * χ a - ∑ a, (Formalism.QuantumDeterminants.rhoStd n a : ℂ) * (Formalism.QuantumDeterminants.rhoStd n a : ℂ) := by
  rw [gelfVal_succ χ 1, pow_one]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  have e : ∀ a : Fin n, (if a = b then χ a + ((n : ℂ) - 1) / 2 else if a < b then -1 else 0) =
      (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if a ∈ Finset.Iio b then 1 else 0) := by
    intro a
    by_cases h1 : a = b
    · subst h1; simp
    · by_cases h2 : a < b <;> simp [h1, h2]
  simp only [Amat, Matrix.of_apply, e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Fin.card_Iio, Formalism.QuantumDeterminants.rhoStd]
  push_cast
  ring

theorem gelfVal_two_eq_cvalR (ε : Fin n → Bool) (lam : Fin n → ℝ) :
    gelfVal (fun a => (lam a : ℂ)) 2 = ((cvalR ε lam : ℝ) : ℂ) := by
  rw [gelfVal_two_eq]
  simp only [cvalR, nsq, dot, Pi.add_apply, half_sum_roots_standard n ε, Formalism.QuantumDeterminants.rhoStd]
  push_cast
  rfl

theorem gelf_one_eq (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    gelf ε 1 f g = ∑ a, ∑ b, Eab ε a b (Eab ε b a f) g := by
  unfold gelf
  rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rfl

theorem inner_eabV {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f : Matrix (Fin n) (Fin n) ℂ → H} (hf : SmoothOnGV ε f) (y : H) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Eab ε a b (fun x => ⟪y, f x⟫_ℂ) g = ⟪y, EabV ε a b f g⟫_ℂ := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have k1 := (rdVPair_of vector_right_derivative_extends n ε H ℂ (innerSL ℂ y) f _ g hf h1 hg).2
  have k2 := (rdVPair_of vector_right_derivative_extends n ε H ℂ (innerSL ℂ y) f _ g hf h2 hg).2
  simp only [innerSL_apply_apply, rdV_eq] at k1 k2
  simp only [Eab, Ec, EabV, EcV, inner_add_right, inner_smul_right, k1, k2]

theorem cas_eq_of_isZEigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ Vs) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → ((∀ u, u ∈ Vs ↔ SmoothOnGV ε (fun g => σ g u)) ∧ GlRel E ∧ IsUnitary ε E ∧ (∀ X, inG ε X → ∀ u : Vs, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0) ∧ ∀ a b (u : Vs), ∀ g ∈ UJset ε, σ g (E a b u) = EabV ε a b (fun g => σ g u) g) → ∀ u : Vs, (∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g u⟫_ℂ)) → Cas E u = ((cvalR ε lam : ℝ) : ℂ) • u := by
  intro n ε H _ _ _ σ Vs E lam hσ ⟨hV, _, _, _, hE⟩ u hu
  have hone : ∀ v, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.SmoothVecMod.inUJ_one
  have key : ∀ (y : H) (a b : Fin n) (v : Vs) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Eab ε a b (fun x => ⟪y, σ x v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro y a b v g hg
    rw [hE a b v g hg]
    exact inner_eabV ((hV v).1 v.2) y a b hg
  apply Subtype.ext
  refine ext_inner_left ℂ fun y => ?_
  have h := (hu y).2 1 1 h1
  rw [gelf_one_eq, gelfVal_two_eq_cvalR ε lam] at h
  have e : ∀ a b : Fin n, Eab ε a b (Eab ε b a (fun x => ⟪y, σ x u⟫_ℂ)) 1 =
      ⟪y, ((E a b (E b a u) : Vs) : H)⟫_ℂ := by
    intro a b
    have := GlobalTheory.SmoothVecMod.eabV_congr (E := ℂ) (key y b a u) a b h1
    rw [eabV_eq, eabV_eq] at this
    rw [this, key y a b _ 1 h1, hone]
  simp only [e, hone] at h
  simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, inner_sum, Submodule.coe_smul,
    inner_smul_right]
  exact h

end GlobalTheory.CasimirEigen
