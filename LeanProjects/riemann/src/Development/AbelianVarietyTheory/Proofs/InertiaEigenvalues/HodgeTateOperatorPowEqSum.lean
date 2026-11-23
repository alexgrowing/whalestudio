import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem htOp_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (C : Core l) (ξ : Ainf l) (a : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (r : ↥(GK K) →* GL (Fin a) (Om l)) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → ∀ (σ : GQ l) (z : ℂ_[l]) (H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), U * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) → IsHT C ξ (fun g => (r g).val.map σ) z u → ∀ n : ℕ, u ^ n = ∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x) := by
  intro l _ K C ξ a d ρ r b e hR σ z H U u hU hu
  have hσz : ∀ c : ℤ_[l], σ (zOm l c) = zOm l c := fun c => by simp [zOm]
  have hθo : ∀ w : Om l, Per.θD l (C.o w) = algebraMap (Om l) ℂ_[l] w := fun w => C.o_sec.th w

  let S : Set (Om l) := Set.range fun t : Fin d × Fin a × Fin a => σ (b t.1 t.2.1 t.2.2)
  haveI : Finite S := (Set.finite_range _).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] S, hfd⟩
  have hfix : ∀ g : GQ l, g ∈ GK K' → ∀ i m k, g (σ (b i m k)) = σ (b i m k) := by
    intro g hg i m k
    exact (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg _
      (IntermediateField.subset_adjoin _ _ ⟨(i, m, k), rfl⟩)
  let B : Fin a → Matrix (Fin a) (Fin d) ℂ_[l] := fun k m i => algebraMap (Om l) ℂ_[l] (σ (b i m k))
  have hVu : IsUnit (H.V.map (Per.θD l)) := H.unit.map (Per.θD l).mapMatrix
  have col : ∀ k, u * B k * H.V.map (Per.θD l) = B k * U * H.V.map (Per.θD l) := by

    intro k
    ext m j
    let y : Fin a → Per.BdRp l := fun m => ∑ i, C.o (σ (b i m k)) * H.V i j
    let x : Fin a → Per.BdR l := fun m => ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * H.Q i j
    have hy : ∀ m, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * x m = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * y m) := by
      intro m
      simp only [x, y, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hq := H.Q_eq i j
      calc algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * (algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * H.Q i j)
          = algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ H.q * H.Q i j) := by ring
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * H.V i j) := by rw [hq]
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ H.p j * (C.o (σ (b i m k)) * H.V i j)) := by simp only [map_mul, map_pow]; ring
    have hx : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' →
        ((r g).val.map σ).map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o) *ᵥ (fun i => Per.σD (g : GQ l) (x i)) = x := by
      intro g hg
      funext m'
      have hσD : ∀ m, Per.σD (g : GQ l) (x m) = ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * Per.σD (g : GQ l) (H.Q i j) := by
        intro m
        simp only [x, map_sum, map_mul, PrimeEx.sigD_o, hfix _ hg]
      have e1 : ∀ i, ∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) =
          ∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k))) := by
        intro i
        have h1 := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (M m' k)))) (hR.equi g i)
        simpa [Matrix.mul_apply, Matrix.sum_apply, map_sum, map_mul, hσz] using h1
      have e2 : ∀ s, ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * Per.σD (g : GQ l) (H.Q i j) = H.Q s j := by
        intro s
        have h1 := congrFun (congrFun (H.inv g g.2) s) j
        simpa [Matrix.mul_apply] using h1
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.comp_apply, hσD]
      calc ∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k))) * Per.σD (g : GQ l) (H.Q i j)
          = ∑ i, (∑ m, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ ((r g).val m' m))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b i m k)))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
        _ = ∑ i, (∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k)))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [e1]
        _ = ∑ s, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (σ (b s m' k))) * ∑ i, algebraMap (Per.BdRp l) (Per.BdR l) (C.o (zOm l ((ρ g).val s i))) * Per.σD (g : GQ l) (H.Q i j) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
        _ = x m' := by simp only [e2, x]
    have h := hu K' (H.p j) H.q x y hx hy
    have hθy : (fun m => Per.θD l (y m)) = fun m => (B k * H.V.map (Per.θD l)) m j := by
      funext m'
      simp only [y, Matrix.mul_apply, Matrix.map_apply]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hθo]
    rw [hθy] at h
    have h2 := congrFun h m
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_assoc u, Matrix.mul_assoc (B k), hU, ← Matrix.mul_assoc (B k), Matrix.mul_diagonal, Matrix.mul_apply, h2, mul_comm]
  have comm : ∀ k, u * B k = B k * U := by
    intro k
    have hd : IsUnit (H.V.map (Per.θD l)).det := (Matrix.isUnit_iff_isUnit_det _).1 hVu
    calc u * B k = u * B k * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by
          rw [Matrix.mul_assoc (u * B k), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = B k * U * H.V.map (Per.θD l) * (H.V.map (Per.θD l))⁻¹ := by rw [col k]
      _ = B k * U := by rw [Matrix.mul_assoc (B k * U), Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have key : ∀ x : Fin d → ℂ_[l], u * (∑ i, x i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w)) =
      ∑ i, (U *ᵥ x) i • (b i).map fun w => algebraMap (Om l) ℂ_[l] (σ w) := by
    intro x
    ext m k
    have h := congrFun (congrArg (· *ᵥ x) (comm k)) m
    simp only [← Matrix.mulVec_mulVec] at h
    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, B] at h
    refine (Finset.sum_congr rfl fun x1 _ => ?_).trans (h.trans (Finset.sum_congr rfl fun c _ => ?_))
    · congr 1
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    · simp only [Matrix.mulVec, dotProduct]
      exact mul_comm _ _
  have one : ∑ i, (fun s => algebraMap (Om l) ℂ_[l] (zOm l (e s))) i • (b i).map (fun w => algebraMap (Om l) ℂ_[l] (σ w)) = 1 := by
    ext m k
    have h := congrArg (fun M : Matrix (Fin a) (Fin a) (Om l) => algebraMap (Om l) ℂ_[l] (σ (M m k))) hR.one
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hσz] at h
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [h]
    by_cases hmk : m = k <;> simp [Matrix.one_apply, hmk]
  intro n
  induction n with
  | zero => simpa using one.symm
  | succ n ih => rw [pow_succ', ih, key, Matrix.mulVec_mulVec, ← pow_succ']

end GlobalTheory.BKLim
