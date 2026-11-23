import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.IntegralAE

open GlobalTheory.InertSph (latAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}

theorem exists_zsmul_mem {L : Submodule (𝓞 E) (Fin d → E)} (hL : L.IsLattice E) (w : Fin d → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  first
  | exact @_root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem
  | exact _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem
  | (apply _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem ..)

theorem smul_mem_latAt (W : Spc F E d) (v : Pl F) {a : AF F} (ha : evFin F v a ∈ v.adicCompletionIntegers F)
    {z : Fin d → AE F E} (hz : z ∈ latAt W v) : a • z ∈ latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, hb', y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun u hu => ?_, ?_, y, hy, smul_smul _ _ _⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u, hb u hu, mul_zero]
    · rw [map_mul]; exact mul_mem ha hb'
  | zero => rw [smul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [smul_neg]; exact neg_mem h1

theorem eventually_partFin_mem (W : Spc F E d) (hL : W.L.IsLattice E) (x : Fin d → AE F E) :
    ∀ᶠ v in cofinite, partFin v x ∈ latAt W v := by
  classical
  have hadd : ∀ x y : Fin d → AE F E, (∀ᶠ v in cofinite, partFin v x ∈ latAt W v) →
      (∀ᶠ v in cofinite, partFin v y ∈ latAt W v) → ∀ᶠ v in cofinite, partFin v (x + y) ∈ latAt W v :=
    fun x y hx hy => (hx.and hy).mono fun v h => by
      rw [partFin, smul_add]; exact add_mem h.1 h.2
  have hzero : ∀ᶠ v in cofinite, partFin v (0 : Fin d → AE F E) ∈ latAt W v :=
    Eventually.of_forall fun v => by rw [partFin, smul_zero]; exact zero_mem _
  have hs : ∀ (i : Fin d) (t : AE F E), ∀ᶠ v in cofinite, partFin v (Pi.single i t : Fin d → AE F E) ∈ latAt W v := by
    intro i t
    induction t using TensorProduct.induction_on with
    | zero => simpa using hzero
    | add s t h1 h2 => rw [Pi.single_add]; exact hadd _ _ h1 h2
    | tmul a c =>
      obtain ⟨N, hN, hy⟩ := exists_zsmul_mem hL (Pi.single i c : Fin d → E)
      have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.2 hN
      set b : AF F := (N : F)⁻¹ • a with hb
      have hint : ∀ᶠ v in cofinite, evFin F v b ∈ v.adicCompletionIntegers F := b.2.2
      have e : (Pi.single i (a ⊗ₜ[F] c) : Fin d → AE F E) =
          b • fun j => inclR (F := F) (AF F) ((N • (Pi.single i c : Fin d → E)) j) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [Pi.single_eq_same, Pi.smul_apply]
          change _ = b • ((1 : AF F) ⊗ₜ[F] (N • c))
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hb, TensorProduct.smul_tmul,
            ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hNF, one_smul]
        · simp [Pi.single_eq_of_ne hj]
      refine hint.mono fun v hv => ?_
      rw [e, partFin, smul_comm]
      refine smul_mem_latAt W v hv (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v 1, ?_, _, hy, rfl⟩)
      rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _
  rw [← Finset.univ_sum_single x]
  exact Finset.sum_induction _ (fun y : Fin d → AE F E => ∀ᶠ v in cofinite, partFin v y ∈ latAt W v) hadd hzero
    fun i _ => hs i _

theorem eventually_mulVec_mem (W : Spc F E d) (hL : W.L.IsLattice E) (A : Matrix (Fin d) (Fin d) (AE F E)) :
    ∀ᶠ v in cofinite, ∀ z ∈ latAt W v, A *ᵥ z ∈ latAt W v := by
  have hfg : (W.L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.2 hL.fg
    have : Module.Finite ℤ W.L := Module.Finite.trans (𝓞 E) W.L
    exact Module.Finite.iff_fg.1 (show Module.Finite ℤ (W.L.restrictScalars ℤ) from this)
  obtain ⟨s, hs⟩ := hfg
  have h1 : ∀ᶠ v in cofinite, ∀ y ∈ s, partFin v (A *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
    (eventually_all_finset s).2 fun y _ => eventually_partFin_mem W hL _
  refine h1.mono fun v hv z hz => ?_
  have h2 : ∀ y ∈ W.L, partFin v (A *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v := by
    intro y hy
    have hy' : y ∈ Submodule.span ℤ (s : Set (Fin d → E)) := by rw [hs]; exact hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy => exact hv y hy
    | zero =>
      have : (fun i => inclR (F := F) (AF F) ((0 : Fin d → E) i)) = 0 := funext fun i => map_zero _
      rw [this, Matrix.mulVec_zero, partFin, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => inclR (F := F) (AF F) ((x + y) i)) =
          (fun i => inclR (F := F) (AF F) (x i)) + fun i => inclR (F := F) (AF F) (y i) := funext fun i => map_add _ _ _
      rw [this, Matrix.mulVec_add, partFin, smul_add]; exact add_mem hx hy
    | smul n x _ hx =>
      have : (fun i => inclR (F := F) (AF F) ((n • x) i)) =
          n • (fun i => inclR (F := F) (AF F) (x i)) := funext fun i => map_zsmul _ _ _
      rw [this, Matrix.mulVec_smul, partFin, smul_comm]; exact zsmul_mem hx _
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, hb', y, hy, rfl⟩ := hz
    rw [Matrix.mulVec_smul, ← partFin_of_at hb, partFin, smul_eq_mul, mul_comm, mul_smul]
    exact smul_mem_latAt W v hb' (h2 y hy)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [Matrix.mulVec_neg]; exact neg_mem h1

theorem mulVec_eq_of_loc (W : Spc F E d) (v : Pl F) {A B : Matrix (Fin d) (Fin d) (AE F E)}
    (h : ∀ u : AF F, At (evFin F v) u → u • A = u • B) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    A *ᵥ z = B *ᵥ z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, -, y, -, rfl⟩ := hz
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, h b hb]
  | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  | add _ _ _ _ h1 h2 => rw [Matrix.mulVec_add, Matrix.mulVec_add, h1, h2]
  | neg _ _ h1 => rw [Matrix.mulVec_neg, Matrix.mulVec_neg, h1]

theorem eventually_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d), W.L.IsLattice E → ∀ hf : UA σ W.J,
    ∀ᶠ v in Filter.cofinite, ∀ g ∈ UAt σ W (evFin F v), (∀ u : AF F, At (evFin F v) u → u • mat g = u • mat hf) →
      g ∈ GlobalTheory.InertSph.KAt σ W v := by
  intro F E _ _ _ _ _ σ d W hL hf
  refine ((eventually_mulVec_mem W hL (mat hf)).and (eventually_mulVec_mem W hL (mat hf⁻¹))).mono
    fun v hv g hg h => ⟨hg, fun z hz => ⟨?_, ?_⟩⟩
  · rw [mulVec_eq_of_loc W v h hz]; exact hv.1 z hz
  · have h' : ∀ u : AF F, At (evFin F v) u → u • mat g⁻¹ = u • mat hf⁻¹ := fun u hu => by
      calc u • mat g⁻¹ = mat g⁻¹ * (u • mat hf) * mat hf⁻¹ := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, GlobalTheory.StabHaar.mat_mul_inv, Matrix.mul_one]
        _ = u • mat hf⁻¹ := by
            rw [← h u hu, Matrix.mul_smul, GlobalTheory.StabHaar.mat_inv_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [mulVec_eq_of_loc W v h' hz]; exact hv.2 z hz

end GlobalTheory.IntegralAE
