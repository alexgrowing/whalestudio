import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceAdelicCmExtension
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sum_coord {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    x = ∑ k, ((Algebra.TensorProduct.basis R b).repr x k) • ((1 : R) ⊗ₜ[F] b k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr x]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply]

theorem coord_sig {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E)
    (x : R ⊗[F] E) (l : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ x) l =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k *
        (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] σ (b k)) l := by
  have h : sigR R σ x =
      ∑ k, ((Algebra.TensorProduct.basis R b).repr x k) • ((1 : R) ⊗ₜ[F] σ (b k)) := by
    conv_lhs => rw [sum_coord (R := R) b x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp [sigR]
  rw [h, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

variable [FiniteDimensional F E]

theorem trace_coord {R : Type} [CommRing R] [Algebra F R] {d : ℕ} (b : Module.Basis (Fin d) F E) (x : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) x =
      ∑ k, (Algebra.TensorProduct.basis R b).repr x k * algebraMap F R (Algebra.trace F E (b k)) := by
  conv_lhs => rw [sum_coord (R := R) b x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, GlobalTheory.LatVac.trace_tmul, one_mul, smul_eq_mul]

theorem trace_tmul_one {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (x : R ⊗[F] E) :
    (Algebra.trace R (R ⊗[F] E) x) ⊗ₜ[F] (1 : E) = x + sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, TensorProduct.add_tmul, hx, hy, map_add]
    abel
  | tmul a e =>
    have h1 : (a * algebraMap F R (Algebra.trace F E e)) ⊗ₜ[F] (1 : E) =
        a ⊗ₜ[F] algebraMap F E (Algebra.trace F E e) := by
      rw [mul_comm, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have h2 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [sigR]
    rw [GlobalTheory.LatVac.trace_tmul, h1, hσ, TensorProduct.tmul_add, h2]

theorem half_trace_tmul {R : Type} [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e) (h2 : (2 : F) ≠ 0) (x : R ⊗[F] E)
    (hx : sigR R σ x = x) :
    (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) x) ⊗ₜ[F] (1 : E) = x := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul', trace_tmul_one σ hσ, hx, ← two_smul F x, smul_smul,
    one_div, inv_mul_cancel₀ h2, one_smul]

end Loc

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem latH_iff_at {d : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ e, algebraMap F E (Algebra.trace F E e) = e + σ e)
    (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ)
    (h2 : (2 : F) ≠ 0)
    (hh : algebraMap F (Fv F v) (1 / 2) ∈ v.adicCompletionIntegers F)
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] (1 : E)) k ∈
      v.adicCompletionIntegers F)
    (hs : ∀ i k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] σ (b i)) k ∈
      v.adicCompletionIntegers F)
    (ht : ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F)
    (Y : HermR (Fv F v) σ n) :
    Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈
        (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  constructor
  · rintro ⟨hd, ho⟩ a i k
    rcases lt_trichotomy a i with h | h | h
    · exact ho a i h k
    · subst h
      have e := half_trace_tmul (R := Fv F v) σ hσ h2 ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) (Y.2 a a)
      have e2 : (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) k =
          (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) *
          (Algebra.TensorProduct.basis (Fv F v) b).repr ((1 : Fv F v) ⊗ₜ[F] (1 : E)) k := by
        conv_lhs => rw [← e]
        have e3 : (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) ⊗ₜ[F] (1 : E) =
            (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
            ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a)) • ((1 : Fv F v) ⊗ₜ[F] (1 : E)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e3, map_smul, Finsupp.smul_apply, smul_eq_mul]
      show (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a a) k ∈ v.adicCompletionIntegers F
      rw [e2]
      exact mul_mem (hd a) (h1 k)
    · show (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) k ∈ v.adicCompletionIntegers F
      have e : sigR (Fv F v) σ ((Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i a) =
          (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i := Y.2 a i
      rw [← e, coord_sig]
      exact sum_mem fun l _ => mul_mem (ho i a h l) (hs l k)
  · intro h
    refine ⟨fun i => ?_, fun i j _ k => h i j k⟩
    rw [trace_coord b]
    exact mul_mem hh (sum_mem fun l _ => mul_mem (h i i l) (ht l))

end Place

theorem latH_iff_latV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔ (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hCM n d b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  obtain ⟨I1, I2⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hT : ∀ k, ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F := by
    intro k
    by_cases h0 : Algebra.trace F E (b k) = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · filter_upwards [I2 _ h0] with v hv
      exact hv.le
  filter_upwards [I2 (1 / 2) (by norm_num), I1 1, Filter.eventually_all.2 fun i => I1 (σ (b i)),
    Filter.eventually_all.2 hT] with v hh h1 hs ht Y
  exact latH_iff_at σ (GlobalTheory.CMTrace.trace_eq hCM) b v n two_ne_zero hh.le h1 hs ht Y

end GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp
