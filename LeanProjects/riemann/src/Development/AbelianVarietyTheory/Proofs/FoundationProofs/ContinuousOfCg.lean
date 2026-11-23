import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHtPresNu7
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HtPresNu7MonoLoss
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemIntegersOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.LambdaValuationPowers.AllRoots

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem pres_of_vanish (A : ValuationSubring Ω) (c : Coef l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → Z m s 1 = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l), HTPresNuOfPolys A c m 0 Z ζ P o := by
  refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, hζ, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
  have h := GlobalTheory.Col.kumPres_empty A (n := m - 0) (r := m) (ζ := ζ ^ l ^ 0) (by simpa using hζ) (by omega) (Z m) hZ
  convert h using 2 <;> exact Empty.elim ‹_›

theorem continuous_of_cg [Algebra.IsAlgebraic ℚ Ω] (f : G ℚ Ω → Qbar l)
    (h : ∀ n : ℕ, ∃ E0 : Finset Ω, ∀ s s' : G ℚ Ω, (∀ z ∈ E0, s' z = z) → Cg n (f (s * s')) (f s)) : Continuous f := by
  have hnl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have : (l : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have hlt1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt1
  obtain ⟨E0, hE⟩ := h n
  have hopen : ∀ᶠ t in nhds (1 : G ℚ Ω), ∀ z ∈ E0, t z = z := by
    rw [Filter.eventually_all_finset]
    intro z _
    have ho := stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Ω) z
    exact ho.mem_nhds (one_mem _)
  have hcont : Filter.Tendsto (fun t : G ℚ Ω => s⁻¹ * t) (nhds s) (nhds 1) := by
    have := (continuous_const_mul s⁻¹).tendsto s
    rwa [inv_mul_cancel] at this
  filter_upwards [hcont.eventually hopen] with t ht
  have := hE s (s⁻¹ * t) ht
  rw [mul_inv_cancel_left, Cg, norm_pow, hnl] at this
  rw [dist_eq_norm]
  exact this.trans_lt hn

end GlobalTheory.LambdaValuationPowers.AllRoots
