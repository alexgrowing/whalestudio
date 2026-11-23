import Mathlib
import GroundTheory.GlobalFields.Adele.Approximation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSqEmbeddingImagQuadraticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoprimeIdeleApproximationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFMulPosPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ConjApprox

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteAdeleMap finiteCompletionMap finiteCompletionMap_mapsTo)

theorem exists_approx {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (n : ℕ) :
    ∃ m : K, m ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) (n : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K := by
  set a : Af K := algebraMap K (Af K) (n : K)⁻¹
  set ti : Af K := ((t⁻¹ : (Af K)ˣ) : Af K)
  set U : Set (Af K) := {x | ∀ v : HeightOneSpectrum (𝓞 K), (a * (ti * x - 1)) v ∈ v.adicCompletionIntegers K}
  have hO : IsOpen {z : Af K | ∀ v : HeightOneSpectrum (𝓞 K), z v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
      fun _ => Valued.isOpen_valuationSubring _
  have hU : IsOpen U :=
    hO.preimage (continuous_const.mul ((continuous_const.mul continuous_id).sub continuous_const))
  have hV : IsOpen (U ∩ {0}ᶜ) := hU.inter isClosed_singleton.isOpen_compl
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (𝓞 K)
  let v0 : HeightOneSpectrum (𝓞 K) :=
    ⟨m0, hm0.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm0 (RingOfIntegers.not_isField K)⟩
  haveI : Nontrivial (Af K) := ⟨⟨0, 1, fun h => by
    have h' := congrArg (fun x : Af K => x v0) h
    exact zero_ne_one h'⟩⟩
  have ht : (t : Af K) ∈ U ∩ {0}ᶜ := by
    refine ⟨fun v => ?_, t.ne_zero⟩
    have : ti * (t : Af K) - 1 = 0 := by simp [ti]
    rw [this, mul_zero]
    exact zero_mem _
  obtain ⟨m, hm1, hm2⟩ := GlobalTheory.AdeleCharTwist.denseRange_fin.exists_mem_open hV ⟨_, ht⟩
  refine ⟨m, fun h => hm2 (by simp [h]), hm1⟩

theorem finiteAdeleMap_algebraMap {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (x : K) : finiteAdeleMap K E (algebraMap K (Af K) x) = algebraMap E (Af E) (algebraMap K E x) :=
  FiniteAdeleRing.ext _ fun w => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe K E w x

theorem mem_of_approx {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ) (k j : ℕ) (hk : 0 < k) (hj : 0 < j) (hjc : ((j : ℕ) : OF E) ∈ c) (m : K)
    (hm : ∀ v : HeightOneSpectrum (𝓞 K),
      (algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) v ∈
        v.adicCompletionIntegers K) :
    ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) *
          ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro u hu
  set zK : Af K := algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ * (((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)
    with hzK
  set Z : Af E := finiteAdeleMap K E zK with hZ
  have hZi : ∀ w : HeightOneSpectrum (𝓞 E), Z w ∈ w.adicCompletionIntegers E := fun w =>
    finiteCompletionMap_mapsTo K E w (hm (w.under (𝓞 K)))
  have hjZ : (j : Af E) * Z ∈ hatO c := by
    have := GlobalTheory.CMVal.PicFin.mul_mem_hatO hjc hZi
    simpa only [map_natCast] using this
  set U' : Af E := ((upIdele K E t : (Af E)ˣ) : Af E) with hU'
  set Ui : Af E := (((upIdele K E t)⁻¹ : (Af E)ˣ) : Af E) with hUi
  set Yi : Af E := ((y⁻¹ : (Af E)ˣ) : Af E) with hYi
  set M : Af E := algebraMap E (Af E) (algebraMap K E m) with hM
  set Uu : Af E := algebraMap E (Af E) u with hUu
  set Kinv : Af E := algebraMap E (Af E) (k : E)⁻¹ with hKinv
  have e1 : U' * Ui = 1 := Units.mul_inv _
  have e3 : (k : Af E) * Kinv = 1 := by
    rw [hKinv, ← map_natCast (algebraMap E (Af E)), ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hk.ne'), map_one]
  have eK : ((k * j : ℕ) : Af K) * algebraMap K (Af K) ((k * j : ℕ) : K)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap K (Af K)), ← map_mul,
      mul_inv_cancel₀ (by exact_mod_cast (Nat.mul_pos hk hj).ne'), map_one]
  have e2K : ((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m = 1 + ((k * j : ℕ) : Af K) * zK := by
    rw [hzK]; linear_combination (-(((t⁻¹ : (Af K)ˣ) : Af K) * algebraMap K (Af K) m - 1)) * eK
  have e2 : Ui * M = 1 + (k : Af E) * ((j : Af E) * Z) := by
    have := congrArg (finiteAdeleMap K E) e2K
    rw [map_mul, map_add, map_one, map_mul, map_natCast, finiteAdeleMap_algebraMap] at this
    have hUi' : Ui = finiteAdeleMap K E ((t⁻¹ : (Af K)ˣ) : Af K) := by rw [hUi, ← map_inv]; rfl
    rw [hUi', hM, this, hZ]
    push_cast
    ring
  have hA : Ui * M ∈ hatO c := by
    rw [e2]
    refine add_mem (one_mem _) (mul_mem ?_ hjZ)
    exact_mod_cast natCast_mem (hatO c) k
  have hu' : Uu * U' * Yi ∈ hatO c := by
    have h := hu
    simp only [lattice, Set.mem_setOf_eq, mul_inv_rev, inv_inv, Units.val_mul] at h
    rw [hUu, hU', hYi, _root_.mul_assoc]; exact h
  constructor
  · show algebraMap E (Af E) (algebraMap K E m * u) * Yi ∈ hatO c
    have : algebraMap E (Af E) (algebraMap K E m * u) * Yi = (Ui * M) * (Uu * U' * Yi) := by
      rw [map_mul]; linear_combination (-(M * Uu * Yi)) * e1
    rw [this]; exact mul_mem hA hu'
  · have : (U' * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * Yi =
        -((j : Af E) * Z) * (Uu * U' * Yi) := by
      simp only [div_eq_mul_inv, map_mul]
      rw [← hKinv, ← hM, ← hUu]
      linear_combination (Kinv * Uu * Yi * M) * e1 - (Kinv * Uu * Yi * U') * e2 - ((j : Af E) * Z * Uu * U' * Yi) * e3
    rw [this]; exact mul_mem (neg_mem hjZ) hu'

theorem approx_idele : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ k : ℕ, 0 < k → ∃ (m : K) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ Complex.normSq (io m) = b / modF t ∧
      ∀ u ∈ lattice c (y * (upIdele K E t)⁻¹), algebraMap K E m * u ∈ lattice c y ∧
        ((upIdele K E t : Af E) * algebraMap E (Af E) (u / k) - algebraMap E (Af E) (algebraMap K E m * u / k)) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro K _ _ d δ io hK hd hδ E _ _ _ _ t c y hc k hk
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : 0 < N := Nat.pos_of_ne_zero (by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff])
  have hNc : ((N : ℕ) : OF E) ∈ c := Ideal.absNorm_mem c
  obtain ⟨m, hm0, hm⟩ := exists_approx t (k * N)
  obtain ⟨b, hb0, hbk, hb⟩ := GlobalTheory.T.norm_coprime_idele_approximation t k (k * N) (Nat.mul_pos hk hN) (dvd_mul_right k N) m hm0 hm
  exact ⟨m, b, hb0, hbk, by rw [GlobalTheory.T.norm_sq_embedding_imag_quadratic d δ io hK hd hδ, hb], mem_of_approx t c y k N hk hN hNc m hm⟩

end GlobalTheory.ConjApprox
