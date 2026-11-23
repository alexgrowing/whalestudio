import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_small_of_mem_nhds {t : Set (FiniteAdeleRing R K)}
    (ht : t ∈ nhds (0 : FiniteAdeleRing R K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : FiniteAdeleRing R K,
      (∀ v : HeightOneSpectrum R, Valued.v (y v) ≤ v.intValuation r) → y ∈ t := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let z0 : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨0, (v.adicCompletionIntegers K).zero_mem⟩
  let t' : Set (RestrictedProduct (fun v : HeightOneSpectrum R => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite) := t
  have h1' : t' ∈
      nhds (RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z0) := ht
  rw [RestrictedProduct.nhds_eq_map_structureMap hAopen, Filter.mem_map, nhds_pi,
    Filter.mem_pi'] at h1'
  obtain ⟨I, u, hu, hIu⟩ := h1'
  have hW : ∀ v, ∃ W : Set (v.adicCompletion K), W ∈ nhds (0 : v.adicCompletion K) ∧
      ∀ y : v.adicCompletion K, (hy : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) →
        y ∈ W → (⟨y, hy⟩ : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∈ u v := by
    intro v
    obtain ⟨W, hW, hWu⟩ := (mem_nhds_subtype _ (z0 v) (u v)).mp (hu v)
    exact ⟨W, hW, fun y hy hyW => hWu hyW⟩
  choose W hW0 hWu using hW
  obtain ⟨r, hr, hsmall⟩ :=
    PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_small_finset (R := R) (K := K) I W (fun v _ => hW0 v)
  refine ⟨r, hr, fun y hy => ?_⟩
  have hint : ∀ v : HeightOneSpectrum R,
      y v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v
    rw [SetLike.mem_coe, mem_adicCompletionIntegers]
    exact (hy v).trans (v.intValuation_le_one r)
  let z : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨y v, hint v⟩
  have hz : z ∈ Set.pi (↑I) u := fun v hv => hWu v _ (hint v) (hsmall v hv _ (hy v))
  have hmem := hIu hz
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z = y := by
    ext v; rfl
  rw [← e]
  exact hmem

end GlobalTheory.OpenSubAdele

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem exists_nat_mul_mem_of_mem_nhds {F : Type} [Field F] [NumberField F] {t : Set (Af F)}
    (ht : t ∈ nhds (0 : Af F)) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ b ∈ GlobalTheory.HolDict.ShortVec.intRing F, (M₀ : Af F) * b ∈ t := by
  obtain ⟨r, hr, h⟩ := exists_small_of_mem_nhds (R := 𝓞 F) (K := F) ht
  have hc := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := Ideal.span {r}) hr
    (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hm
  have hdvd : r ∣ ((m.natAbs : ℕ) : 𝓞 F) := by
    refine hm.trans ((map_dvd (algebraMap ℤ (𝓞 F)) (Int.dvd_natAbs.mpr dvd_rfl)).trans ?_)
    simp
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨m.natAbs, Int.natAbs_pos.mpr hm0, fun b hb => h _ fun v => ?_⟩
  have hb' : evalV F v b ∈ v.adicCompletionIntegers F := Subring.mem_iInf.mp hb v
  change Valued.v (evalV F v ((m.natAbs : Af F) * b)) ≤ _
  have e : ((m.natAbs : ℕ) : Fv F v) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (r * c)) := by
    rw [← hc]; simp
  rw [map_mul, map_natCast, e, Valuation.map_mul, PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R, map_mul]
  calc v.intValuation r * v.intValuation c * Valued.v (evalV F v b)
      ≤ v.intValuation r * 1 * 1 :=
        mul_le_mul' (mul_le_mul' le_rfl (v.intValuation_le_one c))
          ((mem_adicCompletionIntegers _ _ _).mp hb')
    _ = v.intValuation r := by simp

end GlobalTheory.OpenSubAdele

namespace GlobalTheory.OpenSubAdele

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable def singleEntry (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) (c : Af D.host.F) : WO V W :=
  Matrix.of fun i' j' => if i = i' then if j = j' then
    pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k else 0 else 0

theorem continuous_singleEntry (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) : Continuous (singleEntry D V W i j k) := by
  have hp : Continuous (fun c : Af D.host.F => pairA D.host.F 0 c) := by
    unfold pairA; fun_prop
  have ht : Continuous (fun c : Af D.host.F =>
      (pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)) := by
    have e : (fun c : Af D.host.F =>
        (pairA D.host.F 0 c ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)) =
        fun c => pairA D.host.F 0 c •
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D) := by
      funext c; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact hp.smul (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k : AE D)))
  unfold singleEntry
  refine continuous_pi fun i' => continuous_pi fun j' => ?_
  simp only [Matrix.of_apply]
  split_ifs
  · exact ht
  · exact continuous_const
  · exact continuous_const

theorem singleEntry_zero (D : D7) (V W : HSp D) (i : Fin W.rank) (j : Fin V.rank)
    (k : Fin (Module.finrank D.host.F D.host.E)) : singleEntry D V W i j k 0 = 0 := by
  ext i' j'
  have h0 : pairA D.host.F 0 0 = 0 := rfl
  simp [singleEntry, h0]

theorem exists_nat_mul_mem_openAddSubgroup : ∀ (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)),
    IsOpen (U : Set (WO V W)) → ∃ M₀ : ℕ, 0 < M₀ ∧
      ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
        (∀ i j k, a i j k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) →
        (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
          Module.finBasis D.host.F D.host.E k : WO V W) ∈ U := by
  intro D V W U hU
  have hnhds : (⋂ x : Fin W.rank × Fin V.rank × Fin (Module.finrank D.host.F D.host.E),
      singleEntry D V W x.1 x.2.1 x.2.2 ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) := by
    refine Filter.iInter_mem.mpr fun x => ?_
    refine (continuous_singleEntry D V W x.1 x.2.1 x.2.2).continuousAt.preimage_mem_nhds ?_
    rw [singleEntry_zero]
    exact hU.mem_nhds U.zero_mem
  obtain ⟨M₀, hM₀, hM⟩ := exists_nat_mul_mem_of_mem_nhds hnhds
  refine ⟨M₀, hM₀, fun a ha => ?_⟩
  have hsum : (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
          Module.finBasis D.host.F D.host.E k : WO V W) =
      ∑ i, ∑ j, ∑ k, singleEntry D V W i j k ((M₀ : Af D.host.F) * a i j k) := by
    ext i' j'
    simp [singleEntry, Matrix.sum_apply]
  rw [hsum]
  refine U.sum_mem fun i _ => U.sum_mem fun j _ => U.sum_mem fun k _ => ?_
  have := hM _ (ha i j k)
  exact Set.mem_iInter.mp this (i, j, k)

end GlobalTheory.OpenSubAdele
