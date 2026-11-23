import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.SkewLatSelfDual

open GlobalTheory.FunObj.SqNum

variable {D : D7}

abbrev FI (D : D7) : Type := FractionalIdeal (𝓞 D.host.E)⁰ D.host.E

theorem star_eq_conj (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_smul_conj_smul (𝔞 : Ideal (𝓞 D.host.E)) : D.host.conj • (D.host.conj • 𝔞) = 𝔞 := by
  rw [smul_smul]
  have : D.host.conj * D.host.conj = 1 := AlgEquiv.ext (VacMove.conj_conj D)
  rw [this, one_smul]

theorem conj_smul_ne_bot {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) : D.host.conj • 𝔞 ≠ ⊥ := by
  intro h'
  apply h
  rw [← conj_smul_conj_smul 𝔞, h']
  ext x
  simp [Ideal.mem_pointwise_smul_iff_inv_smul_mem]

theorem coe_ne_zero {𝔞 : Ideal (𝓞 D.host.E)} (h : 𝔞 ≠ ⊥) : ((𝔞 : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
  rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

theorem conj_mem_div {A B : Ideal (𝓞 D.host.E)} (hB : B ≠ ⊥) {x : D.host.E}
    (hx : x ∈ ((A : FI D) / (B : FI D))) :
    D.host.conj x ∈ (((D.host.conj • A : Ideal (𝓞 D.host.E)) : FI D) / ((D.host.conj • B : Ideal (𝓞 D.host.E)) : FI D)) := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero hB)] at hx
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (coe_ne_zero (conj_smul_ne_bot hB))]
  intro y hy
  obtain ⟨β, hβ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have hβ' : D.host.conj • β ∈ B := by
    have := Ideal.smul_mem_pointwise_smul D.host.conj β _ hβ
    rwa [conj_smul_conj_smul] at this
  obtain ⟨α, hα, hαe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hx _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hβ', rfl⟩))
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨D.host.conj • α, Ideal.smul_mem_pointwise_smul _ _ _ hα, ?_⟩
  have e1 : algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • α) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E α) := rfl
  have e2 : algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • β) = D.host.conj (algebraMap (𝓞 D.host.E) D.host.E β) := rfl
  rw [e1, hαe, e2, map_mul, VacMove.conj_conj]

theorem mem_skewLat {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} (v : Fin N → D.host.E) :
    v ∈ skewLat D 𝔪 N ↔ ∀ i, v i ∈ ((𝔪 : FI D) / ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FI D)) := by
  simp [skewLat, Submodule.mem_pi]

theorem skewLat_SD {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : SD D (skewLat D 𝔪 N) := by
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪 with h𝔫
  have h𝔫0 : 𝔫 ≠ ⊥ := conj_smul_ne_bot h𝔪
  have h𝔪𝔫 : D.host.conj • 𝔫 = 𝔪 := conj_smul_conj_smul 𝔪
  set I : FI D := (𝔪 : FI D) / (𝔫 : FI D) with hIdef
  set J : FI D := (𝔫 : FI D) / (𝔪 : FI D) with hJdef
  have hI0 : I ≠ 0 := div_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hJ0 : J ≠ 0 := div_ne_zero (coe_ne_zero h𝔫0) (coe_ne_zero h𝔪)
  have hJI : J * I = 1 := by
    rw [hIdef, hJdef, div_mul_div_comm, mul_comm (𝔫 : FI D), div_self]
    exact mul_ne_zero (coe_ne_zero h𝔪) (coe_ne_zero h𝔫0)
  have hIJ' : 1 / J = I := by rw [hJdef, hIdef, one_div_div]
  have cI : ∀ x ∈ I, D.host.conj x ∈ J := fun x hx => by
    have := conj_mem_div h𝔫0 hx
    rwa [h𝔪𝔫] at this
  have cJ : ∀ z ∈ J, D.host.conj z ∈ I := fun z hz => by
    have := conj_mem_div h𝔪 hz
    rwa [h𝔪𝔫] at this
  have memL : ∀ v : Fin N → D.host.E, v ∈ skewLat D 𝔪 N ↔ ∀ i, v i ∈ I := mem_skewLat
  letI := D.host.cmStar
  show IsSDLat D.host.E N (skewLat D 𝔪 N)
  refine ⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (I : Submodule (𝓞 D.host.E) D.host.E))
      (fun h => hI0 (FractionalIdeal.coeToSubmodule_injective (h.trans FractionalIdeal.coe_zero.symm)))
    have hs : ∀ i : Fin N, (Pi.single i a : Fin N → D.host.E) ∈ skewLat D 𝔪 N := fun i => by
      rw [memL]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using ha
      · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    rw [Submodule.eq_top_iff']
    intro x
    have : x = ∑ i, (x i * a⁻¹) • (Pi.single i a : Fin N → D.host.E) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, ha0]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs i))
  · rw [memL] at hx hy
    unfold Formalism.BasicNotions.stdH
    refine Subring.sum_mem _ fun i _ => ?_
    have hm : star (x i) * y i ∈ J * I := by
      rw [star_eq_conj]
      exact FractionalIdeal.mul_mem_mul (cI _ (hx i)) (hy i)
    rw [hJI] at hm
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    exact ⟨a, ha⟩
  · rw [memL]
    intro i
    rw [← hIJ', FractionalIdeal.mem_div_iff_of_ne_zero hJ0]
    intro z hz
    have hx : (Pi.single i (D.host.conj z) : Fin N → D.host.E) ∈ skewLat D 𝔪 N := by
      rw [memL]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using cJ z hz
      · rw [Pi.single_eq_of_ne hj]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    have h1 := h _ hx
    unfold Formalism.BasicNotions.stdH at h1
    have e : (∑ j, star ((Pi.single i (D.host.conj z) : Fin N → D.host.E) j) * y j) = y i * z := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, star_eq_conj, VacMove.conj_conj, mul_comm]
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
    rw [e] at h1
    obtain ⟨a, ha⟩ := h1
    exact (FractionalIdeal.mem_one_iff _).2 ⟨a, ha⟩

end GlobalTheory.SkewLatSelfDual
