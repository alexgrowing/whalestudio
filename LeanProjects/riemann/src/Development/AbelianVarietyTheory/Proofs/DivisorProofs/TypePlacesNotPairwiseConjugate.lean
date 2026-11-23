import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
open scoped Pointwise

namespace GlobalTheory.TypePlaces

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem not_isConjPl : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (Pl D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl PP PP' := by
  intro D Pb Pg hPg PP hP PP' hP' hc
  obtain ⟨k, hk⟩ := (hPg PP).1 hP
  obtain ⟨k', hk'⟩ := (hPg PP').1 hP'
  have hle : D.host.conj • PP.asIdeal ≤ PP'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hzv, hz⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hz.trans (star_eq_conj D _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hzv
  have hmax : (D.host.conj • PP.asIdeal).IsMaximal := by
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • PP.asIdeal = PP'.asIdeal := hmax.eq_of_le PP'.isPrime.ne_top hle
  obtain ⟨ho, hm⟩ := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP
    (Pb.overP hk)).2.2.2 (Pb.pb k) (Pb.pb_over k) PP' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj PP PP').2 heq)
  have hkk : k ≠ k' := by
    rintro rfl
    exact hm.1 hk hk'
  have ho' := Pb.overP hk'
  have hne : D.host.g k ≠ D.host.g k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k'
    · exact absurd rfl hkk
    · exact this
    · exact this.symm
    · exact absurd rfl hkk
  have hco : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hne)
  obtain ⟨a, b, hab⟩ := hco
  apply PP'.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ ho) (Ideal.mul_mem_left _ _ ho')

end GlobalTheory.TypePlaces
