import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove in

theorem inverseHalfDifferent_local_trivial_at_prime_norm {R : Ranks} (H : Host R) (P : HeightOneSpectrum (𝓞 H.E)) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (H.AA0 : Submodule (𝓞 H.E) H.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 H.E) H.E) := by
  have := P.isPrime
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hnd := GlobalTheory.PeriodIdealUnit.not_dvd_different (K := H.K) hp P.asIdeal hmem h2
  have hnot : ¬ H.𝔟 ≤ P.asIdeal := fun hle => hnd (by
    rw [H.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := SetLike.not_le_iff_exists.1 hnot
  have hB : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 := H.𝔟_spec.2
      simp [h] at h3
  refine GlobalTheory.PeriodIdealUnit.locP_eq_one P _ ?_ ?_
  · intro t ht
    have ht' : t ∈ H.AA0 := ht
    unfold Host.AA0 at ht'
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hB).1 ht' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine (mem_locP P 1 t).2 ⟨z, hzP, Submodule.mem_one.2 ⟨w, ?_⟩⟩
    rw [Algebra.smul_def, hw, mul_comm]
  · refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [one_smul]
    show (1 : H.E) ∈ H.AA0
    unfold Host.AA0
    refine (FractionalIdeal.mem_inv_iff hB).2 fun y hy => ?_
    rw [one_mul]
    exact FractionalIdeal.coeIdeal_le_one hy

theorem aaUnit_sall : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  intro B X I hOk u a χ P hP
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr hOk.sel_ok
    (hOk.T_mem u) hOk.g_mem P hP
  show Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Th.perAA B.host ⊤) = _
  rw [Th.perAA_top]
  exact inverseHalfDifferent_local_trivial_at_prime_norm B.host P bad.2.1 bad.2.2.1

end GlobalTheory.Mem.Col2.AdT
