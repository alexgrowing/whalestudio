import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffDen

theorem exists_den_avoid : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (G : HeightOneSpectrum (𝓞 E) → Prop) (c : ℕ), 0 < c → ∀ x : Formalism.L2.Col.HomE E a b, (c : E) • x ∈ M → (∀ Q : HeightOneSpectrum (𝓞 E), ¬ G Q → x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M) → ∃ d : 𝓞 E, d ≠ 0 ∧ (d : E) • x ∈ M ∧ ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q := by
  intro E _ _ a b M G c hc x hcx hloc
  classical
  have hsm : ∀ d : 𝓞 E, (d : E) • x = d • x := fun d => by
    rw [← algebraMap_smul E d x]
  set J : Ideal (𝓞 E) := M.comap (LinearMap.toSpanSingleton (𝓞 E) _ x) with hJ
  have memJ : ∀ d : 𝓞 E, d ∈ J ↔ d • x ∈ M := fun d => by simp [hJ]
  have hc0 : (c : 𝓞 E) ≠ 0 := by exact_mod_cast hc.ne'
  have hcx' : (c : 𝓞 E) • x ∈ M := by
    have hcE : ((c : 𝓞 E) : E) = (c : E) := by simp
    rw [← hsm, hcE]; exact hcx
  have hfin : {Q : HeightOneSpectrum (𝓞 E) | (c : 𝓞 E) ∈ Q.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(c : 𝓞 E)}) (by simpa using hc0)).subset ?_
    intro Q hQ
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hQ)
  set S : Set (HeightOneSpectrum (𝓞 E)) := {Q | (c : 𝓞 E) ∈ Q.asIdeal ∧ ¬ G Q} with hS
  have hSfin : S.Finite := hfin.subset fun Q hQ => hQ.1
  have hnot : ¬ ((J : Set (𝓞 E)) ⊆ ⋃ Q ∈ S, (Q.asIdeal : Set (𝓞 E))) := by
    intro hsub
    rcases S.eq_empty_or_nonempty with h0 | ⟨Q₀, _⟩
    · have hm := hsub ((memJ _).2 hcx')
      simp [h0] at hm
    obtain ⟨Q, hQ, hle⟩ := (Ideal.subset_union_prime_finite hSfin (f := fun Q => Q.asIdeal) Q₀ Q₀
      (fun Q _ _ _ => Q.isPrime)).1 hsub
    obtain ⟨s, hs, hsx⟩ := hloc Q hQ.2
    exact hs (hle ((memJ s).2 hsx))
  obtain ⟨d, hdJ, hdS⟩ := Set.not_subset.1 hnot
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hdS
  have key : ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q :=
    fun Q hcQ hdQ => by_contra fun hG => hdS Q ⟨hcQ, hG⟩ hdQ
  by_cases hd0 : d = 0
  · refine ⟨c, hc0, ?_, fun Q hcQ _ => key Q hcQ (hd0 ▸ Q.asIdeal.zero_mem)⟩
    rw [hsm]; exact hcx'
  · exact ⟨d, hd0, by rw [hsm]; exact (memJ d).1 hdJ, key⟩

end GlobalTheory.OffDen
