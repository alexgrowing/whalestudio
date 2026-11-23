import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.LinkThIndepOfGen

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem embT_inj : Function.Injective (embT D) := by
  intro τ τ' h
  have h2 : D.host.sigmaOf ((D.eTau τ : D.R.Psi) : D.R.GG) =
      D.host.sigmaOf ((D.eTau τ' : D.R.Psi) : D.R.GG) := by
    refine AlgEquiv.ext fun x => ?_
    exact D.host.φ₀.injective (congrArg (fun f : D.host.E →+* ℂ => f x) h)
  have h3 := congrArg (D.host.galE) h2
  rw [galE_sigmaOf, galE_sigmaOf] at h3
  exact D.eTau.injective (Subtype.ext h3)

abbrev algKC : Algebra D.host.K ℂ := (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toAlgebra

def embA (τ : D.what₂.Tau) : @AlgHom D.host.K D.host.E ℂ _ _ _ _ (algKC D) :=
  letI := algKC D
  { embT D τ with
    commutes' := fun r => by
      show embT D τ (r : D.host.E) = D.host.φ₀ (r : D.host.E)
      exact embT_K D τ _ r.2 }

theorem bE_mem : D.host.sqd ∈ D.host.K :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

theorem embA_bij : letI := algKC D; Function.Bijective (embA D) := by
  letI := algKC D
  constructor
  · intro τ τ' h
    apply embT_inj D
    ext x
    exact congrArg (fun f : D.host.E →ₐ[D.host.K] ℂ => f x) h
  · intro σ
    obtain ⟨τ, hτ | hτ⟩ := emb_cases D (σ : D.host.E →+* ℂ)
    · refine ⟨τ, AlgHom.ext fun x => ?_⟩
      have := congrArg (fun f : D.host.E →+* ℂ => f x) hτ
      exact this.symm
    · exfalso
      have hb := bE_mem D
      have h1 : σ (D.host.sqd) = D.host.φ₀ (D.host.sqd) :=
        σ.commutes ⟨_, hb⟩
      have h2 := congrArg (fun f : D.host.E →+* ℂ => f (D.host.sqd)) hτ
      simp only [AlgHom.coe_toRingHom, RingHom.comp_apply] at h2
      rw [embT_K D τ _ hb, h1] at h2
      have h0 : D.host.φ₀ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) :=
        D.host.φ₀_mem
      rw [h0, map_mul, Complex.conj_I, Complex.conj_ofReal] at h2
      have hs := Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.sqrt_d_pos D
      have : (Real.sqrt D.host.d : ℂ) = 0 := by
        have h3 : 2 * Complex.I * (Real.sqrt D.host.d : ℂ) = 0 := by linear_combination h2
        simpa [Complex.I_ne_zero] using h3
      exact hs.ne' (by exact_mod_cast this)

theorem sum_tau_trace (z : D.host.E) :
    ∑ τ : D.what₂.Tau, embT D τ z =
      D.host.φ₀ ((Algebra.trace D.host.K D.host.E z : D.host.K) : D.host.E) := by
  letI := algKC D
  have h := _root_.trace_eq_sum_embeddings (K := D.host.K) (L := D.host.E) ℂ (x := z)
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at h
  change _ = D.host.φ₀ (algebraMap D.host.K D.host.E _)
  rw [h, ← (Equiv.ofBijective _ (embA_bij D)).sum_comp]
  rfl

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ (D.host.conj x) = starRingEnd ℂ (φ x) := by
  exact D.host.conjE_apply φ x

theorem Hf_embV (T : Tor D) (hT : ∀ τ x, T.emb τ x = embT D τ x) {N N' : ℕ}
    (A B : Matrix (Fin N') (Fin N) D.host.E) :
    Hf D T (embV D T A) (embV D T B) =
      D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E) / (area T.abelian₂ : ℂ) := by
  unfold Hf hYY
  congr 1
  rw [← sum_tau_trace]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [embV, hT, map_sum, map_mul, emb_conj]

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.FL

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def HfArithRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ c ∈ cc, ∀ c' ∈ cc, ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L',
        Good D (δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) *
          starRingEnd ℂ (δ * D.host.φ₀ (((c' : D.host.K) : D.host.E))) *
          (D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E) / (area (lamOf D cc δ) : ℂ)))

theorem HfGenRec_of_arith (h : HfArithRec) : HfGenRec := by
  intro D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'
  rw [FL.Hf_embV D (tor0 D cc δ) (fun _ _ => rfl) A B]
  exact h D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'

theorem LinkThIndep_of_arith (hA : HfArithRec) (hB : SelfDualRec) : LinkThIndep :=
  LinkThIndep_of_gen (HfGenRec_of_arith hA) hB

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
