import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.SignedRename

open MvPolynomial

section General

variable {ι κ : Type} (σ : ι ≃ κ) (s : ι → ℂ)

def ren : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ := aeval fun v => s v • (X (σ v) : MvPolynomial κ ℂ)

theorem ren_monomial (k : ι →₀ ℕ) (c : ℂ) :
    ren σ s (monomial k c) = monomial (k.mapDomain σ) ((k.prod fun v n => s v ^ n) * c) := by
  classical
  have h1 : ∀ (v : ι) (n : ℕ), (s v • (X (σ v) : MvPolynomial κ ℂ)) ^ n =
      C (s v ^ n) * monomial (Finsupp.single (σ v) n) 1 := by
    intro v n
    rw [smul_pow, X_pow_eq_monomial, smul_eq_C_mul]
  rw [ren, aeval_monomial, Finsupp.mapDomain, monomial_finsupp_sum_index]
  simp only [Finsupp.prod, h1, Finset.prod_mul_distrib, algebraMap_eq]
  rw [← map_prod, C_mul]
  ring

theorem coeff_ren (k : ι →₀ ℕ) (P : MvPolynomial ι ℂ) :
    coeff (k.mapDomain σ) (ren σ s P) = (k.prod fun v n => s v ^ n) * coeff k P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [ren_monomial, coeff_monomial, coeff_monomial]
    by_cases hm : m = k
    · subst hm
      simp
    · rw [if_neg hm, if_neg (fun h => hm (Finsupp.mapDomain_injective σ.injective h)), mul_zero]
  | add P Q hP hQ => rw [map_add, coeff_add, coeff_add, hP, hQ, mul_add]

theorem isHomogeneous_ren {ι κ : Type} (f : ι → κ) (s : ι → ℂ) (d : ℕ) (P : MvPolynomial ι ℂ) (h : P.IsHomogeneous d) :
    (aeval (fun v => s v • (X (f v) : MvPolynomial κ ℂ)) P).IsHomogeneous d := by
  have hg : ∀ v, (s v • (X (f v) : MvPolynomial κ ℂ)).IsHomogeneous 1 := by
    intro v
    rw [smul_eq_C_mul]
    exact isHomogeneous_C_mul_X _ _
  have h0 : ∀ r : ℂ, (algebraMap ℂ (MvPolynomial κ ℂ) r).IsHomogeneous 0 := fun r => isHomogeneous_C κ r
  rw [aeval_def]
  simpa only [one_mul] using h.eval₂ (algebraMap ℂ (MvPolynomial κ ℂ)) _ h0 hg

theorem fockIp_ren (hs : ∀ v, s v * conj (s v) = 1) (P Q : MvPolynomial ι ℂ) :
    fockIp (ren σ s P) (ren σ s Q) = fockIp P Q := by
  classical
  have hs0 : ∀ v, s v ≠ 0 := fun v h0 => by simpa [h0] using hs v
  have hp : ∀ k : ι →₀ ℕ, (k.prod fun v n => s v ^ n) ≠ 0 := by
    intro k
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hs0 v)
  have hpc : ∀ k : ι →₀ ℕ, (k.prod fun v n => s v ^ n) * conj (k.prod fun v n => s v ^ n) = 1 := by
    intro k
    rw [Finsupp.prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [map_pow, ← mul_pow, hs v, one_pow]
  have hback : ∀ k' : κ →₀ ℕ, (k'.mapDomain σ.symm).mapDomain σ = k' := by
    intro k'
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  have hfwd : ∀ k : ι →₀ ℕ, (k.mapDomain σ).mapDomain σ.symm = k := by
    intro k
    rw [← Finsupp.mapDomain_comp, Equiv.symm_comp_self, Finsupp.mapDomain_id]
  have hc : ∀ (R : MvPolynomial ι ℂ) (k' : κ →₀ ℕ), coeff k' (ren σ s R) =
      ((k'.mapDomain σ.symm).prod fun v n => s v ^ n) * coeff (k'.mapDomain σ.symm) R := by
    intro R k'
    conv_lhs => rw [← hback k']
    exact coeff_ren σ s _ R
  unfold fockIp
  refine Finset.sum_nbij' (fun k' => k'.mapDomain σ.symm) (fun k => k.mapDomain σ) ?_ ?_ ?_ ?_ ?_
  · intro k' hk'
    rw [mem_support_iff] at hk' ⊢
    rw [hc] at hk'
    exact right_ne_zero_of_mul hk'
  · intro k hk
    rw [mem_support_iff] at hk ⊢
    rw [coeff_ren]
    exact mul_ne_zero (hp k) hk
  · intro k' _
    exact hback k'
  · intro k _
    exact hfwd k
  · intro k' _
    have hF : ((k'.prod fun _ e => e.factorial : ℕ) : ℂ) =
        (((k'.mapDomain σ.symm).prod fun _ e => e.factorial : ℕ) : ℂ) := by
      have := Finsupp.prod_mapDomain_index_inj (h := fun (_ : κ) (e : ℕ) => e.factorial) σ.injective
        (s := k'.mapDomain σ.symm)
      rw [hback] at this
      rw [this]
    rw [hc P, hc Q, hF, map_mul]
    have := hpc (k'.mapDomain σ.symm)
    calc _ = (((k'.mapDomain σ.symm).prod fun v n => s v ^ n) *
          conj ((k'.mapDomain σ.symm).prod fun v n => s v ^ n)) *
          (coeff (k'.mapDomain σ.symm) P * conj (coeff (k'.mapDomain σ.symm) Q) *
          (((k'.mapDomain σ.symm).prod fun _ e => e.factorial : ℕ) : ℂ)) := by ring
      _ = _ := by rw [this, one_mul]

end General

open GlobalTheory.Chain.RealIt.PolyIso in

theorem exists_isPolyIso_graded_isometry : ∀ (p q r s a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool) (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b), SignCompat ε e → SignCompat ε' e' → ∃ κ : LPol b a ≃ₗ[ℂ] Pol p q r s, IsPolyIso ε ε' e e' κ ∧ Graded κ ∧ ∀ P Q, fockIp (κ P) (κ Q) = fockIp P Q := by
  intro p q r s a b ε ε' e e' h h'
  refine ⟨(kap ε e e').toLinearEquiv, ⟨fun Z P => fwd_locS h h' Z P, fun Z P => fwd_locT h h' Z P⟩, ?_, ?_⟩
  · intro d P
    constructor
    · intro hP
      have hb : bwd ε e e' ((kap ε e e').toLinearEquiv P) = P := (kap ε e e').symm_apply_apply P
      rw [← hb]
      exact isHomogeneous_ren (fun l : Ix p q × Ix r s => (e' l.2, e l.1))
        (fun l => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε (e l.1))) d _ hP
    · intro hP
      exact isHomogeneous_ren (fun v : Fin b × Fin a => (e.symm v.2, e'.symm v.1))
        (fun v => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) d P hP
  · intro P Q
    let τ : Fin b × Fin a ≃ Ix p q × Ix r s := (Equiv.prodComm _ _).trans (Equiv.prodCongr e.symm e'.symm)
    have hs : ∀ v : Fin b × Fin a, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2) * conj (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) = 1 := by
      intro v
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn
      split <;> simp
    exact fockIp_ren τ (fun v => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε v.2)) hs P Q

end GlobalTheory.ArchRec.SignedRename

end
