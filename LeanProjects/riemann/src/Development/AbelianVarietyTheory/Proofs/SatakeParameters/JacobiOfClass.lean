import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.HostCls
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsOrth
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HostInert

open Formalism.InvariantFactorPaths.G7 (lgF at1) in
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp) in

theorem inParamK_eq {l : ℕ} [Fact l.Prime] {ι : Type} (f : MvPowerSeries ι ℂ_[l]) :
    @Formalism.MainNotions.FormalGroupSystem.inParamK l _ ι ℂ_[l] _ (wittFractionAlgebraCp l) f = MvPowerSeries.subst (fun i => at1 i (lgF ℂ_[l] l)) f := by
  unfold Formalism.MainNotions.FormalGroupSystem.inParamK
  have hlog : PowerSeries.map (k0ToC l) (Formalism.MainNotions.FormalGroupSystem.logF l) = lgF ℂ_[l] l := by
    ext n
    rw [PowerSeries.coeff_map]
    simp only [Formalism.MainNotions.FormalGroupSystem.logF, lgF, PowerSeries.coeff_mk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_mul]
    split_ifs <;> simp
  congr 1
  funext i
  rw [show @algebraMap (Formalism.MainNotions.FormalGroupSystem.K0 l) ℂ_[l] _ _ (wittFractionAlgebraCp l) = k0ToC l from rfl, hlog]
  rfl

theorem jacobi_of_class (D : D7) (p : ℕ) [Fact p.Prime] (h : IsResidueClassZero D p ∨ IsSg D p) :
    jacobiSym (-(D.host.d : ℤ)) p = -1 := by
  have hp : p.Prime := Fact.out
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have key : p ≠ D.host.d ∧ jacobiSym (-(D.host.d : ℤ)) p ≠ 1 := by
    have h' : D.host.cls p = PrimeClass.inertClass ∨
        D.host.cls p = PrimeClass.signal := h
    rcases h' with h' | h'
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_inert_iff _).1 h'
      exact ⟨h3, h4⟩
    · obtain ⟨-, -, h3, h4, -⟩ := (primeClass_eq_signal_iff _).1 h'
      exact ⟨h3, h4⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rcases jacobiSym.trichotomy (-(D.host.d : ℤ)) p with h0 | h1 | h1
  · exfalso
    rw [jacobiSym.eq_zero_iff_not_coprime] at h0
    apply h0
    have : Nat.Coprime D.host.d p := (Nat.coprime_primes hd hp).2 key.1.symm
    simpa [Int.gcd_neg, Int.gcd_natCast_natCast] using this
  · exact absurd h1 key.2
  · exact h1

theorem hostAt_inert : Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam := by
  intro h1 h2 h3 D cc δ B χ hc hδ hχ p _ lam h5 hcl
  have hin := jacobi_of_class D p hcl
  obtain ⟨cc', δ', g, -, -, hL, hlam, hAt, hM, hLT⟩ := h1 D cc δ hc hδ p h5 hin lam
  obtain ⟨g2, g3, ε, s2, -, -, -, -, hn, ⟨a1, a2, a3, a4, a5, -, F, hF, -⟩, hD⟩ := h2 D cc' δ' p g hLT hAt h5 hin hM
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.fieldDataCM p h5
  refine ⟨_, g2, g3, s2, ε, σ, F, hn, ⟨h5, a1, a2, a3, a4, hσ, hF, a5 σ hσ⟩, ?_⟩
  intro N N' L L' hA
  obtain ⟨r, b, hb, ho⟩ := Formalism.L2.KerInert.orthBasisExists_of Formalism.L2.KerInert.global_orthonormal_basis_four
    Formalism.L2.KerInert.weakApprox_of_approx_and_separation D p h5 hin N N' L L' hA
  refine ⟨r, b, hb, ho, fun G hG => ?_⟩
  obtain ⟨C, wq, hC, hw, hd⟩ := hD D
  have hΛ : g.abelian₂ = B.tor.abelian₂ := hAt.2.2.2.1.trans hL
  subst hlam
  rw [hΛ] at hC hw hd
  have := hd N N' r b G (h3 D cc δ B hc hδ χ hχ p h5 hin g.lam N N' L L' hA G hG C wq r b hC hw hb ho)
  rw [HostLog.iff_phSum]
  rw [inParamK_eq] at this
  exact this

end GlobalTheory.KerStd.HostInert
