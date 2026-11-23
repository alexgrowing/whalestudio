import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryReductionPolynomialHeightBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.LatMatch

theorem exists_nat_mul_intAf' {F : Type} [Field F] [NumberField F] (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    ∃ m : ℕ, 0 < m ∧ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * t ∈ intAf F := by
  obtain ⟨m, hm, h⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_intAd t
  exact ⟨m, hm, fun v => h v⟩

set_option maxHeartbeats 1000000 in
theorem exists_nat_smul_intAE {D : D7} (w : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ k : ℕ, 0 < k ∧ k • w ∈ intAE D := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | tmul β z =>
    obtain ⟨m, hm, hβ⟩ := exists_nat_mul_intAf' β
    obtain ⟨M, hM, o, ho⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.exists_nat_mul_mem z
    refine ⟨m * M, Nat.mul_pos hm hM, ?_⟩
    have e : (m * M) • (β ⊗ₜ[D.host.F] z) = ((m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * β) ⊗ₜ[D.host.F] ((o : 𝓞 D.host.E) : D.host.E) := by
      have ho' : ((o : 𝓞 D.host.E) : D.host.E) = (M : D.host.E) * z := ho
      rw [ho', mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, nsmul_eq_mul]
    rw [e]
    exact AddSubgroup.subset_closure ⟨_, hβ, o, rfl⟩
  | add w w' h h' =>
    obtain ⟨k, hk, m⟩ := h
    obtain ⟨k', hk', m'⟩ := h'
    refine ⟨k * k', Nat.mul_pos hk hk', ?_⟩
    have e : (k * k') • (w + w') = k' • (k • w) + k • (k' • w') := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm k' k]
    rw [e]
    exact add_mem (nsmul_mem m k') (nsmul_mem m' k)

theorem exists_nat_smul_single {D : D7} (V : HSp D) :
    ∃ b : ℕ, 0 < b ∧ ∀ j : Fin V.rank, (Pi.single j (b : D.host.E) : Fin V.rank → D.host.E) ∈ GlobalTheory.Member.latC V := by
  classical
  have hspan := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.1
  have key : ∀ v : Fin V.rank → D.host.E, ∃ m : ℕ, 0 < m ∧ (m : D.host.E) • v ∈ GlobalTheory.Member.latC V := by
    intro v
    have hv : v ∈ Submodule.span D.host.E (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
      rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨k, hk, hky⟩ := hy
      refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
      have e : ((m * k : ℕ) : D.host.E) • (x + y) = k • ((m : D.host.E) • x) + m • ((k : D.host.E) • y) := by
        simp only [smul_add, Nat.cast_mul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul]
        rw [mul_comm (k : D.host.E) (m : D.host.E)]
      rw [e]
      exact add_mem (Submodule.smul_of_tower_mem _ k hmx) (Submodule.smul_of_tower_mem _ m hky)
    | smul c x _ hx =>
      obtain ⟨m, hm, hmx⟩ := hx
      obtain ⟨d, hd, hdc⟩ := GlobalTheory.SmoothForms.Reduce.exists_nat_integral (fun _ : Unit => c)
      refine ⟨d * m, Nat.mul_pos hd hm, ?_⟩
      have e : ((d * m : ℕ) : D.host.E) • (c • x) = (⟨(d : D.host.E) * c, (mem_integralClosure_iff _ _).2 (hdc ())⟩ : 𝓞 D.host.E) • ((m : D.host.E) • x) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Algebra.smul_def]
        change (((d * m : ℕ) : D.host.E)) * (c * x i) = ((d : D.host.E) * c) * ((m : D.host.E) * x i)
        push_cast
        ring
      rw [e]
      exact (GlobalTheory.Member.latC V).smul_mem _ hmx
  choose m hm hmv using fun j : Fin V.rank => key (Pi.single j 1)
  refine ⟨∏ j, m j, Finset.prod_pos fun j _ => hm j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have : (Pi.single j (((∏ i ∈ Finset.univ.erase j, m i) * m j : ℕ) : D.host.E) : Fin V.rank → D.host.E) =
      (∏ i ∈ Finset.univ.erase j, m i) • ((m j : D.host.E) • Pi.single j 1) := by
    funext i
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Pi.single_apply, h]
  rw [this]
  exact Submodule.smul_of_tower_mem _ _ (hmv j)

theorem mul_mem_intAE' (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem mulVec_lamHat_bound : ∀ {D : D7} (V V' : HSp D) (X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  intro D V V' X
  classical
  obtain ⟨m, hm, hden⟩ := GlobalTheory.SmoothForms.Reduce.den_hat (D := D) (GlobalTheory.Member.latC V)
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.1
  choose k hk hkX using fun p : Fin V'.rank × Fin V.rank => exists_nat_smul_intAE (D := D) (X p.1 p.2)
  have hc : 0 < ∏ p, k p := Finset.prod_pos fun p _ => hk p
  have hcX : ∀ j i, (∏ p, k p) • X j i ∈ intAE D := by
    intro j i
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (j, i)), mul_smul]
    exact nsmul_mem (hkX (j, i)) _
  obtain ⟨b, hb, hbs⟩ := exists_nat_smul_single V'
  refine ⟨b * ((∏ p, k p) * m), Nat.mul_pos hb (Nat.mul_pos hc hm), fun y hy => ?_⟩
  have hy' : ∀ i, m • y i ∈ intAE D := hden y (by rw [← GlobalTheory.LatDual.lamHat_eq_hat]; exact hy)
  have hw : ∀ j, ((∏ p, k p) * m) • X.mulVec y j ∈ intAE D := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum]
    refine sum_mem fun i _ => ?_
    have := mul_mem_intAE' D (hcX j i) (hy' i)
    convert this using 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have hV' : ∀ w : Fin V'.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (∀ j, w j ∈ intAE D) →
      (fun j => (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w j) ∈ Formalism.L2.NTheta.LamHat V' := by
    intro w hw
    have e : (fun j => (b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * w j) = ∑ l, (fun j => w l *
        ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single l (b : D.host.E) : Fin V'.rank → D.host.E) j)) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, ← Algebra.TensorProduct.natCast_def', mul_comm]
      · intro l _ hl
        rw [Pi.single_eq_of_ne (Ne.symm hl), TensorProduct.tmul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [e]
    refine sum_mem fun l _ => GlobalTheory.LatDual.smul_mem_lamHat V' _ (hw l) _ ?_
    refine AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, _, ?_, rfl⟩
    have h := (GlobalTheory.Member.mem_latC V' _).1 (hbs l)
    rw [Module.Basis.equivFun_symm_apply] at h
    exact h
  have := hV' _ hw
  convert this using 1
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.LatMatch
