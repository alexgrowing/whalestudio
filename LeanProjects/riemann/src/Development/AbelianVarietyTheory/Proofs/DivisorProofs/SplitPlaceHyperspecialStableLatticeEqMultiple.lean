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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceChartOfSplitIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitSupportedUnitaryComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMultipleOfStandardLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.SplitLatMatch

open GlobalTheory.SplitHecke

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem half (V : HSp D) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e)
    (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)))
    (hM : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M)
    (hf : ∀ z ∈ M, finPart D (e + cA D e) • z = z)
    (hb : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V)
    (hK : ∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) :
    ∃ a a' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, finPart D e * a * a' = finPart D e ∧
      ∀ z, (finPart D e • z ∈ M ↔ (finPart D e * a) • z ∈ Formalism.L2.NTheta.LamHat V) := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨β, hβ⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ V
  obtain ⟨φ, hφ⟩ := GlobalTheory.SplitFrame.exists_factor hπ
  have hπe : π e = 1 := GlobalTheory.SplitHomLattice.pi_idem he hπ
  have hpe : φ (finPart D e) = 1 := by rw [hφ]; exact hπe
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hφs : Function.Surjective φ := fun t => by
    obtain ⟨a, rfl⟩ := hπ.1 t
    exact ⟨finPart D a, hφ a⟩
  have hker : ∀ x, φ x = 0 → finPart D e * x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := GlobalTheory.SplitHecke.Stab.finPart_surj x
    rw [hφ] at hx
    rw [← map_mul, (hπ.2.1 a).1 hx, map_zero]
  let T : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V.rank → Fv D.host.F v) :=
    { toFun := fun z => (β⁻¹).1 *ᵥ fun k => φ (z k)
      map_zero' := by
        have : (fun k : Fin V.rank => φ ((0 : Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) k)) = 0 :=
          funext fun k => by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
        simp only [this, Matrix.mulVec_zero]
      map_add' := by
        intro x y
        have : (fun k => φ ((x + y) k)) = (fun k => φ (x k)) + fun k => φ (y k) :=
          funext fun k => by rw [Pi.add_apply, map_add, Pi.add_apply]
        simp only [this, Matrix.mulVec_add] }
  have hT : ∀ z, T z = (β⁻¹).1 *ᵥ fun k => φ (z k) := fun z => rfl
  have hTs : ∀ (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) z, T (x • z) = φ x • T z := by
    intro x z
    rw [hT, hT, ← Matrix.mulVec_smul]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  have hTp : ∀ z, T (finPart D e • z) = T z := by
    intro z; rw [hTs, hpe, one_smul]
  have hmem : ∀ z, finPart D e • z ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, T z i ∈ v.adicCompletionIntegers D.host.F := by
    intro z
    choose y hy using fun k => GlobalTheory.SplitHecke.Stab.finPart_surj (z k)
    have e1 : finPart D e • z = fun i => finPart D (e * y i) := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, hy]
    have e2 : (fun k => φ (z k)) = fun k => π (y k) := funext fun k => by rw [← hy, hφ]
    rw [e1, hβ y, hT, e2]
    exact forall_congr' fun i => isInt_Ov
  have hinj : ∀ z m, T z = T m → finPart D e • z = finPart D e • m := by
    intro z m h
    have h1 : (fun k => φ (z k)) = fun k => φ (m k) := by
      have := congrArg (fun u => β.1 *ᵥ u) h
      simpa only [hT, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] using this
    funext k
    have h2 := hker (z k - m k) (by rw [map_sub, sub_eq_zero]; exact congrFun h1 k)
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at h2
    exact h2
  let S : AddSubgroup (Fin V.rank → Fv D.host.F v) := M.map T
  have hS : ∀ z, T z ∈ S ↔ finPart D e • z ∈ M := by
    intro z
    constructor
    · rintro ⟨m, hm, h⟩
      rw [hinj z m h.symm]
      exact hM _ hpO m hm
    · intro h
      exact ⟨_, h, hTp z⟩
  obtain ⟨N, hN, hlo, hup⟩ := hb
  have : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F (Fv D.host.F v)).injective
  have hN' : ((N : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hφN : φ ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = (N : Fv D.host.F v) := map_natCast φ N
  have hf' : finPart D (e + cA D e) * finPart D e = finPart D e := by
    rw [(finPart D).map_add, add_mul, hpp, mul_comm (finPart D (cA D e)), hpq, add_zero]
  obtain ⟨t, ht, hSt⟩ := GlobalTheory.LatticeBetweenMultiples.eq_multiple_of_standard_lattice v S (by
      intro o ho w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨a, ha⟩ := hπ.1 o
      refine ⟨finPart D (e * a) • m, hM _ ((hπ.2.2.2 a).2 (isInt_Ov.2 (ha ▸ ho))) m hm, ?_⟩
      rw [hTs, hφ, map_mul, hπe, one_mul, ha])
    (by
      refine ⟨N, hN', fun w hw => ?_⟩
      choose z hz using fun k => hφs ((β.1 *ᵥ w) k)
      have hTz : T z = w := by
        rw [hT, (funext hz : (fun k => φ (z k)) = β.1 *ᵥ w), Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec]
      have hzL : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := (hmem z).2 (by rw [hTz]; exact hw)
      have h1 := hlo _ hzL
      rw [smul_smul (finPart D (e + cA D e)), hf'] at h1
      exact ⟨_, h1, by rw [hTs, hTp, hφN, hTz]⟩)
    (by
      refine ⟨N, hN', fun w hw i => ?_⟩
      obtain ⟨m, hm, rfl⟩ := hw
      have h2 : finPart D e • (((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • m) ∈ Formalism.L2.NTheta.LamHat V :=
        GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ (hup m hm)
      have h3 := (hmem _).1 h2 i
      rwa [hTs, hφN, Pi.smul_apply, smul_eq_mul] at h3)
    (by
      intro x hx1 hx2 w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v π he hπ V β x
      have hgK : g ∈ KsphC V ∅ := (GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ V β hβ g hg).2 (by
        rw [hgx]
        exact ⟨fun i j => isInt_Ov.2 (hx1 i j), fun i j => isInt_Ov.2 (hx2 i j)⟩)
      refine ⟨_, hK g hgK hg m hm, ?_⟩
      have e1 : (fun k => φ ((finMat D.sp.cm.sig V.gram g *ᵥ m) k)) = (mt V g).map π *ᵥ fun k => φ (m k) := by
        funext k
        rw [RingHom.map_mulVec, GlobalTheory.SplitHecke.Stab.finMat_eq, Matrix.map_map]
        congr 2
        funext y
        exact hφ y
      rw [hT, hT, e1, ← hgx, rho_val, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one])
  obtain ⟨a, ha⟩ := hφs t
  obtain ⟨a', ha'⟩ := hφs t⁻¹
  refine ⟨a, a', ?_, fun z => ?_⟩
  · have := hker (a * a' - 1) (by rw [map_sub, map_mul, ha, ha', mul_inv_cancel₀ ht, map_one, sub_self])
    linear_combination this
  · rw [← hS, hSt, mul_smul, hmem, hTs, ha]
    simp only [Pi.smul_apply, smul_eq_mul]

end GlobalTheory.SplitLatMatch

namespace GlobalTheory.SplitLatMatch

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem lat_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e + cA D e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e + cA D e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  intro D V P e hP M hMs hf hb hK
  have he : IsSplitIdem D e := hP.1
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨a, a', ha, hA⟩ := half V e he M hMs hf hb hK
  have hsum : cA D e + cA D (cA D e) = e + cA D e := by rw [cA_cA, add_comm]
  obtain ⟨b, b', hb', hB⟩ := half V (cA D e) he' M hMs (by rw [hsum]; exact hf) (by rw [hsum]; exact hb)
    (by rw [hsum]; exact hK)
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hqq : finPart D (cA D e) * finPart D (cA D e) = finPart D (cA D e) := by rw [← map_mul, he'.1]
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hqO : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hqq
  have hfe : finPart D (e + cA D e) = finPart D e + finPart D (cA D e) := map_add _ _ _
  rw [hfe] at hf
  rw [hfe]
  refine ⟨finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e))),
    isUnit_iff_exists_inv.2 ⟨finPart D e * a' + finPart D (cA D e) * b' + (1 - (finPart D e + finPart D (cA D e))),
      by linear_combination (a * a' - a - a' + 1) * hpp + (b * b' - b - b' + 1) * hqq +
        (a * b' + b * a' - a - a' - b - b' + 2) * hpq + ha + hb'⟩, fun z => ⟨fun hz => ⟨hf z hz, ?_⟩, fun ⟨hz, hc⟩ => ?_⟩⟩
  · have h1 := (hA z).1 (hMs _ hpO z hz)
    have h2 := (hB z).1 (hMs _ hqO z hz)
    have h3 := hf z hz
    have e1 : (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z =
        (finPart D e * a) • z + (finPart D (cA D e) * b) • z + (z - (finPart D e + finPart D (cA D e)) • z) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, h3, sub_self, add_zero]
    exact add_mem h1 h2
  · have e2 : ∀ (p c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), p * (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) = p * c →
        p • ((finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z) = (p * c) • z := by
      intro p c h
      rw [smul_smul, h]
    have h1 : finPart D e • z ∈ M := (hA z).2 (by
      rw [← e2 (finPart D e) a (by linear_combination (a - 1) * hpp + (b - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ hc)
    have h2 : finPart D (cA D e) • z ∈ M := (hB z).2 (by
      rw [← e2 (finPart D (cA D e)) b (by linear_combination (b - 1) * hqq + (a - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hqO _ hc)
    rw [← hz, add_smul]
    exact add_mem h1 h2

end GlobalTheory.SplitLatMatch
