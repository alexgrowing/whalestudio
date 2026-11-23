import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
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

noncomputable section

namespace GlobalTheory.IdemSumVac

variable {D : D7}

theorem symplOH_eq_zero_of_hO {S T : HSp D} {u u' : WO S T} (h : hO S T u u' = 0) : symplOH S T u u' = 0 := by
  rw [symplOH, symplO, h, mul_zero, map_zero, mul_zero]

theorem heisO_sum_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (f : WO S T → ℂ)
    (hf : IsLatVac (heisO ψ S T) Λ f) (hΛ : ∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ)
    {ι : Type} (p : ι → AE D) (s : Finset ι) (hs : ∀ i ∈ s, IsSplitIdem D (p i))
    (hc : ∀ i ∈ s, ∀ j ∈ s, p i * cA D (p j) = 0) (x : WO S T) (hx : x ∈ Λ) :
    heisO ψ S T ((∑ i ∈ s, p i) • x) f = f := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, zero_smul]; exact GlobalTheory.LatVac.heisO_zero ψ f
  | insert a s ha ih =>
    have hsa := hs a (Finset.mem_insert_self _ _)
    have ih' := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
    have hmem : p a • x ∈ Λ := hΛ _ (GlobalTheory.SplitHomLattice.idem_int hsa) x hx
    have hhalf : IsHalf (p a) (p a • x) := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hsa.1]
    have h1 : heisO ψ S T (p a • x) f = f := hf.2 (p a) hsa _ hmem hhalf
    have hz : hO S T (p a • x) ((∑ i ∈ s, p i) • x) = 0 := by
      rw [GlobalTheory.LatVacSign.hO_smul_smul, map_sum, Finset.mul_sum,
        Finset.sum_eq_zero (fun j hj => hc a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)),
        zero_mul]
    have key := GlobalTheory.LatVac.heisO_heisO ψ (p a • x) ((∑ i ∈ s, p i) • x) f
    rw [ih', h1, symplOH_eq_zero_of_hO hz, ψ.map_zero_eq_one, one_smul, ← add_smul] at key
    rw [Finset.sum_insert ha]
    exact key.symm

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨he1, he2, v, ε, hpl, he3⟩ := he
  exact ⟨by rw [← RingHom.map_mul, he1], by rw [GlobalTheory.LatVac.cA_cA, mul_comm, he2], v, ε, hpl,
    by rw [GlobalTheory.LatVac.cA_cA, add_comm, he3]⟩

theorem heisO_idemSum_fix : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T))
    (f : WO S T → ℂ), IsLatVac (heisO ψ S T) Λ f → (∀ w : AE D, finPart D w ∈ intAE D → ∀ u ∈ Λ, w • u ∈ Λ) →
    ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ x ∈ Λ,
      heisO ψ S T (e • x) f = f ∧ heisO ψ S T (cA D e • x) f = f := by
  intro D ψ S T Λ f hf hΛ e SS he x hx
  obtain ⟨⟨es, hes, rfl⟩, hce⟩ := he
  have h1 : ∀ i ∈ SS, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hcross : ∀ i ∈ SS, ∀ j ∈ SS, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es SS h1 hce
  refine ⟨heisO_sum_smul ψ S T Λ f hf hΛ es SS (fun i hi => (hes i hi).1) hcross x hx, ?_⟩
  rw [map_sum]
  refine heisO_sum_smul ψ S T Λ f hf hΛ (fun i => cA D (es i)) SS (fun i hi => isSplitIdem_cA (hes i hi).1)
    (fun i hi j hj => ?_) x hx
  rw [← RingHom.map_mul, hcross i hi j hj, map_zero]

end GlobalTheory.IdemSumVac
