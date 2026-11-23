import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.CyclicRecursionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuCoeffZeroNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepBasisCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfIntertwined
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRepReductionStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanTopOfResidueSpanTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueFieldTiltStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

namespace GlobalTheory.DetInv

theorem exists_span_top_of_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ], ∀ (h : ℕ) (D : Datum ε h Λ), ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ), ∃ (N : ℕ) (x : Fin N → Fin h → Ainf p O) (y : Fin N → Fin h → ℤ_[p]), h = N * d ∧ Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => D.ρM (b ij.2) *ᵥ x ij.1) = ⊤ ∧ Submodule.span ℤ_[p] (Set.range fun ij : Fin N × Fin d => D.ρT (b ij.2) *ᵥ y ij.1) = ⊤ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ h D d b
  obtain ⟨hdom, hloc, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  haveI := hdom
  haveI := hloc
  obtain ⟨-, hmu, -⟩ := GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε hε
  obtain ⟨N, y, hN, hy, hcp⟩ := GlobalTheory.T.exists_rep_basis_charpoly p Λ h d b D.ρT
  obtain ⟨k, _, _, _, r, hr⟩ := GlobalTheory.T.exists_residue_field_tilt p C v O hv
  obtain ⟨hscal, -⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  let j : Ainf p O →+* WittVector p k := WittVector.map r
  let s : ℤ_[p] →+* WittVector p k := j.comp (ofPadic p O)
  let ρ : Λ →+* Matrix (Fin h) (Fin h) (WittVector p k) := (RingHom.mapMatrix j).comp D.ρM
  have hρscal : ∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = s c • (1 : Matrix (Fin h) (Fin h) (WittVector p k)) := by
    intro c
    simp only [ρ, s, RingHom.comp_apply, hscal c, RingHom.mapMatrix_apply]
    ext i l
    by_cases hil : i = l <;> simp [hil]
  have hcpM : ∀ a : Λ, (D.ρM a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map (ofPadic p O) := by
    intro a
    rw [GlobalTheory.DetInv.charpoly_eq_of_intertwined (Ainf p O) h (mu ε) D.F D.G ((D.ρT a).map (ofPadic p O)) (D.ρM a) hmu D.G_mul_F (D.F_act a), Matrix.charpoly_map, hcp a]
  have hcpρ : ∀ a, (ρ a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map s := by
    intro a
    show ((D.ρM a).map j).charpoly = _
    rw [Matrix.charpoly_map, hcpM a, Polynomial.map_map]
  obtain ⟨xb, hxb⟩ := GlobalTheory.T.witt_rep_reduction_structure p Λ k h d N b s ρ hρscal hcpρ
  let c : Ainf p O →+* k := WittVector.constantCoeff.comp j
  have hc : Function.Surjective c := by
    intro z
    obtain ⟨w, rfl⟩ := hr z
    refine ⟨WittVector.teichmuller p w, ?_⟩
    simp [c, j, WittVector.map_teichmuller, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  choose lift hlift using hc
  refine ⟨N, fun i l => lift (xb i l), y, hN, ?_, hy⟩
  apply GlobalTheory.DetInv.span_top_of_residue_span_top (Ainf p O) k (Fin N × Fin d) h c _ (fun z => ⟨lift z, hlift z⟩)
  convert hxb using 3
  funext ij l
  rw [RingHom.map_mulVec]
  congr 1
  funext m
  exact hlift _

end GlobalTheory.DetInv
