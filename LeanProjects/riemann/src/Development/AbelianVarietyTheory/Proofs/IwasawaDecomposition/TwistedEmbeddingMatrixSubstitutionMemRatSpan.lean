import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.RatStab

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

theorem twSub_eq_subP (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    twSub (embT D) M s P = C (∏ τ, (embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (s τ)) *
      Formalism.L2.Forms.subP (fun τ => (M : Matrix (Fin n) (Fin n) D.host.E).map (embT D τ)) P := by
  rfl

theorem twSub_mem_ratSpan : ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ),
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → twSub (embT D) M s P0 ∈ Formalism.L2.Forms.RatSpan D lam := by
  classical
  intro D n lam M s P0 hP
  let A : Matrix (Fin n) (Fin n) D.host.E := (M : Matrix (Fin n) (Fin n) D.host.E)
  let ML : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL := fun τ => A.map (Formalism.L2.G.Cmp.tEL D τ)
  have hoM : ∀ τ, A.map (embT D τ) = (ML τ).map D.what₂.embLL := fun τ => by
    ext a b
    exact (Formalism.L2.G.Cmp.tEL_emb D τ _).symm
  have hdetA : A.det ≠ 0 := (Matrix.isUnits_det_units M).ne_zero
  have hMdet : ∀ τ, (ML τ).det ≠ 0 := by
    intro τ h
    apply hdetA
    have : Formalism.L2.G.Cmp.tEL D τ A.det = 0 := by
      rw [RingHom.map_det]; exact h
    exact (map_eq_zero _).1 this
  have hc : (∏ τ, (embT D τ A.det) ^ (s τ)) =
      D.what₂.embLL (∏ τ, (ML τ).det ^ s τ) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, hoM τ, RingHom.map_det D.what₂.embLL, RingHom.mapMatrix_apply]
  rw [twSub_eq_subP]
  show C (∏ τ, (embT D τ A.det) ^ (s τ)) * Formalism.L2.Forms.subP (fun τ => A.map (embT D τ)) P0 ∈ _
  rw [hc, MvPolynomial.C_mul']
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    rw [map_smul, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.substitution_tensor, smul_smul, ← map_mul]
    apply Formalism.L2.GlobalTheoryTheory.LemB.rat_ten D _ Finset.univ
    · intro τ _
      rw [hoM τ]
      exact Formalism.L2.GlobalTheoryTheory.LemB.rat_rowAct_mem D _ (Formalism.L2.DIV.natW_antitone _) (ML τ) (hMdet τ) _
        (Submodule.subset_span ⟨f τ, hf τ, rfl⟩)
    · intro τ hτ
      exact absurd (Finset.mem_univ τ) hτ
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.IntegralityCompare

end
