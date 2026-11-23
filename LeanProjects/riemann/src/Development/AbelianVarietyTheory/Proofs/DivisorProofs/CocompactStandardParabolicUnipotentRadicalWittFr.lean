import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.CuspCocpt
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem cocompact_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X S) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S
  by_cases hS0 : S = ∅
  · subst hS0
    rw [unip_empty]
    refine ⟨Set.univ, ?_, fun u => ⟨1, Subgroup.one_mem _, Set.mem_univ _⟩⟩
    exact Set.Subsingleton.isCompact fun a _ b _ => Subsingleton.elim a b
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hσ := sigma_sigma h
  have hs : m.val + 1 ≤ r := m.2
  have hS : ∀ i : Fin r, i.val < m.val + 1 ↔ ∃ k ∈ S, i ≤ k := fun i =>
    ⟨fun hi => ⟨m, hm, Fin.le_def.2 (Nat.lt_succ_iff.1 hi)⟩,
      fun ⟨k, hk, hik⟩ => Nat.lt_succ_iff.2 (le_trans (Fin.le_def.1 hik) (Fin.le_def.1 (hm' k hk)))⟩
  have e := (GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (m.val + 1) hs hS
    (fun i => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl).1
  have hC : IsIsoCols σ J (X.submatrix id (Fin.castLE hs)) := isIsoCols_of_isWittFrame hW hσ hJ hs
  exact e ▸ cocompact_unipFlag hJ hσ hC _

end GlobalTheory.CuspCocpt
