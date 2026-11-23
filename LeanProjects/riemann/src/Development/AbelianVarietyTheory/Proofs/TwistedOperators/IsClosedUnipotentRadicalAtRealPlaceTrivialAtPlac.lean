import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCompactKinfAndConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem isClosed_cmp_eq_one {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau) :
    IsClosed {p : NI V C | cmp θ τ (p : GA D V) = 1} :=
  isClosed_eq ((GlobalTheory.Cusp.KinfCompact.continuous_realMat hθ V τ).comp continuous_subtype_val)
    continuous_const

theorem isClosed_atP_and_isClosed_offP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau), IsClosed (GlobalTheory.FibreAtTau.atP θ V C τ : Set (NI V C)) ∧ IsClosed (GlobalTheory.FibreAtTau.offP θ V C τ : Set (NI V C)) := by
  intro D θ hθ V r C τ
  constructor
  · have e : (atP θ V C τ : Set (NI V C)) = (Subtype.val ⁻¹' (GinfC V : Set (GA D V))) ∩
        ⋂ (τ' : D.what₂.Tau) (_ : τ' ≠ τ), {p : NI V C | cmp θ τ' (p : GA D V) = 1} := by
      ext p
      simp only [SetLike.mem_coe, mem_atP, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [e]
    exact ((GlobalTheory.Cusp.KinfCompact.isClosed_realPts V).preimage continuous_subtype_val).inter
      (isClosed_iInter fun τ' => isClosed_iInter fun _ => isClosed_cmp_eq_one hθ V C τ')
  · have e : (offP θ V C τ : Set (NI V C)) = {p : NI V C | cmp θ τ (p : GA D V) = 1} := by
      ext p
      simp only [SetLike.mem_coe, mem_offP, Set.mem_ofPred_eq]
    rw [e]
    exact isClosed_cmp_eq_one hθ V C τ

end GlobalTheory.FibreAtTau
