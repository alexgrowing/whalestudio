import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupportStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open GlobalTheory.Member

namespace GlobalTheory.UnRep.Space

theorem finrank_two (D : D7) : Module.finrank D.host.F D.host.E = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield D.host.E) D.host.E

theorem isUnA_finHom {D : D7} (V : HSp D) (g : GA D V) : GlobalTheory.UnRep.IsUnA (cF D) V.gramᵀ (finHom V g).1 := by
  intro x y
  rw [GlobalTheory.UnitarySplit.hermA_eq, GlobalTheory.UnitarySplit.hermA_eq]
  exact (GlobalTheory.Member.RatElt.mem_UJ_iff _ _ _).1 (GlobalTheory.UnitarySplit.finHom_mem V g) y x

theorem herm_neg_eq {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) u v = -GlobalTheory.UnRep.hermE (cF D) V.gramᵀ u v := by
  unfold herm GlobalTheory.UnRep.hermE
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change u a * (-V.gram b a) * cc (v b) = -(u a * V.gram b a * cc (v b))
  ring

set_option maxHeartbeats 1000000 in

theorem exists_rep_suppSplit : ∀ (D : D7) (V : HSp D) (N : ℕ), 0 < N → ∀ g : GA D V, ∃ γ ∈ GQ V, ∃ a ∈ GinfC V, ∃ h ∈ GfC V, ∃ k ∈ GfC V, g = γ * a * h * k ∧ FinCong V N k ∧ GlobalTheory.UnRep.SuppSplit (cF D) N (finHom V h).1 := by
  intro D V N hN g
  obtain ⟨e1, -, hfg, hsp, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, -⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (finrank_two D) (latC V) hfg hsp (finHom V g) N (isUnA_finHom V g) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [herm_neg_eq, herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, γ⁻¹ * g * k⁻¹ * h⁻¹, ?_, h, hh, k, hk', by group, ?_, ?_⟩
  · change finHom V _ = 1
    simp only [map_mul, map_inv, e]
    group
  · unfold FinCong
    rw [e1, ek]
    exact hk
  · rw [eh]
    exact hs

end GlobalTheory.UnRep.Space
