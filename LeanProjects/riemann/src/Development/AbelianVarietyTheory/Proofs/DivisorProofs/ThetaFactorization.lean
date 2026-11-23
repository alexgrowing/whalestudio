import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleAdaptedRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleAdaptedIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleAdaptedConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleAdaptedEigenStatement

noncomputable section

namespace GlobalTheory.ThetaFacMain

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem mem_polData_left {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hf, -, rfl, -, -⟩ := h
  refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hf i).1, φ i, (hf i).2.1, ?_, rfl⟩
  exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun h => hv ((hf i).2.2 v h))

theorem mem_polData_right {Φ Φ'} (h : PolMatch B G X R Rf Φ Φ') : Φ' ∈ PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', -, hf', -, rfl, -⟩ := h
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hf' j).1, φ' j, (hf' j).2.1, ?_, rfl⟩
  exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun h => hv ((hf' j).2.2 v h))

end GlobalTheory.ThetaFacMain

theorem GlobalTheory.ThetaFacMain.factor : GlobalTheory.ThK.KP → GlobalTheory.ThK.Factor := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  refine ⟨fun Φ hΦ => ?_, fun Φ' hSo hΦ' => ?_⟩
  · by_contra hne
    obtain ⟨N, hN, hker, hnot⟩ := GlobalTheory.T.matched_triple_adapted_restriction hK F E σ B a a' G X om om' R Rf hM Φ (GlobalTheory.ThetaFacMain.mem_polData_left hΦ) hne
    exact hnot (GlobalTheory.T.matched_triple_adapted_integral hK F E σ B a a' G X om om' R Rf hM N hN hker Φ hΦ)
  · by_contra hne
    obtain ⟨N, hN, hker, hnot⟩ :=
      GlobalTheory.T.matched_triple_adapted_constant hK F E σ B a a' G X om om' R Rf hM Φ' ⟨GlobalTheory.ThetaFacMain.mem_polData_right hΦ', hSo⟩ hne
    exact hnot (GlobalTheory.T.matched_triple_adapted_eigen hK F E σ B a a' G X om om' R Rf hM N hN hker Φ' hSo hΦ')

end
