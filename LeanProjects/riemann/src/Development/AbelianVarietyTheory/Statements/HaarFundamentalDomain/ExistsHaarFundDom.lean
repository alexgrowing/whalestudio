import Mathlib
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.KernelSt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCtxBase
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsWeakOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HypModel

theorem exists_haar_fundDom (D : D7) (V : HSp D) :
    ∃ (ν : Measure (GA D V)) (𝓖 : Set (GA D V)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓖 ν := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  obtain ⟨𝓖, h⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V Measure.haar inferInstance
  exact ⟨Measure.haar, 𝓖, inferInstance, h⟩

theorem hypotheses (D : D7) (p q : ℕ) : ∃ (S T : HSp D) (C : Ctx S T), T.rank = p + q ∧ C.X.p0 = p ∧
    4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank ∧ T.rank ≤ S.rank ∧
    (∃ μ 𝓕, IsCovolOne (ratL T S) μ 𝓕) ∧
    (∃ (Lv : SW.Level C.X) (M : ℕ) (B : C.Bas) (f' : WO S T → ℂ), IdemTwo Lv.w ∧ 0 < M ∧
      (M : 𝓞 D.host.E) ∈ Lv.𝔪 ∧ C.IsB B ∧ C.IsBase Lv B f') ∧
    C.IsFam (fun _ : Fin 1 => 1) ∧
    (∃ (ν : Measure (GA D S)) (𝓖 : Set (GA D S)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ S) 𝓖 ν) ∧
    (∃ ν : Measure (GA D T), ν.IsHaarMeasure) ∧
    (p + q = 0 → ∃ om, IsWeak C.ψ S T om) := by
  obtain ⟨S, T, C, h1, h2, h3, -, -, Lv, B, f, hw, hB, hf⟩ :=
    GlobalTheory.Ker.Inhab.exists_ctx_base D (2 * (Module.finrank ℚ D.host.E * (p + q)) + 2 + (p + q)) p q
  have hr : T.rank = p + q := by rw [← C.hr, h2, h3]
  obtain ⟨ν, 𝓖, hν, -⟩ := exists_haar_fundDom D T
  refine ⟨S, T, C, hr, h2, by rw [h1, hr]; omega, by rw [h1, hr]; omega,
    (GlobalTheory.Ker.ScalarProduct.ip_basic D S T C).1,
    ⟨Lv, Ideal.absNorm Lv.𝔪, B, f, hw, ?_, Ideal.absNorm_mem _, hB, hf⟩,
    (GlobalTheory.Ker.Base.level_base_fam D S T C).2.2, exists_haar_fundDom D S, ⟨ν, hν⟩,
    fun h0 => ⟨1, isWeak_one_of_rank_zero D _ S T (hr.trans h0)⟩⟩
  exact Nat.pos_of_ne_zero fun h => Lv.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem base_mem_lats {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) : C.X.Λ ∈ Lv.lats :=
  ⟨GlobalTheory.SW.Lev.selfD_of_sympl C.sympl, 1, GlobalTheory.SW.Lev.cop_one,
    fun v hv => by rwa [one_smul], fun v hv => by rwa [one_smul]⟩

end GlobalTheory.Ker.HypModel
