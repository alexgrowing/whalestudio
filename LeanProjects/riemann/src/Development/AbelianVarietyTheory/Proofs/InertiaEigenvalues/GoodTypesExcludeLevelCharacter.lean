import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLaws
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqAct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExistStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteSpaceFormsFunctionalPrincipalTypeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorConvMirabolicAvgEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentMulMirabolicDetAverageEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndepStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetAverageEqHarishChandraRestrictiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterLabelRootOfHarishChandraConstituentStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.GoodTypeNoChi

open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

theorem p_comp : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ {G : Type} [Group G] [Fintype G] (eG : G ≃* Formalism.L2.DIV.G0 L.Pg L.r) (c c' : G → ℂ) (F : GA D V → ℂ),
    HasType V β (flag1L L) F →
      gaL V β L eG c (gaL V β L eG c' F) = gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F := by
  intro D V β L hL G _ _ eG c c' F hF
  have hm : ∀ y z : G, actL V β L (eG y) (actL V β L (eG z) F) = actL V β L (eG (y * z)) F := fun y z => by
    rw [map_mul]
    exact Formalism.IndefR.Eqv.Act.levelGroupAction_mul_of_lifts hL (eG y) (eG z) hF
  have lhs : gaL V β L eG c (gaL V β L eG c' F) =
      ∑ y : G, ∑ z : G, (c y * c' z) • actL V β L (eG (y * z)) F := by
    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [mul_comm]
  have rhs : gaL V β L eG (fun x => ∑ y, c y * c' (y⁻¹ * x)) F =
      ∑ y : G, ∑ x : G, (c y * c' (y⁻¹ * x)) • actL V β L (eG x) F := by
    simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  rw [lhs, rhs]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun z => by simp

theorem p_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 →
    ∀ (i : Fin D.R.m) (t : T), LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h i t
  obtain ⟨c, hc⟩ := h.βV i
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T R.toLevCh A.μ0 h t i).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem isClass_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem charLab_inv {g : ℕ} [Fact g.Prime] {L : LabelDatum g} {θ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g}
    (h : GlobalTheory.GLp.IsCharLab L θ c) : GlobalTheory.GLp.IsCharLab L θ⁻¹ c⁻¹ := by
  obtain ⟨hc, hv⟩ := h
  refine ⟨inv_ne_zero hc, fun u hu => ?_⟩
  have e1 : ((θ⁻¹ u : ℂˣ) : ℂ) = ((θ u : ℂˣ) : ℂ)⁻¹ := by simp
  have hx : algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective]
  have e2 : L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c⁻¹) = (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))⁻¹ := by
    rw [map_inv₀]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  rw [e1, hv u hu, e2]

theorem seriesKillsAvg : SeriesKillsAvg := by
  intro g _ L r f θ c hc hf hf' a b ha
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := by
    cases r with
    | zero => exact absurd (_root_.funext fun i : Fin 0 => Fin.elim0 i) ha
    | succ n => exact ⟨n, rfl⟩
  obtain ⟨hfin, -⟩ := irr_finite_and_finsum_zOf_eq_one (Gn g (n + 1))
  rw [eSerC_eq_sum L (n + 1) hfin f, Finset.sum_mul]
  refine Finset.sum_eq_zero fun ψ hψ => ?_
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hψ
  obtain ⟨hirr, hlab⟩ := hψ
  apply GlobalTheory.T.centralIdempotent_mul_mirabolicDetAverage_eq_zero g (n + 1) ψ hirr θ a b
  rw [GlobalTheory.T.trace_mirabolicDetCharacterAverage_vector_indep g n ψ (isClass_irr hirr) θ a ha b]
  have hinv := charLab_inv hc
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).1]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det g n ψ hirr θ).1 (right_ne_zero_of_mul hne)
    exact hf' ((GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).1 hip)
  · simp only [if_true]
    rw [(GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction g n ψ θ).2]
    by_contra hne
    obtain ⟨σ, hσ, hip⟩ := (GlobalTheory.T.exists_irr_harishChandraInduction_thetaInv_det g n ψ hirr θ).2 (right_ne_zero_of_mul hne)
    exact hf' ((GlobalTheory.T.detCharacterLabel_root_of_harishChandraConstituent g L n ψ f hirr hlab σ hσ θ⁻¹ c⁻¹ hinv).2 hip)

theorem goodNoChi : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodNoChi R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t
  have hc : GlobalTheory.Hk3.Core R F := hG.core
  have hl : R.toLevCh.Is A.μ0 := hc.lev
  have hL : LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := p_lifts D G Pl0 T A Ks R hl i t
  intro y hy PP a ha b ε hε l
  have hT : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (fun h => l (R.extV i t y h)) :=
    GlobalTheory.T.definiteSpace_forms_functional_principalType D G Pl0 T A Ks R F hc i t y l
  have hy' := hy l
  have e1 := p_comp _ _ _ hL R.eG (mirC R i PP a b ε) (RealDat.eC (A := A) (sg0 D A)) _ hT
  have e0 := congrArg (gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (mirC R i PP a b ε)) hy'
  have h0 : (fun x => ∑ y, mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x)) = fun _ => 0 :=
    funext (GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero seriesKillsAvg D G Pl0 T A Ks R F hG i PP a ha b ε hε)
  have e2 := congrArg (fun c => gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG c (fun h => l (R.extV i t y h))) h0
  have e3 : gaL (Vc D i) (R.βV i) (R.datVt i t) R.eG (fun _ : G => (0 : ℂ)) (fun h => l (R.extV i t y h)) = 0 := by
    simp only [gaL, zero_smul, Finset.sum_const_zero, LinearMap.zero_apply]
  exact e0.symm.trans (e1.trans (e2.trans e3))

end GlobalTheory.GoodTypeNoChi

end
