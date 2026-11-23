import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjMemStandardLeviOfReducibleCharpolyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestDataTraceIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEqZeroOfCommuteSepAlg
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitTorusZero

open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

variable {D : D7} {V : HSp D}

theorem exists_minLevi (Φ : WittFrame V) (γ : GF V) :
    ∃ (g : GF V) (P : Finset (SV (wittIndex V))), IsMinLevi Φ (g * γ * g⁻¹) P := by
  classical
  let A : Finset (Finset (SV (wittIndex V))) := Finset.univ.filter fun P =>
    IsPar P ∧ ∃ g : GF V, rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P
  have hA : (∅ : Finset (SV (wittIndex V))) ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨by simp, by simp⟩, 1, ?_⟩
    simp [WittFrame.levi]
  obtain ⟨P, hPA, hmax⟩ := A.exists_max_image Finset.card ⟨_, hA⟩
  obtain ⟨hP, g, hg⟩ := (Finset.mem_filter.1 hPA).2
  refine ⟨g, P, hP, hg, fun g' P' hP' h' => hmax P' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP', g' * g, ?_⟩)⟩
  have e : g' * g * γ * (g' * g)⁻¹ = g' * (g * γ * g⁻¹) * g'⁻¹ := by group
  rw [e]; exact h'

theorem rat_mem_GQ (g : GF V) : rat V g ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨g, rfl⟩

theorem zeroClause_of_conj (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ g : GF V)
    (h : ZeroClause μ f (rat V (g * γ * g⁻¹))) : ZeroClause μ f (rat V γ) := by
  have hg := rat_mem_GQ g
  have e : ratClass (GQ V) (rat V (g * γ * g⁻¹)) = ratClass (GQ V) (rat V γ) := by
    ext δ
    simp only [ratClass, Set.mem_ofPred_eq, map_mul, map_inv]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(rat V g)⁻¹ * k, mul_mem (inv_mem hg) hk, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨rat V g * k, mul_mem hg hk, by group⟩
  intro 𝓕 h𝓕
  have := h 𝓕 h𝓕
  unfold HasClassInt classKernel at *
  rw [e] at this
  exact this

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_of_quot {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) (hi : Integrable (descend (GQ V) φ) (autMeasure V μ)) :
    IntegrableOn φ 𝓕 μ ∧ ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (p := 1)).1 (memLp_one_iff_integrable.2 hi)
    rw [hφ.lift_descend] at this
    exact memLp_one_iff_integrable.1 this
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

theorem exists_regular {k : ℕ} (c c' : ℝ) : ∃ T : A0 k, Regular c T ∧ Regular c' T := by
  set C := max (max c c') 1
  have h1 : c ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : c' ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : 1 ≤ C := le_max_right _ _
  have key : ∀ b, b ≤ C → Regular b (WithLp.toLp 2 fun i : Fin k => C * ((k : ℝ) - i) : A0 k) := fun b hb => by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      nlinarith
    · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast i.2
      nlinarith
  exact ⟨_, key c h1, key c' h2⟩

theorem exists_haar_cent (γ : GA D V) : ∃ dt : Measure (cent γ), dt.IsHaarMeasure := by
  have : LocallyCompactSpace (cent γ) := (GlobalTheory.Orb.isClosed_cent γ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

theorem hyperZero : GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm →
    GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → HyperZero := by
  intro hLW hPC hTV hRS D V lam S M T U μa μf μ _ _ fa ff hTD γ hreg hirr hna
  obtain ⟨Φ, L, a, hgood⟩ := exists_isGood V
  obtain ⟨g, P, hP⟩ := exists_minLevi Φ γ
  refine zeroClause_of_conj μ _ γ g ?_
  set γ0 := g * γ * g⁻¹ with hγ0
  have hreg0 : IsRegSS γ0.1.1 := by
    show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)
    unfold IsRegSS
    rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact hreg
  have hPne : P ≠ ∅ := by
    obtain ⟨g', P', hpar', hne', hmem'⟩ := GlobalTheory.T.exists_conj_mem_standardLevi_of_reducible_charpoly hTD.1.pos hRS Φ γ hreg hirr hna
    have e : g' * g⁻¹ * γ0 * (g' * g⁻¹)⁻¹ = g' * γ * g'⁻¹ := by rw [hγ0]; group
    have hle := hP.2.2 (g' * g⁻¹) P' hpar' (e ▸ hmem')
    rintro rfl
    have := Finset.card_pos.2 hne'
    rw [Finset.card_empty] at hle
    omega
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V :=
    (IsTestFnG.isPureTensor ⟨fa, ff, hTD.2.2.2.2.2.1, hTD.2.2.2.2.2.2, rfl⟩).2
  obtain ⟨c1, hc1⟩ := ((hLW.2 D V Φ L a hgood).2 μ).1 _ hf
  obtain ⟨dt, hdt⟩ := exists_haar_cent (rat V γ0)
  obtain ⟨c2, hc2⟩ := ((hLW.2 D V Φ L a hgood).2 μ).2 _ hf γ0 hreg0 P hP dt
  obtain ⟨Tr, h1, h2⟩ := exists_regular (k := wittIndex V) c1 c2
  have hint := (hc1 Tr h1).1 _ (GlobalTheory.regSS_conjClass_isSSClass γ0 hreg0)
  have heq := (hc2 Tr h2).2
  have hz := GlobalTheory.T.elliptic_trace_from_model hLW hPC hTV hRS D V lam S M T U μa μf μ fa ff hTD Φ L a hgood γ0 hreg0 P hP hPne dt Tr
  have hk : kT Φ (levelAll D.sp.cm.sig V.gram L a) {δ | IsConj γ0 δ} (tensor D.sp.cm.sig V.gram fa ff) Tr =
      classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff) :=
    funext (GlobalTheory.T.test_data_trace_identity hPC hTD Φ _ γ0 Tr)
  rw [hk] at hint heq
  intro 𝓕 h𝓕
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (classKernel (GQ V) (rat V γ0) (tensor D.sp.cm.sig V.gram fa ff)) :=
    fun δ hδ x => classKernel_mul _ _ hδ x
  obtain ⟨hi, hv⟩ := fd_of_quot h𝓕 hinv hint
  refine ⟨summable_class (GlobalTheory.Orb.continuous_of_mem_ccAd hf).2 (rat_mem_GQ γ0), hi, ?_⟩
  rw [hv, heq, hz, mul_zero]

end GlobalTheory.SplitTorusZero
