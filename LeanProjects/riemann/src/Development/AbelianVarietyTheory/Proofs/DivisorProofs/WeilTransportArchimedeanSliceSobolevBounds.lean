import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimFinitePartsWeilOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchDerivativeKeepsSumsFixedFinitePartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepDerivativeLawOfL2IsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicDualBasisIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzL2WordBoundExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteL2ABoundWordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ATransportGramTransposeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedArchHeisenbergDirectionsContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardArchimedeanAddCharOfStandardCharStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

open MeasureTheory

namespace GlobalTheory.WeilL2Words

section Core

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_decomp {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

theorem list_sum_ne_top {l : List ENNReal} (h : ∀ a ∈ l, a ≠ ⊤) : l.sum ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons]
    exact ENNReal.add_ne_top.2 ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

variable [Invertible (2 : AdeleRing (𝓞 F) F)] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

theorem dS_mem (hψ : IsStdInf F ψ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_decomp hΦ
  obtain ⟨f', hf'⟩ := GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

theorem word_mem (hψ : IsStdInf F ψ) : ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ},
    Φ ∈ GlobalTheory.WeilM.schA F κ → word F ψ w Φ ∈ GlobalTheory.WeilM.schA F κ
  | [], _, hΦ => hΦ
  | h :: w, _, hΦ => by
    rw [word_cons]
    exact dS_mem hψ h (word_mem hψ w hΦ)

theorem word_sum (hψ : IsStdInf F ψ) {m : ℕ} (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      word F ψ w (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i)
  | [], f => ⟨f, rfl⟩
  | h :: w, f => by
    obtain ⟨f1, e1⟩ := word_sum hψ g w f
    obtain ⟨f2, e2⟩ := GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts F κ ψ hψ m g f1 h
    exact ⟨f2, by rw [word_cons, e1, e2]⟩

theorem word_law (hψ : IsStdInf F ψ) {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ) (p : G) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ}, φ ∈ GlobalTheory.WeilM.schA F κ →
      word F ψ w (om p φ) = om p (word F ψ (w.map (M p)) φ)
  | [], _, _ => rfl
  | h :: w, φ, hφ => by
    rw [List.map_cons, word_cons, word_cons, word_law hψ om pres M himpl μ hμ hiso p w hφ]
    exact GlobalTheory.T.weilRep_derivative_law_of_L2Isometric F κ ψ hψ om pres M himpl μ hμ hiso p h _ (word_mem hψ _ hφ)

theorem slice_l2_of (hψ : IsStdInf F ψ) {G : Type} [Group G] [TopologicalSpace G]
    (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (hM : ∀ h, Continuous fun p => M p h)
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (p0 : G)
    (hfin : ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (yy j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (y : (κ → FiniteAdeleRing (𝓞 F) F)) (i j : ℕ) :
    ∃ B : ℝ, ∀ᶠ p in nhds p0,
      ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2 ≤ B := by
  obtain ⟨L, C, hL⟩ := GlobalTheory.T.adelic_schwartz_l2_word_bound_exists F κ ψ hψ i j
  obtain ⟨N, hN, m, g, yy, hg, hdual, hf⟩ := hfin
  obtain ⟨CG, hCG, hG⟩ := GlobalTheory.T.finite_adelic_dual_basis_integral F κ m g yy hg hdual μ hμ y
  set R : ℝ := ∑ h ∈ L.flatten.toFinset, (‖M p0 h‖ + 1) with hR
  have hev : ∀ᶠ p in nhds p0, ∀ h ∈ L.flatten.toFinset, ‖M p h‖ ≤ R := by
    refine (Filter.eventually_all_finset _).2 fun h hh => ?_
    have hc : ContinuousAt (fun p => ‖M p h‖) p0 := ((hM h).norm).continuousAt
    filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one ‖M p0 h‖)] with p hp
    exact hp.le.trans (Finset.single_le_sum (f := fun h => ‖M p0 h‖ + 1) (fun _ _ => by positivity) hh)
  have hB : ∀ w ∈ L, ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ws.length = w.length →
      (∀ h ∈ ws, ‖h‖ ≤ R) → l2A F μ (word F ψ ws Φ) ≤ B :=
    fun w _ => GlobalTheory.T.exists_finite_l2A_bound_words F κ ψ hψ Φ hΦ μ hμ w.length R
  choose! B hBtop hBle using hB
  have htop : ENNReal.ofReal C * (L.map fun w => CG * B w).sum ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (list_sum_ne_top fun a ha => ?_)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    exact ENNReal.mul_ne_top hCG (hBtop w hw)
  refine ⟨(ENNReal.ofReal C * (L.map fun w => CG * B w).sum).toReal, ?_⟩
  filter_upwards [hev, hN] with p hp hpN
  have key := hL (om p Φ) (pres p Φ hΦ) y
  have hsum : (L.map fun w => ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum ≤
      (L.map fun w => CG * B w).sum := by
    refine List.sum_le_sum fun w hw => ?_
    obtain ⟨f, hfp⟩ := hf p hpN
    obtain ⟨f', hf'⟩ := word_sum hψ g w f
    have e1 : word F ψ w (om p Φ) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by rw [hfp, hf']
    calc ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
        ≤ CG * l2A F μ (word F ψ w (om p Φ)) := by rw [e1]; exact hG f'
      _ = CG * l2A F μ (word F ψ (w.map (M p)) Φ) := by
          rw [word_law hψ om pres M himpl μ hμ hiso p w hΦ, hiso p _ (word_mem hψ _ hΦ)]
      _ ≤ CG * B w := by
          gcongr
          refine hBle w hw _ (List.length_map _) fun h hh => ?_
          obtain ⟨h0, h0m, rfl⟩ := List.mem_map.1 hh
          exact hp h0 (List.mem_toFinset.2 (List.mem_flatten.2 ⟨w, hw, h0m⟩))
  exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (key.trans (by gcongr))

end Core

end GlobalTheory.WeilL2Words

theorem GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) p0 (i j : ℕ), ∃ B : ℝ,
      ∀ᶠ p in nhds p0, ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y)) x‖) ^ 2 ≤ B := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ _ co hco ω hω om hom Φ hΦ y p0 i j
  have hI := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  obtain ⟨M, himpl, hM⟩ := GlobalTheory.T.transported_archHeisenbergDirections_continuous D ψ _ _ JA JB ξ κ co om hI.2
  obtain ⟨μ, hμ, hiso⟩ := GlobalTheory.T.l2A_transport_gram_transpose D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  exact GlobalTheory.WeilL2Words.slice_l2_of (GlobalTheory.T.isStandardArchimedeanAddChar_of_standardChar D ψ hψ) om hI.1 M himpl hM μ hμ hiso hΦ p0
    (GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom Φ hΦ p0) y i j
