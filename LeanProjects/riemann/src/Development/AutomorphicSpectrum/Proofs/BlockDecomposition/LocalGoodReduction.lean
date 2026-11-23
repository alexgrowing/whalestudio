import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocGoodProof

section Generic

variable {G G' : Type} [Group G] [Group G']

theorem mem_twCent_prodMap (θ : G →* G) (θ' : G' →* G') (δ g : G × G') :
    g ∈ twCent (θ.prodMap θ') δ ↔ g.1 ∈ twCent θ δ.1 ∧ g.2 ∈ twCent θ' δ.2 := by
  change g * δ = δ * (θ.prodMap θ') g ↔ g.1 * δ.1 = δ.1 * θ g.1 ∧ g.2 * δ.2 = δ.2 * θ' g.2
  exact Prod.ext_iff

theorem mul_norm_comm (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) {δ g : G} (hg : g ∈ twCent θ δ) :
    g * (δ * θ δ) = δ * θ δ * g := by
  have h : g * δ = δ * θ g := hg
  have h' : θ g * θ δ = θ δ * g := by
    have := congrArg θ h
    simpa only [map_mul, hθ] using this
  rw [← mul_assoc, h, mul_assoc, h', mul_assoc]

variable [TopologicalSpace G] [TopologicalSpace G']

theorem isCompact_closure_zpowers_of_map [T2Space G'] (φ : G →* G') (hφ : Continuous φ) (t : G)
    (ht : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (φ t) : Set G')) := by
  have hC := ht.image hφ
  refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem cptPart_le_prod [T2Space G] [T2Space G'] [ContinuousMul G] [ContinuousMul G'] (S : Subgroup (G × G'))
    (T : Subgroup G) (T' : Subgroup G') (hS : ∀ g ∈ S, g.1 ∈ T ∧ g.2 ∈ T') :
    cptPart S ≤ (cptPart T).prod (cptPart T') := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨htS, htc⟩
  exact ⟨Subgroup.subset_closure ⟨(hS t htS).1,
      isCompact_closure_zpowers_of_map (MonoidHom.fst G G') continuous_fst t htc⟩,
    Subgroup.subset_closure ⟨(hS t htS).2,
      isCompact_closure_zpowers_of_map (MonoidHom.snd G G') continuous_snd t htc⟩⟩

theorem good_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G)
    (K' : Subgroup G') (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (ho' : IsOpen (K' : Set G'))
    (hc' : IsCompact (K' : Set G')) (δ : G × G')
    (hcomm : ∀ a b, a ∈ twCent θ δ.1 → b ∈ twCent θ δ.1 → a * b = b * a)
    (hcomm' : ∀ a b, a ∈ twCent θ' δ.2 → b ∈ twCent θ' δ.2 → a * b = b * a)
    (H : Subgroup G) (H' : Subgroup G') (hH : IsCompact (H : Set G)) (hH' : IsCompact (H' : Set G'))
    (hP : cptPart (twCent θ δ.1) ≤ H) (hP' : cptPart (twCent θ' δ.2) ≤ H') :
    PositivityTheory.Rg.BcB.G8.Fin.Good (θ.prodMap θ') (K.prod K') δ := by
  have hmem := fun g => mem_twCent_prodMap θ θ' δ g
  have hKo : IsOpen ((K.prod K' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact ho.prod ho'
  have hKc : IsCompact ((K.prod K' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact hc.prod hc'
  have hHc : IsCompact ((H.prod H' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact hH.prod hH'
  have hle : cptPart (twCent (θ.prodMap θ') δ) ≤ H.prod H' :=
    (cptPart_le_prod _ _ _ fun g hg => (hmem g).1 hg).trans (Subgroup.prod_mono hP hP')
  refine ⟨fun g hg g' hg' => ?_, fun x => ⟨GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj _ hKc x),
    GlobalTheory.LocFin.relIndex_cptPart_ne_zero _ _ _ (GlobalTheory.LocFin.isOpen_map_conj _ hKo x) hHc hle⟩⟩
  obtain ⟨ga, gb⟩ := (hmem g).1 hg
  obtain ⟨ga', gb'⟩ := (hmem g').1 hg'
  exact Prod.ext (hcomm _ _ ga ga') (hcomm' _ _ gb gb')

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_nrmL_comm (hU : Unr E) (n : ℕ) (w : Pl E) {y g : GLw n w} (hg : g ∈ twCent (thL n w) y) :
    g * nrmL n w y = nrmL n w y * g := by
  have hinv := (GlobalTheory.BCT.ThBasic.twist_basic E hU n w).2.1
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    rw [h1] at hg
    have h : g * y = y * g := hg
    simpa only [nrmL, if_pos hs] using h
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    rw [h1] at hg hinv
    simpa only [nrmL, if_neg hs] using mul_norm_comm _ hinv hg

theorem twCent_comm (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (g h : GLw n w) (hg : g ∈ twCent (thL n w) y) (hh : h ∈ twCent (thL n w) y) : g * h = h * g := by
  have key : ∀ {u : GLw n w}, u ∈ twCent (thL n w) y → Commute (nrmL n w y).val u.val := fun {u} hu => by
    have := congrArg Units.val (mul_nrmL_comm hU n w hu)
    rw [Units.val_mul, Units.val_mul] at this
    exact this.symm
  exact Units.ext (GlobalTheory.BCT.CentComm.commute_of_commute_separable hy (key hg) (key hh)).eq

theorem cptPart_le_compact (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hs : (nrmL n w y).val.charpoly.Separable) :
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  set M := nrmL n w y with hM
  set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN
  have hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g := by
    intro g hg
    have := congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq
    simpa [Units.val_mul] using this
  have hadj : ∀ g : GLw n w, Commute g M →
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N} :=
    fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)
  have hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h := by
    intro g h hg hh
    have h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hval g hg
    exact Units.ext (by simpa [Units.val_mul] using h1.eq)
  let S : Set (GLw n w) := {g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}
  let H0 : Subgroup (GLw n w) :=
    { carrier := S
      one_mem' := by
        refine ⟨Commute.one_left M, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
        exact isCompact_singleton
      mul_mem' := by
        intro g h hg hh
        refine ⟨hg.1.mul_left hh.1, ?_⟩
        have hK := hg.2.mul hh.2
        refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
        rintro x ⟨k, rfl⟩
        simp only
        rw [(hcomm g h hg.1 hh.1).mul_zpow]
        exact Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)
      inv_mem' := by
        intro g hg
        refine ⟨hg.1.inv_left, ?_⟩
        show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))
        rw [Subgroup.zpowers_inv]
        exact hg.2 }
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin E w n N hs
  have hB := GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace E w n c
  have hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
    intro g hg
    have hg' : g⁻¹ ∈ H0 := H0.inv_mem hg
    intro i j
    exact ⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j,
      hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩
  refine ⟨H0.topologicalClosure, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe]
    exact hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)
  · refine le_trans ?_ (Subgroup.le_topologicalClosure H0)
    rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, htc⟩
    exact ⟨mul_nrmL_comm hU n w ht, htc⟩

theorem good_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable) :
    PositivityTheory.Rg.BcB.G8.Fin.Good ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) y := by
  obtain ⟨ho₁, hc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨ho₂, hc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  obtain ⟨H₁, hH₁, hP₁⟩ := cptPart_le_compact hU a w y.1 h₁
  obtain ⟨H₂, hH₂, hP₂⟩ := cptPart_le_compact hU b w y.2 h₂
  exact good_prod (G := GLw a w) (G' := GLw b w) (thL a w) (thL b w) (GlobalTheory.LFun.KGL w a) (GlobalTheory.LFun.KGL w b)
    ho₁ hc₁ ho₂ hc₂ y (twCent_comm hU a w y.1 h₁) (twCent_comm hU b w y.2 h₂) H₁ H₂ hH₁ hH₂ hP₁ hP₂

theorem locGood : PositivityTheory.Rg.BcB.G8.Fin.LocGood := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact good_pair hU a b w y h₁ h₂

end GlobalTheory.CompanionTheory.LocGoodProof

end
