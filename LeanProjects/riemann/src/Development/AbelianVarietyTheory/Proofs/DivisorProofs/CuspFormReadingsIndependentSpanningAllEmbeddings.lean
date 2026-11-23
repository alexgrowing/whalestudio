import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsEqModelValuesSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGoodEmbeddingIndependentReadingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelConjugationAntilinearBijectionStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnifAll

theorem span_range_le {F U H : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup H] [Module ℂ H] {σ : F →+* ℂ}
    (j : U →ₛₗ[σ] H) {n : ℕ} (b : Module.Basis (Fin n) F U) :
    Submodule.span ℂ (Set.range j) ≤ Submodule.span ℂ (Set.range fun k => j (b k)) := by
  rw [Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  rw [← b.sum_repr u, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_top {F U H H' : Type} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H'] [Module ℂ H'] {σ σ' : F →+* ℂ} (j : U →ₛₗ[σ] H) (j' : U →ₛₗ[σ'] H') {n : ℕ}
    (b : Module.Basis (Fin n) F U) (c : H ≃ₗ⋆[ℂ] H') (hi : LinearIndependent ℂ fun k => j (b k))
    (hs : Submodule.span ℂ (Set.range j') = ⊤) : Submodule.span ℂ (Set.range j) = ⊤ := by
  have h1 : Submodule.span ℂ (Set.range fun k => j' (b k)) = ⊤ := top_le_iff.1 (hs ▸ span_range_le j' b)
  have h2 : Submodule.span ℂ (Set.range fun k => c.symm (j' (b k))) = ⊤ := by
    have h3 := congrArg (Submodule.map (c.symm : H' →ₗ⋆[ℂ] H)) h1
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3
  haveI : Module.Finite ℂ H := ⟨h2 ▸ Submodule.fg_span (Set.finite_range _)⟩
  have h4 : Module.finrank ℂ H ≤ n := by simpa using finrank_le_of_span_eq_top h2
  have h5 : Fintype.card (Fin n) = Module.finrank ℂ H :=
    le_antisymm hi.fintype_card_le_finrank (by simpa using h4)
  refine top_le_iff.1 ((hi.span_eq_top_of_card_eq_finrank' h5).symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨b k, rfl⟩

theorem indep_of_conj {H X : Type} [AddCommGroup H] [Module ℂ H] {m : ℕ} (ev : H → X → ℂ)
    (hadd : ∀ x y, ev (x + y) = ev x + ev y) (hsmul : ∀ (a : ℂ) x, ev (a • x) = a • ev x) (w : Fin m → H)
    (φ : Fin m → X → ℂ) (hφ : LinearIndependent ℂ φ) (h : ∀ k g, ev (w k) g = starRingEnd ℂ (φ k g)) :
    LinearIndependent ℂ w := by
  let E : H →ₗ[ℂ] (X → ℂ) := { toFun := ev, map_add' := hadd, map_smul' := hsmul }
  rw [Fintype.linearIndependent_iff] at hφ ⊢
  intro a ha k
  have h1 : ∑ k, starRingEnd ℂ (a k) • φ k = 0 := by
    funext g
    have h2 := congrFun (congrArg E ha) g
    rw [map_sum, map_zero, Finset.sum_apply] at h2
    have h3 := congrArg (starRingEnd ℂ) h2
    rw [map_sum, Pi.zero_apply, map_zero] at h3
    rw [Finset.sum_apply, Pi.zero_apply, ← h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    show _ = starRingEnd ℂ (a k * ev (w k) g)
    rw [h, map_mul, Complex.conj_conj]
    rfl
  simpa using hφ _ h1 k

theorem unif_all : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hp hκ hn i σ
  have good := GlobalTheory.T.uniformisation_goodEmbedding_independent_readings h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hp hκ hn i
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · exact good σ hσ
  obtain ⟨hc, hb⟩ := GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM hT
  have hbar := hb (GlobalTheory.T.cuspFormAdelicFunctions_eq_modelValues_semilinear h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hp)
  have hg := good_resC T hσ
  have hV := hT.laws.spaceW _ (inR i) _ hg
  obtain ⟨v, -, hv⟩ := jTop_bar T R κ v₀ hσ hV (hbar i σ hσ hV)
  have ind : ∀ (m : ℕ) (b : Fin m → Cu T κ i), LinearIndependent T.Q.c.F b →
      LinearIndependent ℂ fun k => jTop T R κ v₀ i σ (b k) := fun m b hb =>
    indep_of_conj (evAt R i σ v) (fun x y => by simp only [evAt, map_add]; rfl)
      (fun a x => by simp only [evAt, map_smul]; rfl) _ _
      (GlobalTheory.PhiIndep.phiC_indep D T κ hT.laws i _ hg hV m b hb) fun k g => congrFun (hv (b k)) g
  refine ⟨ind, ?_⟩
  obtain ⟨c⟩ := hc i σ hσ
  obtain ⟨b⟩ := hasB_nTop T hT.laws κ i
  exact span_top _ _ b c (ind _ _ b.linearIndependent) (good ((starRingEnd ℂ).comp σ) hg).2

end GlobalTheory.UnifAll
