import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEqBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsIndependentGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspFormOfExtremalVectorMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedSectionOfBoundedHolomorphicFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicCuspFormOfAdelicConstantTermsZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertModelConjugationAntilinearBijectionStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingSpan

theorem lastPos_of_kapIs {D : D7} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} (h : KapIs κ) (i : Fin D.R.m) :
    ∀ τ k, 1 ≤ (κ i).aP τ k := by
  intro τ k
  rw [(h i τ).1 k, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by simp only [Ranks.sigW]; omega
  have hk2 := k.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (D.R.k + i - 1 - k) k (by simp only [Ranks.r]; omega)
  have h4 : Formalism.L2.NTheta.lamAt (D.hc τ) (k + (D.R.k + i - 1 - k)) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  have h5 := (D.hc τ).gap_be i
  have h6 : ((D.R.k + i - 1 - k : ℕ) : ℚ) = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - (k + 1) := by
    rw [show D.R.k + i - 1 - k = (D.R.sigW ((i : ℕ) + 1)).1 - (k + 1) by omega, Nat.cast_sub hk2]
    push_cast
    rfl
  rw [h4, h6] at h3
  simp only [aPl, if_pos k.2]
  rw [Int.le_toNat (Int.floor_nonneg.2 (by linarith)), Int.le_floor]
  push_cast
  linarith

theorem finrank_le_of_antilinear {H H' : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
    [FiniteDimensional ℂ H'] (e : H ≃ₗ⋆[ℂ] H') : Module.finrank ℂ H ≤ Module.finrank ℂ H' := by
  have b := Module.finBasis ℂ H'
  have h : Submodule.span ℂ (Set.range fun k => e.symm.toLinearMap (b k)) = ⊤ := by
    rw [← span_range_eq_basis b e.symm.toLinearMap, show Set.range e.symm.toLinearMap = Set.univ from Set.range_eq_univ.2 e.symm.surjective, Submodule.span_univ]
  rw [← finrank_top, ← h]
  exact (finrank_range_le_card _).trans (Fintype.card_fin _).le

theorem adel_rdU_eq {D : D7} (T : CoreJ D) {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    adel W (castDict hV (T.dict j σ)) (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) (T.cE j σ))
      (rdU (T.U j σ) f) = ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ)⁻¹ • phiC T hV a f := by
  subst hV
  have hl : ((lieFac (T.Q.Dw j) (xiR D) a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  exact (inv_smul_smul₀ hl _).symm

set_option maxHeartbeats 1000000 in

theorem evAt_mem_span (hP : GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels)
    (ht : TieIn T R κ v₀) (hp : T.pb = R.C.P.pb) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i)
    (x : (R.HW i σ).H) : evAt R i σ (v₀ i σ) x ∈
      Submodule.span ℂ (Set.range fun f : Cu T κ i => phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1))) := by
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ ht i σ hσ
  have hg := GlobalTheory.T.coreDictionary_good_at_good_embedding D G Pl0 T0 A T R κ v₀ hL hM ht hp i σ hσ hV w hw
  have hx : (R.HW i σ).e x ∈ R.Wall i σ := (hM.HW i σ).2.1 ▸ LinearMap.mem_range_self _ x
  obtain ⟨h1, h2⟩ := GlobalTheory.T.holomorphic_cusp_form_of_extremal_vector_multiplicity hP D R.θ _ _ (R.MW i σ) w (v₀ i σ) hM.inf hs hw (ht.hv₀ i σ).1 _ _ _ hx
  rw [show levChi _ (R.βW i) (R.datWp i R.triv) = fun _ => 1 from funext (GlobalTheory.ConjEval.levChi_principal R i)] at h1
  obtain ⟨P, hP0, hPb, hP⟩ := GlobalTheory.T.exists_boundedSection_of_boundedHolomorphicForm D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hs hg _ h1
  have hc := GlobalTheory.T.isHolomorphicCuspForm_of_adelic_constantTerms_zero D R.θ _ _ _ w _ _ _ _ _ _ _ _ _ hs hg P hPb (hP.symm ▸ h2)
  have hτ : D.what₂.Tau := D.eTau.symm ⟨1, Subgroup.one_mem _⟩
  have hmem := GlobalTheory.OntoCore.holSub0_le_span_cuspA D T ht.laws _ (inR i) (κ i) (fun τ k _ => lastPos_of_kapIs ht.kap i τ k)
    ((ht.kap i hτ).2.2.symm ▸ hn) _ hσ ⟨holCusp_mem_holSub _ _ hc, hP0⟩
  have h3 := Submodule.mem_map_of_mem (f := adel (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ)))
    (muPin (Wc D i) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ)))
      (T.cE ((i : ℕ) + 1) (res T σ)))) hmem
  rw [hP, Submodule.map_span] at h3
  refine Submodule.span_le.2 ?_ h3
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  rw [adel_rdU_eq T hV (wtA (κ i)) f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨f, hf⟩, rfl⟩)

set_option maxHeartbeats 1000000 in

theorem jUnif : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ → JEvBar T R κ → EvInj T R v₀ → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ := by
  intro hP D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hp hJ hB hI hn
  refine jUnif_of T R κ v₀ ht.laws hJ hB hI (GlobalTheory.PhiIndep.phiC_indep D T κ ht.laws)
    (evAt_mem_span hP T R κ v₀ hL hM ht hp hn) fun i σ hσ => ?_
  obtain ⟨e⟩ := (GlobalTheory.T.hilbertModel_conjugation_antilinear_bijection D G Pl0 T0 A T R κ v₀ hM ht).1 i σ hσ
  exact finrank_le_of_antilinear e

end GlobalTheory.ReadingSpan
