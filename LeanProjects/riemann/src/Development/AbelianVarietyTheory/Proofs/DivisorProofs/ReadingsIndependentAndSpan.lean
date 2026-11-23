import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicLinearIndependent
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnfoldingConstantTermsAgreeAtGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFDOfCuspFiniteClaim
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseDictionaryExistsGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterExpansionWeightCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCharacterDetPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterTrivialOnSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastWeightPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterTrivialOnLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicExtremalNegativeFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicExtremalNegativeFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodEmbeddingLabelIffStatement

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

theorem card_le_finrank_of_semilinear {K C Y : Type} [Field K] [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup Y] [Module ℂ Y] {σ : K →+* ℂ} (j : C →ₛₗ[σ] Y) {m : ℕ} (f : Fin m → Y) (hf : LinearIndependent ℂ f)
    (hm : ∀ k, f k ∈ Submodule.span ℂ (Set.range j)) : m ≤ Module.finrank K C := by
  let b := Module.finBasis K C
  have hle : Submodule.span ℂ (Set.range j) ≤ Submodule.span ℂ (Set.range fun k => j (b k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h1 := linearIndependent_le_span_aux' f hf (Set.range fun k => j (b k))
    (by rintro _ ⟨k, rfl⟩; exact hle (hm k))
  have h2 : Fintype.card (Set.range fun k => j (b k)) ≤ Module.finrank K C :=
    (Fintype.card_range_le _).trans (Fintype.card_fin _).le
  exact (Fintype.card_fin m).symm.le.trans (h1.trans h2)

theorem linearIndependent_conj {ι : Type} {m : ℕ} {f : Fin m → ι → ℂ} (hf : LinearIndependent ℂ f) :
    LinearIndependent ℂ fun k x => starRingEnd ℂ (f k x) := by
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc k
  have h := hf (fun k => starRingEnd ℂ (c k)) (funext fun x => by
    have := congrArg (starRingEnd ℂ) (congrFun hc x)
    simpa [Finset.sum_apply, map_sum] using this) k
  simpa using h

theorem eval_eq_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (he : ∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x : H)
    (hx : e x v = 0) : x = 0 := by
  rw [← inner_self_eq_zero (𝕜 := ℂ), he]
  refine mul_eq_zero_of_right _ ?_
  by_cases h : ∃ c, IsMultIP M μ 𝓕 (e x) (e x) c
  · have h1 := (ipM_spec M μ 𝓕 _ _ h v v).2
    simp only [hx, Pi.zero_apply, mul_zero, integral_zero, inner_self_eq_norm_sq_to_K, hv] at h1
    simpa using h1.symm
  · exact dif_neg h

set_option maxHeartbeats 1000000 in

theorem adel_mem_span {D : D7} (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n) (hL : LastPos (T.Q.Dw j) a)
    (hn : 8 * D.R.f * D.R.r + 4 ≤ n) (P : FDSec (T.U j σ).X) (hP : IsHolCusp (T.U j σ).X (laU (T.U j σ) a n) P) :
    adel (T.V j σ) (T.dict j σ) (T.mu j σ) P ∈ Submodule.span ℂ
      (Set.range ((adel (T.V j σ) (T.dict j σ) (T.mu j σ)).comp (rdC (T.U j) σ a n))) := by
  obtain ⟨-, hA, -, -, -, hdeg, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr1 : 1 ≤ D.R.r := (hnum j hj).2.1
  obtain ⟨hrk, hW⟩ := h.modelW j hj σ hσ
  obtain ⟨th, hrk', -, hdict⟩ := h.dictU j hj σ hσ
  have hG := GlobalTheory.RunIn.gamAt_of_lawsJ D T h
  have hle := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr1 hA (fun σ hσ => h.unf j hj σ hσ) σ hσ
    (fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩)
    (by
      intro k ga hga hv
      refine hG j hj σ hσ k ga hga fun x hx => ?_
      obtain ⟨u, hu, he⟩ := hv x hx
      refine ⟨u, hu, ?_⟩
      rw [he, Nat.cast_smul_eq_nsmul]
      exact add_sub_cancel_left _ _)
    a n hD hL
    (by
      rw [hdeg]
      calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
        _ ≤ n := hn)
    (fun k => h.chiTriv j hj σ hσ a n hD k)
  have hle' : GlobalTheory.Dict.holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (Set.range (rdC (T.U j) σ a n)) := by
    refine le_trans hle (Submodule.span_mono ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  have hmem : (fun k => ((T.U j σ).X k).dom.indicator (P k)) ∈ GlobalTheory.Dict.holSub0 (T.U j σ).X (laU (T.U j σ) a n) := by
    refine ⟨Submodule.subset_span fun k => ?_, fun k x hx => Set.indicator_of_notMem hx _⟩
    exact (GlobalTheory.DomCongr.bddSec_cusp_congr _ _ ((T.U j σ).X k) _ (P k) _
      (fun x hx => (Set.indicator_of_mem hx _).symm)).2 (hP k)
  have he : adel (T.V j σ) (T.dict j σ) (T.mu j σ) (fun k => ((T.U j σ).X k).dom.indicator (P k)) =
      adel (T.V j σ) (T.dict j σ) (T.mu j σ) P := by
    funext g
    show T.mu j σ g * ((T.U j σ).X (T.dict j σ g).1).dom.indicator (P (T.dict j σ g).1) (T.dict j σ g).2 =
      T.mu j σ g * P (T.dict j σ g).1 (T.dict j σ g).2
    rw [Set.indicator_of_mem (hdict.2.2.2.1 g)]
  rw [← he]
  have h2 := Submodule.mem_map_of_mem (f := adel (T.V j σ) (T.dict j σ) (T.mu j σ)) (hle' hmem)
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

set_option maxHeartbeats 1000000 in

theorem card_le_finrank_cusp {D : D7} (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n) (hL : LastPos (T.Q.Dw j) a)
    (hn : 8 * D.R.f * D.R.r + 4 ≤ n) (θ : InfFam D) (hθ : IsInfFam θ) (w : D.what₂.Tau → ℕ → ℤ) (e : D.what₂.Tau → ℤ)
    (hmu : ∀ k ∈ T.Kf j σ, T.mu j σ k = 1) (hinf : ∀ ρ, HasInfExp D (T.chiW j σ) ρ (-(e ρ : ℚ)))
    (hw : ∀ k (ρ : D.what₂.Tau) (τ : ((T.U j σ).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r,
      laU (T.U j σ) a n k τ c = w ρ c + e ρ)
    {W : HSp D} (hV : T.V j σ = W) (x : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hx : NegFirst W (D.R.sigW j).2 x) {m : ℕ} (φ : Fin m → GA D W → ℂ) (hφ : LinearIndependent ℂ φ)
    (hh : ∀ k, IsHolFor θ W x (fun ρ c => w ρ c) (φ k)) (hl : ∀ k, ∀ γ ∈ GQ W, ∀ g, φ k (γ * g) = φ k g)
    (hk : ∀ Kf, IsLevelK W (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ κ ∈ Kf, ∀ g, φ k (g * κ) = φ k g)
    (hb : ∀ k, ∃ C : ℝ, ∀ g, ‖φ k g‖ ≤ C) : m ≤ Module.finrank T.Q.c.F (T.cuspA j a n) := by
  subst hV
  obtain ⟨hr, x₀, hB⟩ := GlobalTheory.T.base_dictionary_exists_good_embedding D T h j hj σ hσ θ hθ
  have hK := h.levelK j hj σ hσ
  have hM := h.muUnit j hj σ hσ
  have hq : ∀ k, ((T.U j σ).X k).p0 = (D.R.sigW j).2 := fun k =>
    ((h.unf j hj σ hσ).2.1 k).1.trans (h.pins.2.2.2 j hj).2.1
  obtain ⟨u, hu⟩ := GlobalTheory.T.character_expansion_weight_compat D θ _ _ hr _ _ _ _ x₀ (laU (T.U j σ) a n) x _ (fun ρ c => w ρ c) e (T.mu j σ) hθ hB
    (fun k hk => ((hK k).1 hk).1) hq hx hM.1 hM.2.1 hM.2.2.1 hmu
    (GlobalTheory.T.archimedean_character_det_power D θ _ _ _ e hθ (h.muVal j hj σ hσ) hinf) (fun k ρ τ hτ c => hw k ρ τ hτ _)
    (h.chiTriv j hj σ hσ a n hD) (fun k τ c d hc hd => by
      rw [← hq k] at hc hd
      simp only [laU, if_pos hd, if_neg (not_le.2 hc)]
      omega)
  have : FiniteDimensional T.Q.c.F (T.cuspA j a n) := h.cuspFD j hj a n hD
  refine card_le_finrank_of_semilinear ((adel (T.V j σ) (T.dict j σ) (T.mu j σ)).comp (rdC (T.U j) σ a n))
    (fun k g => φ k (g * u)) ?_ fun k => ?_
  · rw [Fintype.linearIndependent_iff] at hφ ⊢
    intro c hc
    refine hφ c (funext fun g => ?_)
    have := congrFun hc (g * u⁻¹)
    simpa [Finset.sum_apply] using this
  · obtain ⟨P, hP, hPe⟩ := hu (φ k) (hh k) (hl k) (hk _ hK k) (hb k)
    rw [show (fun g => φ k (g * u)) = adel (T.V j σ) (T.dict j σ) (T.mu j σ) P from funext hPe]
    exact adel_mem_span T h j hj σ hσ a n hD hL hn P hP

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def evL (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (v : (R.MW i σ).Vec) : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) where
  toFun := evAt R i σ v
  map_add' x y := by simp [evAt]
  map_smul' c x := by simp [evAt]

theorem parAt_sig (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ) = Formalism.L2.NTheta.holPar (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2
      (Formalism.L2.NTheta.kapW (D.hc (lab σ ρ)) _ _) := by
  unfold kapAt
  rw [show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]

set_option maxHeartbeats 1000000 in

theorem finrank_model_le (hP : GlobalTheory.Published.CuspRapidDecay) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hL : R.toLevCh.Is A.μ0)
    (hθ : R.models_inf) (hH : R.models_HW) (h : TieIn T R κ v₀) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank T.Q.c.F (Cu T κ i) := by
  have hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
    have := D.R.m_add_three_le_k
    have := i.2
    simp only [Ranks.sigW, Ranks.r]
    omega
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h1 : ∃ ρ, tauE D ρ = τ
    · exact ⟨h1.choose⟩
    · exact ⟨(not_not.1 (mt (GlobalTheory.SmoothForms.RealPts.tauE_cm D τ).2 h1)).choose⟩
  have hn' : 8 * D.R.f * D.R.r + 4 ≤ (κ i).n := (h.kap i ρ₀).2.2 ▸ hn
  let β := Module.finBasis ℂ (R.HW i σ).H
  have hM : ∀ x, IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i R.triv)) (Lev.levChi _ (R.βW i) (R.datWp i R.triv))
      ((R.HW i σ).e x) := fun x =>
    (GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 ((hH i σ).2.1.le ⟨x, rfl⟩)
  have hind : LinearIndependent ℂ fun k => (R.HW i σ).e (β k) (v₀ i σ) :=
    β.linearIndependent.map' (evL T R i σ (v₀ i σ)) (LinearMap.ker_eq_bot'.2 fun x hx =>
      eval_eq_zero _ (R.HW i σ).e _ _ _ (hH i σ).2.2 _ ((h.hv₀ i σ).norm R) x hx)
  have hlev : ∀ Kf, IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ c ∈ Kf, ∀ g,
      (R.HW i σ).e (β k) (v₀ i σ) (g * c) = (R.HW i σ).e (β k) (v₀ i σ) g := fun Kf hK k c hc g => by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.level_character_trivial_on_subgroup D T0 R.toLevCh A.μ0 hL i Kf hK c hc
    rw [(hM _).lev _ c h1, h2, one_mul]
  have hbd : ∀ k, ∃ C : ℝ, ∀ g, ‖(R.HW i σ).e (β k) (v₀ i σ) g‖ ≤ C := fun k =>
    GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ ((hM _).aut _) ((hM _).cusp _)
  have key : ∀ σ' : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ') → (∀ ρ, lab σ' ρ = lab σ ρ) →
      ∀ x, NegFirst (Wc D i) (D.R.sigW ((i : ℕ) + 1)).2 x → ∀ φ : Fin (Module.finrank ℂ (R.HW i σ).H) → GA D (Wc D i) → ℂ,
      LinearIndependent ℂ φ → (∀ k, IsHolFor R.θ (Wc D i) x
        (fun ρ c => wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c) (φ k)) →
      (∀ k, ∀ γ ∈ GQ (Wc D i), ∀ g, φ k (γ * g) = φ k g) →
      (∀ Kf, IsLevelK (Wc D i) (D.host.g 0 * D.host.g 1) Kf → ∀ k, ∀ c ∈ Kf, ∀ g, φ k (g * c) = φ k g) →
      (∀ k, ∃ C : ℝ, ∀ g, ‖φ k g‖ ≤ C) → Module.finrank ℂ (R.HW i σ).H ≤ Module.finrank T.Q.c.F (Cu T κ i) := by
    intro σ' hσ' hlab x hx φ h1 h2 h3 h4 h5
    choose e he using fun ρ => (D.hc (lab σ' ρ)).e_int i
    refine card_le_finrank_cusp T h.laws _ (inR i) _ hσ' _ _ (dom_wtA (κ i)) (GlobalTheory.T.last_weight_positive D T κ h.laws h.kap i) hn' R.θ hθ
      (fun ρ c => wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c) e
      (GlobalTheory.T.level_character_trivial_on_level D G Pl0 T0 A T R h.laws hL h.chiR i σ' hσ') (fun ρ => he ρ ▸ (h.chiR i σ' hσ').2.2.1 ρ)
      (fun k ρ τ hτ c => ?_) (h.laws.spaceW _ (inR i) _ hσ') x hx φ h1 h2 h3 h4 h5
    rw [← hlab ρ]
    exact GlobalTheory.T.weight_label_at_unfolding D T κ h.laws h.alg h.kap i σ' hσ' e (fun ρ => (he ρ).symm) k ρ τ hτ c
  by_cases hσ : GoodEmb T.Q.c (res T σ)
  · obtain ⟨x, hx, hhol⟩ := GlobalTheory.T.holomorphic_extremal_negative_first D R.θ _ _ (R.MW i σ) (fun ρ => D.hc (lab σ ρ)) _ _ hθ hpq (rank_Wc i)
      (fun ρ => (if_pos ((GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).1.1 hσ)).trans (parAt_sig i σ ρ)) _ (h.hv₀ i σ).1
    exact key σ hσ (fun _ => rfl) x hx _ hind (fun k => hhol _ _ _ (hM _)) (fun k => ((hM _).aut _).left) hlev hbd
  · obtain ⟨x, hx, hhol⟩ := GlobalTheory.T.antiholomorphic_extremal_negative_first D R.θ _ _ (R.MW i σ) (fun ρ => D.hc (lab σ ρ)) _ _ hθ hpq (rank_Wc i)
      (fun ρ => (if_neg (mt (GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).1.2 hσ)).trans (congrArg dualPar (parAt_sig i σ ρ))) _
      (h.hv₀ i σ).1
    refine key ((starRingEnd ℂ).comp σ) (good_resC T hσ) (fun ρ => (GlobalTheory.T.good_embedding_label_iff D T h.laws h.alg σ ρ).2) x hx _
      (linearIndependent_conj hind) (fun k => hhol _ _ _ (hM _)) (fun k γ hγ g => ?_) (fun Kf hK k c hc g => ?_)
      fun k => (hbd k).imp fun C hC g => ?_
    · exact congrArg _ (((hM _).aut _).left γ hγ g)
    · exact congrArg _ (hlev Kf hK k c hc g)
    · exact (Complex.norm_conj _).trans_le (hC g)

end GlobalTheory.HolRead
