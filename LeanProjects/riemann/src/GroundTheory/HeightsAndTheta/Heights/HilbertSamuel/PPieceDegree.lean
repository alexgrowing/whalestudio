import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConjIntNum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.GlobalFields.ComplexMultiplication.ExistsRingEquivExtendOfIsTranscendenceBasis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

namespace PieceDegreeAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [Algebra F Ω]

def rels (y : (Σ k, ι k) → Ω) (s : F →+* ℂ) : Set (MvPolynomial (Σ k, ι k) ℂ) :=
  {f | ∃ (d : K → ℕ) (g h : MRing ι) (θ : F), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval y g = algebraMap F Ω θ * aeval y h ∧
    f = MvPolynomial.map (Int.castRingHom ℂ) g - C (s θ) * MvPolynomial.map (Int.castRingHom ℂ) h}

def pieceIdeal (y : (Σ k, ι k) → Ω) (s : F →+* ℂ) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℂ)) ⊔ Ideal.span (rels y s)

omit [Fintype K] in

theorem zero_pieceIdeal_iff (y : (Σ k, ι k) → Ω) (s : F →+* ℂ) (z : (Σ k, ι k) → ℂ) :
    (∀ f ∈ pieceIdeal y s, eval z f = 0) ↔
      (∀ f ∈ mCoordIdeal y, eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0) ∧ LiesOver y s z := by
  have key : ∀ I : Ideal (MvPolynomial (Σ k, ι k) ℂ), (∀ f ∈ I, eval z f = 0) ↔ I ≤ RingHom.ker (eval z) :=
    fun I => ⟨fun h f hf => RingHom.mem_ker.2 (h f hf), fun h f hf => RingHom.mem_ker.1 (h hf)⟩
  rw [key, pieceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le]
  apply and_congr
  · exact ⟨fun h f hf => RingHom.mem_ker.1 (Ideal.mem_comap.1 (h hf)),
      fun h f hf => Ideal.mem_comap.2 (RingHom.mem_ker.2 (h f hf))⟩
  · constructor
    · intro h d g g' θ hg hg' hgg
      have := h ⟨d, g, g', θ, hg, hg', hgg, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, eval_C] at this
      exact sub_eq_zero.1 this
    · rintro h f ⟨d, g, g', θ, hg, hg', hgg, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, eval_C]
      exact sub_eq_zero.2 (h d g g' θ hg hg' hgg)

omit [Fintype K] in

theorem pieceIdeal_map (y : (Σ k, ι k) → Ω) (s : F →+* ℂ) (τ : ℂ ≃+* ℂ) :
    (pieceIdeal y s).map (MvPolynomial.map (τ : ℂ →+* ℂ)) = pieceIdeal y ((τ : ℂ →+* ℂ).comp s) := by
  have hint : (τ : ℂ →+* ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ := RingHom.ext_int _ _
  have hmm : ∀ g : MRing ι, MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map (Int.castRingHom ℂ) g) = MvPolynomial.map (Int.castRingHom ℂ) g := by
    intro g
    rw [MvPolynomial.map_map, hint]
  rw [pieceIdeal, pieceIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span]
  congr 1
  · congr 1
    exact RingHom.ext hmm
  · congr 1
    ext f
    constructor
    · rintro ⟨_, ⟨d, g, g', θ, hg, hg', hgg, rfl⟩, rfl⟩
      refine ⟨d, g, g', θ, hg, hg', hgg, ?_⟩
      rw [map_sub, map_mul, map_C, hmm, hmm]
      rfl
    · rintro ⟨d, g, g', θ, hg, hg', hgg, rfl⟩
      refine ⟨_, ⟨d, g, g', θ, hg, hg', hgg, rfl⟩, ?_⟩
      rw [map_sub, map_mul, map_C, hmm, hmm]
      rfl

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem radical_map_conj (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (τ : ℂ ≃+* ℂ) :
    (I.map (MvPolynomial.map (τ : ℂ →+* ℂ))).radical = I.radical.map (MvPolynomial.map (τ : ℂ →+* ℂ)) := by
  have hinj : Function.Injective (MvPolynomial.map (σ := Σ k, ι k) (τ : ℂ →+* ℂ)) := map_injective _ τ.injective
  refine (Ideal.map_radical_of_surjective (map_surjective _ τ.surjective) ?_).symm
  rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
  exact bot_le

theorem exists_ringEquiv_comp [NumberField F] (sg sg' : F →+* ℂ) :
    ∃ τ : ℂ ≃+* ℂ, (τ : ℂ →+* ℂ).comp sg = sg' := by
  have hc : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have hΩ : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  have h1 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg.toAlgebra hc hΩ
  have h2 := @GroundTheory.Global.trdeg_eq_cardinalMk_of_countable ℂ _ _ F _ sg'.toAlgebra hc hΩ
  obtain ⟨τ, hτ⟩ := @GroundTheory.Global.exists_ringEquiv_extend_of_trdeg_eq ℂ _ _ F F _ _ sg.toAlgebra sg'.toAlgebra
    (RingEquiv.refl F) (h1.trans h2.symm)
  exact ⟨τ, RingHom.ext fun a => hτ a⟩

theorem piece_open [NumberField F] {y : (Σ k, ι k) → Ω}
    (hex : ∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) (s : F →+* ℂ) :
    ∀ z ∈ mcPts (mCoordIdeal y), (∀ f ∈ pieceIdeal y s, eval z f = 0) →
      ∀ᶠ z' in 𝓝 z, z' ∈ mcPts (mCoordIdeal y) → ∀ f ∈ pieceIdeal y s, eval z' f = 0 := by
  intro z hz hzI
  have hzs : LiesOver y s z := ((zero_pieceIdeal_iff y s z).1 hzI).2
  let U : Set ((Σ k, ι k) → ℂ) := ⋃ s' ∈ ({s}ᶜ : Set (F →+* ℂ)), {z | LiesOver y s' z}
  have hU : IsClosed U :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun s' _ => EmbeddingWeight.isClosed_liesOver y s'
  have hzU : z ∉ U := by
    simp only [U, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, not_exists]
    intro s' hs' h'
    exact hs' ((hex z hz).unique h' hzs)
  filter_upwards [hU.isOpen_compl.mem_nhds hzU] with z' hz' hz'P
  obtain ⟨s', hs', -⟩ := hex z' hz'P
  have hss : s' = s := by
    by_contra hne
    exact hz' (Set.mem_biUnion (x := s') hne hs')
  subst hss
  exact (zero_pieceIdeal_iff y s' z').2 ⟨hz'P.2, hs'⟩

end PieceDegreeAlt

open PieceDegreeAlt

theorem PieceDegree.proof (hI : PieceIntegral.Statement) (hC : ConjIntNum.Statement) :
    PieceDegree.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D L sg sg' hP _ hL hex
  classical
  have hint : ∀ s : F →+* ℂ,
      ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y s z}.indicator fun _ => (1 : ℝ)) =
        NumbersDVR.intNum ℂ (pieceIdeal y s).radical (fun j => (L j).a) := by
    intro s
    rw [← hI K ι (mCoordIdeal y) D L (pieceIdeal y s) hP hL le_sup_left (piece_open hex s)]
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) fun z hz => ?_
    have hiff : z ∈ {z | LiesOver y s z} ↔ z ∈ {z | ∀ f ∈ pieceIdeal y s, eval z f = 0} := by
      simp only [Set.mem_ofPred_eq, zero_pieceIdeal_iff]
      exact ⟨fun h => ⟨hz.2, h⟩, fun h => h.2⟩
    by_cases h : LiesOver y s z
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.1 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hiff.2 h'))]
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_comp sg sg'
  rw [hint, hint, ← hτ, ← pieceIdeal_map y sg τ, radical_map_conj]
  exact congrArg (fun x : ℤ => (x : ℝ)) (hC K ι ℂ τ (pieceIdeal y sg).radical D (fun j => (L j).a)).symm

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
