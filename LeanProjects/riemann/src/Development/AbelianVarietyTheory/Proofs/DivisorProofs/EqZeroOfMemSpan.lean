import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRankDeficientReduction
open GlobalTheory.WeilM GlobalTheory.SplitFlip
open scoped Matrix

noncomputable section
namespace GlobalTheory.LiftLowerLoc

theorem eq_zero_of_mem_span {X : Type} [TopologicalSpace X] (φ : GlobalTheory.WeilM.SB X →ₗ[ℂ] ℂ) (G : Set (X → ℂ))
    (hG : ∀ g ∈ G, ∃ hg : g ∈ GlobalTheory.WeilM.SB X, φ ⟨g, hg⟩ = 0) (Ψ : GlobalTheory.WeilM.SB X)
    (hΨ : Ψ.1 ∈ Submodule.span ℂ G) : φ Ψ = 0 := by
  have hle : Submodule.span ℂ G ≤ (LinearMap.ker φ).map (GlobalTheory.WeilM.SB X).subtype := by
    refine Submodule.span_le.2 fun g hg => ?_
    obtain ⟨hg', h0⟩ := hG g hg
    exact ⟨⟨g, hg'⟩, h0, rfl⟩
  obtain ⟨y, hy, hy'⟩ := hle hΨ
  have : y = Ψ := Subtype.ext hy'
  rw [← this]; exact hy

theorem omA_one_one {A D : Type*} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν β : kˣ →* ℂˣ) (Φ : Matrix A D k → ℂ) : omA ν β (1 : GL A k) (1 : GL D k) Φ = Φ :=
  LinearMap.congr_fun ((repA ν β).map_one) Φ

def firstVar {X : Type} [TopologicalSpace X]
    (Bf : GlobalTheory.WeilM.SB X →ₗ[ℂ] GlobalTheory.WeilM.SB X →ₗ⋆[ℂ] ℂ) (Ψ₂ : GlobalTheory.WeilM.SB X) : GlobalTheory.WeilM.SB X →ₗ[ℂ] ℂ where
  toFun Ψ := Bf Ψ Ψ₂
  map_add' x y := by simp
  map_smul' c x := by simp

theorem loc_of_parts
    (HM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ℓ : Fin a → k), ℓ ≠ 0 → ∀ (ψv : AddChar k ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ L : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →ₗ⋆[ℂ] ℂ,
      (∀ (z : Fin d → k) (Ψ Ψ' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k)), Ψ'.1 = (fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * Ψ.1 Y) → L Ψ' = L Ψ) →
      ∀ Ψ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Matrix.vecMul ℓ Y = 0 → Ψ.1 Y = 0) → L Ψ = 0)
    (HF : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin a) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ (h : GL (Fin (a + b)) k) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      ∃ (L : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ) (χ : kˣ →* ℂˣ) (s : ℝ), (χ = ν ∨ χ = ν⁻¹) ∧
        (∀ Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Ψ₁, Bf Ψ₁ Ψ₂ = 0) → L Ψ₂ = 0) ∧
        (∀ (g : GL (Fin a) k) (Ψ Ψ' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
          Ψ'.1 = (fun Y => Ψ.1 (Y * (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k))))) →
          L Ψ' = ((χ (Matrix.GeneralLinearGroup.det g) : ℂ) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) (s : ℂ)) * L Ψ) ∧
        (∀ Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), L Ψ₂ = 0 → ∃ U ∈ nhds (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))),
          ∀ Ψ₁ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y ∉ U, Ψ₁.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0))
    (HL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SmGL.IsSmoothChar χ →
    (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((χ ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (s : ℝ) (ℓ : Fin a → k), ℓ ≠ 0 →
    ∀ L : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ,
      (∀ Ψ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y : Matrix (Fin a) (Fin (a + b)) k, Matrix.vecMul ℓ Y = 0 → Ψ.1 Y = 0) → L Ψ = 0) →
      (∀ (g : GL (Fin a) k) (Ψ Ψ' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ'.1 = (fun Y => Ψ.1 (Y * (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1 0 0 (1 : Matrix (Fin b) (Fin b) k))))) →
        L Ψ' = ((χ (Matrix.GeneralLinearGroup.det g) : ℂ) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) (s : ℂ)) * L Ψ) →
      L = 0) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (ν β : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ (ℓ : Fin a → k), ℓ ≠ 0 → ∀ (ψv : AddChar k ℂ), Continuous ψv → ψv ≠ 1 →
    ∀ Bf : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ[ℂ] GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin a) k) (Ψ₁ Ψ₁' Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β g 1 Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ (h : GL (Fin (a + b)) k) (Ψ₁ Ψ₁' Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₁'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₁.1 → Ψ₂'.1 = GlobalTheory.SplitFlip.omA ν β 1 h Ψ₂.1 → Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      (∀ (z : Fin (a + b) → k) (Ψ₁ Ψ₂ Ψ₂' : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)),
        Ψ₂'.1 = (fun Y => ψv (ℓ ⬝ᵥ (Y *ᵥ z)) * Ψ₂.1 Y) → Bf Ψ₁ Ψ₂' = Bf Ψ₁ Ψ₂) →
      Bf = 0 := by
  intro k _ _ _ _ a b ν β ϖ hϖ hνs hνu hβs hβu hνr ℓ hℓ ψv hψc hψ1 Bf h1 h2 h3
  have hZ : ∀ Ψ₁ Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k),
      (∀ Y : Matrix (Fin a) (Fin (a + b)) k, Matrix.vecMul ℓ Y = 0 → Ψ₂.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0 :=
    fun Ψ₁ Ψ₂ hΨ₂ => HM k a (a + b) ℓ hℓ ψv hψc hψ1 (Bf Ψ₁) (fun z Ψ Ψ' hΨ' => h3 z Ψ₁ Ψ Ψ' hΨ') Ψ₂ hΨ₂
  obtain ⟨L, χ, s, hχ, hL0, hLeq, hLloc⟩ := HF k a b ν β hνs hνu hβs hβu Bf h1 h2
  have hχs : GlobalTheory.SmGL.IsSmoothChar χ := by
    rcases hχ with rfl | rfl
    · exact hνs
    · exact hνs.inv
  have hχr : ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((χ ϖ : ℂ)) ^ m ≠ (r : ℂ) := by
    rcases hχ with rfl | rfl
    · exact hνr
    · intro m hm r hr
      apply hνr m hm r⁻¹
      have e : ((ν⁻¹ ϖ : ℂˣ) : ℂ) = ((ν ϖ : ℂˣ) : ℂ)⁻¹ := by simp
      rw [e, inv_pow] at hr
      rw [Complex.ofReal_inv, ← hr, inv_inv]
  have hLz : L = 0 := HL k a b χ ϖ hϖ hχs hχr s ℓ hℓ L (fun Ψ hΨ => hL0 Ψ fun Ψ₁ => hZ Ψ₁ Ψ hΨ) hLeq
  have hloc : ∀ Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k),
      ∃ U ∈ nhds (X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))),
        ∀ Ψ₁ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y ∉ U, Ψ₁.1 Y = 0) → Bf Ψ₁ Ψ₂ = 0 :=
    fun Ψ₂ => hLloc Ψ₂ (by simp [hLz])
  have hmove : ∀ (Ψ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) (h : GL (Fin (a + b)) k),
      ∃ V : Set (Matrix (Fin a) (Fin (a + b)) k), IsOpen V ∧
        X0 k (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) * (invT h).val ∈ V ∧
        ∀ Ψ₁ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y, Ψ₁.1 Y ≠ 0 → Y ∈ V) → Bf Ψ₁ Ψ₂ = 0 := by
    intro Ψ₂ h
    let Φ₂ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := ⟨omA ν β 1 h Ψ₂.1, omA_mem_SB ν β 1 h Ψ₂.2⟩
    obtain ⟨U, hU, hUB⟩ := hloc Φ₂
    have hc : Continuous fun Y : Matrix (Fin a) (Fin (a + b)) k => Y * ((invT h)⁻¹).val :=
      continuous_id.matrix_mul continuous_const
    refine ⟨interior ((fun Y => Y * ((invT h)⁻¹).val) ⁻¹' U), isOpen_interior, ?_, ?_⟩
    · rw [mem_interior_iff_mem_nhds]
      apply hc.continuousAt.preimage_mem_nhds
      simpa [Matrix.mul_assoc] using hU
    · intro Ψ₁ hΨ₁
      let Φ₁ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := ⟨omA ν β 1 h Ψ₁.1, omA_mem_SB ν β 1 h Ψ₁.2⟩
      have hback : ∀ Ψ : Matrix (Fin a) (Fin (a + b)) k → ℂ, Ψ = omA ν β 1 h⁻¹ (omA ν β 1 h Ψ) := fun Ψ => by
        rw [← omA_mul, mul_one, inv_mul_cancel, omA_one_one]
      rw [h2 h⁻¹ Φ₁ Ψ₁ Φ₂ Ψ₂ (hback _) (hback _)]
      apply hUB
      intro Y hY
      show omA ν β 1 h Ψ₁.1 Y = 0
      have hz : Ψ₁.1 (Y * (invT h).val) = 0 := by
        by_contra hne
        have hm := interior_subset (hΨ₁ _ hne)
        simp only [Set.mem_preimage, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at hm
        exact hY hm
      simp [omA, hz]
  have hfull : ∀ Ψ₂ Ψ₁ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k),
      (∀ Y, Ψ₁.1 Y ≠ 0 → Y.rank = a) → Bf Ψ₁ Ψ₂ = 0 := by
    intro Ψ₂ Ψ₁ hrank
    have hcl : IsClosed (Function.support Ψ₁.1) := by
      have : Function.support Ψ₁.1 = (Ψ₁.1 ⁻¹' {0})ᶜ := by ext; simp
      rw [this]; exact (Ψ₁.2.1.isOpen_fiber 0).isClosed_compl
    have hcpt : IsCompact (Function.support Ψ₁.1) := by
      have := Ψ₁.2.2
      rw [HasCompactSupport, tsupport, hcl.closure_eq] at this
      exact this
    have hex : ∀ Y : Function.support Ψ₁.1, ∃ V : Set (Matrix (Fin a) (Fin (a + b)) k), IsOpen V ∧ Y.1 ∈ V ∧
        ∀ Ψ : GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k), (∀ Y, Ψ.1 Y ≠ 0 → Y ∈ V) → Bf Ψ Ψ₂ = 0 := by
      rintro ⟨Y, hY⟩
      obtain ⟨h, rfl⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock (k := k) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) Y).1
        (by rw [Fintype.card_fin]; exact hrank Y hY)
      exact hmove Ψ₂ h
    choose V hVo hYV hVB using hex
    obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover V hVo (fun Y hY => Set.mem_iUnion.2 ⟨⟨Y, hY⟩, hYV _⟩)
    have hspan := GlobalTheory.CoverSB.mem_span_of_cover k (Fin a) (Fin (a + b)) t (fun i => V i.1) (fun i => hVo _)
      Ψ₁.1 Ψ₁.2 (fun Y hY => by
        obtain ⟨i, hi, hYi⟩ := Set.mem_iUnion₂.1 (ht hY)
        exact ⟨⟨i, hi⟩, hYi⟩)
    refine eq_zero_of_mem_span (firstVar Bf Ψ₂) _ ?_ Ψ₁ hspan
    rintro g ⟨hg, i, hgi⟩
    exact ⟨hg, hVB _ ⟨g, hg⟩ hgi⟩
  have hν1 : ν ϖ ≠ 1 := fun h => hνr 1 one_pos 1 (by simp [h])
  refine LinearMap.ext fun Ψ₁ => LinearMap.ext fun Ψ₂ => ?_
  obtain ⟨Φ₀, hΦ₀, hΦ₀r, hsub⟩ := GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan k a (a + b) (by omega) ν β hνs hνu
    ϖ hϖ hν1 Ψ₁.1 Ψ₁.2
  have hdiff : Ψ₁.1 - Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := sub_mem Ψ₁.2 hΦ₀
  have e : Ψ₁ = ⟨Φ₀, hΦ₀⟩ + ⟨Ψ₁.1 - Φ₀, hdiff⟩ := Subtype.ext (by simp)
  have hA : Bf ⟨Φ₀, hΦ₀⟩ Ψ₂ = 0 := hfull Ψ₂ ⟨Φ₀, hΦ₀⟩ (fun Y hY => by
    by_contra hr; exact hY (hΦ₀r Y hr))
  have hB : firstVar Bf Ψ₂ ⟨Ψ₁.1 - Φ₀, hdiff⟩ = 0 := by
    refine eq_zero_of_mem_span (firstVar Bf Ψ₂) _ ?_ _ hsub
    rintro z ⟨g, Ψ, hΨ, rfl⟩
    refine ⟨sub_mem (omA_mem_SB ν β g 1 hΨ) hΨ, ?_⟩
    have e2 : (⟨omA ν β g 1 Ψ - Ψ, sub_mem (omA_mem_SB ν β g 1 hΨ) hΨ⟩ :
        GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) = ⟨omA ν β g 1 Ψ, omA_mem_SB ν β g 1 hΨ⟩ - ⟨Ψ, hΨ⟩ := rfl
    rw [e2, map_sub, sub_eq_zero]
    exact h1 g ⟨Ψ, hΨ⟩ _ Ψ₂ rfl
  rw [e, map_add, LinearMap.add_apply, hA, zero_add]
  simpa [firstVar] using hB

end GlobalTheory.LiftLowerLoc
