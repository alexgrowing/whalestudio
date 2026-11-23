import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.PosSemidefOfForallCombination
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRankAdditiveExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeKernelAddImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeHalfRankLogOfGramBoundStatement
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.TorusSlope

theorem slope_le_of_torusExt : ∀ (m : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (r m' : ℕ) (h : HermFam K (Fin m → K)) (L : Submodule (𝓞 K) (Fin m → K)) (ε : Fin r → Fin m → K) (q : (Fin m → K) →ₗ[K] (Fin m' → K)) (h' : HermFam K (Fin m' → K)) (L' : Submodule (𝓞 K) (Fin m' → K)), TorusExt h L ε q h' L' C → -deg h' L' ≤ -deg h L + C' ∧ ∀ ν : ℝ, 0 ≤ ν → MuLe h' L' ν → MuLe h L (ν + C') := by
  intro m C hC
  refine ⟨(m + 1 : ℝ) * Real.log C, by have := Real.log_nonneg hC; positivity, ?_⟩
  intro K _ _ r m' h L ε q h' L' hT
  obtain ⟨hL, hL', hε, hqs, _hker, hLker, hqL, hG⟩ := hT
  have hC0 : (0 : ℝ) < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hPSD : ∀ (W : Submodule (𝓞 K) (Fin m → K)) (σ : K →+* ℂ) (n : ℕ) (v : Fin n → Fin m → K),
      (∀ i, v i ∈ W) → ((C : ℂ) • h.gram σ v - h'.gram σ (q ∘ v)).PosSemidef :=
    fun W σ n v _ => (hG σ).2 n v
  have hFG : ∀ W ≤ L, W.FG := fun W hW => by
    haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL.1
    have h2 := (IsNoetherian.noetherian (W.comap L.subtype)).map L.subtype
    rwa [Submodule.map_comap_eq_of_le (by simpa using hW)] at h2
  have hmapL : ∀ W ≤ L, W.map (q.restrictScalars (𝓞 K)) ≤ L' := fun W hW => by
    rintro _ ⟨x, hx, rfl⟩
    exact hqL x (hW hx)
  have hInf : ∀ W ≤ L, W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K) ≤
      Submodule.span (𝓞 K) (Set.range ε) := fun W hW => by
    rw [← hLker]; exact inf_le_inf_right _ hW
  have hTor : ∀ W ≤ L, deg h (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) ≤
      (latRank K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) : ℝ) / 2 * Real.log C :=
    fun W hW => GlobalTheory.T.degree_le_half_rank_log_of_gram_bound K m r h ε C hC0 hε (fun σ => (hG σ).1) _ (hInf W hW)
  have hExt : ∀ W ≤ L, deg h W ≤ deg h (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) +
      deg h' (W.map (q.restrictScalars (𝓞 K))) +
      (latRank K (W.map (q.restrictScalars (𝓞 K))) : ℝ) / 2 * Real.log C :=
    fun W hW => GlobalTheory.T.degree_le_kernel_add_image K m m' h h' q C hC0 W (hFG W hW) (hPSD W)
  have hRk : ∀ W : Submodule (𝓞 K) (Fin m → K), (latRank K W : ℝ) =
      latRank K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) +
        latRank K (W.map (q.restrictScalars (𝓞 K))) := fun W => by
    exact_mod_cast GlobalTheory.T.lattice_rank_additive_exact K m m' q W
  constructor
  ·
    have hmapFG : (L.map (q.restrictScalars (𝓞 K))).FG := hL.1.map _
    have hspan : (L' : Set (Fin m' → K)) ⊆
        Submodule.span K ((L.map (q.restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin m' → K)) :
          Set (Fin m' → K)) := by
      have : Submodule.span K ((L.map (q.restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin m' → K)) :
          Set (Fin m' → K)) = ⊤ := by
        rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hL.2,
          Submodule.map_top, LinearMap.range_eq_top.mpr hqs]
      rw [this]; exact fun _ _ => Submodule.mem_top
    have hle := deg_of_le h' hmapFG hL'.1 (hmapL L le_rfl) hspan
    have hidx : 0 ≤ Real.log ((L.map (q.restrictScalars (𝓞 K))).toAddSubgroup.relIndex
        L'.toAddSubgroup : ℝ) / Module.finrank ℚ K :=
      div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    have hrkL : (latRank K L : ℝ) ≤ m := by
      have : latRank K L ≤ m := by
        unfold latRank
        calc Module.finrank K (Submodule.span K (L : Set (Fin m → K)))
            ≤ Module.finrank K (Fin m → K) := Submodule.finrank_le _
          _ = m := by simp
      exact_mod_cast this
    have h1 := hExt L le_rfl
    have h2 := hTor L le_rfl
    have h3 := hRk L
    have h4 : (latRank K L : ℝ) / 2 * Real.log C ≤ (m + 1 : ℝ) * Real.log C := by
      have : (latRank K L : ℝ) / 2 ≤ m + 1 := by
        have := Nat.cast_nonneg (α := ℝ) (latRank K L); linarith
      exact mul_le_mul_of_nonneg_right this hlogC
    nlinarith
  · intro ν hν hMu W hW
    have h1 := hExt W hW
    have h2 := hTor W hW
    have h3 := hRk W
    have h5 := hMu _ (hmapL W hW)
    set a := (latRank K (W ⊓ (LinearMap.ker q).restrictScalars (𝓞 K)) : ℝ)
    set b := (latRank K (W.map (q.restrictScalars (𝓞 K))) : ℝ)
    have ha : 0 ≤ a := Nat.cast_nonneg _
    have hb : 0 ≤ b := Nat.cast_nonneg _
    rw [h3]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    nlinarith [mul_nonneg ha hν, mul_nonneg ha hlogC, mul_nonneg hb hlogC, mul_nonneg (mul_nonneg ha hm) hlogC,
      mul_nonneg (mul_nonneg hb hm) hlogC]

end GlobalTheory.TorusSlope
end
