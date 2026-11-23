import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorDualLatticeIndicaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicatorStatement

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum InDual Lifts)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.Comm.DualCosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem inDual_add {L : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual L η) (h' : InDual L ξ) :
    InDual L (η + ξ) := by
  intro y hy
  rw [add_dotProduct]
  exact add_mem (h y hy) (h' y hy)

theorem inDual_sub {L : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual L η) (h' : InDual L ξ) :
    InDual L (η - ξ) := by
  intro y hy
  rw [sub_dotProduct]
  exact sub_mem (h y hy) (h' y hy)

theorem inDual_smul {L : Submodule 𝒪[k] (n → k)} {η : n → k} (h : InDual L η) (s : 𝒪[k]) :
    InDual L (s • η) := by
  intro y hy
  rw [smul_dotProduct, Algebra.smul_def]
  exact mul_mem s.2 (h y hy)

theorem isLocallyConstant_of_periodic (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] {g : (n → k) → ℂ}
    (hg : ∀ η ξ, InDual L ξ → g (η + ξ) = g η) : IsLocallyConstant g := by
  have hD := (dual_compact_open L).2
  refine (IsLocallyConstant.iff_exists_open g).2 fun x => ?_
  refine ⟨{η | InDual L (η - x)}, hD.preimage (continuous_sub_right x), ?_, fun η hη => ?_⟩
  · intro y _
    simp
  · have h := hg x (η - x) hη
    rwa [add_sub_cancel] at h

private theorem secondCountableTopology_localField' (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : SecondCountableTopology K := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  obtain ⟨r⟩ := (IsRankLeOne.nonempty : Nonempty (ValuativeRel.RankLeOneStruct K))
  letI : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).RankOne :=
    { hom' := r.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := r.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact secondCountable_of_proper

variable [MeasurableSpace k] [BorelSpace k]

theorem integrable_of_periodic (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (q : Unif k)
    (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] {g : (n → k) → ℂ}
    (hg : ∀ η ξ, InDual L ξ → g (η + ξ) = g η) (hs : ∀ η, g η ≠ 0 → InDual L (q.1 • η)) : Integrable g μ := by
  haveI := secondCountableTopology_localField' k
  have hlc := isLocallyConstant_of_periodic L hg
  have hK : IsCompact {η : n → k | InDual L (q.1 • η)} := by
    have h2 : {η : n → k | InDual L (q.1 • η)} =
        (Homeomorph.smulOfNeZero ((q.1 : 𝒪[k]) : k) q.ne_zero) ⁻¹' {η | InDual L η} := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Homeomorph.smulOfNeZero_apply, Algebra.smul_def]
      rfl
    rw [h2, Homeomorph.isCompact_preimage]
    exact (dual_compact_open L).1
  have hcs : HasCompactSupport g := HasCompactSupport.intro hK fun η hη => by
    by_contra h
    exact hη (hs η h)
  exact hlc.continuous.integrable_of_hasCompactSupport hcs

end GlobalTheory.FinPl.Comm.DualCosets

namespace GlobalTheory.FinPl.Comm.DualCosets

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem dualInd_add (L : Submodule 𝒪[k] (n → k)) (η ξ : n → k) (hξ : InDual L ξ) :
    dualInd L (η + ξ) = dualInd L η := by
  unfold dualInd
  by_cases h : InDual L η
  · rw [if_pos (inDual_add h hξ), if_pos h]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    simpa using inDual_sub h' hξ

theorem dualInd_supp (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) (h : dualInd L η ≠ 0) :
    InDual L (q.1 • η) := by
  unfold dualInd at h
  by_cases hd : InDual L η
  · exact inDual_smul hd q.1
  · exact absurd (if_neg hd) h

theorem cosetInd_add (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : Module.Dual 𝓀[k] (Red L)) (η ξ : n → k)
    (hξ : InDual L ξ) : cosetInd q L f (η + ξ) = cosetInd q L f η := by
  unfold cosetInd
  have e : (∃ F : n → k, Lifts L F f ∧ InDual L (η + ξ - q.inv • F)) ↔
      ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F) := by
    constructor
    · rintro ⟨F, hF, hd⟩
      refine ⟨F, hF, ?_⟩
      have h := inDual_sub hd hξ
      rwa [show η + ξ - q.inv • F - ξ = η - q.inv • F by abel] at h
    · rintro ⟨F, hF, hd⟩
      refine ⟨F, hF, ?_⟩
      have h := inDual_add hd hξ
      rwa [show η - q.inv • F + ξ = η + ξ - q.inv • F by abel] at h
  by_cases h : ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F)
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]

theorem inDual_of_lifts {L : Submodule 𝒪[k] (n → k)} {F : n → k} {f : Module.Dual 𝓀[k] (Red L)} (h : Lifts L F f) :
    InDual L F := by
  intro y hy
  obtain ⟨s, hs, -⟩ := h ⟨y, hy⟩
  rw [← hs]
  exact s.2

theorem cosetInd_supp (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : Module.Dual 𝓀[k] (Red L)) (η : n → k)
    (h : cosetInd q L f η ≠ 0) : InDual L (q.1 • η) := by
  unfold cosetInd at h
  by_cases hc : ∃ F : n → k, Lifts L F f ∧ InDual L (η - q.inv • F)
  · obtain ⟨F, hF, hd⟩ := hc
    have hq1 : q.1 • q.inv = 1 := by
      rw [Algebra.smul_def, Unif.inv]
      exact mul_inv_cancel₀ q.ne_zero
    have hq : q.1 • (q.inv • F) = F := by
      rw [← smul_assoc, hq1, one_smul]
    have h3 : q.1 • η = q.1 • (η - q.inv • F) + F := by
      rw [smul_sub, hq, sub_add_cancel]
    rw [h3]
    exact inDual_add (inDual_smul hd q.1) (inDual_of_lifts hF)
  · exact absurd (if_neg hc) h

theorem inner_add (χ : AddChar k Circle) (hχ : HasConductor χ 1) {e : k} (he : e = 1 ∨ e = -1)
    [MeasurableSpace k] (μ : Measure (n → k)) (L : Submodule 𝒪[k] (n → k)) {a : (n → k) → ℂ}
    (ha : ∀ y, y ∉ L → a y = 0) (η ξ : n → k) (hξ : InDual L ξ) :
    ∫ y, a y * (χ (e * ((η + ξ) ⬝ᵥ y)) : ℂ) ∂μ = ∫ y, a y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ := by
  congr 1
  funext y
  by_cases hy : y ∈ L
  · have hm : e * (ξ ⬝ᵥ y) ∈ 𝒪[k] := by
      rcases he with rfl | rfl
      · simpa using hξ y hy
      · simpa using neg_mem (hξ y hy)
    have h1 : χ (e * (ξ ⬝ᵥ y)) = 1 := apply_int_eq_one hχ ⟨_, hm⟩
    rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, h1, mul_one]
  · rw [ha y hy, zero_mul, zero_mul]

end GlobalTheory.FinPl.Comm.DualCosets

namespace GlobalTheory.FinPl.Comm.DualCosets

theorem fpair_charInd_dualInd_add_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n), fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) := by
  intro k _ _ _ _ _ _ n _ _ q χ hχ e he μ _ Q
  have ha : ∀ y, y ∉ Q.lat → charInd (resChar χ hχ q) Q y = 0 := fun y hy => by
    simp [charInd, vecInd, hy]
  have hF : ∀ (L : Submodule 𝒪[k] (n → k)), L = Q.lat → ∀ η ξ, InDual L ξ →
      (∫ y, charInd (resChar χ hχ q) Q y * (χ (e * ((η + ξ) ⬝ᵥ y)) : ℂ) ∂μ) =
        ∫ y, charInd (resChar χ hχ q) Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ := by
    rintro L rfl η ξ hξ
    exact inner_add χ hχ he μ Q.lat ha η ξ hξ
  have hint1 : Integrable (fun η => (∫ y, charInd (resChar χ hχ q) Q y * (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) *
      dualInd Q.lat η) μ := by
    refine integrable_of_periodic μ q Q.lat (fun η ξ hξ => ?_) (fun η h => ?_)
    · simp only [hF Q.lat rfl η ξ hξ, dualInd_add Q.lat η ξ hξ]
    · exact dualInd_supp q Q.lat η (right_ne_zero_of_mul h)
  have hint2 : ∀ Q'' ∈ withLat Q.lat, Integrable (fun η => (∫ y, charInd (resChar χ hχ q) Q y *
      (χ (e * (η ⬝ᵥ y)) : ℂ) ∂μ) * cosetInd q Q''.lat Q''.red η) μ := by
    intro Q'' hQ''
    have hl : Q''.lat = Q.lat := mem_withLat.1 hQ''
    refine integrable_of_periodic μ q Q''.lat (fun η ξ hξ => ?_) (fun η h => ?_)
    · simp only [hF Q''.lat hl η ξ hξ, cosetInd_add q Q''.lat Q''.red η ξ hξ]
    · exact cosetInd_supp q Q''.lat Q''.red η (right_ne_zero_of_mul h)
  have key : fpair χ e μ (charInd (resChar χ hχ q) Q)
      (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) =
      fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) +
        ∑ Q'' ∈ withLat Q.lat, fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) := by
    simp only [fpair]
    rw [← integral_finset_sum _ hint2, ← integral_add hint1 (integrable_finset_sum _ hint2)]
    congr 1
    funext η
    simp only [Pi.add_apply, Finset.sum_apply, mul_add, Finset.mul_sum]
  obtain ⟨ε, hε⟩ : ∃ ε : 𝓀[k]ˣ, (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1) := by
    rcases he with h | h
    · exact ⟨1, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨-1, Or.inr ⟨h, rfl⟩⟩
  rw [key, GlobalTheory.T.fourierPairing_pairCharIndicator_dualLatticeIndicator_zero k n q χ hχ e he μ Q, zero_add, Finset.sum_eq_single (ε • Q)]
  · exact (GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hε μ Q (ε • Q) (Pair.dia_lat ε Q)).1 rfl
  · intro Q'' hQ'' hne
    exact (GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator k n q χ hχ e ε hε μ Q Q'' (mem_withLat.1 hQ'')).2 hne
  · intro h
    exact absurd (mem_withLat.2 (Pair.dia_lat ε Q)) h

end GlobalTheory.FinPl.Comm.DualCosets
