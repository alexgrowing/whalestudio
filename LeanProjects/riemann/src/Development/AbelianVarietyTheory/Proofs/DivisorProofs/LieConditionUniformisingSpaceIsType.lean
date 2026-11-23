import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionSumEmbeddingsEigenspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersJointEigenspaceDisjointBiSupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointEigenspaceAddConjEqMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspaceDimensionOfUniformizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LieType

theorem exists_ext (F : Type) [Field F] [NumberField F] (τ : 𝓞 F →+* ℂ) :
    ∃ τ' : F →+* ℂ, ∀ c : 𝓞 F, τ' (c : F) = τ c := by
  have hinj : Function.Injective τ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker τ) hne (by simpa [RingHom.mem_ker] using hx)
      (Algebra.IsIntegral.isIntegral x)
    apply hI
    rw [eq_bot_iff]
    intro n hn
    simp only [Ideal.mem_comap, RingHom.mem_ker, map_intCast] at hn
    simpa using hn
  refine ⟨IsFractionRing.lift hinj, fun c => ?_⟩
  exact IsFractionRing.lift_algebraMap hinj c

theorem root_cases {r z : ℂ} {tr nm : ℤ} (hd : tr ^ 2 - 4 * nm < 0) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (z ≠ r ↔ (starRingEnd ℂ) z = r) := by
  have hc : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hfac : ∀ x : ℂ, x ^ 2 - tr * x + nm = 0 → x = r ∨ x = tr - r := by
    intro x hx
    have : (x - r) * (x - (tr - r)) = 0 := by linear_combination hx - hr
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    have him : r.im = 0 := Complex.conj_eq_iff_im.1 h
    have hre := congrArg Complex.re hr
    have himr : r = (r.re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [himr] at hre
    simp [sq] at hre
    have : ((2 * r.re - tr) ^ 2 : ℝ) = (tr : ℝ) ^ 2 - 4 * nm := by linear_combination 4 * hre
    have h2 : ((tr : ℝ) ^ 2 - 4 * nm) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * r.re - tr)]
  have hcr : (starRingEnd ℂ) r = tr - r := (hfac _ hc).resolve_left hne
  constructor
  · intro h
    have : z = tr - r := (hfac z hz).resolve_left h
    rw [this, ← hcr]; simp
  · intro h hzr
    rw [hzr] at h
    exact hne h

theorem lie_isType : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → b.IsType σ ρ := by
  intro p _ D R _ b N σ ρ o h hL D' t Q e hU
  classical
  choose τ hτ using fun i => exists_ext D.F (σ.comp (b.t i))
  have hτ' : ∀ i (c : 𝓞 D.F), τ i (c : D.F) = σ (b.t i c) := fun i c => hτ i c
  obtain ⟨hrank, hcov⟩ := GlobalTheory.T.eigenspace_dimension_of_uniformization p D R b N σ ρ o h hL D' t Q e hU τ hτ'
  have hsum := GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul p D D' ρ Q hU.2.1
  set r := σ b.ρ with hrdef
  have hr : r ^ 2 - D.tr * r + D.nm = 0 := by
    have := congrArg σ b.ρ_root
    simpa using this
  have hω : (D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hτω : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ^ 2 - D.tr * τ' (D.ω : D.F) + D.nm = 0 := by
    intro τ'
    have := congrArg (fun x : 𝓞 D.F => τ' (x : D.F)) hω
    simpa using this
  have key : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) ≠ r ↔ ((starRingEnd ℂ).comp τ') (D.ω : D.F) = r :=
    fun τ' => root_cases D.disc_neg hr (hτω τ')

  have hinj : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker σ := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have h1 := hτ' i x
      have h2 := hτ' j x
      rw [hij] at h1
      simp [RingHom.mem_ker, ← h1, ← h2]
    rw [b.comax i j hne] at hle
    have : (1 : R) ∈ RingHom.ker σ := hle Submodule.mem_top
    simp [RingHom.mem_ker] at this
  have hτA : ∀ i, τ i (D.ω : D.F) = r := fun i => by rw [hτ', b.t_ω]
  set d : (D.F →+* ℂ) → ℕ := fun τ' => Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ') with hd

  have hzero : ∀ τ' : D.F →+* ℂ, τ' (D.ω : D.F) = r → τ' ∉ Finset.univ.image τ → d τ' = 0 := by
    intro τ' h1 h2
    have hbot : eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ' = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hu' : ρ (algebraMap (𝓞 D.F) D.O D.ω) *ᵥ u = r • u := by
        have := hu D.ω
        rw [h1] at this
        exact this
      have hmem := hcov u hu'
      have hle : (⨆ i, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) (τ i)) ≤ ⨆ τ'' ∈ Finset.univ.image τ, eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'' := by
        refine iSup_le fun i => ?_
        exact le_biSup (fun τ'' => eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ'') (Finset.mem_image_of_mem τ (Finset.mem_univ i))
      have := (GlobalTheory.T.ringOfIntegersJointEigenspace_disjoint_biSup D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) _ τ' h2).le_bot ⟨hu, hle hmem⟩
      simpa using this
    simp [hd, hbot]
  have hA : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ i, (D.m : ℂ) * σ (b.t i c) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hA' : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) =
      ∑ i, (D.m : ℂ) * (starRingEnd ℂ) (σ (b.t i c)) := by
    intro c
    rw [← Finset.sum_subset (s₁ := Finset.univ.image τ)]
    · rw [Finset.sum_image (fun i _ j _ h => hinj h)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hd, hrank i, hτ']
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      simp [hτA i]
    · intro x hx hx'
      have : x (D.ω : D.F) = r := by simpa using hx
      simp [hzero x this hx']
  have hconj : ∀ c : 𝓞 D.F, ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => ¬ τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * (starRingEnd ℂ) (τ' (c : D.F)) := by
    intro c
    refine Finset.sum_nbij' (fun τ' => (starRingEnd ℂ).comp τ') (fun τ' => (starRingEnd ℂ).comp τ') ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have := (key x).1 (by simpa using hx)
      simpa using this
    · intro x hx
      have hx' : x (D.ω : D.F) = r := by simpa using hx
      have : ¬ ((starRingEnd ℂ).comp x) (D.ω : D.F) = r := by
        exact fun h => (key x).2 h hx'
      simpa using this
    · intro x _; ext; simp
    · intro x _; ext; simp
    · intro x _; simp
  intro c
  have htr : (ρ (algebraMap (𝓞 D.F) D.O c)).trace = ∑ τ' : D.F →+* ℂ, (d τ' : ℂ) * τ' (c : D.F) := GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace D.F D.g (ρ.comp (algebraMap (𝓞 D.F) D.O)) c
  rw [htr, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r)]
  have hB : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (d τ' : ℂ) * τ' (c : D.F) =
      ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), ((D.m : ℂ) * D.n * τ' (c : D.F) -
        (d ((starRingEnd ℂ).comp τ') : ℂ) * τ' (c : D.F)) := by
    refine Finset.sum_congr rfl fun τ' _ => ?_
    have := hsum τ'
    have h' : (d τ' : ℂ) + d ((starRingEnd ℂ).comp τ') = D.m * D.n := by exact_mod_cast this
    linear_combination τ' (c : D.F) * h'
  rw [hB, Finset.sum_sub_distrib, hconj c, hA c, hA' c]
  have e1 : ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.m : ℂ) * D.n * τ' (c : D.F) =
      D.m * ∑ τ' ∈ Finset.univ.filter (fun τ' : D.F →+* ℂ => τ' (D.ω : D.F) ≠ r), (D.n : ℂ) * τ' (c : D.F) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]
  simp only [← Finset.mul_sum]
  ring

end GlobalTheory.UPel.HT.LieType
