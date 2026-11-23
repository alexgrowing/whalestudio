import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.PlaneBasis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

theorem splitLat_induction (τ : E →ₐ[F] v.adicCompletion F) (L : Submodule (𝓞 E) (Fin n → E))
    {p : (Fin n → v.adicCompletion F) → Prop}
    (h1 : ∀ a ∈ v.adicCompletionIntegers F, ∀ z ∈ L, p (a • fun r => τ (z r)))
    (h0 : p 0) (hadd : ∀ u w, p u → p w → p (u + w)) (hneg : ∀ u, p u → p (-u))
    {u : Fin n → v.adicCompletion F} (hu : u ∈ splitLat τ L) : p u := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => p (splitVec τ y)) (fun a ha z hz => ?_) ?_ ?_ ?_ hy
  · convert h1 a ha z hz using 1
    funext r; simp [splitVec]
  · convert h0; funext r; simp [splitVec]
  · intro y z hy hz; rw [splitVec_add]; exact hadd _ _ hy hz
  · intro y hy; convert hneg _ hy using 1; funext r; simp [splitVec]

theorem tau_mem_splitLat (τ : E →ₐ[F] v.adicCompletion F) {L : Submodule (𝓞 E) (Fin n → E)}
    {z : Fin n → E} (hz : z ∈ L) : (fun r => τ (z r)) ∈ splitLat τ L :=
  ⟨fun i => (1 : v.adicCompletion F) ⊗ₜ[F] z i, tmul_mem_latLoc (one_mem _) hz, funext fun r => by simp [splitVec]⟩

theorem smul_mem_int {S : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)}
    {a : v.adicCompletion F} (ha : a ∈ v.adicCompletionIntegers F) {u : Fin n → v.adicCompletion F}
    (hu : u ∈ S) : a • u ∈ S := S.smul_mem ⟨a, ha⟩ hu

theorem mem_colSpan {M : Matrix (Fin n) (Fin n) (v.adicCompletion F)} {u : Fin n → v.adicCompletion F} :
    u ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range fun i r => M r i) ↔
      ∃ w : Fin n → v.adicCompletion F, (∀ i, w i ∈ v.adicCompletionIntegers F) ∧ M *ᵥ w = u := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i => c i, fun i => (c i).2, ?_⟩
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun i => ⟨w i, hw i⟩, ?_⟩
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl

end GlobalTheory.PlaneBasis

noncomputable section

namespace GlobalTheory.PlaneBasis

def unskip (i₀ i₁ i : ℕ) : ℕ := if i < i₀ then i else if i < i₁ then i - 1 else i - 2

theorem skip_ne_left {i₀ i₁ : ℕ} (h : i₀ < i₁) (j : ℕ) : skip i₀ i₁ j ≠ i₀ := by
  unfold skip; split_ifs <;> omega

theorem skip_ne_right {i₀ i₁ : ℕ} (h : i₀ < i₁) (j : ℕ) : skip i₀ i₁ j ≠ i₁ := by
  unfold skip; split_ifs <;> omega

theorem skip_lt {i₀ i₁ n₁ : ℕ} {j : ℕ} (hj : j < n₁) : skip i₀ i₁ j < n₁ + 2 := by
  unfold skip; split_ifs <;> omega

theorem unskip_skip {i₀ i₁ : ℕ} (h : i₀ < i₁) (j : ℕ) : unskip i₀ i₁ (skip i₀ i₁ j) = j := by
  unfold skip unskip; split_ifs <;> omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

def colMat {n n₁ : ℕ} (τ : E →ₐ[F] v.adicCompletion F) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : Matrix (Fin n₁) (Fin n₁) (v.adicCompletion F)) (i₀ i₁ : ℕ) : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  fun r i => if i.1 = i₀ then τ (x r) else if i.1 = i₁ then τ (y r) else
    if h : unskip i₀ i₁ i.1 < n₁ then (ι.map τ * β₁) r ⟨_, h⟩ else 0

end GlobalTheory.PlaneBasis

namespace GlobalTheory.PlaneBasis

theorem exists_isSplitBasis_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] v.adicCompletion F) (n n₁ : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (v.adicCompletion F)) (i₀ i₁ : ℕ), n = n₁ + 2 → i₀ < i₁ → i₁ < n → L.IsLattice E →
    (∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y) →
    ((∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1) →
    ((∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1) →
    IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁ →
    ∃ β : GL (Fin n) (v.adicCompletion F), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  intro F E _ _ _ _ _ σ _ v τ n n₁ L x y ι β₁ i₀ i₁ hn h01 h1n hL hdec hx hy hβ₁
  subst hn
  have hO : ∀ a : v.adicCompletion F, a ∈ v.adicCompletionIntegers F ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  set M := colMat τ x y ι β₁.1 i₀ i₁ with hM
  set P := Submodule.span (v.adicCompletionIntegers F) (Set.range fun i r => M r i) with hP
  have hsmul : ∀ (c : E) (z : Fin (n₁ + 2) → E), (fun r => τ ((c • z) r)) = τ c • fun r => τ (z r) :=
    fun c z => funext fun r => by simp
  have hτmul : ∀ u : Fin n₁ → E, (fun r => τ ((ι *ᵥ u) r)) = ι.map τ *ᵥ fun r => τ (u r) :=
    fun u => funext fun r => by simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hc0 : (fun r => M r ⟨i₀, by omega⟩) = fun r => τ (x r) := funext fun r => by simp [hM, colMat]
  have hc1 : (fun r => M r ⟨i₁, h1n⟩) = fun r => τ (y r) := funext fun r => by
    simp [hM, colMat, h01.ne']
  have hcj : ∀ j : Fin n₁, (fun r => M r ⟨skip i₀ i₁ j, skip_lt j.2⟩) = fun r => (ι.map τ * β₁.1) r j :=
    fun j => funext fun r => by
      simp [hM, colMat, skip_ne_left h01, skip_ne_right h01, unskip_skip h01, j.2]
  have hPx : (fun r => τ (x r)) ∈ P := hc0 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPy : (fun r => τ (y r)) ∈ P := hc1 ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPcol : ∀ j : Fin n₁, (fun r => (ι.map τ * β₁.1) r j) ∈ P := fun j =>
    hcj j ▸ Submodule.subset_span ⟨_, rfl⟩
  have hPimg : ∀ w₁ : Fin n₁ → v.adicCompletion F, (∀ j, w₁ j ∈ v.adicCompletionIntegers F) →
      (ι.map τ * β₁.1) *ᵥ w₁ ∈ P := by
    intro w₁ hw
    have : (ι.map τ * β₁.1) *ᵥ w₁ = ∑ j, w₁ j • (fun r => (ι.map τ * β₁.1) r j) := by
      funext r; simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    exact sum_mem fun j _ => smul_mem_int (hw j) (hPcol j)
  have hSub : ∀ z ∈ L, (fun r => τ (z r)) ∈ P := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hdec z hz
    have hu' : u ∈ L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) := hu
    have h1 := hβ₁.mem_iff.1 (tau_mem_splitLat τ hu')
    have e : (fun r => τ (u r)) = β₁.1 *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have : (fun r => τ ((s • x + ι *ᵥ u + t • y) r)) = τ s • (fun r => τ (x r)) +
        (ι.map τ * β₁.1) *ᵥ ((β₁⁻¹).1 *ᵥ fun r => τ (u r)) + τ t • fun r => τ (y r) := by
      rw [← Matrix.mulVec_mulVec, ← e, ← hτmul, ← hsmul, ← hsmul]; funext r; simp
    rw [this]
    exact add_mem (add_mem (smul_mem_int ((hO _).2 (hx.1 s hs)) hPx) (hPimg _ h1))
      (smul_mem_int ((hO _).2 (hy.1 t ht)) hPy)
  have hImg : ∀ u ∈ splitLat τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))),
      ι.map τ *ᵥ u ∈ splitLat τ L := fun u hu =>
    splitLat_induction τ _ (p := fun u => ι.map τ *ᵥ u ∈ splitLat τ L)
      (fun a ha z hz => by
        rw [Matrix.mulVec_smul, ← hτmul]; exact smul_mem_int ha (tau_mem_splitLat τ hz))
      (by rw [Matrix.mulVec_zero]; exact zero_mem _)
      (fun u w hu hw => by rw [Matrix.mulVec_add]; exact add_mem hu hw)
      (fun u hu => by rw [Matrix.mulVec_neg]; exact neg_mem hu) hu
  have hunit : ∀ z : Fin (n₁ + 2) → E, ((∀ c : E, c • z ∈ L → Valued.v (τ c) ≤ 1) ∧
      ∃ c : E, c • z ∈ L ∧ Valued.v (τ c) = 1) → (fun r => τ (z r)) ∈ splitLat τ L := by
    rintro z ⟨-, c, hc, hv⟩
    have hne : τ c ≠ 0 := by intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have h2 := tau_mem_splitLat τ hc
    rw [hsmul] at h2
    have hinv : (τ c)⁻¹ ∈ v.adicCompletionIntegers F := (hO _).2 (by rw [map_inv₀, hv, inv_one])
    have := smul_mem_int hinv h2
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hColSL : ∀ i, (fun r => M r i) ∈ splitLat τ L := by
    intro i
    by_cases h0 : i.1 = i₀
    · convert hunit x hx using 1; funext r; simp [hM, colMat, h0]
    by_cases h1 : i.1 = i₁
    · convert hunit y hy using 1; funext r; simp only [hM, colMat, if_neg h0, if_pos h1]
    by_cases h2 : unskip i₀ i₁ i.1 < n₁
    · have : (fun r => M r i) = ι.map τ *ᵥ (β₁.1 *ᵥ Pi.single ⟨_, h2⟩ 1) := by
        funext r
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
        simp only [hM, colMat, if_neg h0, if_neg h1, dif_pos h2, Matrix.transpose_apply]
        rfl
      rw [this]
      refine hImg _ ((hβ₁ _).1 fun k => ?_)
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    · convert zero_mem (splitLat τ L) using 1; funext r; simp [hM, colMat, h0, h1, h2]
  have hPle : P ≤ splitLat τ L := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hColSL i)
  have hSLle : ∀ u ∈ splitLat τ L, u ∈ P := fun u hu =>
    splitLat_induction τ L (p := (· ∈ P)) (fun a ha z hz => smul_mem_int ha (hSub z hz)) (zero_mem _)
      (fun _ _ => add_mem) (fun _ => neg_mem) hu
  have hR : ∀ z : Fin (n₁ + 2) → E, (fun r => τ (z r)) ∈ LinearMap.range M.mulVecLin := by
    intro z
    have hz : z ∈ Submodule.span E (L : Set (Fin (n₁ + 2) → E)) := by rw [hL.span_eq_top]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, -, hw⟩ := mem_colSpan.1 (hSub z hz)
      exact ⟨w, hw⟩
    | zero => convert zero_mem (LinearMap.range M.mulVecLin) using 1; funext r; simp
    | add a b _ _ ha hb =>
      convert add_mem ha hb using 1; funext r; simp
    | smul c a _ ha =>
      rw [hsmul]; exact Submodule.smul_mem _ _ ha
  have hsurj : Function.Surjective M.mulVec := by
    intro u
    have : u ∈ LinearMap.range M.mulVecLin := by
      rw [← Finset.univ_sum_single u]
      refine sum_mem fun k _ => ?_
      have e : Pi.single k (u k) = u k • fun r => τ ((Pi.single k (1 : E) : Fin (n₁ + 2) → E) r) := by
        funext r
        by_cases h : r = k
        · subst h; simp
        · simp [h]
      rw [e]
      exact Submodule.smul_mem _ _ (hR _)
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw⟩
  have hU : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  refine ⟨hU.unit, fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h]
  · intro h r; rw [IsUnit.unit_spec]; simp [hM, colMat, h, h01.ne']
  · intro j h r
    rw [IsUnit.unit_spec]
    have : i = ⟨skip i₀ i₁ j, skip_lt j.2⟩ := Fin.ext h
    subst this
    exact congrFun (hcj j) r
  · intro u
    rw [IsUnit.unit_spec]
    constructor
    · intro hu; exact hPle (mem_colSpan.2 ⟨u, hu, rfl⟩)
    · intro hu
      obtain ⟨w, hw, e⟩ := mem_colSpan.1 (hSLle _ hu)
      have := Matrix.mulVec_injective_iff_isUnit.2 hU e
      rw [← this]; exact hw

end GlobalTheory.PlaneBasis
