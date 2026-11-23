import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.StdPairSB

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) (p : 𝒪[k])
    (hAB : ∀ i j, valuation k (B i j - A i j) ≤ valuation k (p : k)) :
    valuation k (B.det - A.det) ≤ valuation k (p : k) := by
  let A' : Matrix (Fin n) (Fin n) 𝒪[k] := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin n) (Fin n) 𝒪[k] := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have hA' : A = (algebraMap 𝒪[k] k).mapMatrix A' := by ext i j; rfl
  have hB' : B = (algebraMap 𝒪[k] k).mapMatrix B' := by ext i j; rfl
  have hdvd : ∀ x y : 𝒪[k], valuation k (x : k) ≤ valuation k (y : k) ↔ y ∣ x :=
    fun x y => Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k))
  have key : (Ideal.Quotient.mk (Ideal.span {p})).mapMatrix B' =
      (Ideal.Quotient.mk (Ideal.span {p})).mapMatrix A' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, ← hdvd]
    simpa [A', B'] using hAB i j
  have h2 : B'.det - A'.det ∈ Ideal.span {p} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, key]
  rw [Ideal.mem_span_singleton, ← hdvd] at h2
  rw [hA', hB', ← RingHom.map_det, ← RingHom.map_det]
  exact h2

open Classical in

def gfun (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) {m r : ℕ} (A : Matrix (Fin m) (Fin m) k)
    (B : Matrix (Fin m) (Fin r) k) : ℂ :=
  if h : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) then
    (((ν (Units.mk0 _ h.1))⁻¹ : ℂˣ) : ℂ) else 0

theorem prop_of_ne {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c m r : ℕ} {A : Matrix (Fin m) (Fin m) k}
    {B : Matrix (Fin m) (Fin r) k} (h : gfun ν ϖ c A B ≠ 0) :
    A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
  by_contra hP
  exact h (by unfold gfun; rw [dif_neg hP])

theorem stable {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ c ν) {m r : ℕ} {A A' : Matrix (Fin m) (Fin m) k}
    {B B' : Matrix (Fin m) (Fin r) k}
    (hP : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c))
    (hA : ∀ i j, valuation k (A' i j - A i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k))
    (hB : ∀ i j, valuation k (B' i j - B i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k)) :
    (A'.det ≠ 0 ∧ IsGLO A' ∧ ∀ i j, B' i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ∧
      gfun ν ϖ c A' B' = gfun ν ϖ c A B := by
  obtain ⟨hd0, ⟨hAint, hAdet⟩, hBc⟩ := hP
  have hu : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  have hγc : valuation k ((ϖ ^ max c 1 : kˣ) : k) ≤ valuation k ((ϖ ^ c : kˣ) : k) := by
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_pow_right_of_le_one' hu.le (le_max_left _ _)
  have hγ1 : valuation k ((ϖ ^ max c 1 : kˣ) : k) < 1 := by
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_one₀ zero_le' hu (by omega)
  have hA'int : ∀ i j, A' i j ∈ 𝒪[k] := by
    intro i j
    have h1 : valuation k (A i j) ≤ 1 := hAint i j
    rw [Valuation.mem_integer_iff, ← sub_add_cancel (A' i j) (A i j)]
    exact Valuation.map_add_le _ ((hA i j).trans hγ1.le) h1
  have hB'c : ∀ i j, B' i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
    intro i j
    rw [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, ← sub_add_cancel (B' i j) (B i j)]
    exact Valuation.map_add_le _ ((hB i j).trans hγc) (hBc i j)
  have hdiff := det_sub_le A A' hAint hA'int ⟨((ϖ ^ max c 1 : kˣ) : k), hγ1.le⟩ hA
  have hdiff1 : valuation k (A'.det - A.det) < valuation k A.det := by
    rw [hAdet]; exact lt_of_le_of_lt hdiff hγ1
  have hdet' : valuation k A'.det = 1 := by
    rw [← sub_add_cancel A'.det A.det, Valuation.map_add_eq_of_lt_right _ hdiff1, hAdet]
  have hd0' : A'.det ≠ 0 := by
    intro h; rw [h, map_zero] at hdet'; exact zero_ne_one hdet'
  refine ⟨⟨hd0', ⟨hA'int, hdet'⟩, hB'c⟩, ?_⟩
  unfold gfun
  rw [dif_pos ⟨hd0', ⟨hA'int, hdet'⟩, hB'c⟩, dif_pos ⟨hd0, ⟨hAint, hAdet⟩, hBc⟩]
  set u := Units.mk0 A.det hd0
  set u' := Units.mk0 A'.det hd0'
  have hr : ν (u⁻¹ * u') = 1 := by
    apply hν
    refine ⟨?_, ?_⟩
    · simp [u, u', hAdet, hdet']
    · have : ((u⁻¹ * u' : kˣ) : k) - 1 = A.det⁻¹ * (A'.det - A.det) := by
        simp only [u, u', Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        rw [mul_sub, inv_mul_cancel₀ hd0]
      rw [this, map_mul, map_inv₀, hAdet, inv_one, one_mul]
      exact hdiff.trans hγc
  have hu' : u' = u * (u⁻¹ * u') := by group
  rw [hu', map_mul, hr, mul_one]

theorem isLocallyConstant_gfun {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ c ν) (m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨A, B⟩
  have hnh : ∀ x : k, ∀ᶠ y in 𝓝 x, valuation k (y - x) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k) := by
    intro x
    have ht : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id.sub_const x : Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 (x - x)))
    exact ht (GlobalTheory.SplitWeil.cball_mem_nhds (ϖ ^ max c 1))
  have hev : ∀ᶠ q in 𝓝 (A, B),
      (∀ i j, valuation k ((q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k).1 i j - A i j) ≤
        valuation k ((ϖ ^ max c 1 : kˣ) : k)) ∧
      ∀ i j, valuation k (q.2 i j - B i j) ≤ valuation k ((ϖ ^ max c 1 : kˣ) : k) := by
    refine Filter.Eventually.and ?_ ?_
    · refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact ((continuous_fst.matrix_elem i j).tendsto (A, B)).eventually (hnh (A i j))
    · refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact ((continuous_snd.matrix_elem i j).tendsto (A, B)).eventually (hnh (B i j))
  filter_upwards [hev] with q hq
  by_cases hP : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · exact (stable hϖ hν hP hq.1 hq.2).2
  · have h0 : gfun ν ϖ c A B = 0 := by unfold gfun; rw [dif_neg hP]
    show gfun ν ϖ c q.1 q.2 = gfun ν ϖ c A B
    rw [h0]
    by_contra hne
    refine hP (stable hϖ hν (prop_of_ne hne) (fun i j => ?_) (fun i j => ?_)).1
    · rw [Valuation.map_sub_swap]; exact hq.1 i j
    · rw [Valuation.map_sub_swap]; exact hq.2 i j

theorem integral_of_ne {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {m r : ℕ}
    {A : Matrix (Fin m) (Fin m) k} {B : Matrix (Fin m) (Fin r) k} (h : gfun ν ϖ c A B ≠ 0) :
    (∀ i j, A i j ∈ 𝒪[k]) ∧ ∀ i j, B i j ∈ 𝒪[k] := by
  obtain ⟨-, ⟨hA, -⟩, hB⟩ := prop_of_ne h
  have hu : valuation k (ϖ : k) < 1 := by rw [hϖ]; exact uniformizer_lt_one
  refine ⟨hA, fun i j => ?_⟩
  rw [Valuation.mem_integer_iff]
  refine (show valuation k (B i j) ≤ valuation k ((ϖ ^ c : kˣ) : k) from hB i j).trans ?_
  simp only [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_one₀ zero_le' hu.le

end Local

end GlobalTheory.StdPairSB

theorem GlobalTheory.StdPairSB.stdPair_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ)
    (c a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SplitFlip.CondLE ϖ c ν →
      stdA ν ϖ c a a' ∈ SB (Matrix (Fin a) (Fin (a + a')) k) ∧ stdB ν ϖ c a a' ∈ SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ c a a' hϖ hν
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSB.isLocallyConstant_gfun hϖ hν a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSB.isLocallyConstant_gfun hϖ hν a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
