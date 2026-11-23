import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LatCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def MajV (X : Data E r) (_x : Frame X.Ψ r) : Type := ↥X.Ψ → Fin r → ℂ

variable (X : Data E r) (x : Frame X.Ψ r)

instance : AddCommGroup (MajV X x) := inferInstanceAs (AddCommGroup (↥X.Ψ → Fin r → ℂ))
instance : Module ℝ (MajV X x) := inferInstanceAs (Module ℝ (↥X.Ψ → Fin r → ℂ))
instance : FiniteDimensional ℝ (MajV X x) := inferInstanceAs (FiniteDimensional ℝ (↥X.Ψ → Fin r → ℂ))

def majIp (u w : MajV X x) : ℝ := ∑ τ, (X.Hf x τ (u τ) (w τ)).re

theorem Hf_add_left (τ : X.Ψ) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u + u') w = X.Hf x τ u w + X.Hf x τ u' w := by
  simp only [Data.Hf_eq_two_ppos, Data.ppos_add, hermC_add_left]
  ring

theorem Hf_smul_left (τ : X.Ψ) (c : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (c • u) w = c * X.Hf x τ u w := by
  simp only [Data.Hf_eq_two_ppos, Data.ppos_smul, hermC_smul_left]
  ring

theorem Hf_zero_left (τ : X.Ψ) (w : Fin r → ℂ) : X.Hf x τ 0 w = 0 := by
  have := Hf_smul_left X x τ 0 0 w
  rwa [zero_smul, zero_mul] at this

theorem Hf_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    starRingEnd ℂ (X.Hf x τ u w) = X.Hf x τ w u := by
  have h1 := X.hermC_ppos_left hx τ u w
  have h2 := X.hermC_ppos_left hx τ w u
  rw [Data.Hf_eq_two_ppos, Data.Hf_eq_two_ppos, h1, h2, map_sub, map_mul,
    hermC_conj τ.1 X.Gm_herm, hermC_conj τ.1 X.Gm_herm, map_ofNat]

theorem re_Hf_self_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ (X.Hf x τ v v).re := by
  by_cases h : v = 0
  · rw [h, Hf_zero_left, Complex.zero_re]
  · rw [Data.Hf_self X hx, Complex.ofReal_re]
    exact (X.maj_pos hx τ h).le

def majCore {x : Frame X.Ψ r} (hx : x ∈ X.dom) : InnerProductSpace.Core ℝ (MajV X x) where
  inner u w := majIp X x u w
  conj_inner_symm u w := by
    simp only [conj_trivial, majIp]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Hf_conj X hx τ (u τ) (w τ), Complex.conj_re]
  re_inner_nonneg u := by
    simp only [RCLike.re_to_real, majIp]
    exact Finset.sum_nonneg fun τ _ => re_Hf_self_nonneg X hx τ (u τ)
  add_left u v w := by
    simp only [majIp, ← Finset.sum_add_distrib, ← Complex.add_re]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact congrArg Complex.re (Hf_add_left X x τ (u τ) (v τ) (w τ))
  smul_left u w c := by
    simp only [conj_trivial, majIp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e : (c • u) τ = (c : ℂ) • u τ := (Complex.coe_smul c (u τ)).symm
    rw [e, Hf_smul_left, Complex.re_ofReal_mul]
  definite u h := by
    have h' : ∑ τ, (X.Hf x τ (u τ) (u τ)).re = 0 := h
    rw [Finset.sum_eq_zero_iff_of_nonneg fun τ _ => re_Hf_self_nonneg X hx τ (u τ)] at h'
    funext τ
    by_contra hne
    have h0 := h' τ (Finset.mem_univ _)
    rw [Data.Hf_self X hx, Complex.ofReal_re] at h0
    exact (X.maj_pos hx τ hne).ne' h0

open NumberField.ComplexEmbedding in

theorem card_cmType : X.Ψ.card = fdeg E := by
  classical
  have hc : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ conjugate τ ∉ X.Ψ := X.cmType
  have hcc : ∀ σ : E →+* ℂ, conjugate (conjugate σ) = σ := fun σ => star_star σ
  have himg : X.Ψ.image conjugate = Finset.univ.filter (· ∉ X.Ψ) := by
    ext σ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact (hc τ).1 hτ
    · intro hσ
      exact ⟨conjugate σ, by rw [hc, hcc]; exact hσ, hcc σ⟩
  have hinj : (X.Ψ.image conjugate).card = X.Ψ.card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa [hcc] using congrArg conjugate h)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (p := (· ∈ X.Ψ))
  have hf : Finset.univ.filter (· ∈ X.Ψ) = X.Ψ := by
    ext σ; simp
  rw [hf, ← himg, hinj, Finset.card_univ, Embeddings.card] at hsplit
  unfold fdeg
  omega

theorem finrank_majV : Module.finrank ℝ (MajV X x) = 2 * fdeg E * r := by
  change Module.finrank ℝ (↥X.Ψ → Fin r → ℂ) = _
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, card_cmType]
  ring

end GlobalTheory.LatCount

namespace GlobalTheory.LatCount

open scoped ENNReal

theorem encard_le (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r)
    (x : Frame X.Ψ r) (ε R : ℝ) (hx : x ∈ X.dom) (hε : 0 < ε) (hR : 0 ≤ R)
    (hsep : ∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) :
    ({v | v ∈ X.L' ∧ ∑ τ, X.maj x τ (Data.emb τ.1 v) ≤ R}.encard : ℝ≥0∞) ≤
      ENNReal.ofReal ((1 + 2 * Real.sqrt (R / ε)) ^ (2 * fdeg E * r)) := by
  classical
  set Q : (Fin r → E) → ℝ := fun v => ∑ τ, X.maj x τ (Data.emb τ.1 v) with hQ
  set S : Set (Fin r → E) := {v | v ∈ X.L' ∧ Q v ≤ R} with hS
  set B : ℝ := (1 + 2 * Real.sqrt (R / ε)) ^ (2 * fdeg E * r) with hB
  letI core : InnerProductSpace.Core ℝ (MajV X.toData x) := majCore X.toData hx
  letI : NormedAddCommGroup (MajV X.toData x) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  letI : InnerProductSpace ℝ (MajV X.toData x) := InnerProductSpace.ofCore core.toCore
  let g : (Fin r → E) → MajV X.toData x := fun v τ => Data.emb τ.1 v
  have hg : ∀ v, ‖g v‖ = Real.sqrt (Q v) := by
    intro v
    have h2 : ‖g v‖ ^ 2 = Q v := by
      rw [← real_inner_self_eq_norm_sq]
      change ∑ τ, (X.Hf x τ (g v τ) (g v τ)).re = _
      simp only [Data.Hf_self X.toData hx, Complex.ofReal_re, hQ, g]
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  have hsub : ∀ v w, g v - g w = g (v - w) := by
    intro v w
    funext τ a
    simp [g, Data.emb, map_sub]
    rfl
  have hfin : ∀ T : Finset (Fin r → E), (↑T : Set (Fin r → E)) ⊆ S → (T.card : ℝ) ≤ B := by
    intro T hT
    have h := Formalism.SA.P.card_le_of_separated T g (Real.sqrt ε) (Real.sqrt R) (Real.sqrt_pos.2 hε)
      (Real.sqrt_nonneg _) ?_ ?_
    · rw [finrank_majV, mul_div_assoc, ← Real.sqrt_div' R hε.le] at h
      rw [hB]
      exact h
    · intro v hv w hw hvw
      rw [hsub, hg]
      refine Real.sqrt_le_sqrt (hsep _ (X.L'.sub_mem (hT hv).1 (hT hw).1) (sub_ne_zero.2 hvw))
    · intro v hv
      rw [hg]
      exact Real.sqrt_le_sqrt (hT hv).2
  by_cases hSf : S.Finite
  · rw [hSf.encard_eq_coe_toFinset_card]
    have h := hfin hSf.toFinset (by simp)
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal h
  · exfalso
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hSf (⌈B⌉₊ + 1)
    have h := hfin T hT
    rw [hcard] at h
    push_cast at h
    linarith [Nat.le_ceil B]

end GlobalTheory.LatCount
