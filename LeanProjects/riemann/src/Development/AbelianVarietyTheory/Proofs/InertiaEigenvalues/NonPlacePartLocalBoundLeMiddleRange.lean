import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.BBSize

variable {D : D7}

theorem sum_locDeg_le (i : D.nd.Loc) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hS : ∀ v ∈ S, v ∈ placesOver D.host.E (D.nd.l i)) :
    ∑ w ∈ S, (locDeg D.host.E w : ℝ) ≤ 2 * D.R.f := by
  have hl := (D.nd.lPrime i).out
  refine le_trans ?_ (TwistedPlaces.sum_nLam_le D hl)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    exact (Set.Finite.mem_toFinset _).2 (hS v hv)
  · intro v _ _
    positivity

theorem card_le_sum_locDeg (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    (S.card : ℝ) ≤ ∑ w ∈ S, (locDeg D.host.E w : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro v _
  exact_mod_cast TwistedPlaces.nLam_pos D v

theorem vdel_nonneg (i : D.nd.Loc) : (0 : ℝ) ≤ (D.nd.vdel i : ℝ) := by
  have : (0 : ℚ) ≤ D.nd.vdel i := by
    unfold NData.vdel
    positivity
  exact_mod_cast this

theorem vdel_le_two_t (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) : (D.nd.vdel i : ℝ) ≤ 2 * D.R.t := by
  have := D.nd.lPrime i
  have h := LargeLevelLemmas.vdel_le i
  have hs : D.nd.s0 i = 1 := UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i h2
  have hv : (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) ≤ D.R.t := by
    exact_mod_cast padicValNat_factorial_le (D.nd.l i) D.R.t
  rw [hs] at h
  have : D.nd.vdel i ≤ 2 * (D.R.t : ℚ) := by
    push_cast at h
    linarith
  exact_mod_cast this

theorem blk_arith {f t n V large₂ c A k b v h : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 6 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hb0 : 0 ≤ b)
    (hb : b ≤ c * t * n * V * large₂) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) (hh : h ≤ c * t) :
    t * (A * b) + 4 * V * (k + 1) * v + t * k * h ≤ 32 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : t * (A * b) ≤ 6 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * (A * b) ≤ t * ((6 * f) * (c * t * n * V * large₂)) := by gcongr
      _ = _ := by ring
  have h2 : 4 * V * (k + 1) * v ≤ 24 * (c * f * n * t ^ 2 * V * large₂) := by
    calc 4 * V * (k + 1) * v ≤ 4 * V * (3 * f) * (2 * t) := by gcongr; linarith
      _ = 24 * (1 * f * 1 * (t * 1) * V * 1) := by ring
      _ ≤ 24 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : t * k * h ≤ 2 * (c * f * n * t ^ 2 * V * large₂) := by
    calc t * k * h ≤ t * k * (c * t) := by gcongr
      _ ≤ t * (2 * f) * (c * t) := by gcongr
      _ = 2 * (c * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  linarith

theorem col_arith {f t n V large₂ c A k m r v : ℝ} (hf : 1 ≤ f) (ht : 1 ≤ t) (hn : 1 ≤ n) (hV : 1 ≤ V)
    (hL : 1 ≤ large₂) (hc : 1 ≤ c) (hA : A ≤ 2 * f) (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hm0 : 0 ≤ m) (hm : m ≤ t)
    (hr0 : 0 ≤ r) (hr : r ≤ t) (hv0 : 0 ≤ v) (hv : v ≤ 2 * t) :
    A * (m * v) + k * (2 * v + 2 * (c * r * n * V * large₂)) ≤ 16 * (c * f * n * t ^ 2 * V * large₂) := by
  have h1 : A * (m * v) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc A * (m * v) ≤ (2 * f) * (t * (2 * t)) := by gcongr
      _ = 4 * (1 * f * 1 * t ^ 2 * 1 * 1) := by ring
      _ ≤ _ := by gcongr
  have h2 : k * (2 * v) ≤ 8 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * v) ≤ (2 * f) * (2 * (2 * t)) := by gcongr
      _ = 8 * (1 * f * 1 * (t * 1) * 1 * 1) := by ring
      _ ≤ 8 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  have h3 : k * (2 * (c * r * n * V * large₂)) ≤ 4 * (c * f * n * t ^ 2 * V * large₂) := by
    calc k * (2 * (c * r * n * V * large₂)) ≤ (2 * f) * (2 * (c * t * n * V * large₂)) := by gcongr
      _ = 4 * (c * f * n * (t * 1) * V * large₂) := by ring
      _ ≤ 4 * (c * f * n * (t * t) * V * large₂) := by gcongr
      _ = _ := by ring
  rw [mul_add]
  linarith

theorem f_ge_one (D : D7) : (1 : ℝ) ≤ D.R.f := (TwistedPlaces.m_ge_one D).trans (TwistedPlaces.m_le_f D)

theorem nV_ge_one (D : D7) : (1 : ℝ) ≤ D.R.nV := by
  have := TwistedPlaces.t_ge_one D
  have h0 : (0 : ℝ) ≤ D.R.r := by positivity
  unfold Ranks.nV
  push_cast
  linarith

theorem blockBoundDeclaration_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small) (dc : TruncatedSeriesCountingIdentities.Decl D i) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t) :
    (KillingConditions.localErrorBoundDecomposition i dc cB : ℝ) ≤ 32 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hrow := sum_locDeg_le i dc.row (fun v hv => (dc.cover v).1 (Or.inl hv))
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hr := card_le_sum_locDeg dc.row
  have hk := card_le_sum_locDeg dc.col
  have hA : ∑ w ∈ dc.row, ((locDeg D.host.E w : ℝ) + 2) ≤ 6 * D.R.f := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  have := blk_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hA
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg cB) hB (vdel_nonneg i)
    (vdel_le_two_t i h2) hh
  unfold KillingConditions.localErrorBoundDecomposition
  push_cast
  rw [← Finset.sum_mul]
  exact this

theorem blockBoundAtZero_le_middleRange (L : SizeData₂ D) (i : D.nd.Loc) (h2 : D.nd.l i ∉ D.host.small)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) {c : ℝ}
    (hc : 1 ≤ c) (hB : (cB : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * TwistedPlaces.large₂ L)
    (hh : (h0 D.nd i dc.col : ℝ) ≤ c * D.R.t)
    (hu : ∀ u ∈ dc.col, (c0 u : ℝ) ≤ c * D.R.n * D.R.nV * TwistedPlaces.large₂ L ∧
      (Br.h0W i u ρ π : ℝ) ≤ c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L) :
    (localErrorBoundPlaces i ρ π dc c0 cB : ℝ) ≤ 48 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L) := by
  have hb := blockBoundDeclaration_le_middleRange L i h2 dc cB hc hB hh
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hk := card_le_sum_locDeg dc.col
  have hrt : (D.R.r : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.t_ge D]
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by linarith [TwistedPlaces.m_le_k D, TwistedPlaces.k_le_r D]
  have hc' := col_arith (f_ge_one D) (TwistedPlaces.t_ge_one D) (TwistedPlaces.n_ge_one D) (nV_ge_one D) (TwistedPlaces.L_ge_one L) hc hcol
    (Nat.cast_nonneg dc.col.card) (hk.trans hcol) (Nat.cast_nonneg D.R.m) hmt (Nat.cast_nonneg D.R.r) hrt
    (vdel_nonneg i) (vdel_le_two_t i h2)
  have hs : ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * (D.R.m : ℝ) * (D.nd.vdel i : ℝ) + 2 * (D.nd.vdel i : ℝ) +
        (Br.h0W i u ρ π : ℝ) + (D.R.r : ℝ) * (c0 u : ℝ)) ≤
      ∑ u ∈ dc.col, ((locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ)) +
        (2 * (D.nd.vdel i : ℝ) + 2 * (c * D.R.r * D.R.n * D.R.nV * TwistedPlaces.large₂ L))) := by
    apply Finset.sum_le_sum
    intro u hu'
    obtain ⟨h1, h3⟩ := hu u hu'
    have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) D.R.r)
    linarith
  rw [Finset.sum_add_distrib (f := fun u => (locDeg D.host.E u : ℝ) * ((D.R.m : ℝ) * (D.nd.vdel i : ℝ))),
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at hs
  unfold KillingConditions.localErrorBoundDecomposition at hb
  unfold localErrorBoundPlaces
  push_cast at hb ⊢
  linarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (c : ℝ), 1 ≤ c → KillingConditions.DataAD L HW X R → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X c → KillingConditions.BBLe L X (60 * c) := by
  intro D L _ HW X R c hc hD hJ i hi hg hR π hπ
  obtain ⟨hB, hh, hS⟩ := hJ i hi hg hR
  have h2 : D.nd.l i ∉ D.host.small := fun h => hR.1 (Or.inl h)
  have hq : D.nd.l i ≠ D.host.q := fun h => hR.2.1 (Or.inl h)
  have hd : D.nd.l i ≠ D.host.d := fun h => hR.2.1 (Or.inr h)
  have hL := TwistedPlaces.L_ge_one L
  have hM0 : 0 ≤ c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L := by
    have : 0 ≤ c := by linarith
    have : 0 ≤ TwistedPlaces.large₂ L := by linarith
    positivity
  have hM := le_mul_of_one_le_right hM0 hL
  have hE : 60 * c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * (TwistedPlaces.large₂ L) ^ 2 =
      60 * (c * D.R.f * D.R.n * (D.R.t : ℝ) ^ 2 * D.R.nV * TwistedPlaces.large₂ L * TwistedPlaces.large₂ L) := by ring
  rw [hE]
  rcases TwistedPlaces.split_or_inert D h2 hq hd with hs | hin
  · rw [hD.error_bound_split_eq i hs π]
    have := blockBoundAtZero_le_middleRange L i h2 (X.ρ i) π (X.dc i) (X.c0 i) (X.cB i) hc hB hh
      (fun u hu => ⟨(hS hs u hu).1, (hS hs u hu).2 π hπ⟩)
    linarith
  · rw [hD.error_bound_inert_eq i hin π]
    have := blockBoundDeclaration_le_middleRange L i h2 (X.dc i) (X.cB i) hc hB hh
    linarith

end GlobalTheory.NLink.BBSize

end
