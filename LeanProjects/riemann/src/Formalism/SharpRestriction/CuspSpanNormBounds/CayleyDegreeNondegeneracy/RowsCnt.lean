import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDef
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_skeleton {P κ : Type*} [DecidableEq κ] (S : Finset P) (w a₁ a₂ : P → ℝ) (c₁ c₂ : P → κ) (M : ℝ) (N : κ → κ → ℝ)
    (α₁ α₂ : κ → ℝ) (hw : ∀ p ∈ S, 0 ≤ w p) (h1 : ∀ p ∈ S, 0 ≤ a₁ p) (h2 : ∀ p ∈ S, 0 ≤ a₂ p)
    (hα₁ : ∀ p ∈ S, a₁ p ≤ α₁ (c₁ p)) (hα₂ : ∀ p ∈ S, a₂ p ≤ α₂ (c₂ p))
    (hN : ∀ x y, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p ≤ M * N x y) :
    ∑ p ∈ S, w p * (a₁ p * a₂ p) ≤ M * ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, N x y * (α₁ x * α₂ y) := by
  have hα₁0 : ∀ x ∈ S.image c₁, 0 ≤ α₁ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (h1 p hp).trans (hα₁ p hp)
  have hα₂0 : ∀ y ∈ S.image c₂, 0 ≤ α₂ y := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    exact (h2 p hp).trans (hα₂ p hp)
  have hmaps : ∀ p ∈ S, (fun p => (c₁ p, c₂ p)) p ∈ S.image c₁ ×ˢ S.image c₂ := fun p hp =>
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  calc ∑ p ∈ S, w p * (a₁ p * a₂ p)
      ≤ ∑ p ∈ S, w p * (α₁ (c₁ p) * α₂ (c₂ p)) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (hw p hp)
        exact mul_le_mul (hα₁ p hp) (hα₂ p hp) (h2 p hp) ((h1 p hp).trans (hα₁ p hp))
    _ = ∑ q ∈ S.image c₁ ×ˢ S.image c₂,
          ∑ p ∈ S.filter (fun p => (c₁ p, c₂ p) = q), w p * (α₁ (c₁ p) * α₂ (c₂ p)) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂,
          ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p * (α₁ x * α₂ y) := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        have hfe : S.filter (fun p => (c₁ p, c₂ p) = (x, y)) = S.filter (fun p => c₁ p = x ∧ c₂ p = y) := by
          ext p
          simp only [Finset.mem_filter, Prod.mk.injEq]
        rw [hfe]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        obtain ⟨-, hx, hy⟩ := Finset.mem_filter.mp hp
        rw [hx, hy]
    _ = ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂,
          (∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), w p) * (α₁ x * α₂ y) := by
        simp only [Finset.sum_mul]
    _ ≤ ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, (M * N x y) * (α₁ x * α₂ y) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        exact mul_le_mul_of_nonneg_right (hN x y) (mul_nonneg (hα₁0 x hx) (hα₂0 y hy))
    _ = M * ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, N x y * (α₁ x * α₂ y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        ring

section Count

variable {D : D7} {large₂ : SizeData₂ D} (X : TermTie D) {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def pairToTriple (p : D.s.Pair u u') : Trip D ((Tu D u' : ℕ) : D.host.E) :=
  (X.fl' (D.s.pfst p), X.fl' (D.s.psnd p), X.beta p)

variable {X}

theorem rows_isTermF (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0) : IsTermF D (X.abelian₂ t) (lf D Y.F0) (X.fl' t) := by
  have hfl := Y.fl_eq t
  unfold IsTermF IsTerm
  refine ⟨⟨X.lift' t, ?_, ?_⟩, Y.frame_ok t⟩
  · rw [← hfl]
    exact X.adm t
  · rw [← hfl]
    intro h0
    apply hG
    have h := X.10 t
    rw [h0] at h
    exact (algebraMap _ _).injective (h.trans (map_zero _).symm)

def wordSublatticeTripleBound (D : D7) (large₂ : SizeData₂ D) (u : D.what₂.Word) (C : ℝ) (Z' Z'' : GramM D) (s : ℕ) (De : ℝ) : ℝ :=
  (De / NT D u) ^ D.R.k * XiS D u (HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'') C s *
    (HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'') ^ (C * ((s : ℝ) + D.R.m) * D.R.m + C * cF D.R.f) *
    (C * s * D.R.f) ^ (6 * s * D.R.f)

theorem rows_fibre_le (Z' Z'' : GramM D) (s : ℕ) (De : ℝ) (Λ : LatV D) (S : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S, X.abelian₂ (D.s.pfst p) = Λ ∧ D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧
      ZEquiv (termGramMatrix X (D.s.pfst p)) Z' ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) Z'' ∧ D.s.s0 p = s ∧ pairDeterminant X p ≤ De) :
    ((S.card : ℕ) : ℕ∞) ≤ cntPairs D Λ ((Tu D u' : ℕ) : D.host.E) (lf D Y.F0) Z' Z'' s De := by
  have hmem : ∀ p ∈ S,
      pairToTriple X p ∈ PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D Y.F0) Z' Z'' s De := by
    intro p hp
    obtain ⟨hΛ, hG1, hG2, hZ1, hZ2, hs, hDe⟩ := hS p hp
    have hΛ2 : X.abelian₂ (D.s.psnd p) = Λ := (X.16 p).symm.trans hΛ
    have hfl : X.fl (D.s.pfst p) = lf D Y.F0 := Y.fl_eq _
    have hfl2 : X.fl (D.s.psnd p) = lf D Y.F0 := Y.fl_eq _
    simp only [PairSet, pairToTriple, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hΛ]
      exact rows_isTermF Y _ hG1
    · rw [← hΛ2]
      exact rows_isTermF Y _ hG2
    · rw [← hΛ, ← hfl]
      exact X.19 p
    · rw [← hfl]
      exact hZ1
    · rw [← hfl2]
      exact hZ2
    · rw [← hΛ, ← hfl, ← X.20 p]
      exact hs
    · rw [← hΛ, ← hfl]
      exact hDe
  have hinj : ∀ i j : S, PEqv D Λ (lf D Y.F0) (pairToTriple X i.1) (pairToTriple X j.1) → i = j := by
    intro i j h
    apply Subtype.ext
    refine Y.pair_inj _ _ ?_ ?_
    · rw [(hS i.1 i.2).1, (hS j.1 j.2).1]
    · rw [(hS i.1 i.2).1]
      exact h
  have key := Formalism.MainNotions.S.Lem.Cnt.card_le_cntCl (PairSet D Λ ((Tu D u' : ℕ) : D.host.E) (lf D Y.F0) Z' Z'' s De)
    (PEqv D Λ (lf D Y.F0)) (fun a _ => Formalism.MainNotions.S.Lem.Cnt.PEqv_refl D Λ _ a) (fun i : S => pairToTriple X i.1)
    (fun i => hmem i.1 i.2) hinj
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe] at key
  exact key

theorem rows_mean_real {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (LatV D)) (N : LatV D → ℕ∞) (B : ℝ)
    (hB : 0 ≤ B) (hM : MeanLe D F0 what₂ N B) (n : LatV D → ℕ) (hn : ∀ Λ ∈ what₂, (n Λ : ℕ∞) ≤ N Λ) :
    ∑ Λ ∈ what₂, wRow D F0 Λ * n Λ ≤ massRows D F0 what₂ * B := by
  have hw : ∀ Λ, 0 ≤ wRow D F0 Λ := fun Λ => by unfold wRow; positivity
  have hmass : 0 ≤ massRows D F0 what₂ := Finset.sum_nonneg (fun Λ _ => hw Λ)
  unfold MeanLe at hM
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hmass hB)]
  calc ENNReal.ofReal (∑ Λ ∈ what₂, wRow D F0 Λ * (n Λ : ℝ))
      = ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * ((n Λ : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun Λ _ => mul_nonneg (hw Λ) (Nat.cast_nonneg _))]
        refine Finset.sum_congr rfl (fun Λ _ => ?_)
        rw [ENNReal.ofReal_mul (hw Λ), ENNReal.ofReal_natCast]
    _ ≤ ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N Λ : ℝ≥0∞) := by
        gcongr with Λ hΛ
        have h := ENat.toENNReal_le.mpr (hn Λ hΛ)
        rwa [ENat.toENNReal_coe] at h
    _ ≤ (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal B := hM
    _ = ENNReal.ofReal (massRows D F0 what₂ * B) := by
        show _ = ENNReal.ofReal ((∑ Λ ∈ what₂, wRow D F0 Λ) * B)
        rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun Λ _ => hw Λ),
          ENNReal.ofReal_sum_of_nonneg (fun Λ _ => hw Λ)]

open Classical in

theorem rows_sum_wRow (S : Finset (D.s.Pair u u')) :
    ∑ p ∈ S, X.wRow p =
      ∑ Λ ∈ Y.what₂, wRow D Y.F0 Λ * ((S.filter (fun p => X.abelian₂ (D.s.pfst p) = Λ)).card : ℕ) := by
  rw [Finset.sum_congr rfl (fun p _ => Y.wRow_eq p)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => X.abelian₂ (D.s.pfst p)) (t := Y.what₂)
    (fun p _ => Y.Lam_mem _)]
  refine Finset.sum_congr rfl (fun Λ _ => ?_)
  have hc : ∀ p ∈ S.filter (fun p => X.abelian₂ (D.s.pfst p) = Λ),
      wRow D Y.F0 (X.abelian₂ (D.s.pfst p)) = wRow D Y.F0 Λ :=
    fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, mul_comm]

open Classical in

theorem rows_count {C' Cl Cg cb Cu cT CT C0 A Ad C : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hC3 : UnitaryVolumeMass.MeanFlagPairCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C) (Z' Z'' : GramM D) (hZ' : RelZ D Z') (hZ'' : RelZ D Z'')
    (s : ℕ) (hs : 2 ≤ s) (hsk : s ≤ D.R.k) (De : ℝ) (hDe1 : 1 ≤ De)
    (hDe2 : De ≤ (HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'') ^ Ad) (hB : 0 ≤ wordSublatticeTripleBound D large₂ u C Z' Z'' s De)
    (S : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S, D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧
      ZEquiv (termGramMatrix X (D.s.pfst p)) Z' ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) Z'' ∧ D.s.s0 p = s ∧ pairDeterminant X p ≤ De) :
    ∑ p ∈ S, X.wRow p ≤ massRows D Y.F0 Y.what₂ * wordSublatticeTripleBound D large₂ u C Z' Z'' s De := by
  have hM := hC3 hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero Y.what₂ Y.isRows Z' Z'' hZ' hZ'' s hs hsk De hDe1 hDe2
  rw [rows_sum_wRow Y S]
  refine rows_mean_real Y.F0 Y.what₂ _ _ hB hM (fun Λ => (S.filter (fun p => X.abelian₂ (D.s.pfst p) = Λ)).card)
    (fun Λ _ => ?_)
  refine rows_fibre_le Y Z' Z'' s De Λ _ (fun p hp => ?_)
  obtain ⟨hpS, hpΛ⟩ := Finset.mem_filter.mp hp
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS p hpS
  exact ⟨hpΛ, h1, h2, h3, h4, h5, h6⟩

end Count

section One

open Classical in

theorem rows_card_le_mul {α ι : Type} (Xs : Set α) (R : α → α → Prop) (hR : ∀ a ∈ Xs, R a a) (S : Finset ι) (f : ι → α)
    (hf : ∀ i ∈ S, f i ∈ Xs) (P : ℝ≥0∞)
    (hfib : ∀ i₀ ∈ S, ∀ S' : Finset ι, S' ⊆ S → (∀ i ∈ S', R (f i₀) (f i)) → ((S'.card : ℕ) : ℝ≥0∞) ≤ P) :
    ((S.card : ℕ) : ℝ≥0∞) ≤ ((cntCl Xs R : ℕ∞) : ℝ≥0∞) * P := by
  classical
  let cls : ι → Set α := fun i => {b | b ∈ Xs ∧ R (f i) b}
  have hfib' : ∀ O ∈ S.image cls, (((S.filter (fun i => cls i = O)).card : ℕ) : ℝ≥0∞) ≤ P := by
    intro O hO
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hO
    apply hfib i₀ hi₀ _ (Finset.filter_subset _ _)
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    have hmem : f i ∈ cls i := ⟨hf i hi'.1, hR _ (hf i hi'.1)⟩
    rw [hi'.2] at hmem
    exact hmem.2
  have hcl : (((S.image cls).card : ℕ) : ℕ∞) ≤ cntCl Xs R := by
    unfold cntCl
    rw [← Set.encard_coe_eq_coe_finsetCard]
    apply Set.encard_le_encard
    intro O hO
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hO)
    exact ⟨f i, hf i hi, rfl⟩
  have hcl' : (((S.image cls).card : ℕ) : ℝ≥0∞) ≤ ((cntCl Xs R : ℕ∞) : ℝ≥0∞) := by
    have h := ENat.toENNReal_le.mpr hcl
    rwa [ENat.toENNReal_coe] at h
  calc ((S.card : ℕ) : ℝ≥0∞)
      = ∑ O ∈ S.image cls, (((S.filter (fun i => cls i = O)).card : ℕ) : ℝ≥0∞) := by
        rw [Finset.card_eq_sum_card_image cls S, Nat.cast_sum]
    _ ≤ ∑ O ∈ S.image cls, P := Finset.sum_le_sum hfib'
    _ = (((S.image cls).card : ℕ) : ℝ≥0∞) * P := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((cntCl Xs R : ℕ∞) : ℝ≥0∞) * P := by gcongr

variable {D : D7} {large₂ : SizeData₂ D} (X : TermTie D) {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def rowsSingleFibre : Prop :=
  ∀ (Z'' : GramM D) (p₀ : D.s.Pair u u') (S : Finset (D.s.Pair u u')),
    (∀ p ∈ S, X.abelian₂ (D.s.pfst p) = X.abelian₂ (D.s.pfst p₀) ∧ D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧
      D.s.generic (D.s.pfst p) ∧ D.s.generic (D.s.psnd p) ∧ D.s.s0 p = 1 ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) Z'' ∧
      TEqv D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0) (X.fl' (D.s.pfst p₀)) (X.fl' (D.s.pfst p))) →
    ((S.card : ℕ) : ℕ∞) ≤ cntPartners D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0) (X.fl' (D.s.pfst p₀)) Z''

variable {X}

theorem rows_mean_real_mul {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (what₂ : Finset (LatV D)) (N : LatV D → ℕ∞) (B P : ℝ)
    (hB : 0 ≤ B) (hP : 0 ≤ P) (hM : MeanLe D F0 what₂ N B) (n : LatV D → ℕ)
    (hn : ∀ Λ ∈ what₂, ((n Λ : ℕ) : ℝ≥0∞) ≤ (N Λ : ℝ≥0∞) * ENNReal.ofReal P) :
    ∑ Λ ∈ what₂, wRow D F0 Λ * n Λ ≤ massRows D F0 what₂ * (B * P) := by
  have hw : ∀ Λ, 0 ≤ wRow D F0 Λ := fun Λ => by unfold wRow; positivity
  have hmass : 0 ≤ massRows D F0 what₂ := Finset.sum_nonneg (fun Λ _ => hw Λ)
  unfold MeanLe at hM
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hmass (mul_nonneg hB hP))]
  calc ENNReal.ofReal (∑ Λ ∈ what₂, wRow D F0 Λ * (n Λ : ℝ))
      = ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * ((n Λ : ℕ) : ℝ≥0∞) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun Λ _ => mul_nonneg (hw Λ) (Nat.cast_nonneg _))]
        refine Finset.sum_congr rfl (fun Λ _ => ?_)
        rw [ENNReal.ofReal_mul (hw Λ), ENNReal.ofReal_natCast]
    _ ≤ ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * ((N Λ : ℝ≥0∞) * ENNReal.ofReal P) := by
        gcongr with Λ hΛ
        exact hn Λ hΛ
    _ = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N Λ : ℝ≥0∞)) * ENNReal.ofReal P := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun Λ _ => ?_)
        rw [mul_assoc]
    _ ≤ ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal B) * ENNReal.ofReal P :=
        mul_le_mul_of_nonneg_right hM (by positivity)
    _ = ENNReal.ofReal (massRows D F0 what₂ * (B * P)) := by
        show _ = ENNReal.ofReal ((∑ Λ ∈ what₂, wRow D F0 Λ) * (B * P))
        rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun Λ _ => hw Λ), ENNReal.ofReal_mul hB,
          ENNReal.ofReal_sum_of_nonneg (fun Λ _ => hw Λ), mul_assoc]

def wordPairSwapBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C : ℝ) (Z : GramM D) : ℝ :=
  HHZ D large₂.sc.b C Z ^ (C * (D.R.rS : ℝ) ^ 2) * ∏ τ, nV D (Tu D u) (Tu D u') Z τ

def gramPairQuadrupleBound (D : D7) (large₂ : SizeData₂ D) (C : ℝ) (Z' Z'' : GramM D) : ℝ :=
  C ^ D.R.f * (HHZ D large₂.sc.b C Z' * HHZ D large₂.sc.b C Z'') ^ (C * (D.R.rS : ℝ) ^ 2)

open Classical in

theorem rows_countOne {C' Cl Cg cb Cu cT CT C0 A CSW C4 : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C4)
    (hF : rowsSingleFibre X Y) (Z' Z'' : GramM D) (hZ' : RelZ D Z') (hZ'' : RelZ D Z'')
    (hB : 0 ≤ wordPairSwapBound D large₂ u u' CSW Z') (hP : 0 ≤ gramPairQuadrupleBound D large₂ C4 Z' Z'') (S : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S, D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧
      D.s.generic (D.s.pfst p) ∧ D.s.generic (D.s.psnd p) ∧ D.s.s0 p = 1 ∧
      ZEquiv (termGramMatrix X (D.s.pfst p)) Z' ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) Z'' ∧ RelZ D (termGramMatrix X (D.s.pfst p)) ∧
      HHZ D large₂.sc.b C4 (termGramMatrix X (D.s.pfst p)) = HHZ D large₂.sc.b C4 Z') :
    ∑ p ∈ S, X.wRow p ≤ massRows D Y.F0 Y.what₂ * (wordPairSwapBound D large₂ u u' CSW Z' * gramPairQuadrupleBound D large₂ C4 Z' Z'') := by
  have hM := hSW hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero Y.what₂ Y.isRows Z' hZ'
  rw [rows_sum_wRow Y S]
  refine rows_mean_real_mul Y.F0 Y.what₂ _ _ _ hB hP hM
    (fun Λ => (S.filter (fun p => X.abelian₂ (D.s.pfst p) = Λ)).card) (fun Λ hΛ => ?_)
  simp only [Formalism.MainNotions.S.Lem.Cnt.cntSW_eq]
  refine rows_card_le_mul _ (TEqv D Λ (lf D Y.F0)) (fun a _ => Formalism.MainNotions.S.Lem.Cnt.TEqv_refl D _ _ a) _
    (fun p => X.fl' (D.s.pfst p)) ?_ _ ?_
  · intro p hp
    obtain ⟨hpS, hpΛ⟩ := Finset.mem_filter.mp hp
    obtain ⟨hG1, -, hg1, -, -, hZ1, -, -, -⟩ := hS p hpS
    have hT := rows_isTermF Y _ hG1
    rw [hpΛ] at hT
    simp only [Set.mem_setOf_eq]
    refine ⟨hT.1, hT.2, ?_, ?_⟩
    · rw [← hpΛ, ← Y.fl_eq (D.s.pfst p)]
      exact (X.14 _).mp hg1
    · rw [← Y.fl_eq (D.s.pfst p)]
      exact hZ1
  · intro i₀ hi₀ S' hS' hR
    obtain ⟨hi₀S, hi₀Λ⟩ := Finset.mem_filter.mp hi₀
    obtain ⟨hG1₀, -, hg1₀, -, -, -, -, hRel₀, hHH₀⟩ := hS i₀ hi₀S
    have hcnt := hF Z'' i₀ S' (fun p hp => by
      obtain ⟨hpS, hpΛ⟩ := Finset.mem_filter.mp (hS' hp)
      obtain ⟨hG1, hG2, hg1, hg2, hs0, -, hZ2, -, -⟩ := hS p hpS
      refine ⟨hpΛ.trans hi₀Λ.symm, hG1, hG2, hg1, hg2, hs0, hZ2, ?_⟩
      have h := hR p hp
      rw [← hi₀Λ] at h
      exact h)
    have hT₀ := rows_isTermF Y _ hG1₀
    have hgen₀ : IsGeneric (X.abelian₂ (D.s.pfst i₀)) (gS D) (lf D Y.F0) (X.fl' (D.s.pfst i₀)) := by
      rw [← Y.fl_eq (D.s.pfst i₀)]
      exact (X.14 _).mp hg1₀
    have hRel : RelZ D (ZhatL (lf D Y.F0) (X.fl' (D.s.pfst i₀))) := by
      rw [← Y.fl_eq (D.s.pfst i₀)]
      exact hRel₀
    have hrow : IsRowLat D Y.F0 (X.abelian₂ (D.s.pfst i₀)) := Y.isRows.1 _ (Y.Lam_mem _)
    have h4 := hC4 hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero _ hrow _ hT₀ hgen₀ hRel Z'' hZ''
    have hHH : HHZ D large₂.sc.b C4 (ZhatL (lf D Y.F0) (X.fl' (D.s.pfst i₀))) = HHZ D large₂.sc.b C4 Z' := by
      rw [← Y.fl_eq (D.s.pfst i₀)]
      exact hHH₀
    rw [hHH] at h4
    have hc := ENat.toENNReal_le.mpr hcnt
    rw [ENat.toENNReal_coe] at hc
    exact hc.trans h4

def wordPairTermSingleFibre (X : TermTie D) (Y : LoopTie D large₂ X u u' C1) : Prop :=
  ∀ (Z' : GramM D) (p₀ : D.s.Pair u u') (S : Finset (D.s.Pair u u')),
    (∀ p ∈ S, X.abelian₂ (D.s.pfst p) = X.abelian₂ (D.s.pfst p₀) ∧ D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧
      D.s.generic (D.s.pfst p) ∧ D.s.generic (D.s.psnd p) ∧ D.s.s0 p = 1 ∧ ZEquiv (termGramMatrix X (D.s.pfst p)) Z' ∧
      TEqv D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0) (X.fl' (D.s.psnd p₀)) (X.fl' (D.s.psnd p))) →
    ((S.card : ℕ) : ℕ∞) ≤ cntPartners D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0) (X.fl' (D.s.psnd p₀)) Z'

open Classical in

theorem rows_countOne' {C' Cl Cg cb Cu cT CT C0 A CSW C4 : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hSW : UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW) (hC4 : UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C4)
    (hF : wordPairTermSingleFibre X Y) (Z' Z'' : GramM D) (hZ' : RelZ D Z') (hZ'' : RelZ D Z'')
    (hB : 0 ≤ wordPairSwapBound D large₂ u u' CSW Z'') (hP : 0 ≤ gramPairQuadrupleBound D large₂ C4 Z'' Z') (S : Finset (D.s.Pair u u'))
    (hS : ∀ p ∈ S, D.s.Gterm (D.s.pfst p) ≠ 0 ∧ D.s.Gterm (D.s.psnd p) ≠ 0 ∧
      D.s.generic (D.s.pfst p) ∧ D.s.generic (D.s.psnd p) ∧ D.s.s0 p = 1 ∧
      ZEquiv (termGramMatrix X (D.s.pfst p)) Z' ∧ ZEquiv (termGramMatrix X (D.s.psnd p)) Z'' ∧ RelZ D (termGramMatrix X (D.s.psnd p)) ∧
      HHZ D large₂.sc.b C4 (termGramMatrix X (D.s.psnd p)) = HHZ D large₂.sc.b C4 Z'') :
    ∑ p ∈ S, X.wRow p ≤ massRows D Y.F0 Y.what₂ * (wordPairSwapBound D large₂ u u' CSW Z'' * gramPairQuadrupleBound D large₂ C4 Z'' Z') := by
  have hM := hSW hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero Y.what₂ Y.isRows Z'' hZ''
  rw [rows_sum_wRow Y S]
  refine rows_mean_real_mul Y.F0 Y.what₂ _ _ _ hB hP hM
    (fun Λ => (S.filter (fun p => X.abelian₂ (D.s.pfst p) = Λ)).card) (fun Λ hΛ => ?_)
  simp only [Formalism.MainNotions.S.Lem.Cnt.cntSW_eq]
  refine rows_card_le_mul _ (TEqv D Λ (lf D Y.F0)) (fun a _ => Formalism.MainNotions.S.Lem.Cnt.TEqv_refl D _ _ a) _
    (fun p => X.fl' (D.s.psnd p)) ?_ _ ?_
  · intro p hp
    obtain ⟨hpS, hpΛ⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hG2, -, hg2, -, -, hZ2, -, -⟩ := hS p hpS
    have hT := rows_isTermF Y _ hG2
    rw [← X.16 p, hpΛ] at hT
    simp only [Set.mem_setOf_eq]
    refine ⟨hT.1, hT.2, ?_, ?_⟩
    · rw [← hpΛ, X.16 p, ← Y.fl_eq (D.s.psnd p)]
      exact (X.14 _).mp hg2
    · rw [← Y.fl_eq (D.s.psnd p)]
      exact hZ2
  · intro i₀ hi₀ S' hS' hR
    obtain ⟨hi₀S, hi₀Λ⟩ := Finset.mem_filter.mp hi₀
    obtain ⟨-, hG2₀, -, hg2₀, -, -, -, hRel₀, hHH₀⟩ := hS i₀ hi₀S
    have hcnt := hF Z' i₀ S' (fun p hp => by
      obtain ⟨hpS, hpΛ⟩ := Finset.mem_filter.mp (hS' hp)
      obtain ⟨hG1, hG2, hg1, hg2, hs0, hZ1, -, -, -⟩ := hS p hpS
      refine ⟨hpΛ.trans hi₀Λ.symm, hG1, hG2, hg1, hg2, hs0, hZ1, ?_⟩
      have h := hR p hp
      rw [← hi₀Λ] at h
      exact h)
    have hT₀ := rows_isTermF Y _ hG2₀
    rw [← X.16 i₀] at hT₀
    have hgen₀ : IsGeneric (X.abelian₂ (D.s.pfst i₀)) (gS D) (lf D Y.F0) (X.fl' (D.s.psnd i₀)) := by
      rw [X.16 i₀, ← Y.fl_eq (D.s.psnd i₀)]
      exact (X.14 _).mp hg2₀
    have hRel : RelZ D (ZhatL (lf D Y.F0) (X.fl' (D.s.psnd i₀))) := by
      rw [← Y.fl_eq (D.s.psnd i₀)]
      exact hRel₀
    have hrow : IsRowLat D Y.F0 (X.abelian₂ (D.s.pfst i₀)) := Y.isRows.1 _ (Y.Lam_mem _)
    have h4 := hC4 hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero _ hrow _ hT₀ hgen₀ hRel Z' hZ'
    have hHH : HHZ D large₂.sc.b C4 (ZhatL (lf D Y.F0) (X.fl' (D.s.psnd i₀))) = HHZ D large₂.sc.b C4 Z'' := by
      rw [← Y.fl_eq (D.s.psnd i₀)]
      exact hHH₀
    rw [hHH] at h4
    have hc := ENat.toENNReal_le.mpr hcnt
    rw [ENat.toENNReal_coe] at hc
    exact hc.trans h4

def wordPairTermInjective (X : TermTie D) (Y : LoopTie D large₂ X u u' C1) : Prop :=
  ∀ t t' : D.s.Term u u', X.abelian₂ t = X.abelian₂ t' → TEqv D (X.abelian₂ t) (lf D Y.F0) (X.fl' t) (X.fl' t') → t = t'

def wordPairBetaUnique (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∀ p q : D.s.Pair u u', D.s.pfst p = D.s.pfst q → D.s.psnd p = D.s.psnd q → D.s.s0 p = 1 → D.s.s0 q = 1 →
    D.s.generic (D.s.pfst p) → D.s.generic (D.s.psnd p) → D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → p = q

def wordPairSymmetric (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → D.s.s0 p = 1 → ∃ β,
    IsPair (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.fl' (D.s.pfst p)) β (gS D) ∧
      Lat.s0 (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.fl' (D.s.pfst p)) β D.R.k = 1

theorem rows_OneFibre_of (hT : wordPairTermInjective X Y) (hU : wordPairBetaUnique D u u') : rowsSingleFibre X Y := by
  intro Z'' p₀ S hS
  have hf : ∀ p ∈ S, D.s.pfst p = D.s.pfst p₀ := by
    intro p hp
    obtain ⟨hΛ, -, -, -, -, -, -, hE⟩ := hS p hp
    exact (hT _ _ hΛ.symm hE).symm
  have hmem : ∀ i : S, X.fl' (D.s.psnd i.1) ∈
      Partners D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0) (X.fl' (D.s.pfst p₀)) Z'' := by
    intro i
    obtain ⟨-, hG1, hG2, -, hg2, hs0, hZ, -⟩ := hS i.1 i.2
    have hfi := hf i.1 i.2
    rw [← hfi]
    simp only [Partners, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, X.beta i.1, ?_, ?_⟩
    · rw [X.16 i.1]
      exact rows_isTermF Y _ hG2
    · rw [X.16 i.1, ← Y.fl_eq (D.s.psnd i.1)]
      exact (X.14 _).mp hg2
    · rw [← Y.fl_eq (D.s.psnd i.1)]
      exact hZ
    · rw [← Y.fl_eq (D.s.pfst i.1)]
      exact X.19 i.1
    · rw [← Y.fl_eq (D.s.pfst i.1), ← X.20 i.1]
      exact hs0
  have hinj : ∀ i j : S, TEqv D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0) (X.fl' (D.s.psnd i.1)) (X.fl' (D.s.psnd j.1)) →
      i = j := by
    intro i j h
    obtain ⟨hΛi, hG1i, hG2i, hg1i, hg2i, hs0i, -, -⟩ := hS i.1 i.2
    obtain ⟨hΛj, -, -, -, -, hs0j, -, -⟩ := hS j.1 j.2
    have hLi : X.abelian₂ (D.s.psnd i.1) = X.abelian₂ (D.s.pfst p₀) := (X.16 i.1).symm.trans hΛi
    have hLj : X.abelian₂ (D.s.psnd j.1) = X.abelian₂ (D.s.pfst p₀) := (X.16 j.1).symm.trans hΛj
    have hsnd : D.s.psnd i.1 = D.s.psnd j.1 := hT _ _ (hLi.trans hLj.symm) (by rw [hLi]; exact h)
    exact Subtype.ext (hU _ _ ((hf i.1 i.2).trans (hf j.1 j.2).symm) hsnd hs0i hs0j hg1i hg2i hG1i hG2i)
  have key := Formalism.MainNotions.S.Lem.Cnt.card_le_cntCl _ (TEqv D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0))
    (fun a _ => Formalism.MainNotions.S.Lem.Cnt.TEqv_refl D _ _ a) (fun i : S => X.fl' (D.s.psnd i.1)) hmem hinj
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe] at key
  exact key

theorem rows_OneFibre'_of (hT : wordPairTermInjective X Y) (hU : wordPairBetaUnique D u u') (hP : wordPairSymmetric X u u') :
    wordPairTermSingleFibre X Y := by
  intro Z' p₀ S hS
  have hL0 : X.abelian₂ (D.s.psnd p₀) = X.abelian₂ (D.s.pfst p₀) := (X.16 p₀).symm
  have hf : ∀ p ∈ S, D.s.psnd p = D.s.psnd p₀ := by
    intro p hp
    obtain ⟨hΛ, -, -, -, -, -, -, hE⟩ := hS p hp
    refine (hT _ _ (hL0.trans (hΛ.symm.trans (X.16 p))) ?_).symm
    rw [hL0]
    exact hE
  have hmem : ∀ i : S, X.fl' (D.s.pfst i.1) ∈
      Partners D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0) (X.fl' (D.s.psnd p₀)) Z' := by
    intro i
    obtain ⟨hΛ, hG1, hG2, hg1, -, hs0, hZ, -⟩ := hS i.1 i.2
    obtain ⟨β, hβ, hβs⟩ := hP i.1 hG1 hG2 hs0
    rw [← hf i.1 i.2, ← hΛ]
    simp only [Partners, Set.mem_setOf_eq]
    refine ⟨rows_isTermF Y _ hG1, ?_, ?_, β, ?_, ?_⟩
    · rw [← Y.fl_eq (D.s.pfst i.1)]
      exact (X.14 _).mp hg1
    · rw [← Y.fl_eq (D.s.pfst i.1)]
      exact hZ
    · rw [← Y.fl_eq (D.s.pfst i.1)]
      exact hβ
    · rw [← Y.fl_eq (D.s.pfst i.1)]
      exact hβs
  have hinj : ∀ i j : S, TEqv D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0) (X.fl' (D.s.pfst i.1)) (X.fl' (D.s.pfst j.1)) →
      i = j := by
    intro i j h
    obtain ⟨hΛi, hG1i, hG2i, hg1i, hg2i, hs0i, -, -⟩ := hS i.1 i.2
    obtain ⟨hΛj, -, -, -, -, hs0j, -, -⟩ := hS j.1 j.2
    have hfst : D.s.pfst i.1 = D.s.pfst j.1 := hT _ _ (hΛi.trans hΛj.symm) (by rw [hΛi]; exact h)
    exact Subtype.ext (hU _ _ hfst ((hf i.1 i.2).trans (hf j.1 j.2).symm) hs0i hs0j hg1i hg2i hG1i hG2i)
  have key := Formalism.MainNotions.S.Lem.Cnt.card_le_cntCl _ (TEqv D (X.abelian₂ (D.s.pfst p₀)) (lf D Y.F0))
    (fun a _ => Formalism.MainNotions.S.Lem.Cnt.TEqv_refl D _ _ a) (fun i : S => X.fl' (D.s.pfst i.1)) hmem hinj
  rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe] at key
  exact key

end One

section Det

open NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem rows_one_le_latDet (M : Submodule (𝓞 E) S.V) (hM : ∀ x ∈ M, ∀ y ∈ M, ∃ o : 𝓞 E, (o : E) = S.hT y x) :
    1 ≤ latDet S M := by
  have hle : M ≤ dualIn S M := by
    intro x hx
    have hd : x ∈ Formalism.E.hdual S.hT M := by
      unfold Formalism.E.hdual
      simp only [Submodule.mem_iInf, Submodule.mem_comap]
      intro y hy
      obtain ⟨o, ho⟩ := hM x hx y hy
      exact Submodule.mem_one.2 ⟨o, ho⟩
    exact ⟨hd, Submodule.subset_span hx⟩
  unfold latDet latDetH
  rw [Real.one_le_sqrt]
  unfold genIdxH
  refine finprod_induction (fun x : ℝ => 1 ≤ x) le_rfl (fun _ _ => one_le_mul_of_one_le_of_one_le) fun P => ?_
  have hN : (1 : ℝ) ≤ ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) := by
    have : Ideal.absNorm P.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have := P.isPrime
  rw [Formalism.MainNotions.LatticeGluingRadicals.i_lidx_of_le (S := S) P.asIdeal hle, zpow_natCast]
  exact one_le_pow₀ hN

variable {r : ℕ} {T : E}

theorem rows_Lsub_integral (Λ : Submodule (𝓞 E) S.V) (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (F : LFlag S r T) :
    ∀ x ∈ Lsub Λ F, ∀ y ∈ Lsub Λ F, ∃ o : 𝓞 E, (o : E) = S.hT y x := by
  intro x hx y hy
  have horth : ∀ v, v ∈ orth S (Xsp F) → ∀ a ∈ Xsp F, S.hT a v = 0 := by
    intro v hv a ha
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hv
    exact hv a ha
  obtain ⟨l, hl, a, ha, rfl⟩ := Submodule.mem_sup.1 hx.1
  obtain ⟨l', hl', a', ha', rfl⟩ := Submodule.mem_sup.1 hy.1
  have h1 : S.hT a' (l + a) = 0 := horth _ hx.2 a' ha'
  have h2 : S.hT l' a = 0 := by
    have := S.herm.eq a l'
    rw [horth l' hl'.2 a ha] at this
    simpa using this.symm
  have h3 : l ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hΛ]; exact hl.1
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at h3
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at h3
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h3 l' hl'.1)
  refine ⟨o, ?_⟩
  have e1 : S.hT (l' + a') (l + a) = S.hT l' (l + a) + S.hT a' (l + a) := by
    rw [map_add (S.hT) l' a', LinearMap.add_apply]
  have e2 : S.hT l' (l + a) = S.hT l' l + S.hT l' a := map_add _ _ _
  rw [e1, h1, add_zero, e2, h2, add_zero]
  exact ho

end Det

section Det2

variable {D : D7} {X : TermTie D} {u u' : D.what₂.Word}

theorem rows_one_le_iIdx (hP : PrimeHyp D u (Tu D u')) (Λ : UnitaryVolumeMass.Lt D) (F : UnitaryVolumeMass.Fl D (Tu D u)) (F' : UnitaryVolumeMass.Fl D (Tu D u'))
    (hF : FixedHyp D Λ F) (hT : IsTerm Λ (gS D) F F') : (1 : ℝ) ≤ (iIdx Λ (gS D) F F' : ℝ) := by
  obtain ⟨hfin, _, _, _, φ, hφ, _⟩ := Formalism.MainNotions.LatticeGluingRadicals.lemma_one_section D u (Tu D u') Λ F F' hF hP hT
  have := hfin
  have : Finite (La Λ (gS D) F F' ⧸ (Thp Λ F F').comap (La Λ (gS D) F F').subtype) := Finite.of_injective φ hφ
  have : 0 < iIdx Λ (gS D) F F' := by
    unfold iIdx idx
    exact Nat.card_pos
  exact_mod_cast this

theorem rows_DetGeOne_of (hSt : Cnt.Stand D u u') : wordPairDeterminantGeOne X u u' := by
  intro p hG1 hG2
  have hP := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hF := X.fixed (D.s.pfst p)
  have hne : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → Gval (X.fl t) (X.fl' t) ≠ 0 := by
    intro t hG
    rw [← X.G_eq t]
    exact (map_ne_zero_iff _ (algebraMap D.host.F D.host.E).injective).2 hG
  have hT1 : IsTerm (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) :=
    ⟨X.lift' _, X.adm _, hne _ hG1⟩
  have hT2 : IsTerm (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.psnd p)) := by
    rw [X.pLam p, X.pfl p]
    exact ⟨X.lift' _, X.adm _, hne _ hG2⟩
  have h1 := rows_one_le_iIdx hP _ _ _ hF hT1
  have h2 := rows_one_le_iIdx hP _ _ _ hF hT2
  have hLa : La (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) ≤
      Lsub (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) := by
    unfold La
    rw [Submodule.span_le]
    intro x hx
    exact hx.2.1.1
  have h3 : 1 ≤ latDet (hS D) (Mlat (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p))
      (X.fl' (D.s.psnd p)) (X.beta p) (gS D)) :=
    rows_one_le_latDet _ fun x hx y hy =>
      rows_Lsub_integral _ hF.2.1 _ x (hLa hx.1) y (hLa hy.1)
  unfold pairDeterminant
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 h1) h2

theorem rows_PairSymm_holds (X : TermTie D) (u u' : D.what₂.Word) : wordPairSymmetric X u u' := by
  intro p hG1 hG2 hs
  have hP := X.isPair p
  have hF := X.fixed (D.s.pfst p)
  have hne : ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → Gval (X.fl t) (X.fl' t) ≠ 0 := by
    intro t hG
    rw [← X.G_eq t]
    exact (map_ne_zero_iff _ (algebraMap D.host.F D.host.E).injective).2 hG
  have hU' := Formalism.MainNotions.LatticeGluingRadicals.a_HU (X.abelian₂ (D.s.pfst p)) hF.1 (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) hF.2.2.1.2
    (X.lift' (D.s.pfst p)).2
  have hU'' := Formalism.MainNotions.LatticeGluingRadicals.a_HU (X.abelian₂ (D.s.pfst p)) hF.1 (X.fl (D.s.pfst p)) (X.fl' (D.s.psnd p)) hF.2.2.1.2
    (X.lift' (D.s.psnd p)).2
  have hN' := Formalism.MainNotions.LatticeGluingRadicals.a_HNd (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (hne _ hG1)
  have hN'' : Formalism.MainNotions.LatticeGluingRadicals.HNd (X.fl (D.s.pfst p)) (X.fl' (D.s.psnd p)) := by
    rw [X.pfl p]
    exact Formalism.MainNotions.LatticeGluingRadicals.a_HNd _ _ (hne _ hG2)
  refine ⟨(X.beta p).symm, Formalism.MainNotions.LatticeGluingRadicals.k_pair_symm hP, ?_⟩
  have h0 := X.s0_eq p
  rw [hs] at h0
  unfold Lat.s0 at h0 ⊢
  rw [Formalism.MainNotions.LatticeGluingRadicals.k_Th_swap hP, Formalism.MainNotions.LatticeGluingRadicals.c_finrank_Th'' hU' hN', ← Formalism.MainNotions.LatticeGluingRadicals.c_finrank_Th hU'' hN'']
  exact h0.symm

theorem rows_OneFibre'_of' {large₂ : SizeData₂ D} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1) (hT : wordPairTermInjective X Y)
    (hU : wordPairBetaUnique D u u') : wordPairTermSingleFibre X Y := rows_OneFibre'_of Y hT hU (rows_PairSymm_holds X u u')

def wordPairBetaLattice (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∀ (Λ : UnitaryVolumeMass.Lt D) (F : UnitaryVolumeMass.Fl D (Tu D u)) (F' F'' : UnitaryVolumeMass.Fl D (Tu D u')) (β₁ β₂ : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    IsPair Λ F F' F'' β₁ (gS D) → IsPair Λ F F' F'' β₂ (gS D) →
    Lat.s0 Λ F F' F'' β₁ D.R.k = 1 → Lat.s0 Λ F F' F'' β₂ D.R.k = 1 →
      ∀ x ∈ orth (hS D) (Xsp F'), β₂ x - β₁ x ∈ Xsp F''

theorem rows_BetaUnique_of {large₂ : SizeData₂ D} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1) (hB : wordPairBetaLattice D u u') :
    wordPairBetaUnique D u u' := by
  intro p q h1 h2 hs1 hs2 hg1 hg2 hG1 hG2
  have hΛ : X.abelian₂ (D.s.pfst p) = X.abelian₂ (D.s.pfst q) := by rw [h1]
  refine Y.pair_inj p q hΛ ?_
  obtain ⟨n', hn', n'', hn'', hf1, hf2, hx⟩ :=
    Formalism.MainNotions.S.Lem.Cnt.PEqv_refl D (X.abelian₂ (D.s.pfst p)) (lf D Y.F0) (pairToTriple X p)
  simp only [pairToTriple] at hf1 hf2 hx
  have hT1 := (rows_isTermF Y _ hG1).1
  rw [← Y.fl_eq (D.s.pfst p)] at hT1
  have hT2 := (rows_isTermF Y _ hG2).1
  rw [← X.16 p, ← Y.fl_eq (D.s.pfst p)] at hT2
  have hGen1 := (X.14 _).mp hg1
  have hGen2 := (X.14 _).mp hg2
  rw [← X.16 p, ← X.17 p] at hGen2
  have hPq := X.19 q
  rw [← h1, ← h2] at hPq
  have hs0p := (X.20 p).symm.trans hs1
  have hs0q := (X.20 q).symm.trans hs2
  rw [← h1, ← h2] at hs0q
  refine ⟨n', hn', n'', hn'', ?_, ?_, ?_⟩
  · rw [← h1]
    exact hf1
  · rw [← h2]
    exact hf2
  · intro x hx'
    rw [← h1] at hx'
    have hb := hB (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p))
      (X.beta p) (X.beta q) (X.fixed _) hT1 hT2 hGen1 hGen2 (X.19 p) hPq hs0p hs0q x hx'
    have hsub := Submodule.add_mem _ hb (hx x hx')
    rw [← h2]
    convert hsub using 1
    abel

end Det2

end Formalism.MainNotions.BridgeLemma₂

end
