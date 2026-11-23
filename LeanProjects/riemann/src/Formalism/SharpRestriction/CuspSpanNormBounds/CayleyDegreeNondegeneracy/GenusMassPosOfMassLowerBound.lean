import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PrimitiveMeanOverWords
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

theorem c3sub_encard_cover {γ ι : Type*} (I : Finset ι) (Qn : ι → Set γ) :
    ∀ Q : Set γ, (Q ⊆ ⋃ n ∈ I, Qn n) → ((Q.encard : ℕ∞) : ℝ≥0∞) ≤ ∑ n ∈ I, (((Qn n).encard : ℕ∞) : ℝ≥0∞) := by
  classical
  have key : ∀ (J : Finset ι) (Q : Set γ), Q ⊆ ⋃ n ∈ J, Qn n →
      ((Q.encard : ℕ∞) : ℝ≥0∞) ≤ ∑ n ∈ J, (((Qn n).encard : ℕ∞) : ℝ≥0∞) := by
    intro J
    refine Finset.induction_on J ?_ ?_
    · intro Q hQ
      have hQe : Q = ∅ := by
        apply Set.subset_empty_iff.mp
        intro x hx
        have hx' := hQ hx
        simp at hx'
      simp [hQe]
    · intro a J ha ih Q hQ
      rw [Finset.sum_insert ha]
      have hsub : Q ⊆ Qn a ∪ ⋃ n ∈ J, Qn n := by
        intro x hx
        have hx' := hQ hx
        simp only [Set.mem_iUnion, Finset.mem_insert] at hx'
        obtain ⟨m, hm, hxm⟩ := hx'
        rcases hm with hm | hm
        · subst hm
          exact Or.inl hxm
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨m, hm, hxm⟩)
      calc ((Q.encard : ℕ∞) : ℝ≥0∞)
          ≤ (((Qn a ∪ ⋃ n ∈ J, Qn n).encard : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_le.mpr (Set.encard_le_encard hsub)
        _ ≤ (((Qn a).encard + (⋃ n ∈ J, Qn n).encard : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_le.mpr (Set.encard_union_le _ _)
        _ = (((Qn a).encard : ℕ∞) : ℝ≥0∞) + (((⋃ n ∈ J, Qn n).encard : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_add _ _
        _ ≤ (((Qn a).encard : ℕ∞) : ℝ≥0∞) + ∑ n ∈ J, (((Qn n).encard : ℕ∞) : ℝ≥0∞) := by
            gcongr
            exact ih _ subset_rfl
  intro Q hQ
  exact key I Q hQ

theorem c3sub_encard_sigma_fin {α β : Type*} (B : α → Set β) (b : ℝ≥0∞) (s : Finset α)
    (h : ∀ a ∈ s, (((B a).encard : ℕ∞) : ℝ≥0∞) ≤ b) :
    ((({p : α × β | p.1 ∈ s ∧ p.2 ∈ B p.1}).encard : ℕ∞) : ℝ≥0∞) ≤ (s.card : ℝ≥0∞) * b := by
  have hsub : {p : α × β | p.1 ∈ s ∧ p.2 ∈ B p.1} ⊆ ⋃ a ∈ s, (Prod.mk a '' B a) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact Set.mem_iUnion₂.mpr ⟨x, hx, y, hy, rfl⟩
  calc ((({p : α × β | p.1 ∈ s ∧ p.2 ∈ B p.1}).encard : ℕ∞) : ℝ≥0∞)
      ≤ ∑ a ∈ s, (((Prod.mk a '' B a).encard : ℕ∞) : ℝ≥0∞) := c3sub_encard_cover s _ _ hsub
    _ ≤ ∑ _a ∈ s, b := by
        apply Finset.sum_le_sum
        intro a ha
        calc (((Prod.mk a '' B a).encard : ℕ∞) : ℝ≥0∞) ≤ (((B a).encard : ℕ∞) : ℝ≥0∞) :=
              ENat.toENNReal_le.mpr (Set.encard_image_le _ _)
          _ ≤ b := h a ha
    _ = (s.card : ℝ≥0∞) * b := by rw [Finset.sum_const, nsmul_eq_mul]

theorem c3sub_encard_sigma {α β : Type*} (A : Set α) (B : α → Set β) (b : ℝ≥0∞)
    (h : ∀ a ∈ A, (((B a).encard : ℕ∞) : ℝ≥0∞) ≤ b) :
    ((({p : α × β | p.1 ∈ A ∧ p.2 ∈ B p.1}).encard : ℕ∞) : ℝ≥0∞) ≤ ((A.encard : ℕ∞) : ℝ≥0∞) * b := by
  classical
  by_cases hA : A.Finite
  · have hs := c3sub_encard_sigma_fin B b hA.toFinset
      (by intro a ha; exact h a (hA.mem_toFinset.mp ha))
    have hset : {p : α × β | p.1 ∈ hA.toFinset ∧ p.2 ∈ B p.1} =
        {p : α × β | p.1 ∈ A ∧ p.2 ∈ B p.1} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.Finite.mem_toFinset]
    rw [hset] at hs
    have hcard : ((A.encard : ℕ∞) : ℝ≥0∞) = (hA.toFinset.card : ℝ≥0∞) := by
      rw [hA.encard_eq_coe_toFinset_card]
      norm_cast
    rw [hcard]
    exact hs
  · have hinf : A.encard = ⊤ := Set.encard_eq_top_iff.mpr hA
    by_cases hb : b = 0
    · subst hb
      have hempty : {p : α × β | p.1 ∈ A ∧ p.2 ∈ B p.1} = ∅ := by
        ext ⟨x, y⟩
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx hy
        have h0 : (B x).encard = 0 := by simpa using h x hx
        rw [Set.encard_eq_zero] at h0
        rw [h0] at hy
        exact hy
      rw [hempty]
      simp
    · rw [hinf]
      simp [hb]

end Count

section Lat

variable (D : D7)

def SublatticeFGProjectiveRankLe (u : D.what₂.Word) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M : LatticeW D, M ≤ L0X D Λ (lf D F0) →
    Module.Finite (𝓞 D.host.E) M ∧ Module.Projective (𝓞 D.host.E) M ∧ finrank (𝓞 D.host.E) M ≤ D.R.k

def sublatticesAtLevel (M : LatticeW D) (j : ℕ) : Set (LatticeW D) := {M' | M' ≤ M ∧ sublatticeIndex' D M M' = j}

def levelWeight (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((j : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f))

theorem c3sub_Bs_le (M : LatticeW D)
    (hM : Module.Finite (𝓞 D.host.E) M ∧ Module.Projective (𝓞 D.host.E) M ∧ finrank (𝓞 D.host.E) M ≤ D.R.k)
    (j : ℕ) (hj : 1 ≤ j) : (((sublatticesAtLevel D M j).encard : ℕ∞) : ℝ≥0∞) ≤ levelWeight D j := by
  obtain ⟨h1, h2, h3⟩ := hM
  refine le_trans ?_ (Formalism.MainNotions.BridgeLemma.sublattice_count_polynomial_bound D M h3 j hj)
  have e : ENat.card {Q : Submodule (𝓞 D.host.E) M // Nat.card (M ⧸ Q) = j} =
      Set.encard {Q : Submodule (𝓞 D.host.E) M | Nat.card (M ⧸ Q) = j} := rfl
  rw [e]
  have : (sublatticesAtLevel D M j).encard ≤ Set.encard {Q : Submodule (𝓞 D.host.E) M | Nat.card (M ⧸ Q) = j} := by
    refine Set.encard_le_encard_of_injOn (f := fun M' => M'.comap M.subtype) ?_ ?_
    · intro M' hM'
      exact hM'.2
    · intro M₁ h₁ M₂ h₂ h
      have h' : Submodule.comap M.subtype M₁ = Submodule.comap M.subtype M₂ := h
      have a1 := Submodule.map_comap_subtype M M₁
      have a2 := Submodule.map_comap_subtype M M₂
      rw [h', a2, inf_eq_right.2 h₂.1, inf_eq_right.2 h₁.1] at a1
      exact a1.symm
  exact_mod_cast this

def latticeQuadruples (L0 : LatticeW D) (s : ℕ) (n : Fin 4 → ℕ) : Set (LatticeW D × LatticeW D × LatticeW D × LatticeW D) :=
  {q | q.1 ∈ PrimSubs (D.sp.X 0).hT L0 (D.R.k - s) (n 0) ∧
    q.2 ∈ {t : LatticeW D × LatticeW D × LatticeW D | t.1 ∈ sublatticesAtLevel D q.1 (n 1) ∧
      t.2 ∈ {w : LatticeW D × LatticeW D | w.1 ∈ sublatticesAtLevel D t.1 (n 2) ∧ w.2 ∈ sublatticesAtLevel D t.1 (n 3)}}}

private theorem le_of_isPrimitiveSub {M L : LatticeW D} (h : IsPrimitiveSub M L) : M ≤ L := by
  unfold IsPrimitiveSub at h
  exact h.1

theorem c3sub_Qn_le (L0 : LatticeW D)
    (hP : ∀ M : LatticeW D, M ≤ L0 →
      Module.Finite (𝓞 D.host.E) M ∧ Module.Projective (𝓞 D.host.E) M ∧ finrank (𝓞 D.host.E) M ≤ D.R.k)
    (s : ℕ) (n : Fin 4 → ℕ) (hn : ∀ i, 1 ≤ n i) :
    (((latticeQuadruples D L0 s n).encard : ℕ∞) : ℝ≥0∞) ≤
      ((cntPrim (D.sp.X 0).hT L0 (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞) *
        (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) := by
  classical
  have hW : ∀ M' : LatticeW D, M' ≤ L0 →
      ((({w : LatticeW D × LatticeW D | w.1 ∈ sublatticesAtLevel D M' (n 2) ∧ w.2 ∈ sublatticesAtLevel D M' (n 3)}).encard : ℕ∞) : ℝ≥0∞)
        ≤ levelWeight D (n 2) * levelWeight D (n 3) := by
    intro M' hM'
    calc ((({w : LatticeW D × LatticeW D | w.1 ∈ sublatticesAtLevel D M' (n 2) ∧ w.2 ∈ sublatticesAtLevel D M' (n 3)}).encard : ℕ∞) : ℝ≥0∞)
        ≤ (((sublatticesAtLevel D M' (n 2)).encard : ℕ∞) : ℝ≥0∞) * levelWeight D (n 3) :=
          c3sub_encard_sigma (sublatticesAtLevel D M' (n 2)) (fun _ => sublatticesAtLevel D M' (n 3)) _
            (fun _ _ => c3sub_Bs_le D M' (hP M' hM') (n 3) (hn 3))
      _ ≤ levelWeight D (n 2) * levelWeight D (n 3) :=
          mul_le_mul_of_nonneg_right (c3sub_Bs_le D M' (hP M' hM') (n 2) (hn 2)) zero_le
  have hT : ∀ M : LatticeW D, M ≤ L0 →
      ((({t : LatticeW D × LatticeW D × LatticeW D | t.1 ∈ sublatticesAtLevel D M (n 1) ∧
          t.2 ∈ {w : LatticeW D × LatticeW D | w.1 ∈ sublatticesAtLevel D t.1 (n 2) ∧ w.2 ∈ sublatticesAtLevel D t.1 (n 3)}}).encard : ℕ∞) : ℝ≥0∞)
        ≤ levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3)) := by
    intro M hM
    calc ((({t : LatticeW D × LatticeW D × LatticeW D | t.1 ∈ sublatticesAtLevel D M (n 1) ∧
          t.2 ∈ {w : LatticeW D × LatticeW D | w.1 ∈ sublatticesAtLevel D t.1 (n 2) ∧ w.2 ∈ sublatticesAtLevel D t.1 (n 3)}}).encard : ℕ∞) : ℝ≥0∞)
        ≤ (((sublatticesAtLevel D M (n 1)).encard : ℕ∞) : ℝ≥0∞) * (levelWeight D (n 2) * levelWeight D (n 3)) :=
          c3sub_encard_sigma (sublatticesAtLevel D M (n 1))
            (fun M' => {w : LatticeW D × LatticeW D | w.1 ∈ sublatticesAtLevel D M' (n 2) ∧ w.2 ∈ sublatticesAtLevel D M' (n 3)}) _
            (fun M' hM' => hW M' (le_trans hM'.1 hM))
      _ ≤ levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3)) :=
          mul_le_mul_of_nonneg_right (c3sub_Bs_le D M (hP M hM) (n 1) (hn 1)) zero_le
  have hle : ∀ M ∈ PrimSubs (D.sp.X 0).hT L0 (D.R.k - s) (n 0), M ≤ L0 := by
    intro M hM
    exact le_of_isPrimitiveSub D hM.1
  calc (((latticeQuadruples D L0 s n).encard : ℕ∞) : ℝ≥0∞)
      ≤ (((PrimSubs (D.sp.X 0).hT L0 (D.R.k - s) (n 0)).encard : ℕ∞) : ℝ≥0∞) *
          (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) :=
        c3sub_encard_sigma _ (fun M => {t : LatticeW D × LatticeW D × LatticeW D | t.1 ∈ sublatticesAtLevel D M (n 1) ∧
          t.2 ∈ {w : LatticeW D × LatticeW D | w.1 ∈ sublatticesAtLevel D t.1 (n 2) ∧ w.2 ∈ sublatticesAtLevel D t.1 (n 3)}}) _
          (fun M hM => hT M (hle M hM))
    _ = ((cntPrim (D.sp.X 0).hT L0 (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞) *
          (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) := by
        unfold cntPrim
        rfl

def indexBox (De : ℝ) : Set (Fin 4 → ℕ) := {q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De}

theorem c3sub_cover (L0 : LatticeW D) (hdet : ∀ M : LatticeW D, M ≤ L0 → ∃ de : ℕ, 1 ≤ de ∧ latticeDetW D M = de)
    (s : ℕ) (De : ℝ) (hfin : (indexBox De).Finite) :
    sublatticeQuadruples D L0 s De ⊆ ⋃ n ∈ hfin.toFinset, latticeQuadruples D L0 s n := by
  intro q hq
  unfold sublatticeQuadruples at hq
  obtain ⟨hprim, hrk, h1, h2, h3, hi1, hi2, hi3, hprod, -⟩ := hq
  obtain ⟨de, hde1, hde⟩ := hdet q.1 (le_of_isPrimitiveSub D hprim)
  have hnI : ![de, sublatticeIndex' D q.1 q.2.1, sublatticeIndex' D q.2.1 q.2.2.1, sublatticeIndex' D q.2.1 q.2.2.2] ∈ indexBox De := by
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · exact hde1
      · exact Nat.one_le_iff_ne_zero.mpr hi1
      · exact Nat.one_le_iff_ne_zero.mpr hi2
      · exact Nat.one_le_iff_ne_zero.mpr hi3
    · rw [Fin.prod_univ_four]
      show ((de * sublatticeIndex' D q.1 q.2.1 * sublatticeIndex' D q.2.1 q.2.2.1 * sublatticeIndex' D q.2.1 q.2.2.2 : ℕ) : ℝ) ≤ De
      push_cast
      rw [← hde]
      exact hprod
  refine Set.mem_iUnion₂.mpr ⟨_, hfin.mem_toFinset.mpr hnI, ?_⟩
  show q ∈ latticeQuadruples D L0 s ![de, sublatticeIndex' D q.1 q.2.1, sublatticeIndex' D q.2.1 q.2.2.1, sublatticeIndex' D q.2.1 q.2.2.2]
  unfold latticeQuadruples PrimSubs sublatticesAtLevel
  simp only [Set.mem_setOf_eq]
  exact ⟨⟨hprim, hrk, hde⟩, ⟨h1, rfl⟩, ⟨h2, rfl⟩, ⟨h3, rfl⟩⟩

end Lat

section Num

theorem log_two_factor_nonneg (f : ℕ) (hf : 1 ≤ f) : 0 ≤ lg2f f := by
  unfold lg2f
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  exact Real.logb_nonneg (by norm_num) (by linarith)

theorem c3sub_log_le_cF (f : ℕ) (hf : 1 ≤ f) : Real.log f ≤ cF f := by
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hf0 : (f:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have h20 : (2:ℝ) ≠ 0 := by norm_num
  have hlogf : 0 ≤ Real.log f := Real.log_nonneg hf'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hq : Real.log f ≤ Real.log f / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    nlinarith
  have hlg : lg2f f = 1 + Real.log f / Real.log 2 := by
    unfold lg2f Real.logb
    rw [Real.log_mul h20 hf0, add_div, div_self hl2.ne']
  unfold cF
  rw [hlg]
  linarith

theorem c3sub_num (k f s : ℕ) (A1 De NT Xi : ℝ) (n : Fin 4 → ℕ) (hn : ∀ i, 1 ≤ n i)
    (hprod : ((∏ i, n i : ℕ) : ℝ) ≤ De) (hf : 1 ≤ f) (hA : 0 ≤ A1) (hNT : 1 ≤ NT) (hXi : 0 ≤ Xi) :
    ((n 1 : ℝ) ^ ((k : ℝ) + lg2f f) * ((n 2 : ℝ) ^ ((k : ℝ) + lg2f f) * (n 3 : ℝ) ^ ((k : ℝ) + lg2f f))) *
        (((n 0 : ℝ) / NT) ^ k * ((n 0 : ℝ) * NT) ^ (A1 * s + A1 * Real.log f) * Xi) ≤
      (De / NT) ^ k * (De * NT) ^ (A1 * ((s : ℝ) + cF f)) * De ^ (cF f) * Xi := by
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have h0 : (1:ℝ) ≤ (n 0 : ℝ) := by exact_mod_cast hn 0
  have h1 : (1:ℝ) ≤ (n 1 : ℝ) := by exact_mod_cast hn 1
  have h2 : (1:ℝ) ≤ (n 2 : ℝ) := by exact_mod_cast hn 2
  have h3 : (1:ℝ) ≤ (n 3 : ℝ) := by exact_mod_cast hn 3
  have hg : 0 ≤ lg2f f := log_two_factor_nonneg f hf
  have hlog : Real.log f ≤ cF f := c3sub_log_le_cF f hf
  have hc : cF f = 1 + lg2f f := by
    unfold cF
    rfl
  have hNT0 : (0:ℝ) < NT := by linarith
  have hM1 : (1:ℝ) ≤ (n 1 : ℝ) * (n 2 : ℝ) * (n 3 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 h2) h3
  have hP : (n 0 : ℝ) * ((n 1 : ℝ) * (n 2 : ℝ) * (n 3 : ℝ)) ≤ De := by
    have hp := hprod
    rw [Fin.prod_univ_four] at hp
    push_cast at hp
    linarith
  have hsplit : (n 1 : ℝ) ^ ((k : ℝ) + lg2f f) * ((n 2 : ℝ) ^ ((k : ℝ) + lg2f f) * (n 3 : ℝ) ^ ((k : ℝ) + lg2f f))
      = ((n 1 : ℝ) * (n 2 : ℝ) * (n 3 : ℝ)) ^ k * ((n 1 : ℝ) * (n 2 : ℝ) * (n 3 : ℝ)) ^ (lg2f f) := by
    have hx : (0:ℝ) < (n 1 : ℝ) * (n 2 : ℝ) * (n 3 : ℝ) := by linarith
    have h12 : (0:ℝ) ≤ (n 1 : ℝ) * (n 2 : ℝ) := by positivity
    have h3' : (0:ℝ) ≤ (n 3 : ℝ) := by positivity
    have h1' : (0:ℝ) ≤ (n 1 : ℝ) := by positivity
    have h2' : (0:ℝ) ≤ (n 2 : ℝ) := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_add hx, Real.mul_rpow h12 h3', Real.mul_rpow h1' h2']
    ring
  rw [hsplit]
  generalize (n 0 : ℝ) = a0 at h0 hP ⊢
  generalize (n 1 : ℝ) * (n 2 : ℝ) * (n 3 : ℝ) = Mv at hM1 hP ⊢
  have hMv0 : 0 ≤ Mv := by linarith
  have ha0De : a0 ≤ De := by nlinarith
  have hMvDe : Mv ≤ De := by nlinarith
  have hDe1 : 1 ≤ De := le_trans h0 ha0De
  have he0 : 0 ≤ A1 * (s:ℝ) + A1 * Real.log f :=
    add_nonneg (mul_nonneg hA (Nat.cast_nonneg _)) (mul_nonneg hA (Real.log_nonneg hf'))
  have he : A1 * (s:ℝ) + A1 * Real.log f ≤ A1 * ((s:ℝ) + cF f) := by
    have hm := mul_le_mul_of_nonneg_left hlog hA
    have e : A1 * ((s:ℝ) + cF f) = A1 * s + A1 * cF f := by ring
    rw [e]
    linarith
  have hB1 : (a0 * Mv / NT) ^ k ≤ (De / NT) ^ k := by
    apply pow_le_pow_left₀ (div_nonneg (by nlinarith) hNT0.le)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hP (inv_nonneg.mpr hNT0.le)
  have hB2 : Mv ^ lg2f f ≤ De ^ cF f :=
    le_trans (Real.rpow_le_rpow hMv0 hMvDe hg)
      (Real.rpow_le_rpow_of_exponent_le hDe1 (by rw [hc]; linarith))
  have hB3 : (a0 * NT) ^ (A1 * (s:ℝ) + A1 * Real.log f) ≤ (De * NT) ^ (A1 * ((s:ℝ) + cF f)) :=
    le_trans (Real.rpow_le_rpow (by nlinarith) (mul_le_mul_of_nonneg_right ha0De hNT0.le) he0)
      (Real.rpow_le_rpow_of_exponent_le (by nlinarith) he)
  have hrw : Mv ^ k * Mv ^ lg2f f * ((a0 / NT) ^ k * (a0 * NT) ^ (A1 * (s:ℝ) + A1 * Real.log f) * Xi)
      = (a0 * Mv / NT) ^ k * (Mv ^ lg2f f * ((a0 * NT) ^ (A1 * (s:ℝ) + A1 * Real.log f) * Xi)) := by
    ring
  rw [hrw]
  calc (a0 * Mv / NT) ^ k * (Mv ^ lg2f f * ((a0 * NT) ^ (A1 * (s:ℝ) + A1 * Real.log f) * Xi))
      ≤ (De / NT) ^ k * (De ^ cF f * ((De * NT) ^ (A1 * ((s:ℝ) + cF f)) * Xi)) := by
        refine mul_le_mul hB1 ?_ ?_ (pow_nonneg (div_nonneg (by linarith) hNT0.le) k)
        · refine mul_le_mul hB2 (mul_le_mul_of_nonneg_right hB3 hXi) ?_ (Real.rpow_nonneg (by linarith) _)
          exact mul_nonneg (Real.rpow_nonneg (by nlinarith) _) hXi
        · exact mul_nonneg (Real.rpow_nonneg hMv0 _) (mul_nonneg (Real.rpow_nonneg (by nlinarith) _) hXi)
    _ = (De / NT) ^ k * (De * NT) ^ (A1 * ((s:ℝ) + cF f)) * De ^ cF f * Xi := by ring

end Num

section Main

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

theorem c3sub_f_pos : 1 ≤ D.R.f := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_le_f
  have h3 : D.R.f = 2 * D.R.toFrame.ord := rfl
  omega

theorem c3sub_NT_ge : 1 ≤ NT D u := by
  unfold NT
  have hT : 2 ≤ (D.mem u).A.T := (D.mem u).A.T_prime.two_le
  have hT' : (1:ℝ) ≤ ((D.mem u).A.T : ℝ) := by exact_mod_cast (by omega : 1 ≤ (D.mem u).A.T)
  exact one_le_pow₀ hT'

theorem c3sub_Xi_nonneg (HH A1 : ℝ) (hA : 0 ≤ A1) (hH : 0 ≤ HH) (s : ℕ) : 0 ≤ XiS D u HH A1 s := by
  have hNT := c3sub_NT_ge D u
  have hm : ∀ t, 0 ≤ massS D t := by
    intro t
    unfold massS massU Formalism.HermitianLatticesTheory.mass
    split_ifs
    · exact Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    · exact le_rfl
  unfold XiS Xi
  split_ifs
  all_goals first
    | exact div_nonneg (mul_nonneg (hm _) (hm _)) (hm _)
    | exact le_rfl
    | (apply mul_nonneg <;> first
        | (apply pow_nonneg; exact mul_nonneg (by assumption) (by first | positivity | linarith))
        | (apply Real.rpow_nonneg; exact mul_nonneg (by assumption) (by first | positivity | linarith)))

theorem sublattice_bound_of_mean_and_det {C' Cl Cg cb Cu cT CT C0 A A1 : ℝ} (hA : 0 ≤ A1)
    (h1 : PrimitiveMeanOverWords D large₂ u u' C' Cl Cg cb Cu cT CT C0 A A1) (hdet : GramDeterminantIsNatural D u) (hproj : SublatticeFGProjectiveRankLe D u) :
    QuadrupleMeanBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A A1 := by
  classical
  unfold QuadrupleMeanBound
  intro hH F0 hF0e hF0z what₂ hrows s hs hsk De hDe HH hHH
  have hC := h1
  unfold PrimitiveMeanOverWords at hC
  have hC' := hC hH F0 hF0e hF0z what₂ hrows s hs hsk
  unfold MeanLe at hC' ⊢
  have hf := c3sub_f_pos D
  have hNT := c3sub_NT_ge D u
  have hDe0 : 0 ≤ De := by linarith
  have hb0 : 0 ≤ large₂.sc.b := by
    unfold Scale.b
    first
      | positivity
      | exact le_of_lt (lt_trans zero_lt_one large₂.sc.one_lt_alt)
      | exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one large₂.sc.one_lt_alt)) _
  have hHH0 : 0 ≤ HH := le_trans (by unfold Hb; exact Real.rpow_nonneg hb0 _) hHH
  have hXi : 0 ≤ XiS D u HH A1 s := c3sub_Xi_nonneg D u HH A1 hA hHH0 s
  have hIS : ∀ n ∈ indexBox De, n ∈ Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 ⌊De⌋₊) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    refine ⟨hn.1 i, ?_⟩
    apply Nat.le_floor
    have hle : n i ≤ ∏ j, n j := Finset.single_le_prod' (fun j _ => hn.1 j) (Finset.mem_univ i)
    have hle' : ((n i : ℕ) : ℝ) ≤ ((∏ j, n j : ℕ) : ℝ) := by exact_mod_cast hle
    linarith [hn.2]
  have hfin : (indexBox De).Finite :=
    (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 ⌊De⌋₊)).finite_toSet.subset (fun n hn => hIS n hn)
  have hcard : (hfin.toFinset.card : ℝ) ≤ De ^ 4 := by
    have h1' : hfin.toFinset.card ≤ ⌊De⌋₊ ^ 4 := by
      calc hfin.toFinset.card ≤ (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 ⌊De⌋₊)).card := by
            apply Finset.card_le_card
            intro n hn
            exact hIS n (hfin.mem_toFinset.mp hn)
        _ = ⌊De⌋₊ ^ 4 := by simp [Fintype.card_piFinset]
    have h2' : (⌊De⌋₊ : ℝ) ≤ De := Nat.floor_le hDe0
    calc (hfin.toFinset.card : ℝ) ≤ ((⌊De⌋₊ ^ 4 : ℕ) : ℝ) := by exact_mod_cast h1'
      _ = (⌊De⌋₊ : ℝ) ^ 4 := by push_cast; ring
      _ ≤ De ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) h2' 4
  have hΛ : ∀ Λ ∈ what₂, (((sublatticeQuadruples D (L0X D Λ (lf D F0)) s De).encard : ℕ∞) : ℝ≥0∞) ≤
      ∑ n ∈ hfin.toFinset, ((cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞) *
        (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) := by
    intro Λ hΛr
    have hrl : IsRowLat D F0 Λ := hrows.1 Λ hΛr
    have hP := hproj F0 hF0e hF0z Λ hrl
    have hd := hdet F0 hF0e hF0z Λ hrl
    calc (((sublatticeQuadruples D (L0X D Λ (lf D F0)) s De).encard : ℕ∞) : ℝ≥0∞)
        ≤ ∑ n ∈ hfin.toFinset, (((latticeQuadruples D (L0X D Λ (lf D F0)) s n).encard : ℕ∞) : ℝ≥0∞) :=
          c3sub_encard_cover hfin.toFinset _ _ (c3sub_cover D _ hd s De hfin)
      _ ≤ ∑ n ∈ hfin.toFinset, ((cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞) *
            (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) := by
          apply Finset.sum_le_sum
          intro n hn
          exact c3sub_Qn_le D _ hP s n (hfin.mem_toFinset.mp hn).1
  have hmain : ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
        (((sublatticeQuadruples D (L0X D Λ (lf D F0)) s De).encard : ℕ∞) : ℝ≥0∞)
      ≤ ∑ n ∈ hfin.toFinset, (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) *
          ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
            ((cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞) := by
    calc ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
          (((sublatticeQuadruples D (L0X D Λ (lf D F0)) s De).encard : ℕ∞) : ℝ≥0∞)
        ≤ ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
            ∑ n ∈ hfin.toFinset, ((cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞) *
              (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) := by
          apply Finset.sum_le_sum
          intro Λ hΛr
          exact mul_le_mul_of_nonneg_left (hΛ Λ hΛr) zero_le
      _ = ∑ n ∈ hfin.toFinset, (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) *
            ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
              ((cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro n _
          apply Finset.sum_congr rfl
          intro Λ _
          ring
  have hR0 : 0 ≤ (De / NT D u) ^ D.R.k * (De * NT D u) ^ (A1 * ((s : ℝ) + cF D.R.f)) * De ^ (cF D.R.f) *
      XiS D u HH A1 s :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (div_nonneg hDe0 (by linarith)) _)
      (Real.rpow_nonneg (mul_nonneg hDe0 (by linarith)) _)) (Real.rpow_nonneg hDe0 _)) hXi
  have hstep : ∀ n ∈ hfin.toFinset, (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) *
        ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
          ((cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞)
      ≤ (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal
          ((De / NT D u) ^ D.R.k * (De * NT D u) ^ (A1 * ((s : ℝ) + cF D.R.f)) * De ^ (cF D.R.f) *
            XiS D u HH A1 s) := by
    intro n hn
    have hnI := hfin.mem_toFinset.mp hn
    have hc := hC' (n 0) (hnI.1 0) HH hHH
    have hP0 : (0:ℝ) ≤ (n 1 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f) *
        ((n 2 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f) * (n 3 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f)) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have hB : levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3)) =
        ENNReal.ofReal ((n 1 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f) *
          ((n 2 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f) * (n 3 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f))) := by
      unfold levelWeight
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    calc (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) *
          ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
            ((cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) (n 0) : ℕ∞) : ℝ≥0∞)
        ≤ (levelWeight D (n 1) * (levelWeight D (n 2) * levelWeight D (n 3))) *
            ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal
              (((n 0 : ℝ) / NT D u) ^ D.R.k * ((n 0 : ℝ) * NT D u) ^ (A1 * ↑s + A1 * Real.log ↑D.R.f) *
                XiS D u HH A1 s)) :=
          mul_le_mul_of_nonneg_left hc zero_le
      _ = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) *
            (ENNReal.ofReal ((n 1 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f) *
              ((n 2 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f) * (n 3 : ℝ) ^ ((D.R.k : ℝ) + lg2f D.R.f))) *
            ENNReal.ofReal
              (((n 0 : ℝ) / NT D u) ^ D.R.k * ((n 0 : ℝ) * NT D u) ^ (A1 * ↑s + A1 * Real.log ↑D.R.f) *
                XiS D u HH A1 s)) := by
          rw [hB]
          ring
      _ ≤ (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal
            ((De / NT D u) ^ D.R.k * (De * NT D u) ^ (A1 * ((s : ℝ) + cF D.R.f)) * De ^ (cF D.R.f) *
              XiS D u HH A1 s) := by
          apply mul_le_mul_of_nonneg_left _ zero_le
          rw [← ENNReal.ofReal_mul hP0]
          exact ENNReal.ofReal_le_ofReal
            (c3sub_num D.R.k D.R.f s A1 De (NT D u) (XiS D u HH A1 s) n hnI.1 hnI.2 hf hA hNT hXi)
  have hDe4 : De ^ (cF D.R.f + 4) = De ^ (cF D.R.f) * De ^ 4 := by
    rw [Real.rpow_add (by linarith : (0:ℝ) < De)]
    congr 1
    exact_mod_cast Real.rpow_natCast De 4
  have hcardE : (hfin.toFinset.card : ℝ≥0∞) ≤ ENNReal.ofReal (De ^ 4) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  refine le_trans hmain (le_trans (Finset.sum_le_sum hstep) ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  calc (hfin.toFinset.card : ℝ≥0∞) * ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal
          ((De / NT D u) ^ D.R.k * (De * NT D u) ^ (A1 * ((s : ℝ) + cF D.R.f)) * De ^ (cF D.R.f) *
            XiS D u HH A1 s))
      ≤ ENNReal.ofReal (De ^ 4) * ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal
          ((De / NT D u) ^ D.R.k * (De * NT D u) ^ (A1 * ((s : ℝ) + cF D.R.f)) * De ^ (cF D.R.f) *
            XiS D u HH A1 s)) := mul_le_mul_of_nonneg_right hcardE zero_le
    _ = (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal
          ((De / NT D u) ^ D.R.k * (De * NT D u) ^ (A1 * ((s : ℝ) + cF D.R.f)) * De ^ (cF D.R.f + 4) *
            XiS D u HH A1 s) := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ De ^ 4), hDe4]
        congr 2
        ring

end Main

section Inv

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem c3sub_dual_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual h (Formalism.HermitianLatticesTheory.gmap γ M) = Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.dual h M) := by
  have hiso : ∀ x y : V, h (γ x) (γ y) = h x y := fun x y => hγ x y
  ext x
  unfold Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.dual E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨γ.symm x, ?_, by simp⟩
    intro m hm
    have hm' := hx (γ m) ⟨m, hm, rfl⟩
    simpa [← hiso m (γ.symm x)] using hm'
  · rintro ⟨z, hz, rfl⟩ y ⟨m, hm, rfl⟩
    have hm' := hz m hm
    simpa [hiso] using hm'

theorem c3sub_span_gmap (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    (Submodule.span K ((Formalism.HermitianLatticesTheory.gmap γ M : Submodule (𝓞 K) V) : Set V)).restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap γ ((Submodule.span K (M : Set V)).restrictScalars (𝓞 K)) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  have key : Submodule.span K (⇑(LinearMap.restrictScalars (𝓞 K) (γ : V →ₗ[K] V)) '' (M : Set V)) =
      (Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V) :=
    Submodule.span_image (γ : V →ₗ[K] V)
  ext x
  rw [Submodule.restrictScalars_mem, Submodule.map_coe, key]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩

theorem c3sub_gmap_inf (γ : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap γ (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap γ A ⊓ Formalism.HermitianLatticesTheory.gmap γ B := by
  unfold Formalism.HermitianLatticesTheory.gmap
  exact Submodule.map_inf _ (fun x y hxy => γ.injective hxy)

theorem c3sub_latDetH_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (M : Submodule (𝓞 K) V) : latDetH h (Formalism.HermitianLatticesTheory.gmap γ M) = latDetH h M := by
  have h1 : dualInH h (Formalism.HermitianLatticesTheory.gmap γ M) = Formalism.HermitianLatticesTheory.gmap γ (dualInH h M) := by
    unfold dualInH
    rw [c3sub_dual_gmap h γ hγ, c3sub_span_gmap, c3sub_gmap_inf]
  unfold latDetH genIdxH
  rw [h1]
  congr 1
  refine finprod_congr fun P => ?_
  have := P.isPrime
  congr 1
  unfold Formalism.HermitianLatticesTheory.gmap
  exact Formalism.EigenvalueLevelCeiling.idxRules_lidx_map P.asIdeal (γ : V →ₗ[K] V) γ.injective _ _

theorem c3sub_prim_maps (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) :
    cntPrim h L j de ≤ cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  classical
  have hinj : Function.Injective (Formalism.HermitianLatticesTheory.gmap γ : Submodule (𝓞 K) V → Submodule (𝓞 K) V) := by
    intro A B hAB
    have hAB' : Submodule.map (LinearMap.restrictScalars (𝓞 K) (γ : V →ₗ[K] V)) A =
        Submodule.map (LinearMap.restrictScalars (𝓞 K) (γ : V →ₗ[K] V)) B := hAB
    have hfi : Function.Injective (LinearMap.restrictScalars (𝓞 K) (γ : V →ₗ[K] V)) :=
      fun x y hxy => γ.injective hxy
    exact Submodule.map_injective_of_injective hfi hAB'
  have hsub : Formalism.HermitianLatticesTheory.gmap γ '' PrimSubs h L j de ⊆ PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
    rintro _ ⟨M, hM, rfl⟩
    unfold PrimSubs at hM ⊢
    unfold IsPrimitiveSub at hM ⊢
    simp only [Set.mem_setOf_eq] at hM ⊢
    obtain ⟨⟨hle, heq⟩, hrk, hdet⟩ := hM
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact Submodule.map_mono hle
    · rw [c3sub_span_gmap, ← c3sub_gmap_inf, ← heq]
    · have key : Submodule.span K ((Formalism.HermitianLatticesTheory.gmap γ M : Submodule (𝓞 K) V) : Set V) =
          (Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V) := by
        unfold Formalism.HermitianLatticesTheory.gmap
        rw [Submodule.map_coe]
        exact Submodule.span_image (γ : V →ₗ[K] V)
      rw [key, LinearEquiv.finrank_map_eq]
      exact hrk
    · rw [c3sub_latDetH_gmap h γ hγ]
      exact hdet
  unfold cntPrim
  calc (PrimSubs h L j de).encard = (Formalism.HermitianLatticesTheory.gmap γ '' PrimSubs h L j de).encard :=
        (Set.InjOn.encard_image (fun a _ b _ hab => hinj hab)).symm
    _ ≤ (PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de).encard := Set.encard_le_encard hsub

theorem c3sub_prim_inv (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) :
    cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de = cntPrim h L j de := by
  have hiso : ∀ x y : V, h (γ x) (γ y) = h x y := fun x y => hγ x y
  have hs : γ.symm ∈ Formalism.HermitianLatticesTheory.isom h := by
    show ∀ x y : V, h (γ.symm x) (γ.symm y) = h x y
    intro x y
    have e := hiso (γ.symm x) (γ.symm y)
    simp only [LinearEquiv.apply_symm_apply] at e
    exact e.symm
  have hback : Formalism.HermitianLatticesTheory.gmap γ.symm (Formalism.HermitianLatticesTheory.gmap γ L) = L := by
    unfold Formalism.HermitianLatticesTheory.gmap
    ext x
    simp [Submodule.mem_map]
  apply le_antisymm
  · have hle := c3sub_prim_maps h γ.symm hs (Formalism.HermitianLatticesTheory.gmap γ L) j de
    rwa [hback] at hle
  · exact c3sub_prim_maps h γ hγ L j de

end Inv

section Mean

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def GenusMassPositive (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ Λ : LatV D, IsRowLat D F0 Λ →
    0 < Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0))

theorem genus_mass_pos_of_mass_lower_bound {C' Cl Cg cb Cu cT CT C0 A : ℝ} (h3 : VanishingOnXAndXPlusMass.PointsLemma D u) :
    GenusMassPositive D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  intro hH F0 he hz what₂ hrows Λ hΛ
  obtain ⟨_, hp, _, h3T, _, hsp, _⟩ := hH.2.1
  have h := ((h3 hp h3T hsp F0 he hz what₂ hrows).2 Λ hΛ).2
  refine lt_of_lt_of_le ?_ h
  have h1 := Formalism.MainNotions.BridgeLemma.massS_pos D D.R.k
  have h2 := c3sub_NT_ge D u
  positivity

theorem mean_comparison_of_genus_mass_pos {C' Cl Cg cb Cu cT CT C0 A A1 : ℝ}
    (hC1 : UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A A1) (hM : MeanOverWordsEqGenus D u)
    (hpos : GenusMassPositive D large₂ u u' C' Cl Cg cb Cu cT CT C0 A) :
    PrimitiveMeanOverWords D large₂ u u' C' Cl Cg cb Cu cT CT C0 A A1 := by
  intro hH F0 he hz what₂ hrows s hs2 hsk de hde HH hHH
  unfold MeanLe
  rcases what₂.eq_empty_or_nonempty with h0 | ⟨Λ₀, hΛ₀⟩
  · simp [h0]
  have hrow0 := hrows.1 Λ₀ hΛ₀
  have hm := hpos hH F0 he hz what₂ hrows Λ₀ hrow0
  have hex : ∃ reps, Formalism.ThetaLiftIndependence.IsClassReps (D.sp.X 0).hT (L0X D Λ₀ (lf D F0)) reps := by
    by_contra hno
    unfold Formalism.HermitianLatticesTheory.mass at hm
    rw [dif_neg hno] at hm
    exact lt_irrefl _ hm
  obtain ⟨reps, hreps⟩ := hex
  have hMG := hM hH.2.1.2.1 hH.2.1.2.2.2.1 hH.2.1.2.2.2.2.2.1 F0 he hz what₂ hrows Λ₀ hrow0 reps hreps
    (fun L => cntPrim (D.sp.X 0).hT L (D.R.k - s) de)
    (fun γ hγ L => c3sub_prim_inv (D.sp.X 0).hT γ hγ L _ _)
  have hc := hC1 hH F0 he hz Λ₀ hrow0 reps hreps s hs2 hsk de hde HH hHH
  set c : ℝ≥0∞ := ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ₀ (lf D F0))) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]; exact (ENNReal.ofReal_pos.2 hm).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_mul hm.le] at hc
  set a : ℝ≥0∞ := ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
    ((cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - s) de : ℕ∞) : ℝ≥0∞) with ha
  have key : a * c ≤ ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal
      (((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (A1 * s + A1 * Real.log D.R.f) * XiS D u HH A1 s)) * c := by
    rw [hMG]
    calc _ ≤ (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * (c * ENNReal.ofReal
          (((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (A1 * s + A1 * Real.log D.R.f) * XiS D u HH A1 s)) := by
          gcongr
      _ = _ := by ring
  set bR : ℝ≥0∞ := (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) * ENNReal.ofReal
      (((de : ℝ) / NT D u) ^ D.R.k * ((de : ℝ) * NT D u) ^ (A1 * s + A1 * Real.log D.R.f) * XiS D u HH A1 s) with hbR
  calc a = a * c * c⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel hc0 hcT, mul_one]
    _ ≤ bR * c * c⁻¹ := by gcongr
    _ = bR := by rw [mul_assoc, ENNReal.mul_inv_cancel hc0 hcT, mul_one]

end Mean

end Formalism.MainNotions.BridgeLemma₂

end
