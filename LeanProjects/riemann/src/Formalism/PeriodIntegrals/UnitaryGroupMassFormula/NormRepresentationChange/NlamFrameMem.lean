import Mathlib
import Formalism.PeriodIntegrals.PairValDefs
import Formalism.PeriodIntegrals.NormRepChange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.Development

noncomputable section

open scoped Classical

namespace PI.NRCW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.PairValDefs Matrix

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem coefX_sum (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) : ∑ a, F.coefX y a • F.e a = y := by
  have h : y ∈ Submodule.span E (Set.range F.e) := hy
  have hc : ∀ a, F.coefX y a = F.e_indep.repr ⟨y, h⟩ a := fun a => by
    simp [FlagG.coefX, h]
  simp_rw [hc]
  have key := F.e_indep.linearCombination_repr ⟨y, h⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => by simp)] at key
  simpa using key

theorem coefX_eq_zero (F : FlagG S r T) {y : S.V} {b : ℕ} (hy : y ∈ F.Xa b) (a : Fin r) (ha : b ≤ a.val) :
    F.coefX y a = 0 := by
  have hy' : y ∈ Submodule.span E (F.e '' {i | i.1 < b}) := hy
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hy'
  have hX : Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e) :=
    Submodule.span_mono (Set.image_subset_range _ _) hy'
  have hrep : F.e_indep.repr ⟨_, hX⟩ = l := F.e_indep.repr_eq rfl
  have hc : F.coefX (Finsupp.linearCombination E F.e l) a = l a := by
    simp [FlagG.coefX, hX, hrep]
  rw [hc]
  by_contra hne
  have h2 : a.1 < b := hl (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
  omega

theorem e_mem_Xa (F : FlagG S r T) (i : Fin r) : F.e i ∈ F.Xa (i.val + 1) :=
  Submodule.subset_span ⟨i, Nat.lt_succ_self i.val, rfl⟩

theorem Xa_le_X (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem z_mem_orth (F : FlagG S r T) : F.z ∈ orth S F.X := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x (hx : x ∈ Submodule.span E (Set.range F.e))
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    exact F.z_orth a
  | zero => simp
  | add x w _ _ hx hw => simp [hx, hw]
  | smul c x _ hx => simp [hx]

theorem frame_castSucc (G : LFlag S r T) (i : Fin r) : frame G i.castSucc = G.fl.e i := by
  simp only [frame, FlagG.fvec, Fin.snoc_castSucc]

theorem frame_last (G : LFlag S r T) : frame G (Fin.last r) = G.fl.z := by
  simp only [frame, FlagG.fvec, Fin.snoc_last]

theorem nlam_frame_mem {Λ : Submodule (𝓞 E) S.V} (G : LFlag S r T) {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ G) :
    (∀ i : Fin r, n (G.fl.e i) - G.fl.e i ∈ G.fl.Xa i.val) ∧ n G.fl.z - G.fl.z ∈ G.fl.X := by
  obtain ⟨-, h1, h2⟩ := hn
  exact ⟨fun i => h1 i.val _ (e_mem_Xa G.fl i), h2 _ (z_mem_orth G.fl)⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepExp (D : D7) : StepExp D := by
  unfold StepExp
  intro Λ T G n hn
  obtain ⟨hE, hZ⟩ := nlam_frame_mem G hn

  have hmem : ∀ b : Fin (D.R.rS + 1), ∀ c : Fin D.R.rS, b.val ≤ c.val →
      G.fl.coefX (n (frame G b) - frame G b) c = 0 := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      intro c hc
      rw [Fin.val_last] at hc
      exact absurd c.is_lt (by omega)
    | cast i =>
      intro c hc
      rw [frame_castSucc]
      exact coefX_eq_zero G.fl (hE i) c (by rwa [Fin.coe_castSucc] at hc)
  have hX : ∀ b : Fin (D.R.rS + 1), n (frame G b) - frame G b ∈ G.fl.X := by
    intro b
    induction b using Fin.lastCases with
    | last => rw [frame_last]; exact hZ
    | cast i => rw [frame_castSucc]; exact Xa_le_X G.fl _ (hE i)
  have hfm : ∀ c b : Fin (D.R.rS + 1), b.val ≤ c.val →
      fmat D G n c b = if c = b then 1 else 0 := by
    intro c b hbc
    have h0 : (if h : c.val < D.R.rS then
        G.fl.coefX (n (frame G b) - frame G b) ⟨c.val, h⟩ else 0) = 0 := by
      split_ifs with h
      · exact hmem b ⟨c.val, h⟩ hbc
      · rfl
    simp only [fmat, h0, add_zero]
  refine ⟨fun i j => ⟨fun hji => ?_, fun hij => ?_⟩, fun b => ?_⟩
  · have hv := Fin.lt_iff_val_lt_val.1 hji
    rw [hfm i j (by omega), if_neg (ne_of_gt hji)]
  · subst hij
    rw [hfm i i le_rfl, if_pos rfl]
  · have hsum := coefX_sum G.fl (hX b)
    have h1 : ∀ i : Fin D.R.rS, fmat D G n i.castSucc b • frame G i.castSucc =
        (if i.castSucc = b then (1 : D.host.E) else 0) • frame G i.castSucc +
          G.fl.coefX (n (frame G b) - frame G b) i • G.fl.e i := by
      intro i
      have hc : (if h : (i.castSucc : Fin (D.R.rS + 1)).val < D.R.rS then
          G.fl.coefX (n (frame G b) - frame G b) ⟨(i.castSucc : Fin (D.R.rS + 1)).val, h⟩ else 0) =
            G.fl.coefX (n (frame G b) - frame G b) i := by
        rw [dif_pos (by simp)]
        rfl
      simp only [fmat, hc, add_smul, frame_castSucc]
    have h2 : fmat D G n (Fin.last _) b = if Fin.last _ = b then 1 else 0 := by
      simp [fmat]
    have h3 : ∑ c : Fin (D.R.rS + 1), (if c = b then (1 : D.host.E) else 0) • frame G c = frame G b := by
      simp [ite_smul]
    rw [Fin.sum_univ_castSucc] at h3
    rw [Fin.sum_univ_castSucc]
    simp_rw [h1, h2, Finset.sum_add_distrib, hsum]
    rw [add_right_comm, h3]
    abel

end PI.NRCW
