import Formalism.GradedWeylDivisibility.FinalD
import Formalism.ThetaLogCoordinates.ResidueClassEstimates.FinalT
import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
import Formalism.SharpRestriction.GrowthBounds.ProjectionLemmaBaseLevel
import Formalism.SharpRestriction.GrowthBounds.ColumnSystems

open Finset

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.GelfandTsetlinBases

def Intl {K N : ℕ} (f : Fin K → Fin N → ℕ) : Prop :=
  ∀ l j : Fin N, j.val = l.val + 1 → ∀ a : Fin K, (∑ b : Fin K with b ≤ a, f b j) ≤ ∑ b : Fin K with b < a, f b l

def SSZ (k : ℕ) (κ : Fin k → ℤ) : Type :=
  {g : Fin k → Fin k → ℕ // Intl g ∧ ∀ t, ((∑ a, g a t : ℕ) : ℤ) = κ t}

theorem sum_le_castSucc {k : ℕ} (F : Fin (k + 1) → ℕ) (a : Fin k) :
    (∑ b : Fin (k + 1) with b ≤ a.castSucc, F b) = ∑ b : Fin k with b ≤ a, F b.castSucc := by
  have h : ¬ (Fin.last k ≤ a.castSucc) := not_le.mpr (Fin.castSucc_lt_last a)
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc, if_neg h, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i ≤ a
  · rw [if_pos hi, if_pos (Fin.castSucc_le_castSucc_iff.mpr hi)]
  · rw [if_neg hi, if_neg (fun h' => hi (Fin.castSucc_le_castSucc_iff.mp h'))]

theorem sum_lt_castSucc {k : ℕ} (F : Fin (k + 1) → ℕ) (a : Fin k) :
    (∑ b : Fin (k + 1) with b < a.castSucc, F b) = ∑ b : Fin k with b < a, F b.castSucc := by
  have h : ¬ (Fin.last k < a.castSucc) := not_lt.mpr (Fin.castSucc_lt_last a).le
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc, if_neg h, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i < a
  · rw [if_pos hi, if_pos (Fin.castSucc_lt_castSucc_iff.mpr hi)]
  · rw [if_neg hi, if_neg (fun h' => hi (Fin.castSucc_lt_castSucc_iff.mp h'))]

theorem sum_le_last {k : ℕ} (F : Fin (k + 1) → ℕ) :
    (∑ b : Fin (k + 1) with b ≤ Fin.last k, F b) = ∑ b, F b := by
  rw [Finset.filter_true_of_mem (fun b _ => Fin.le_last b)]

theorem sum_lt_last {k : ℕ} (F : Fin (k + 1) → ℕ) :
    (∑ b : Fin (k + 1) with b < Fin.last k, F b) = ∑ b : Fin k, F b.castSucc := by
  rw [Finset.sum_filter, Fin.sum_univ_castSucc, if_neg (lt_irrefl _), add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [if_pos (Fin.castSucc_lt_last i)]

theorem intl_zero {K N : ℕ} (f : Fin K → Fin N → ℕ) (hf : Intl f) :
    ∀ (tv : ℕ) (t : Fin N), t.val = tv → ∀ a : Fin K, a.val < tv → f a t = 0 := by
  intro tv
  induction tv with
  | zero => intro t _ a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ m ih =>
    intro t ht a ha
    have hm : m < N := by have := t.isLt; omega
    have key := hf ⟨m, hm⟩ t (by exact ht) a
    have h0 : (∑ b : Fin K with b < a, f b ⟨m, hm⟩) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [Finset.mem_filter] at hb
      exact ih ⟨m, hm⟩ rfl b (by have := hb.2; rw [Fin.lt_def] at this; omega)
    rw [h0, Nat.le_zero, Finset.sum_eq_zero_iff] at key
    exact key a (by simp)

def restr {k : ℕ} (f : Fin (k + 1) → Fin (k + 1) → ℕ) : Fin k → Fin k → ℕ := fun a t => f a.castSucc t.castSucc

def UU (k : ℕ) (μ : Fin (k + 1) → ℤ) : Type :=
  {g : Fin k → Fin k → ℕ // Intl g ∧ (fun t => ((∑ a, g a t : ℕ) : ℤ)) ∈ gtBox μ}

theorem mem_gtBox' {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ : Fin n → ℤ) :
    κ ∈ gtBox μ ↔ ∀ i, μ i.succ ≤ κ i ∧ κ i ≤ μ i.castSucc := by
  rw [show gtBox μ = Fintype.piFinset fun i => Finset.Icc (μ i.succ) (μ i.castSucc) from rfl,
    Fintype.mem_piFinset]
  simp only [Finset.mem_Icc]

theorem restr_mem {k : ℕ} (μ : Fin (k + 1) → ℤ) (f : SSZ (k + 1) μ) :
    Intl (restr f.1) ∧ (fun t => ((∑ a, restr f.1 a t : ℕ) : ℤ)) ∈ gtBox μ := by
  constructor
  · intro l j hlj a
    have := f.2.1 l.castSucc j.castSucc (by simpa using hlj) a.castSucc
    rw [sum_le_castSucc, sum_lt_castSucc] at this
    exact this
  · rw [mem_gtBox']
    intro i
    have hs1 := f.2.2 i.castSucc
    have hs2 := f.2.2 i.succ
    have hI := f.2.1 i.castSucc i.succ (by simp) (Fin.last k)
    rw [sum_le_last, sum_lt_last] at hI
    rw [Fin.sum_univ_castSucc] at hs1
    simp only [restr]
    constructor
    · rw [← hs2]; exact_mod_cast hI
    · rw [← hs1]; exact_mod_cast Nat.le_add_right _ _

def rho {k : ℕ} (μ : Fin (k + 1) → ℤ) (f : SSZ (k + 1) μ) : UU k μ := ⟨restr f.1, restr_mem μ f⟩

theorem rho_inj {k : ℕ} (μ : Fin (k + 1) → ℤ) : Function.Injective (rho μ) := by
  intro f g h
  have hr : restr f.1 = restr g.1 := congrArg Subtype.val h
  have hcol : ∀ t : Fin (k + 1), ∀ a : Fin k, f.1 a.castSucc t = g.1 a.castSucc t := by
    intro t a
    induction t using Fin.lastCases with
    | last =>
      rw [intl_zero f.1 f.2.1 k (Fin.last k) rfl a.castSucc (by rw [Fin.coe_castSucc]; exact a.isLt),
        intl_zero g.1 g.2.1 k (Fin.last k) rfl a.castSucc (by rw [Fin.coe_castSucc]; exact a.isLt)]
    | cast t => exact congrFun (congrFun hr a) t
  apply Subtype.ext
  funext a t
  induction a using Fin.lastCases with
  | cast a => exact hcol t a
  | last =>
    have e1 := f.2.2 t
    have e2 := g.2.2 t
    rw [Fin.sum_univ_castSucc] at e1 e2
    have hs : (∑ a : Fin k, f.1 a.castSucc t) = ∑ a : Fin k, g.1 a.castSucc t :=
      Finset.sum_congr rfl (fun a _ => hcol t a)
    rw [hs] at e1
    have h4 : (∑ a : Fin k, g.1 a.castSucc t) + f.1 (Fin.last k) t =
        (∑ a : Fin k, g.1 a.castSucc t) + g.1 (Fin.last k) t := by exact_mod_cast e1.trans e2.symm
    omega

def ext {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) : Fin (k + 1) → Fin (k + 1) → ℕ :=
  fun a t => Fin.lastCases (motive := fun _ => ℕ)
    (Fin.lastCases (motive := fun _ => ℕ) (μ (Fin.last k)).toNat
      (fun t' => (μ t'.castSucc - ((∑ b, g b t' : ℕ) : ℤ)).toNat) t)
    (fun a' => Fin.lastCases (motive := fun _ => ℕ) 0 (fun t' => g a' t') t) a

theorem ext_cc {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (a t : Fin k) :
    ext μ g a.castSucc t.castSucc = g a t := by
  simp only [Formalism.L2.G.Model.ext, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem ext_cl {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (a : Fin k) :
    ext μ g a.castSucc (Fin.last k) = 0 := by
  simp only [Formalism.L2.G.Model.ext, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem ext_lc {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) (t : Fin k) :
    ext μ g (Fin.last k) t.castSucc = (μ t.castSucc - ((∑ b, g b t : ℕ) : ℤ)).toNat := by
  simp only [Formalism.L2.G.Model.ext, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem ext_ll {k : ℕ} (μ : Fin (k + 1) → ℤ) (g : Fin k → Fin k → ℕ) :
    ext μ g (Fin.last k) (Fin.last k) = (μ (Fin.last k)).toNat := by
  simp only [Formalism.L2.G.Model.ext, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem ext_sum {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) (g : UU k μ) (t : Fin (k + 1)) :
    ((∑ a, ext μ g.1 a t : ℕ) : ℤ) = μ t := by
  induction t using Fin.lastCases with
  | last =>
    rw [Fin.sum_univ_castSucc]
    simp only [ext_cl, ext_ll, Finset.sum_const_zero, zero_add]
    exact Int.toNat_of_nonneg hμ
  | cast t =>
    rw [Fin.sum_univ_castSucc]
    simp only [ext_cc, ext_lc]
    have hb : ((∑ b, g.1 b t : ℕ) : ℤ) ≤ μ t.castSucc := ((mem_gtBox' μ _).1 g.2.2 t).2
    have hnn : 0 ≤ μ t.castSucc - ((∑ b, g.1 b t : ℕ) : ℤ) := by linarith
    rw [Nat.cast_add, Int.toNat_of_nonneg hnn]
    ring

theorem ext_intl {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) (g : UU k μ) : Intl (ext μ g.1) := by
  intro l j hlj a
  have hl : l.val < k := by have := j.isLt; omega
  obtain ⟨l', rfl⟩ : ∃ l' : Fin k, l'.castSucc = l := ⟨⟨l.val, hl⟩, rfl⟩
  induction a using Fin.lastCases with
  | last =>
    rw [sum_le_last, sum_lt_last]
    simp only [ext_cc]
    have hj : j = l'.succ := Fin.ext (by rw [Fin.val_succ, hlj, Fin.coe_castSucc])
    have h1 := ext_sum μ hμ g j
    have h2 : μ j ≤ ((∑ b, g.1 b l' : ℕ) : ℤ) := by rw [hj]; exact ((mem_gtBox' μ _).1 g.2.2 l').1
    have h3 : ((∑ b, ext μ g.1 b j : ℕ) : ℤ) ≤ ((∑ b, g.1 b l' : ℕ) : ℤ) := by rw [h1]; exact h2
    exact_mod_cast h3
  | cast a =>
    rw [sum_le_castSucc, sum_lt_castSucc]
    induction j using Fin.lastCases with
    | last => simp [ext_cl]
    | cast j =>
      simp only [ext_cc]
      exact g.2.1 l' j (by simpa using hlj) a

theorem rho_surj {k : ℕ} (μ : Fin (k + 1) → ℤ) (hμ : 0 ≤ μ (Fin.last k)) : Function.Surjective (rho μ) := by
  intro g
  refine ⟨⟨ext μ g.1, ext_intl μ hμ g, fun t => ext_sum μ hμ g t⟩, ?_⟩
  apply Subtype.ext
  funext a t
  exact ext_cc μ g.1 a t

theorem SSZ_finite (k : ℕ) (κ : Fin k → ℤ) : Finite (SSZ k κ) := by
  have hb : ∀ g : SSZ k κ, ∀ a t, g.1 a t < (∑ t, (κ t).toNat) + 1 := by
    intro g a t
    have h1 : g.1 a t ≤ ∑ a', g.1 a' t :=
      Finset.single_le_sum (f := fun a' => g.1 a' t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    have e := g.2.2 t
    have hnn : 0 ≤ κ t := by rw [← e]; positivity
    have e2 : (((κ t).toNat : ℕ) : ℤ) = κ t := Int.toNat_of_nonneg hnn
    have h2 : (∑ a', g.1 a' t) = (κ t).toNat := by exact_mod_cast e.trans e2.symm
    have h3 : (κ t).toNat ≤ ∑ t', (κ t').toNat :=
      Finset.single_le_sum (f := fun t' => (κ t').toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    omega
  exact Finite.of_injective
    (fun g : SSZ k κ => fun a t => (⟨g.1 a t, hb g a t⟩ : Fin ((∑ t, (κ t).toNat) + 1)))
    (fun g h e => Subtype.ext (funext fun a => funext fun t =>
      congrArg Fin.val (congrFun (congrFun e a) t)))

def fibEquiv {k : ℕ} (μ : Fin (k + 1) → ℤ) : UU k μ ≃ Σ κ : ↥(gtBox μ), SSZ k κ.1 where
  toFun g := ⟨⟨_, g.2.2⟩, ⟨g.1, g.2.1, fun _ => rfl⟩⟩
  invFun x := ⟨x.2.1, x.2.2.1, by
    have : (fun t => ((∑ a, x.2.1 a t : ℕ) : ℤ)) = x.1.1 := funext x.2.2.2
    rw [this]; exact x.1.2⟩
  left_inv g := rfl
  right_inv x := by
    obtain ⟨⟨κ, hκ⟩, ⟨g, hI, hs⟩⟩ := x
    have : (fun t => ((∑ a, g a t : ℕ) : ℤ)) = κ := funext hs
    subst this
    rfl

theorem card_SSZ : ∀ (k : ℕ) (κ : Fin k → ℤ), (∀ t, 0 ≤ κ t) → Nat.card (SSZ k κ) = dGT k κ := by
  intro k
  induction k with
  | zero =>
    intro κ _
    simp only [dGT]
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext (funext fun a => a.elim0)⟩,
      ⟨⟨fun a => a.elim0, fun l => l.elim0, fun t => t.elim0⟩⟩⟩
  | succ k ih =>
    intro μ hμ
    rw [Nat.card_congr (Equiv.ofBijective (rho μ) ⟨rho_inj μ, rho_surj μ (hμ _)⟩),
      Nat.card_congr (fibEquiv μ)]
    haveI : ∀ κ : ↥(gtBox μ), Finite (SSZ k κ.1) := fun κ => SSZ_finite k κ.1
    rw [Nat.card_sigma]
    simp only [dGT]
    rw [← Finset.sum_coe_sort (gtBox μ)]
    refine Finset.sum_congr rfl (fun κ _ => ih κ.1 (fun t => ?_))
    have h1 := ((mem_gtBox' μ κ.1).1 κ.2 t).1
    have h2 := hμ t.succ
    linarith

def ssEquiv (k : ℕ) (ν : Fin k → ℕ) : ↥(ssIdx k k ν) ≃ SSZ k (fun t => (ν t : ℤ)) :=
  Equiv.subtypeEquiv (Finsupp.equivFunOnFinite.trans (Equiv.curry (Fin k) (Fin k) ℕ)) (by
    intro m
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun l j hlj a => ?_, fun t => ?_⟩
      · have := h1 l j hlj a
        rw [zero_add] at this
        exact this
      · exact congrArg Nat.cast (h2 t)
    · rintro ⟨h1, h2⟩
      refine ⟨fun l j hlj a => ?_, fun t => ?_⟩
      · rw [zero_add]
        exact h1 l j hlj a
      · exact Nat.cast_injective (R := ℤ) (h2 t))

theorem card_ssIdx (k : ℕ) (ν : Fin k → ℕ) : Nat.card ↥(ssIdx k k ν) = dGT k (fun t => (ν t : ℤ)) := by
  rw [Nat.card_congr (ssEquiv k ν)]
  exact card_SSZ k _ (fun t => by simp)

theorem finrank_dualWeyl (K : Type) [Field K] (k : ℕ) (ν : Fin k → ℕ) :
    Module.finrank K (dualWeyl K k k ν) = dGT k (fun t => (ν t : ℤ)) := by
  obtain ⟨b, hb, -⟩ := Formalism.GradedWeylDivisibility.sSBasis K k k ν
  haveI : Fintype ↥(ssIdx k k ν) := (Formalism.GradedWeylDivisibility.sSIdxFinite k k ν).fintype
  rw [← hb.2.1, finrank_span_eq_card hb.1, ← Nat.card_eq_fintype_card, card_ssIdx]

theorem prodConv (n : ℕ) (F : ℕ → ℕ → ℝ) :
    ∏ j ∈ range n, ∏ i ∈ range j, F i j = ∏ i : Fin n, ∏ j : Fin n, if i < j then F i j else 1 := by
  conv_rhs => rw [Finset.prod_comm]
  rw [← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, F i j)]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have key : ∀ i : Fin n, (if i < j then F ↑i ↑j else 1) = (if (i : ℕ) < (j : ℕ) then F ↑i ↑j else 1) := by
    intro i
    by_cases h : i < j
    · rw [if_pos h, if_pos (Fin.lt_iff_val_lt_val.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (Fin.lt_iff_val_lt_val.mpr h'))]
  rw [Finset.prod_congr rfl (fun i _ => key i),
    Fin.prod_univ_eq_prod_range (fun m => if m < (j : ℕ) then F m ↑j else 1) n, ← Finset.prod_filter]
  congr 1
  ext m
  simp only [Finset.mem_range, Finset.mem_filter]
  have := j.isLt
  constructor <;> intro h <;> omega

theorem weylQ (n : ℕ) (μ : Fin n → ℤ) (hμ : Antitone μ) :
    ((dGT n μ : ℕ) : ℚ) = ∏ i : Fin n, ∏ j : Fin n,
      if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 := by
  have h := Formalism.InvariantFactorPaths.BranchingDimensions.Top.weylGT n μ hμ
  change ∏ j ∈ range n, ∏ i ∈ range j,
      (((Formalism.InvariantFactorPaths.BranchingDimensions.extW μ i - Formalism.InvariantFactorPaths.BranchingDimensions.extW μ j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)) = _ at h
  have h2 := prodConv n (fun i j => (((Formalism.InvariantFactorPaths.BranchingDimensions.extW μ i - Formalism.InvariantFactorPaths.BranchingDimensions.extW μ j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ)))
  rw [h2] at h
  have he : ∀ i : Fin n, Formalism.InvariantFactorPaths.BranchingDimensions.extW μ (i : ℕ) = μ i := by
    intro i
    show (if h : (i : ℕ) < n then μ ⟨i, h⟩ else 0) = μ i
    rw [dif_pos i.2]
  simp only [he] at h
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [← h]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
  split_ifs
  · push_cast
    ring
  · rw [Rat.cast_one]

theorem weyl_dualWeyl (K : Type) [Field K] (n : ℕ) (nu : Fin n → ℕ) (h : Antitone nu) :
    (Module.finrank K (dualWeyl K n n nu) : ℚ) =
      ∏ i : Fin n, ∏ j : Fin n,
        if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1 := by
  rw [finrank_dualWeyl K n nu, weylQ n (fun t => (nu t : ℤ)) (fun a b hab => Nat.cast_le.mpr (h hab))]
  push_cast
  rfl

theorem weyl_dual_weight_admissible (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.ColumnSystems.adm3 D := by
  intro K _ _ n nu h
  exact weyl_dualWeyl K n nu h

theorem finrank_tensor' (Kf : Type) [Field Kf] (S : Type) [Fintype S] [DecidableEq S] (k n : ℕ)
    (ν : S → Fin n → ℕ) :
    Module.finrank Kf (tensorLat Kf Kf fun s => dualWeyl Kf k n (ν s)) =
      ∏ s, Module.finrank Kf (dualWeyl Kf k n (ν s)) := by
  choose b hb using fun s => Formalism.GradedWeylDivisibility.sSBasis Kf k n (ν s)
  haveI : ∀ s, Fintype ↥(ssIdx k n (ν s)) := fun s => (Formalism.GradedWeylDivisibility.sSIdxFinite k n (ν s)).fintype
  obtain ⟨hli, hsp⟩ := Formalism.GradedWeylDivisibility.tensorBasis Kf Kf S k n (fun s => ↥(ssIdx k n (ν s)))
    (fun s => dualWeyl Kf k n (ν s)) b (fun s => (hb s).1.1) (fun s => (hb s).1.2.1)
  rw [← hsp, finrank_span_eq_card hli, Fintype.card_pi]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [← (hb s).1.2.1, finrank_span_eq_card (hb s).1.1]

theorem lamAt_antitone' {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) (s : Fin n') :
    Antitone (lamAt lam0 s) := by
  intro a b hab
  unfold lamAt
  split_ifs with h
  · exact hdom s hab
  · have := hdom s (Fin.rev_le_rev.mpr hab)
    show -lam0 s b.rev ≤ -lam0 s a.rev
    linarith

theorem weylV_proved : Formalism.MainNotions.flipOneThree.WeylV := by
  intro Kf _ n' m lam0 hdom
  have hA : ∀ s, Antitone (lamAt lam0 s) := lamAt_antitone' lam0 hdom
  have hV : Vsp Kf lam0 = tensorLat Kf Kf fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) := by
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (hA s)]
  show ((Module.finrank Kf (Vsp Kf lam0) : ℕ) : ℚ) = _
  rw [hV, finrank_tensor', Nat.cast_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  have hmono : Antitone (nuOf (lamAt lam0 s)) := fun a b hab =>
    Int.toNat_le_toNat (by linarith [hA s hab])
  rw [weyl_dualWeyl Kf (m + 1) (nuOf (lamAt lam0 s)) hmono]
  have hnu : ∀ t, ((nuOf (lamAt lam0 s) t : ℕ) : ℚ) =
      ((lamAt lam0 s t : ℤ) : ℚ) - ((lamAt lam0 s (Fin.last m) : ℤ) : ℚ) := by
    intro t
    have h0 : 0 ≤ lamAt lam0 s t - lamAt lam0 s (Fin.last m) := sub_nonneg.mpr (hA s (Fin.le_last t))
    have h1 : ((nuOf (lamAt lam0 s) t : ℕ) : ℤ) = lamAt lam0 s t - lamAt lam0 s (Fin.last m) :=
      Int.toNat_of_nonneg h0
    exact_mod_cast h1
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
  split_ifs
  · rw [hnu, hnu]
    ring
  · rfl

theorem fewBadOrbits (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.tableLineDegreeFive.FewBadOrbits D := by
  exact weylV_proved

theorem gl_branching_dimension (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.ColumnSystems.adm2 D := by
  intro K _ _ n lam hlam
  simp only [finrank_dualWeyl]
  simp only [dGT]
  symm
  refine Finset.sum_nbij' (fun mu t => ((mu t : ℕ) : ℤ)) (fun κ t => (κ t).toNat) ?_ ?_ ?_ ?_ ?_
  · intro mu hmu
    rw [Finset.mem_filter] at hmu
    rw [mem_gtBox']
    intro i
    exact ⟨Nat.cast_le.mpr (hmu.2 i).1, Nat.cast_le.mpr (hmu.2 i).2⟩
  · intro κ hκ
    rw [mem_gtBox'] at hκ
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h1 := hκ i
      have h0 : lam i.castSucc ≤ lam 0 := hlam (Fin.zero_le _)
      rw [Finset.mem_range]
      try dsimp only at h1 ⊢
      omega
    · have h1 := hκ i
      try dsimp only at h1 ⊢
      omega
  · intro mu _
    funext t
    simp
  · intro κ hκ
    rw [mem_gtBox'] at hκ
    funext t
    have h1 := (hκ t).1
    try dsimp only at h1 ⊢
    omega
  · intro mu _
    rfl

end Formalism.L2.G.Model
