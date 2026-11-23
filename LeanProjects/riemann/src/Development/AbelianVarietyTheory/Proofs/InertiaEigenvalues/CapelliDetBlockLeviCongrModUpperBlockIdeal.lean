import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.CapHC

open Formalism.REAL

variable {A : Type} [Ring A] [Algebra ℂ A]

def upperSpan {r m : ℕ} (X : Fin (r + m) → Fin (r + m) → A) : Submodule ℂ A :=
  Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin m) (w : A), y = X (Fin.castAdd m p) (Fin.natAdd r q) * w}

theorem span_mul_right_mem {S : Set A} (hS : ∀ y ∈ S, ∀ a : A, y * a ∈ S) {x : A}
    (hx : x ∈ Submodule.span ℂ S) (a : A) : x * a ∈ Submodule.span ℂ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (hS y hy a)
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem levi_mul_mem {r m : ℕ} {X : Fin (r + m) → Fin (r + m) → A} (hX : GlRel X) (s t : Fin m)
    {y : A} (hy : y ∈ upperSpan X) : X (Fin.natAdd r s) (Fin.natAdd r t) * y ∈ upperSpan X := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, rfl⟩ := hy
    have h := hX (Fin.natAdd r s) (Fin.natAdd r t) (Fin.castAdd m p) (Fin.natAdd r q)
    have hne : Fin.natAdd r t ≠ Fin.castAdd m p := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    rw [if_neg hne] at h
    have h' : X (Fin.natAdd r s) (Fin.natAdd r t) * X (Fin.castAdd m p) (Fin.natAdd r q) =
        X (Fin.castAdd m p) (Fin.natAdd r q) * X (Fin.natAdd r s) (Fin.natAdd r t) +
          (0 - if Fin.natAdd r q = Fin.natAdd r s then X (Fin.castAdd m p) (Fin.natAdd r t) else 0) := by
      rw [← h]; abel
    rw [← mul_assoc, h', add_mul, mul_assoc]
    refine add_mem (Submodule.subset_span ⟨p, q, _, rfl⟩) ?_
    rw [zero_sub, neg_mul]
    refine neg_mem ?_
    split_ifs
    · exact Submodule.subset_span ⟨p, t, w, rfl⟩
    · rw [zero_mul]; exact zero_mem _
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem prod_mul_mem (J : Submodule ℂ A) : ∀ (k : ℕ) (g : Fin k → A),
    (∀ i, (∀ y ∈ J, g i * y ∈ J) ∨ (∀ y, g i * y ∈ J)) → (∃ i, ∀ y, g i * y ∈ J) →
    ∀ z, (List.ofFn g).prod * z ∈ J := by
  intro k
  induction k with
  | zero => intro g _ h; obtain ⟨i, _⟩ := h; exact i.elim0
  | succ k ih =>
    intro g hg h z
    obtain ⟨i, hi⟩ := h
    rw [List.ofFn_succ, List.prod_cons, mul_assoc]
    by_cases h0 : ∀ y, g 0 * y ∈ J
    · exact h0 _
    · have hp : ∀ y ∈ J, g 0 * y ∈ J := (hg 0).resolve_right h0
      apply hp
      refine ih (fun j => g j.succ) (fun j => hg _) ?_ z
      cases i using Fin.cases with
      | zero => exact absurd hi h0
      | succ j => exact ⟨j, hi⟩

theorem qminor_cast {n t t' : ℕ} (X : Fin n → Fin n → A) (h : t' = t) (a b : Fin t → Fin n) (u : ℂ) :
    qminor X (a ∘ finCongr h) (b ∘ finCongr h) u = qminor X a b u := by
  subst h; rfl

theorem Tm_restrict {n k : ℕ} (X : Fin n → Fin n → A) (f : Fin k → Fin n) (hf : Function.Injective f)
    (w : ℂ) (p q : Fin k) : Tm (fun p q => X (f p) (f q)) w p q = Tm X w (f p) (f q) := by
  unfold Tm; simp [hf.eq_iff]

theorem glRel_restrict {n k : ℕ} {X : Fin n → Fin n → A} (hX : GlRel X) (f : Fin k → Fin n)
    (hf : Function.Injective f) : GlRel (fun p q => X (f p) (f q)) := by
  intro a b c d
  have := hX (f a) (f b) (f c) (f d)
  simpa [hf.eq_iff] using this

theorem qdet_eq_flip {r m : ℕ} (X : Fin (r + m) → Fin (r + m) → A) (hX : GlRel X) (u : ℂ) :
    qdet X u = qminor X (finAddFlip : Fin (m + r) ≃ Fin (r + m)) finAddFlip u := by
  have hc := qminor_cast X (add_comm m r) (id : Fin (r + m) → Fin (r + m)) id u
  set c : Fin (m + r) ≃ Fin (r + m) := finCongr (add_comm m r) with hcdef
  set τ : Equiv.Perm (Fin (m + r)) := finAddFlip.trans (finCongr (add_comm r m)) with hτ
  have he : (⇑(finAddFlip : Fin (m + r) ≃ Fin (r + m))) = ⇑c ∘ ⇑τ := by
    funext k; apply Fin.ext; simp [c, τ]
  rw [he, quantumMinorRowSkew_holds A (r + m) (m + r) X (⇑c) (⇑c ∘ ⇑τ) τ u,
    quantumMinorColSkew_holds A (r + m) (m + r) X hX ⇑c ⇑c τ u, ← mul_assoc, ← Int.cast_mul,
    ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  exact hc.symm

theorem Tm_levi_mem {r m : ℕ} {X : Fin (r + m) → Fin (r + m) → A} (hX : GlRel X) (w : ℂ) (s t : Fin m)
    {y : A} (hy : y ∈ upperSpan X) : Tm X w (Fin.natAdd r s) (Fin.natAdd r t) * y ∈ upperSpan X := by
  unfold Tm
  rw [add_mul]
  refine add_mem ?_ (levi_mul_mem hX s t hy)
  split_ifs
  · rw [← Algebra.smul_def]; exact Submodule.smul_mem _ w hy
  · rw [zero_mul]; exact zero_mem _

theorem Tm_upper_mem {r m : ℕ} (X : Fin (r + m) → Fin (r + m) → A) (w : ℂ) (p : Fin r) (q : Fin m)
    (y : A) : Tm X w (Fin.castAdd m p) (Fin.natAdd r q) * y ∈ upperSpan X := by
  unfold Tm
  have hne : Fin.castAdd m p ≠ Fin.natAdd r q := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [if_neg hne, zero_add]
  exact Submodule.subset_span ⟨p, q, y, rfl⟩

theorem two_block {r m : ℕ} (X : Fin (r + m) → Fin (r + m) → A) (hX : GlRel X) (u : ℂ) :
    qdet X u - qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u *
      qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) (u - m) ∈ upperSpan X := by
  classical
  rw [qdet_eq_flip X hX u]
  set G : Equiv.Perm (Fin (m + r)) → A := fun σ => ((Equiv.Perm.sign σ : ℤ) : A) *
    (List.ofFn fun k : Fin (m + r) =>
      Tm X (u - (k : ℂ)) ((finAddFlip : Fin (m + r) ≃ Fin (r + m)) (σ k)) (finAddFlip k)).prod with hG
  have h1 : qminor X (finAddFlip : Fin (m + r) ≃ Fin (r + m)) finAddFlip u = ∑ σ, G σ := rfl
  rw [h1, ← Equiv.sum_comp (Equiv.permCongr finSumFinEquiv) G]
  set S := (Finset.univ : Finset (Equiv.Perm (Fin m) × Equiv.Perm (Fin r))).image
    (fun p => Equiv.Perm.sumCongr p.1 p.2) with hS
  rw [← Finset.sum_add_sum_compl S]
  have hblock : ∑ π ∈ S, G (Equiv.permCongr finSumFinEquiv π) =
      qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) u *
        qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) (u - m) := by
    have hinj : Set.InjOn (fun p : Equiv.Perm (Fin m) × Equiv.Perm (Fin r) => Equiv.Perm.sumCongr p.1 p.2)
        (Finset.univ : Finset (Equiv.Perm (Fin m) × Equiv.Perm (Fin r))) := by
      intro x _ y _ hxy
      exact Equiv.Perm.sumCongrHom_injective (α := Fin m) (β := Fin r) hxy
    rw [hS, Finset.sum_image hinj, Fintype.sum_prod_type]
    unfold qdet qminor
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp only [hG, Equiv.permCongr_def, Equiv.Perm.sign_symm_trans_trans, Equiv.Perm.sign_sumCongr,
      Units.val_mul, Int.cast_mul, List.ofFn_add, List.prod_append]
    rw [show ∀ (a b : ℤ) (P Q : A), (a : A) * b * (P * Q) = a * P * (b * Q) by
      intro a b P Q; rw [mul_assoc, ← mul_assoc (b : A), Int.cast_comm b P, mul_assoc, mul_assoc]]
    congr 3
    · refine congrArg List.ofFn (funext fun i => ?_)
      have e : (Fin.castLE (by omega) i : Fin (m + r)) = Fin.castAdd r i := rfl
      simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
        Sum.map_inl, finSumFinEquiv_apply_left, finAddFlip_apply_castAdd, Fin.val_castAdd, id]
      exact (Tm_restrict X (Fin.natAdd r) (fun a b h => Fin.ext (by simpa using congrArg Fin.val h)) _ _ _).symm
    · refine congrArg List.ofFn (funext fun i => ?_)
      simp only [Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply,
        Sum.map_inr, finSumFinEquiv_apply_right, finAddFlip_apply_natAdd, Fin.val_natAdd, id]
      rw [Tm_restrict X (Fin.castAdd m) (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))]
      congr 1
      push_cast; ring
  rw [hblock, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun π hπ => ?_
  have hπ' : π ∉ S := Finset.mem_compl.1 hπ
  have hmaps : ¬ Set.MapsTo π (Set.range Sum.inl) (Set.range Sum.inl) := by
    intro hm
    obtain ⟨⟨α, β⟩, hαβ⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
    exact hπ' (Finset.mem_image.2 ⟨(α, β), Finset.mem_univ _, hαβ⟩)
  obtain ⟨i₀, l₀, hl₀⟩ : ∃ i₀ : Fin m, ∃ l : Fin r, π (Sum.inl i₀) = Sum.inr l := by
    by_contra hc
    apply hmaps
    rintro _ ⟨i, rfl⟩
    cases h : π (Sum.inl i) with
    | inl j => exact ⟨j, rfl⟩
    | inr l => exact absurd ⟨i, l, h⟩ hc
  show ((Equiv.Perm.sign _ : ℤ) : A) * _ ∈ _
  rw [← zsmul_eq_mul]
  refine zsmul_mem ?_ _
  rw [List.ofFn_add, List.prod_append]
  refine prod_mul_mem _ m _ ?_ ⟨i₀, ?_⟩ _
  · intro i
    have e : (Fin.castLE (by omega) i : Fin (m + r)) = Fin.castAdd r i := rfl
    simp only [e, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, finAddFlip_apply_castAdd]
    cases h : π (Sum.inl i) with
    | inl j =>
      left
      intro y hy
      simp only [finSumFinEquiv_apply_left, finAddFlip_apply_castAdd]
      exact Tm_levi_mem hX _ _ _ hy
    | inr l =>
      right
      intro y
      simp only [finSumFinEquiv_apply_right, finAddFlip_apply_natAdd]
      exact Tm_upper_mem X _ _ _ y
  · intro y
    have e : (Fin.castLE (by omega) i₀ : Fin (m + r)) = Fin.castAdd r i₀ := rfl
    simp only [e, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, finAddFlip_apply_castAdd,
      hl₀, finSumFinEquiv_apply_right, finAddFlip_apply_natAdd]
    exact Tm_upper_mem X _ _ _ y

theorem entry_comm {r m : ℕ} {X : Fin (r + m) → Fin (r + m) → A} (hX : GlRel X) (s t : Fin m)
    (p q : Fin r) :
    Commute (X (Fin.natAdd r s) (Fin.natAdd r t)) (X (Fin.castAdd m p) (Fin.castAdd m q)) := by
  have h := hX (Fin.natAdd r s) (Fin.natAdd r t) (Fin.castAdd m p) (Fin.castAdd m q)
  have h1 : Fin.natAdd r t ≠ Fin.castAdd m p := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have h2 : Fin.castAdd m q ≠ Fin.natAdd r s := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [if_neg h1, if_neg h2, sub_zero] at h
  exact sub_eq_zero.1 h

theorem ite_algebraMap_comm (P : Prop) [Decidable P] (c : ℂ) (z : A) :
    Commute (if P then algebraMap ℂ A c else 0) z := by
  split_ifs
  · exact Algebra.commute_algebraMap_left c z
  · exact Commute.zero_left z

theorem qdet_comm {r m : ℕ} {X : Fin (r + m) → Fin (r + m) → A} (hX : GlRel X) (v w : ℂ) :
    Commute (qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q)) v)
      (qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q)) w) := by
  unfold qdet qminor
  refine Commute.sum_left _ _ _ fun α _ => Commute.sum_right _ _ _ fun β _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) (Commute.mul_right (Int.cast_commute _ _).symm ?_)
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
  unfold Tm
  exact Commute.add_left (ite_algebraMap_comm _ _ _)
    (Commute.add_right (ite_algebraMap_comm _ _ _).symm (entry_comm hX _ _ _ _))

theorem modExp_castSucc {c : ℕ} (n : Fin (c + 1) → ℕ) (j : Fin c) :
    modExp (fun i => Fin (n i)) (Fin.castSucc j) =
      modExp (fun i => Fin (n (Fin.castSucc i))) j + n (Fin.last c) := by
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter, Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff,
    Fin.castSucc_lt_last, if_true]
  have : ¬ Fin.last c < Fin.castSucc j := not_lt.2 (Fin.castSucc_lt_last j).le
  simp only [this, if_false]
  ring

theorem modExp_last {c : ℕ} (n : Fin (c + 1) → ℕ) :
    modExp (fun i => Fin (n i)) (Fin.last c) = -((∑ i : Fin c, n (Fin.castSucc i) : ℕ) : ℤ) := by
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter, Fin.sum_univ_castSucc, Fin.castSucc_lt_last, if_true,
    lt_irrefl, if_false]
  have : ∀ i : Fin c, ¬ Fin.last c < Fin.castSucc i := fun i => not_lt.2 (Fin.castSucc_lt_last i).le
  simp only [this, if_false, Finset.sum_const_zero]
  push_cast
  ring

theorem qdet_blocks : ∀ (c : ℕ) {N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (X : Fin N → Fin N → A),
    GlRel X → ∀ u : ℂ, qdet X (u + ((N : ℂ) - 1) / 2) - (List.ofFn fun i : Fin c =>
      qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
        (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod ∈
      Submodule.span ℂ {y : A | ∃ (p q : Fin N) (w : A),
        blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} := by
  intro c
  induction c with
  | zero =>
    intro N n h X hX u
    have hN : N = 0 := by rw [← h]; simp
    subst hN
    have h1 : qdet X (u + (((0 : ℕ) : ℂ) - 1) / 2) = 1 := by unfold qdet qminor; simp
    rw [h1]
    simp
  | succ c ih =>
    intro N n h X hX u
    set r := ∑ i : Fin c, n (Fin.castSucc i) with hr
    set m := n (Fin.last c) with hm
    have hN : r + m = N := by rw [← h, Fin.sum_univ_castSucc]
    subst hN
    set n' : Fin c → ℕ := fun i => n (Fin.castSucc i) with hn'
    have hr' : ∑ i, n' i = r := rfl
    have hL1 : ∀ (i : Fin c) (p : Fin (n (Fin.castSucc i))),
        stdBlocks n h ⟨Fin.castSucc i, p⟩ = Fin.castAdd m (stdBlocks n' hr' ⟨i, p⟩) := by
      intro i p; apply Fin.ext; rw [stdBlocks_val, Fin.val_castAdd, stdBlocks_val]; rfl
    have hL2 : ∀ q : Fin m, stdBlocks n h ⟨Fin.last c, q⟩ = Fin.natAdd r q := by
      intro q; apply Fin.ext; rw [stdBlocks_val, Fin.val_natAdd]; rfl
    have hblkF : ∀ p : Fin r, blk (stdBlocks n h) (Fin.castAdd m p) =
        Fin.castSucc (blk (stdBlocks n' hr') p) := by
      intro p
      obtain ⟨⟨i, p0⟩, rfl⟩ := (stdBlocks n' hr').surjective p
      rw [← hL1, blk_apply, blk_apply]
    have hblkS : ∀ q : Fin m, blk (stdBlocks n h) (Fin.natAdd r q) = Fin.last c := by
      intro q; rw [← hL2, blk_apply]
    have hS : ∀ y ∈ {y : A | ∃ (p q : Fin (r + m)) (w : A),
        blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w}, ∀ a : A,
        y * a ∈ {y : A | ∃ (p q : Fin (r + m)) (w : A),
          blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} := by
      rintro _ ⟨p, q, w, hpq, rfl⟩ a
      exact ⟨p, q, w * a, hpq, mul_assoc _ _ _⟩
    have hJ1 : upperSpan X ≤ Submodule.span ℂ {y : A | ∃ (p q : Fin (r + m)) (w : A),
        blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨p, q, w, rfl⟩
      exact Submodule.subset_span ⟨_, _, w, by rw [hblkF, hblkS]; exact Fin.castSucc_lt_last _, rfl⟩
    have hJ2 : Submodule.span ℂ {y : A | ∃ (p q : Fin r) (w : A),
        blk (stdBlocks n' hr') p < blk (stdBlocks n' hr') q ∧
          y = X (Fin.castAdd m p) (Fin.castAdd m q) * w} ≤
        Submodule.span ℂ {y : A | ∃ (p q : Fin (r + m)) (w : A),
          blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨p, q, w, hpq, rfl⟩
      exact Submodule.subset_span ⟨_, _, w, by
        rw [hblkF, hblkF]; exact Fin.castSucc_lt_castSucc_iff.2 hpq, rfl⟩
    have injC : Function.Injective (Fin.castAdd m : Fin r → Fin (r + m)) := (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
    have h3 := ih n' hr' (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q))
      (glRel_restrict hX _ injC) (u - (m : ℂ) / 2)
    have h2 := two_block X hX (u + (((r + m : ℕ) : ℂ) - 1) / 2)
    rw [(qdet_comm hX _ _).eq] at h2
    have hv : u - (m : ℂ) / 2 + ((r : ℂ) - 1) / 2 = u + (((r + m : ℕ) : ℂ) - 1) / 2 - m := by
      push_cast; ring
    rw [hv] at h3
    rw [List.ofFn_succ', List.prod_concat]
    have hF : (List.ofFn fun i : Fin c =>
        qdet (fun p q : Fin (n (Fin.castSucc i)) =>
          X (stdBlocks n h ⟨Fin.castSucc i, p⟩) (stdBlocks n h ⟨Fin.castSucc i, q⟩))
          (u + ((n (Fin.castSucc i) : ℂ) - 1) / 2 -
            (modExp (fun i => Fin (n i)) (Fin.castSucc i) : ℂ) / 2)) =
        List.ofFn fun i : Fin c =>
          qdet (fun p q : Fin (n' i) =>
            X (Fin.castAdd m (stdBlocks n' hr' ⟨i, p⟩)) (Fin.castAdd m (stdBlocks n' hr' ⟨i, q⟩)))
            (u - (m : ℂ) / 2 + ((n' i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n' i)) i : ℂ) / 2) := by
      refine congrArg List.ofFn (funext fun i => ?_)
      simp only [hL1]
      congr 1
      rw [modExp_castSucc]
      push_cast
      ring
    have hSb : qdet (fun p q : Fin m => X (stdBlocks n h ⟨Fin.last c, p⟩) (stdBlocks n h ⟨Fin.last c, q⟩))
        (u + ((m : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) (Fin.last c) : ℂ) / 2) =
        qdet (fun p q : Fin m => X (Fin.natAdd r p) (Fin.natAdd r q))
          (u + (((r + m : ℕ) : ℂ) - 1) / 2) := by
      simp only [hL2]
      congr 1
      rw [modExp_last, ← hr]
      push_cast
      ring
    rw [hF, hSb]
    refine (show ∀ (a b c d : A), a - c * d = (a - b * d) + (b - c) * d by intros; noncomm_ring)
      _ (qdet (fun p q : Fin r => X (Fin.castAdd m p) (Fin.castAdd m q))
        (u + (((r + m : ℕ) : ℂ) - 1) / 2 - m)) _ _ ▸ ?_
    exact add_mem (hJ1 h2) (span_mul_right_mem hS (hJ2 h3) _)

end GlobalTheory.CapHC

theorem GlobalTheory.CapHC.qdet_blocks_congr : ∀ (A : Type) [Ring A] [Algebra ℂ A] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (X : Fin N → Fin N → A), Formalism.REAL.GlRel X → ∀ u : ℂ, Formalism.REAL.qdet X (u + ((N : ℂ) - 1) / 2) - (List.ofFn fun i : Fin c => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod ∈ Submodule.span ℂ {y : A | ∃ (p q : Fin N) (w : A), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} := by
  intro A _ _ c N n h X hX u
  exact GlobalTheory.CapHC.qdet_blocks c n h X hX u
