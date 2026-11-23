import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialCechComplexExact
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

section Forms
variable {L : Type} [Field L] [Algebra ℂ L]

private def den (B C : Subalgebra ℂ L) (hBC : B ≤ C) (e : B →ₐ[ℂ] ℂ) : Subalgebra ℂ L where
  carrier := {v | ∃ b : B, e b ≠ 0 ∧ (b : L) * v ∈ C}
  mul_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', by simp [hb, hb'], ?_⟩
    have := C.mul_mem h h'
    rwa [show (b : L) * v * (b' * v') = ((b * b' : B) : L) * (v * v') by push_cast; ring] at this
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', by simp [hb, hb'], ?_⟩
    have := C.add_mem (C.mul_mem (hBC b'.2) h) (C.mul_mem (hBC b.2) h')
    rwa [show (b' : L) * (b * v) + b * (b' * v') = ((b * b' : B) : L) * (v + v') by push_cast; ring] at this
  algebraMap_mem' c := ⟨1, by simp, by simpa using C.algebraMap_mem c⟩

private lemma smul_omB (C : Subalgebra ℂ L) (q : ℕ) {c : L} (hc : c ∈ C) {y : DR ℂ L} (hy : y ∈ omB ℂ L C q) :
    c • y ∈ omB ℂ L C q := by
  induction hy using Submodule.span_induction with
  | mem y h =>
    obtain ⟨b, hb, v, hv, rfl⟩ := h
    exact Submodule.subset_span ⟨c * b, C.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha

private lemma one_mul_omB (C : Subalgebra ℂ L) (q : ℕ) {a v : L} (ha : a ∈ C) (hv : v ∈ C) {y : DR ℂ L}
    (hy : y ∈ omB ℂ L C q) : (a • ExteriorAlgebra.ι L (D ℂ L v)) * y ∈ omB ℂ L C (q + 1) := by
  induction hy using Submodule.span_induction with
  | mem y h =>
    obtain ⟨b, hb, w, hw, rfl⟩ := h
    refine Submodule.subset_span ⟨a * b, C.mul_mem ha hb, (Fin.cons v w : Fin (q + 1) → L), ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa using hv
      · simpa using hw i
    · have ht : (Matrix.vecTail fun j => D ℂ L ((Fin.cons v w : Fin (q + 1) → L) j)) = fun j => D ℂ L (w j) := by
        funext j
        simp [Matrix.vecTail]
      rw [ExteriorAlgebra.ιMulti_succ_apply, ht, smul_mul_smul_comm]
      simp
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | smul r a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ha

private lemma pow_smul_omB (C : Subalgebra ℂ L) {β : L} (hβ : β ∈ C) : ∀ (q : ℕ) (v : Fin q → L), (∀ j, β * v j ∈ C) →
    β ^ (2 * q) • ExteriorAlgebra.ιMulti L q (fun j => D ℂ L (v j)) ∈ omB ℂ L C q := by
  intro q
  induction q with
  | zero =>
    intro v _
    refine Submodule.subset_span ⟨1, C.one_mem, v, fun j => j.elim0, ?_⟩
    simp
  | succ q ih =>
    intro v hv
    have h1 := ih (fun j => v j.succ) fun j => hv _
    have h2 := one_mul_omB C q hβ (hv 0) h1
    have h3 := one_mul_omB C q (hv 0) hβ h1
    have hD : β ^ 2 • D ℂ L (v 0) = β • D ℂ L (β * v 0) - (β * v 0) • D ℂ L β := by
      rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, pow_two, add_sub_cancel_right]
    have hι : β ^ 2 • ExteriorAlgebra.ι L (D ℂ L (v 0)) =
        β • ExteriorAlgebra.ι L (D ℂ L (β * v 0)) - (β * v 0) • ExteriorAlgebra.ι L (D ℂ L β) := by
      rw [← map_smul, hD, map_sub, map_smul, map_smul]
    have : β ^ (2 * (q + 1)) • ExteriorAlgebra.ιMulti L (q + 1) (fun j => D ℂ L (v j)) =
        (β • ExteriorAlgebra.ι L (D ℂ L (β * v 0))) * (β ^ (2 * q) • ExteriorAlgebra.ιMulti L q (fun j => D ℂ L (v j.succ))) -
        ((β * v 0) • ExteriorAlgebra.ι L (D ℂ L β)) * (β ^ (2 * q) • ExteriorAlgebra.ιMulti L q (fun j => D ℂ L (v j.succ))) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply, ← sub_mul, ← hι, smul_mul_smul_comm, ← pow_add,
        show 2 * (q + 1) = 2 + 2 * q by ring]
      rfl
    rw [this]
    exact sub_mem h2 h3

private def locS (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) (M : Submodule ℂ (DR ℂ L))
    (hM : ∀ b ∈ B, ∀ m ∈ M, (b : L) • m ∈ M) : Submodule ℂ (DR ℂ L) where
  carrier := {v | ∃ b : B, e b ≠ 0 ∧ (b : L) • v ∈ M}
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', by simp [hb, hb'], ?_⟩
    have := M.add_mem (hM _ b'.2 _ h) (hM _ b.2 _ h')
    rwa [show (b' : L) • (b : L) • v + (b : L) • (b' : L) • v' = ((b * b' : B) : L) • (v + v') by
      rw [smul_add, smul_smul, smul_smul]; push_cast; rw [mul_comm (b' : L)]] at this
  zero_mem' := ⟨1, by simp, by simp⟩
  smul_mem' c v := by
    rintro ⟨b, hb, h⟩
    exact ⟨b, hb, by rw [smul_comm]; exact M.smul_mem c h⟩

private lemma mem_locM (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) (M : Submodule ℂ (DR ℂ L))
    (hM : ∀ b ∈ B, ∀ m ∈ M, (b : L) • m ∈ M) {v : DR ℂ L} :
    v ∈ locM B e M ↔ ∃ b : B, e b ≠ 0 ∧ (b : L) • v ∈ M := by
  have : locM B e M = locS B e M hM := Submodule.span_eq (locS B e M hM)
  rw [this]
  rfl

private lemma le_locM (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) (M : Submodule ℂ (DR ℂ L)) : M ≤ locM B e M :=
  fun m hm => Submodule.subset_span ⟨1, by simp, by simpa using hm⟩

private lemma omB_le_locS (B C C' : Subalgebra ℂ L) (hBC : B ≤ C) (e : B →ₐ[ℂ] ℂ)
    (hC' : C' ≤ den B C hBC e) (q : ℕ) :
    omB ℂ L C' q ≤ locS B e (omB ℂ L C q) (fun _ hb _ hm => smul_omB C q (hBC hb) hm) := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨b0, hb0, v, hv, rfl⟩
  obtain ⟨β0, h0, h0'⟩ := hC' hb0
  choose β hβ hβ' using fun j => hC' (hv j)
  set γ : B := β0 * ∏ j, β j with hγdef
  have hγ : e γ ≠ 0 := by
    rw [hγdef, map_mul, map_prod]
    exact mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun j _ => hβ j)
  have hvj : ∀ j, (γ : L) * v j ∈ C := by
    intro j
    have : (γ : L) = ((β0 * ∏ i ∈ Finset.univ.erase j, β i : B) : L) * (β j : L) := by
      rw [← Subalgebra.coe_mul, mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    rw [this, mul_assoc]
    exact C.mul_mem (hBC (Subtype.property _)) (hβ' j)
  have hbC : (γ : L) * b0 ∈ C := by
    have : (γ : L) * b0 = ((∏ j, β j : B) : L) * ((β0 : L) * b0) := by
      rw [hγdef, Subalgebra.coe_mul]; ring
    rw [this]
    exact C.mul_mem (hBC (Subtype.property _)) h0'
  refine ⟨γ ^ (2 * q + 1), by rw [map_pow]; exact pow_ne_zero _ hγ, ?_⟩
  have := smul_omB C q hbC (pow_smul_omB C (hBC γ.2) q v hvj)
  convert this using 1
  rw [smul_smul, smul_smul]
  congr 1
  push_cast
  ring

private lemma locM_le_locM (B C C' : Subalgebra ℂ L) (hBC : B ≤ C) (hBC' : B ≤ C') (e : B →ₐ[ℂ] ℂ)
    (hC' : C' ≤ den B C hBC e) (q : ℕ) : locM B e (omB ℂ L C' q) ≤ locM B e (omB ℂ L C q) := by
  intro y hy
  obtain ⟨b, hb, hm⟩ := (mem_locM B e _ fun _ hb _ hm => smul_omB C' q (hBC' hb) hm).1 hy
  obtain ⟨b', hb', hm'⟩ := omB_le_locS B C C' hBC e hC' q hm
  refine (mem_locM B e _ fun _ hb _ hm => smul_omB C q (hBC hb) hm).2 ⟨b' * b, by simp [hb, hb'], ?_⟩
  rw [smul_smul] at hm'
  simpa using hm'

end Forms

private lemma cone_exact {σ V : Type} [LinearOrder σ] [AddCommGroup V] [Module ℂ V] (A : Finset σ → Submodule ℂ V) (j : σ)
    (hA : ∀ J, A (insert j J) ≤ A J) (hw : ∀ c, wd (fun _ : σ => (1 : Module.End ℂ V)) c = GlobalTheory.DI.delta c) (n : ℤ) :
    (acx A fun _ => 1).Z n ≤ (acx A fun _ => 1).B n := by
  intro c hc
  obtain ⟨hC, hD⟩ := Submodule.mem_inf.1 hc
  have hdc : GlobalTheory.DI.delta c = 0 := by rw [← hw]; exact hD
  refine Submodule.mem_map.2 ⟨GlobalTheory.MonoCech.cone j c, ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun s _ => ?_
    show GlobalTheory.MonoCech.cone j c s ∈ (if (s.card : ℤ) = n - 1 then A s else ⊥)
    by_cases hs : j ∈ s
    · simp [GlobalTheory.MonoCech.cone, hs]
    · have h1 : c (insert j s) ∈ (if ((insert j s).card : ℤ) = n then A (insert j s) else ⊥) :=
        (Submodule.mem_pi.1 hC) (insert j s) (Set.mem_univ _)
      rw [Finset.card_insert_of_notMem hs] at h1
      by_cases hcard : (s.card : ℤ) = n - 1
      · rw [if_pos hcard]
        rw [if_pos (by push_cast; omega)] at h1
        simp only [GlobalTheory.MonoCech.cone, if_neg hs]
        exact zsmul_mem (hA s h1) _
      · rw [if_neg hcard]
        rw [if_neg (by push_cast; omega)] at h1
        simp [GlobalTheory.MonoCech.cone, hs, (Submodule.mem_bot ℂ).1 h1]
  · have := GlobalTheory.MonoCech.delta_cone_add j c
    rw [hdc, GlobalTheory.MonoCech.cone_zero, add_zero] at this
    show wd _ (GlobalTheory.MonoCech.cone j c) = c
    rw [hw]
    exact this

private lemma loc_mono {L : Type} [Field L] [Algebra ℂ L] (B B' : Subalgebra ℂ L) (h : B' ≤ B) (e : B →ₐ[ℂ] ℂ) :
    loc B' (e.comp (Subalgebra.inclusion h)) ≤ loc B e := by
  rintro v ⟨b, hb, hbv⟩
  exact ⟨Subalgebra.inclusion h b, hb, h hbv⟩

private lemma ex_of_loc (hLG : LG) (hWd : WdBasic) {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) [Algebra.FiniteType ℂ B]
    {d : ℕ} (A : Finset (Fin (d + 1)) → Submodule ℂ (DR ℂ L)) (hst : ∀ J, Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (A J))
    (hloc : ∀ e : B →ₐ[ℂ] ℂ, ∃ j', ∀ J, locM B e (A (insert j' J)) ≤ locM B e (A J)) (m : ℤ) :
    (acx A fun _ => 1).Z m ≤ (acx A fun _ => 1).B m := by
  intro c hc
  have key := (hLG L B (DR ℂ L) (Fin (d + 1)) A (fun _ => 1) hst).1 m c
  simp only [map_one] at key
  refine key fun e => ?_
  obtain ⟨j', hA⟩ := hloc e
  obtain ⟨hC, hD⟩ := Submodule.mem_inf.1 hc
  refine cone_exact _ j' hA (fun c => (hWd _ _ (fun _ => ⊥) (fun _ => 1)).2.2.2.2.1 c) m
    (Submodule.mem_inf.2 ⟨Submodule.mem_pi.2 fun s hs => ?_, hD⟩)
  have := Submodule.mem_pi.1 hC s hs
  show c s ∈ (if (s.card : ℤ) = m then _ else ⊥)
  change c s ∈ (if (s.card : ℤ) = m then _ else ⊥) at this
  split_ifs at this ⊢
  · exact le_locM _ _ _ this
  · exact this

private lemma den_insert {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
    [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
    (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K') (I : Finset (Fin (d + 1)))
    (hmap : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I ∧ j2 b ∈ R2 (xv x) j2 I)
    (hlast : ∀ J, ∀ j ∈ J, ∀ j', ∀ y ∈ R2 (xv x) j2 (insert j' J), ∃ N : ℕ, y * j2 (algebraMap F K ((x j' : F) / x j)) ^ N ∈ R2 (xv x) j2 J)
    (hBR : ∀ J, rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (h0 : RY (xv x) j2 I ∅ = rB ℂ K' (xv x) I)
    (e : rB ℂ K' (xv x) I →ₐ[ℂ] ℂ) (j' : Fin (d + 1)) (hloc : R2 (xv x) j2 {j'} ≤ loc (rB ℂ K' (xv x) I) e)
    (J : Finset (Fin (d + 1))) : RY (xv x) j2 I (insert j' J) ≤ den _ (RY (xv x) j2 I J) (hBR J) e := by
  refine sup_le (fun v hv => ⟨1, by simp, by simpa using hBR J hv⟩) ?_
  intro y hy
  rcases J.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · have hy' : y ∈ R2 (xv x) j2 {j'} := by simpa using hy
    obtain ⟨b, hb, hby⟩ := hloc hy'
    exact ⟨b, hb, hBR ∅ hby⟩
  · obtain ⟨N, hN⟩ := hlast J j hj j' y hy
    have hm : algebraMap F K ((x j : F) / x j') ∈ rB ℂ K (xv x) {j'} :=
      (integralClosure (rA ℂ (xv x) {j'}) K).algebraMap_mem
        ⟨(x j : F) / x j', Algebra.subset_adjoin ⟨j', Finset.mem_singleton_self _, j, rfl⟩⟩
    obtain ⟨b, hb, hbu⟩ := hloc (hmap {j'} _ hm).2
    refine ⟨b ^ N, by rw [map_pow]; exact pow_ne_zero _ hb, ?_⟩
    have hone : j2 (algebraMap F K ((x j : F) / x j')) * j2 (algebraMap F K ((x j' : F) / x j)) = 1 := by
      rw [← map_mul, ← map_mul, div_mul_div_comm, mul_comm (x j : F), div_self (mul_ne_zero (x j').ne_zero (x j).ne_zero),
        map_one, map_one]
    have heq : ((b ^ N : rB ℂ K' (xv x) I) : K') * y =
        ((b : K') * j2 (algebraMap F K ((x j : F) / x j'))) ^ N * (y * j2 (algebraMap F K ((x j' : F) / x j)) ^ N) := by
      have h1 : j2 (algebraMap F K ((x j : F) / x j')) ^ N * j2 (algebraMap F K ((x j' : F) / x j)) ^ N = 1 := by
        rw [← mul_pow, hone, one_pow]
      rw [SubmonoidClass.coe_pow]
      linear_combination (-((b : K') ^ N * y)) * h1
    rw [heq]
    exact mul_mem (pow_mem (hBR J hbu) N) ((le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) hN)

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.rowEx_of :
    LG → OmLoc → RYBasic → RYFT → ValBasic → WdBasic → RowEx := by
  intro hLG _ hRY hFT _ hWd F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY q I hI m
  obtain ⟨h0, -, hmono, hmap, hlast⟩ := hRY F K K' d x j2 hY
  have hBR : ∀ J, rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J := fun J => le_sup_left
  haveI : Algebra.FiniteType ℂ (rB ℂ K' (xv x) I) := by
    have := hFT F K K' d x j2 hY I ∅ hI
    rwa [h0] at this
  refine ex_of_loc hLG hWd (rB ℂ K' (xv x) I) _ (fun J r hr m hm => smul_omB _ q (hBR J hr) hm) (fun e => ?_) m
  obtain ⟨i, hi⟩ := hI
  have hle : rB ℂ K' (xv x) {i} ≤ rB ℂ K' (xv x) I := by
    rw [← h0, ← h0]
    exact hmono _ _ _ _ (Finset.singleton_subset_iff.2 hi) subset_rfl
  obtain ⟨j', hj'⟩ := hY.cov i (e.comp (Subalgebra.inclusion hle))
  have hloc : R2 (xv x) j2 {j'} ≤ loc (rB ℂ K' (xv x) I) e := hj'.trans (loc_mono _ _ hle e)
  exact ⟨j', fun J => locM_le_locM _ _ _ (hBR J) (hBR _) e (den_insert x j2 I hmap hlast hBR (h0 I) e j' hloc J) q⟩
