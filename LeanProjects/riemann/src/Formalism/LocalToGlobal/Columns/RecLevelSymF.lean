import Formalism.LocalToGlobal.Columns.RecLevelSym
import Formalism.LocalToGlobal.Columns.TiedGlMat
import Formalism.LocalToGlobal.HermitianForms.DefsSym

open NumberField Matrix

noncomputable section

namespace Formalism.L2.Col
section TieFormsSym

variable {κ : Type} [CommRing κ] {k' : Type} [Field k']

theorem blkIdx_replicate_top {t : ℕ} (_ht : 0 < t) (j : ℕ) : blkIdx (List.replicate j t) (j * t) = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.replicate_succ, blkIdx, if_neg (by rw [Nat.succ_mul]; omega), show (j + 1) * t - t = j * t by rw [Nat.succ_mul]; omega, ih]

theorem coarse_rep {r t j x : ℕ} (ht : 0 < t) (hx : x ≤ r + j * t) :
    coarse r (List.replicate j t) x = if x < r then 0 else (x - r) / t + 1 := by
  split_ifs with h
  · exact coarse_of_lt h
  · rw [coarse_of_le (Nat.not_lt.mp h)]
    by_cases h2 : x - r < j * t
    · rw [blkIdx_replicate ht j (x - r) h2]
    · have e : x - r = j * t := by omega
      rw [e, blkIdx_replicate_top ht, Nat.mul_div_cancel _ ht]

theorem posSym_eq_symIdx (k rS x : ℕ) : Formalism.L2.Forms.posSym k rS x = symIdx k rS x := by
  unfold Formalism.L2.Forms.posSym symIdx
  split_ifs <;> omega

theorem mem_HJsym_iff_InJSym (e : κ ≃+* k') {n k rS t j : ℕ} (ht : 0 < t) (hn : n ≤ k + 2 * rS + 1 + j * t + 1)
    (h : k + 2 * rS + 1 ≤ n) (M : GL (Fin n) κ) :
    M ∈ HJsym κ n k (k + 2 * rS + 1) t j rS h ↔
      Formalism.L2.Forms.InJSym k rS t false ((M : Matrix (Fin n) (Fin n) κ).map e) := by
  have hrS : k + rS ≤ k + 2 * rS + 1 := by omega
  have hlv : ∀ x : Fin n, Formalism.L2.Forms.lvSym k rS t x.val =
      if x.val < k + 2 * rS + 1 then symIdx k rS x.val else k + 2 * rS + 1 + (x.val - (k + 2 * rS + 1)) / t := by
    intro x
    unfold Formalism.L2.Forms.lvSym Formalism.L2.Forms.rSym
    rw [posSym_eq_symIdx]
  have hco : ∀ x : Fin n, coarse (k + 2 * rS + 1) (List.replicate j t) x.val =
      if x.val < k + 2 * rS + 1 then 0 else (x.val - (k + 2 * rS + 1)) / t + 1 := fun x => coarse_rep ht (by have := x.2; omega)
  have hsym : ∀ x : ℕ, x < k + 2 * rS + 1 → symIdx k rS x < k + 2 * rS + 1 := fun x hx => symIdx_lt hrS hx
  have z0 : ∀ a : κ, e a = 0 ↔ a = 0 := fun a => EmbeddingLike.map_eq_zero_iff
  have z1 : ∀ a : κ, e a = 1 ↔ a = 1 := fun a => ⟨fun h' => e.injective (by rw [h', map_one]), fun h' => by rw [h', map_one]⟩
  unfold HJsym
  rw [mem_HPar]
  constructor
  · rintro ⟨hB, h0⟩
    rw [mem_HPsymF_iff hrS] at h0
    obtain ⟨h1, h2, h3⟩ := h0
    refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h' => absurd h' (by simp)⟩
    · rw [Matrix.map_apply, z0]
      rw [hlv, hlv] at hxy
      by_cases hx : x.val < k + 2 * rS + 1
      · by_cases hy : y.val < k + 2 * rS + 1
        · rw [if_pos hx, if_pos hy] at hxy
          have := h1 ⟨x.val, hx⟩ ⟨y.val, hy⟩ hxy
          rwa [blockZero_val] at this
        · rw [if_pos hx, if_neg hy] at hxy
          have := hsym x.val hx
          generalize (y.val - (k + 2 * rS + 1)) / t = q at hxy
          omega
      · apply hB
        show coarse (k + 2 * rS + 1) (List.replicate j t) y.val < coarse (k + 2 * rS + 1) (List.replicate j t) x.val
        rw [hco, hco, if_neg hx]
        rw [if_neg hx] at hxy
        by_cases hy : y.val < k + 2 * rS + 1
        · rw [if_pos hy]; generalize (x.val - (k + 2 * rS + 1)) / t = qx; omega
        · rw [if_neg hy] at hxy ⊢
          generalize (y.val - (k + 2 * rS + 1)) / t = qy at hxy ⊢
          generalize (x.val - (k + 2 * rS + 1)) / t = qx at hxy ⊢
          omega
    · rw [Matrix.map_apply, z1]
      have := h2 ⟨x.val, hx⟩
      rwa [blockZero_val] at this
    · rw [Matrix.map_apply, z0]
      have := h3 ⟨x.val, by omega⟩ ⟨y.val, by omega⟩ hx hy
      rwa [blockZero_val] at this
  · rintro ⟨h1, h2, h3, _⟩
    have h1' : ∀ x y : Fin n, Formalism.L2.Forms.lvSym k rS t y.val < Formalism.L2.Forms.lvSym k rS t x.val →
        (M : Matrix (Fin n) (Fin n) κ) x y = 0 := fun x y hxy => (z0 _).mp (by rw [← Matrix.map_apply (f := e)]; exact h1 x y hxy)
    have hB : M ∈ blockUT n κ (k + 2 * rS + 1) (List.replicate j t) := by
      intro x y hxy
      apply h1'
      have hxy' : coarse (k + 2 * rS + 1) (List.replicate j t) y.val < coarse (k + 2 * rS + 1) (List.replicate j t) x.val := hxy
      rw [hco, hco] at hxy'
      rw [hlv, hlv]
      generalize hqy : (y.val - (k + 2 * rS + 1)) / t = qy at hxy' ⊢
      generalize hqx : (x.val - (k + 2 * rS + 1)) / t = qx at hxy' ⊢
      by_cases hx : x.val < k + 2 * rS + 1
      · rw [if_pos hx] at hxy'; split_ifs at hxy' <;> omega
      · rw [if_neg hx] at hxy' ⊢
        by_cases hy : y.val < k + 2 * rS + 1
        · rw [if_pos hy]; have := hsym y.val hy; omega
        · rw [if_neg hy] at hxy' ⊢
          omega
    refine ⟨hB, ?_⟩
    rw [mem_HPsymF_iff hrS]
    refine ⟨fun a b hab => ?_, fun a => ?_, fun a b ha hb => ?_⟩
    · rw [blockZero_val]
      apply h1'
      show Formalism.L2.Forms.lvSym k rS t b.val < Formalism.L2.Forms.lvSym k rS t a.val
      unfold Formalism.L2.Forms.lvSym Formalism.L2.Forms.rSym
      rw [if_pos b.2, if_pos a.2, posSym_eq_symIdx, posSym_eq_symIdx]
      exact hab
    · rw [blockZero_val]
      exact (z1 _).mp (by rw [← Matrix.map_apply (f := e)]; exact h2 (Fin.castLE h a) a.2)
    · rw [blockZero_val]
      exact (z0 _).mp (by rw [← Matrix.map_apply (f := e)]; exact h3 (Fin.castLE h a) (Fin.castLE h b) ha hb)

theorem mem_HXmsym_iff_InJSym (e : κ ≃+* k') {n k rS t m : ℕ} (ht : 0 < t) (hn : n = k + 2 * rS + 1 + m * t + 1)
    (h : k + 2 * rS + 1 ≤ n) (M : GL (Fin n) κ) :
    M ∈ HXmsym κ n k (k + 2 * rS + 1) t m rS h ↔
      Formalism.L2.Forms.InJSym k rS t true ((M : Matrix (Fin n) (Fin n) κ).map e) := by
  have z0 : ∀ a : κ, e a = 0 ↔ a = 0 := fun a => EmbeddingLike.map_eq_zero_iff
  have hiff := mem_HJsym_iff_InJSym e ht hn.le h M
  unfold HXmsym
  rw [Subgroup.mem_inf, hiff]
  constructor
  · rintro ⟨⟨h1, h2, h3, _⟩, hf⟩
    refine ⟨h1, h2, h3, fun _ x y hy => ⟨?_, ?_⟩⟩
    · rw [Matrix.map_apply, hf x y (by omega), Matrix.one_apply]
      split_ifs <;> simp
    · by_cases hxy : x = y
      · subst hxy
        rw [Matrix.map_apply, hf x x (by omega), Matrix.one_apply_eq, if_pos rfl, map_one]
      · rw [if_neg hxy]
        apply h1
        unfold Formalism.L2.Forms.lvSym Formalism.L2.Forms.rSym
        have hx : x.val < n := x.2
        have hx' : x.val ≠ y.val := fun h' => hxy (Fin.ext h')
        have hq' : (y.val - (k + 2 * rS + 1)) / t = m := by
          rw [show y.val - (k + 2 * rS + 1) = m * t by omega, Nat.mul_div_cancel _ ht]
        rw [if_neg (show ¬ y.val < k + 2 * rS + 1 by omega), hq']
        split_ifs with hxr
        · rw [posSym_eq_symIdx]; have := symIdx_lt (show k + rS ≤ k + 2 * rS + 1 by omega) hxr; omega
        · have hlt : x.val - (k + 2 * rS + 1) < t * m := by
            have hxn := x.2
            have hxr' : k + 2 * rS + 1 ≤ x.val := Nat.not_lt.mp hxr
            have e3 : x.val - (k + 2 * rS + 1) + (k + 2 * rS + 1) = x.val := Nat.sub_add_cancel hxr'
            have e4 : t * m = m * t := Nat.mul_comm t m
            have hyv : y.val = k + 2 * rS + 1 + m * t := by omega
            have hxy2 : x.val < y.val := by omega
            generalize x.val - (k + 2 * rS + 1) = d at e3 ⊢
            omega
          have hq : (x.val - (k + 2 * rS + 1)) / t < m := Nat.div_lt_of_lt_mul hlt
          generalize (x.val - (k + 2 * rS + 1)) / t = q at hq ⊢
          omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, h2, h3, fun h' => absurd h' (by simp)⟩, fun x y hy => ?_⟩
    have := (h4 rfl x y (by omega)).1
    rw [Matrix.map_apply] at this
    by_cases hxy : x = y
    · rw [if_pos hxy] at this; rw [Matrix.one_apply, if_pos hxy]; exact e.injective (by rw [this, map_one])
    · rw [if_neg hxy] at this; rw [Matrix.one_apply, if_neg hxy]; exact (z0 _).mp this

theorem HJsym_eq_JSymG {κ : Type} [Field κ] {n k rS t j : ℕ} (ht : 0 < t) (hn : n ≤ k + 2 * rS + 1 + j * t + 1)
    (h : k + 2 * rS + 1 ≤ n) :
    HJsym κ n k (k + 2 * rS + 1) t j rS h = Formalism.L2.Forms.JSymG (κ := κ) (n := n) k rS t false := by
  ext M
  have e1 := mem_HJsym_iff_InJSym (RingEquiv.refl κ) ht hn h M
  have e2 := mem_HJsym_iff_InJSym (RingEquiv.refl κ) ht hn h M⁻¹
  rw [show ((M : Matrix (Fin n) (Fin n) κ).map (RingEquiv.refl κ)) = M from by ext; rfl] at e1
  rw [show (((M⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).map (RingEquiv.refl κ)) = ((M⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) from by ext; rfl] at e2
  constructor
  · intro hM
    exact ⟨e1.mp hM, e2.mp (Subgroup.inv_mem _ hM)⟩
  · rintro ⟨h1, _⟩
    exact e1.mpr h1

theorem HXmsym_eq_JSymG {κ : Type} [Field κ] {n k rS t m : ℕ} (ht : 0 < t) (hn : n = k + 2 * rS + 1 + m * t + 1)
    (h : k + 2 * rS + 1 ≤ n) :
    HXmsym κ n k (k + 2 * rS + 1) t m rS h = Formalism.L2.Forms.JSymG (κ := κ) (n := n) k rS t true := by
  ext M
  have e1 := mem_HXmsym_iff_InJSym (RingEquiv.refl κ) ht hn h M
  have e2 := mem_HXmsym_iff_InJSym (RingEquiv.refl κ) ht hn h M⁻¹
  rw [show ((M : Matrix (Fin n) (Fin n) κ).map (RingEquiv.refl κ)) = M from by ext; rfl] at e1
  rw [show (((M⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).map (RingEquiv.refl κ)) = ((M⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) from by ext; rfl] at e2
  constructor
  · intro hM
    exact ⟨e1.mp hM, e2.mp (Subgroup.inv_mem _ hM)⟩
  · rintro ⟨h1, _⟩
    exact e1.mpr h1

end TieFormsSym

section TieLamSym

variable {κ : Type} [CommRing κ] {k' : Type} [Field k'] {K : Type} [Field K]

theorem supSum_map_eq (e : κ ≃+* k') {n a skip : ℕ} (S : Finset ℕ) (hS : ∀ x, x + 1 < a → (x ∈ S ↔ x + 1 ≠ skip))
    (M : Matrix (Fin n) (Fin n) κ) :
    e (supSum a S M) = ∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < a ∧ (y : ℕ) ≠ skip then (M.map e) x y else 0 := by
  unfold supSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : (x : ℕ) + 1 = y ∧ (y : ℕ) < a
  · have h2 : ((x : ℕ) ∈ S ↔ (y : ℕ) ≠ skip) := by rw [← h.1]; exact hS x (by omega)
    by_cases h3 : (x : ℕ) ∈ S
    · rw [if_pos ⟨h.1, h.2, h3⟩, if_pos ⟨h.1, h.2, h2.1 h3⟩]; rfl
    · rw [if_neg (fun h' => h3 h'.2.2), if_neg (fun h' => h3 (h2.2 h'.2.2)), map_zero]
  · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), map_zero]

theorem lamJsym_eq_lamSym (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k rS t j : ℕ} (ht : 0 < t)
    (hn : k + 2 * rS + 1 + j * t ≤ n) (h : k + 2 * rS + 1 ≤ n) (M : ↥(HJsym κ n k (k + 2 * rS + 1) t j rS h)) :
    σ₀ ((lamJsym ψ χ n k (k + 2 * rS + 1) t j rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamSym (glmPsi e σ₀ ψ) (fun s => glmChi e σ₀ (χ s)) k rS t j ((M.1 : Matrix (Fin n) (Fin n) κ).map e) := by
  unfold lamJsym lamPar Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ Formalism.L2.Forms.rSym
  rw [MonoidHom.mul_apply, Units.val_mul, map_mul]
  congr 1
  · rw [MonoidHom.comp_apply, chiSymF_val rfl]
    have e1 : ((HPar0 h (List.replicate j t) (HPsymF κ (k + 2 * rS + 1) k rS) M).1 : Matrix (Fin (k + 2 * rS + 1)) (Fin (k + 2 * rS + 1)) κ) =
        restr h (M.1 : Matrix (Fin n) (Fin n) κ) := rfl
    rw [e1, supSum_restr, ← glmPsi_apply e σ₀ ψ]
    congr 1
    refine supSum_map_eq e _ (fun x hx => ?_) _
    unfold SPsymF
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h' => h'.2
    · exact fun h' => ⟨by omega, h'⟩
  · rw [MonoidHom.comp_apply, detChar_apply, List.length_replicate, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun s hs => ?_
    have h2 := glm_blkDet e ht (Finset.mem_range.1 hs) hn (Subgroup.inclusion (HPar_le h (List.replicate j t) _) M)
    have h3 : (((Subgroup.inclusion (HPar_le h (List.replicate j t) (HPsymF κ (k + 2 * rS + 1) k rS)) M).1 : GL (Fin n) κ) :
        Matrix (Fin n) (Fin n) κ) = (M.1 : Matrix (Fin n) (Fin n) κ) := rfl
    rw [h3] at h2
    rw [← h2]
    exact (glmChi_apply e σ₀ (χ s) _).symm

theorem lamXmsym_eq_lamSym (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k rS t m : ℕ} (ht : 0 < t)
    (hn : k + 2 * rS + 1 + m * t ≤ n) (h : k + 2 * rS + 1 ≤ n) (M : ↥(HXmsym κ n k (k + 2 * rS + 1) t m rS h)) :
    σ₀ ((lamXmsym ψ χ n k (k + 2 * rS + 1) t m rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamSym (glmPsi e σ₀ ψ) (fun s => glmChi e σ₀ (χ s)) k rS t m ((M.1 : Matrix (Fin n) (Fin n) κ).map e) :=
  lamJsym_eq_lamSym e σ₀ ψ χ ht hn h ⟨M.1, M.2.1⟩

end TieLamSym

section MidTie

theorem eB_insEquiv (N c k : ℕ) (hk : k ≤ N) (a : Fin (N + c)) :
    Formalism.L2.Forms.eB N k c hk (insEquiv N c k (N + c) hk rfl a) = a := by
  apply Fin.ext
  show (Formalism.L2.Forms.eBf N k c hk (insEquiv N c k (N + c) hk rfl a)).val = a.val
  unfold insEquiv
  simp only [Equiv.coe_fn_mk]
  by_cases h1 : a.val < k
  · rw [dif_pos h1]; simp [Formalism.L2.Forms.eBf, Formalism.L2.Forms.insB, h1]
  · by_cases h2 : a.val < k + c
    · rw [dif_neg h1, dif_pos h2]; simp [Formalism.L2.Forms.eBf]; omega
    · rw [dif_neg h1, dif_neg h2]; simp [Formalism.L2.Forms.eBf, Formalism.L2.Forms.insB]; split_ifs <;> omega

theorem insGL_map_eq_extMon {κ : Type} [CommRing κ] {k' : Type} [Field k'] (e : κ ≃+* k') (N c k : ℕ) (hk : k ≤ N) (M : GL (Fin N) κ) :
    ((insGL κ N c k (N + c) hk rfl M : GL (Fin (N + c)) κ) : Matrix (Fin (N + c)) (Fin (N + c)) κ).map e =
      Formalism.L2.Forms.extMon k' N k c hk ((M : Matrix (Fin N) (Fin N) κ).map e) := by
  ext a b
  rw [Matrix.map_apply, insGL_val]
  show _ = Matrix.reindex (Formalism.L2.Forms.eB N k c hk) (Formalism.L2.Forms.eB N k c hk) (Matrix.fromBlocks ((M : Matrix (Fin N) (Fin N) κ).map e) 0 0 1) a b
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  have ha : (Formalism.L2.Forms.eB N k c hk).symm a = insEquiv N c k (N + c) hk rfl a := by
    rw [Equiv.symm_apply_eq, eB_insEquiv]
  have hb : (Formalism.L2.Forms.eB N k c hk).symm b = insEquiv N c k (N + c) hk rfl b := by
    rw [Equiv.symm_apply_eq, eB_insEquiv]
  rw [ha, hb]
  rcases insEquiv N c k (N + c) hk rfl a with x | x <;> rcases insEquiv N c k (N + c) hk rfl b with y | y <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

end MidTie

theorem mem_HJsym_iff_InJSym' {κ : Type} [CommRing κ] {k' : Type} [Field k'] (e : κ ≃+* k') {n k rS t j r : ℕ} (hr : r = k + 2 * rS + 1)
    (ht : 0 < t) (hn : n ≤ r + j * t + 1) (h : r ≤ n) (M : GL (Fin n) κ) :
    M ∈ HJsym κ n k r t j rS h ↔ Formalism.L2.Forms.InJSym k rS t false ((M : Matrix (Fin n) (Fin n) κ).map e) := by
  subst hr
  exact mem_HJsym_iff_InJSym e ht hn h M

theorem lamJsym_eq_lamSym' {κ : Type} [CommRing κ] {k' : Type} [Field k'] {K : Type} [Field K] (e : κ ≃+* k') (σ₀ : K →+* ℂ)
    (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n k rS t j r : ℕ} (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : r + j * t ≤ n) (h : r ≤ n)
    (M : ↥(HJsym κ n k r t j rS h)) :
    σ₀ ((lamJsym ψ χ n k r t j rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamSym (glmPsi e σ₀ ψ) (fun s => glmChi e σ₀ (χ s)) k rS t j ((M.1 : Matrix (Fin n) (Fin n) κ).map e) := by
  subst hr
  exact lamJsym_eq_lamSym e σ₀ ψ χ ht hn h M

section MidSteps

open Formalism.BasicNotions (Ranks)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {k' : Type} [Field k']

theorem colLevSym_mid_mem_iff {j : ℕ} (h0 : j ≠ 0) (h1 : j + 1 < R.m) (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k')
    (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)) :
    M ∈ (colLevSym Ch j w).H ↔
      Formalism.L2.Forms.InJSym R.k R.rS R.t false (Formalism.L2.Forms.extMon k' (R.N j) R.k (R.m - 1 - j) (colK_le_N R j)
        ((M : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)).map e)) := by
  rw [colLevSym_mid_H Ch h0 h1 w, Subgroup.mem_comap,
    mem_HJsym_iff_InJSym' e (r_eq_sym R) (t_pos R) (by rw [← Y_eq_X_add (by omega)]; omega) _, insGL_map_eq_extMon]

theorem colLevSym_mid_lam_eq {j : ℕ} (h0 : j ≠ 0) (h1 : j + 1 < R.m) (w : Pr.vGs) (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* k') (σ₀ : X.K →+* ℂ)
    (M : ↥(colLevSym Ch j w).H) :
    σ₀ (((colLevSym Ch j w).lam M : X.Kˣ) : X.K) =
      Formalism.L2.Forms.lamX (glmPsi e σ₀ (Ch.psi0 w)) (fun s => glmChi e σ₀ (extChi (fun s => Ch.chi s w) s)) (R.N j) R.k R.rS R.t
        (R.m - 1 - j) j (colK_le_N R j) ((M.1 : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)).map e) := by
  obtain ⟨x, hx⟩ := M
  have hM : insGL (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) (R.m - 1 - j) R.k (R.N j + (R.m - 1 - j)) (colK_le_N R j) rfl x ∈
      HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N j + (R.m - 1 - j)) R.k R.r R.t j R.rS (r_le_Y (by omega)) := by
    rw [colLevSym_mid_H Ch h0 h1 w] at hx
    exact hx
  rw [colLevSym_mid_lam Ch h0 h1 w ⟨x, hx⟩ hM, lamJsym_eq_lamSym' e σ₀ _ _ (r_eq_sym R) (t_pos R) (by rw [← Y_eq_X_add (by omega)]) _ _]
  unfold Formalism.L2.Forms.lamX
  rw [insGL_map_eq_extMon]

end MidSteps

end Formalism.L2.Col
