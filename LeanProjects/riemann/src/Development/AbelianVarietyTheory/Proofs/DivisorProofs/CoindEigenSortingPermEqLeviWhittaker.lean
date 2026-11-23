import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.FinGL.SortWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

variable {F : Type} [Field F] {r : ℕ}

def bd (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i k => if b i = b k then M i k else 0

theorem bd_apply (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) (i k : Fin r) :
    bd b M i k = if b i = b k then M i k else 0 := rfl

theorem bd_one (b : Fin r → ℕ) : bd b (1 : Matrix (Fin r) (Fin r) F) = 1 := by
  ext i k
  rw [bd_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply_ne]
    rintro rfl
    exact h rfl

theorem bd_bd (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : bd b (bd b M) = bd b M := by
  ext i k
  simp only [bd_apply]
  split_ifs <;> rfl

theorem bd_mul (b : Fin r → ℕ) {M N : Matrix (Fin r) (Fin r) F} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) :
    bd b (M * N) = bd b M * bd b N := by
  ext i k
  simp only [bd_apply, Matrix.mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (b l) (b i) with h1 | h1 | h1
    · rw [hM h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hN (show b k < b l by omega)]; simp
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    by_cases h1 : b i = b l
    · rw [if_neg (show ¬ b l = b k by omega), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem bd_tri (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : (bd b M).BlockTriangular b := by
  intro i k h
  rw [bd_apply, if_neg (by omega)]

def levi (b : Fin r → ℕ) (p : blockTri (κ := F) b) : blockTri (κ := F) b :=
  ⟨⟨bd b ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), bd b (((p⁻¹ : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F),
    by rw [← bd_mul b p.2 (p⁻¹).2, ← Units.val_mul]; simp [bd_one],
    by rw [← bd_mul b (p⁻¹).2 p.2, ← Units.val_mul]; simp [bd_one]⟩, bd_tri b _⟩

theorem levi_apply (b : Fin r → ℕ) (p : blockTri (κ := F) b) (i k : Fin r) :
    ((levi b p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      if b i = b k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0 := rfl

theorem sigma_levi {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (p : blockTri (κ := F) b) :
    σ (levi b p) = σ p := by
  have h : σ (p⁻¹ * levi b p) = 1 := by
    refine hσ.infl _ fun i k hik => ?_
    have h1 : bd b ((((p⁻¹ * levi b p : blockTri (κ := F) b)) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [Subgroup.coe_mul, Units.val_mul, bd_mul b (p⁻¹).2 (levi b p).2]
      have : bd b ((levi b p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
          bd b ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := bd_bd b _
      rw [this, ← bd_mul b (p⁻¹).2 p.2, ← Units.val_mul]
      simp [bd_one]
    have h2 := congrFun (congrFun h1 i) k
    rwa [bd_apply, if_pos hik] at h2
  have : levi b p = p * (p⁻¹ * levi b p) := by group
  rw [this, map_mul, h, mul_one]

theorem edgeSum_levi (b : Fin r → ℕ) (p : blockTri (κ := F) b) :
    edgeSum (blkEdge b) (levi b p : GL (Fin r) F) = edgeSum (blkEdge b) (p : GL (Fin r) F) := by
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [levi_apply, if_pos h.2]
  · rfl

section Perm

variable {b : Fin r → ℕ} {j : ℕ} {w : Equiv.Perm (Fin r)}

theorem lt_iff (h1 : ∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) {a c : Fin r} (h : b (w a) = b (w c)) :
    a < c ↔ w a < w c := by
  refine ⟨fun hac => h1 a c hac h, fun hw => ?_⟩
  rcases lt_trichotomy a c with h' | h' | h'
  · exact h'
  · subst h'; exact absurd hw (lt_irrefl _)
  · exact absurd (h1 c a h' h.symm) (not_lt.2 hw.le)

theorem edge_iff (hb : Monotone b) (h1 : ∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c)
    (h2 : ∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a))
    (h4 : ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) {a c : Fin r} (h : b (w a) = b (w c)) :
    blkEdge b (w a) (w c) ↔ cutEdge j a c := by
  constructor
  · rintro ⟨e1, -⟩
    have hac : a < c := (lt_iff h1 h).2 (by rw [Fin.lt_def]; omega)
    have hac' : a.val < c.val := hac
    have hc : c.val = a.val + 1 := by
      by_contra hne
      let e : Fin r := ⟨a.val + 1, by have := c.2; omega⟩
      have hae : a < e := by rw [Fin.lt_def]; simp [e]
      have hec : e < c := by rw [Fin.lt_def]; simp only [e]; omega
      have hbe := h2 a e c hae.le hec.le h
      have k1 : (w a).val < (w e).val := h1 a e hae hbe.symm
      have k2 : (w e).val < (w c).val := h1 e c hec (hbe.trans h)
      omega
    refine ⟨hc, fun hj => h4 a c (by omega) (by omega) h⟩
  · rintro ⟨e1, -⟩
    refine ⟨?_, h⟩
    have hac : a < c := by rw [Fin.lt_def]; omega
    have hw : (w a).val < (w c).val := h1 a c hac h
    by_contra hne
    let i : Fin r := ⟨(w a).val + 1, by have := (w c).2; omega⟩
    have hai : w a < i := by rw [Fin.lt_def]; simp [i]
    have hic : i < w c := by rw [Fin.lt_def]; simp only [i]; omega
    obtain ⟨e, he⟩ := w.surjective i
    have k1 : b (w a) ≤ b i := hb hai.le
    have k2 : b i ≤ b (w c) := hb hic.le
    rw [← he] at hai hic k1 k2
    have l1 : a.val < e.val := (lt_iff h1 (by omega)).2 hai
    have l2 : e.val < c.val := (lt_iff h1 (by omega)).2 hic
    omega

end Perm

theorem eig_conj_eq_leviWh : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → (∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) → (∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a)) → (∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a)) → (∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = eig σ {p | (p : GL (Fin r) F) ∈ unip F r} (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  intro F _ ψ r V _ _ b σ hσ j w x hx h1 h2 h3 h4
  have hsum : ∀ p : blockTri (κ := F) b, edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x) =
      edgeSum (blkEdge b) (p : GL (Fin r) F) := by
    intro p
    unfold edgeSum
    rw [← Equiv.sum_comp w (fun i => ∑ k, if blkEdge b i k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp w (fun k => if blkEdge b (w a) k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (w a) k else 0)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hx]
    by_cases h : b (w a) = b (w c)
    · simp only [edge_iff hσ.mono h1 h2 h4 h]
    · rw [if_neg (show ¬ blkEdge b (w a) (w c) from fun h' => h h'.2)]
      split_ifs with hc
      · exact p.2 (lt_of_le_of_ne (h3 a c hc) (Ne.symm h))
      · rfl
  ext v
  rw [mem_eig, mem_eig]
  constructor
  · intro H p hp
    have hp' : (p : GL (Fin r) F) ∈ unip F r := hp
    have hm : x⁻¹ * (levi b p : GL (Fin r) F) * x ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun a c hac => ?_, fun a => ?_⟩
      · rw [hx, levi_apply]
        split_ifs with h
        · exact unip_lower hp' (h1 c a hac h.symm)
        · rfl
      · rw [hx, levi_apply, if_pos rfl, unip_diag hp']
    have := H (levi b p) hm
    rw [sigma_levi hσ, hsum, edgeSum_levi] at this
    exact this
  · intro H p hp
    have hp' : x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r := hp
    have hm : (levi b p : GL (Fin r) F) ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun i k hik => ?_, fun i => ?_⟩
      · obtain ⟨a, rfl⟩ := w.surjective i
        obtain ⟨c, rfl⟩ := w.surjective k
        rw [levi_apply]
        split_ifs with h
        · rw [← hx]
          exact unip_lower hp' ((lt_iff h1 h.symm).2 hik)
        · rfl
      · obtain ⟨a, rfl⟩ := w.surjective i
        rw [levi_apply, if_pos rfl, ← hx, unip_diag hp']
    have := H (levi b p) hm
    rw [sigma_levi hσ, edgeSum_levi] at this
    rw [hsum]
    exact this

end GlobalTheory.FinGL.SortWh
