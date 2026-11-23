import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

theorem pos_cover (b : Fin (p + q)) : (∃ a, b = omEmb p q a) ∨ ∃ a, b = wEmb p q a := by
  rcases h : (blockEquiv p q).symm b with a | a
  · exact Or.inl ⟨a, (blockEquiv p q).symm.injective (h.trans (BlockEmbeddings.blockEquiv_symm_omEmb a).symm)⟩
  · exact Or.inr ⟨a, (blockEquiv p q).symm.injective (h.trans (BlockEmbeddings.blockEquiv_symm_wEmb a).symm)⟩

theorem aExt_posOf (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ) (j : Fin (n s))
    (l : Fin (rk Ψ p q s)) : aExt C s j (posOf p q s l) = C s j l := by
  have hi := (BlockEmbeddings.posOf_strictMono (p := p) (q := q) s).injective
  simp only [aExt]
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun e => hb (hi e)]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aExt_off (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (s : Ψ ⊕ Ψ) (j : Fin (n s))
    (b : Fin (p + q)) (hb : ¬ ∃ l, posOf p q s l = b) : aExt C s j b = 0 :=
  Finset.sum_eq_zero fun l _ => if_neg fun e => hb ⟨l, e⟩

theorem tMat_posOf (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (s : Ψ ⊕ Ψ)
    (hs : s = .inl τ ∨ s = .inr τ) (l l' : Fin (rk Ψ p q s)) :
    tMat Ts τ (posOf p q s l) (posOf p q s l') = Ts s l l' := by
  rcases hs with rfl | rfl
  · exact BlockEmbeddings.blocks_wEmb _ _ l l'
  · exact BlockEmbeddings.blocks_omEmb _ _ l l'

theorem blocks_wEmb_omEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R)
    (a : Fin p) (b : Fin q) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (wEmb p q a) (omEmb p q b) =
      0 := by
  rw [Matrix.submatrix_apply, BlockEmbeddings.blockEquiv_symm_wEmb, BlockEmbeddings.blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₂₁]
  rfl

theorem blocks_omEmb_wEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R)
    (a : Fin q) (b : Fin p) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (omEmb p q a) (wEmb p q b) =
      0 := by
  rw [Matrix.submatrix_apply, BlockEmbeddings.blockEquiv_symm_wEmb, BlockEmbeddings.blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₁₂]
  rfl

theorem tMat_off (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (s : Ψ ⊕ Ψ)
    (hs : s = .inl τ ∨ s = .inr τ) (l : Fin (rk Ψ p q s)) (b : Fin (p + q))
    (hb : ¬ ∃ l', posOf p q s l' = b) : tMat Ts τ (posOf p q s l) b = 0 := by
  rcases hs with rfl | rfl
  · rcases pos_cover b with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact blocks_wEmb_omEmb _ _ l a
    · exact absurd ⟨a, rfl⟩ hb
  · rcases pos_cover b with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact absurd ⟨a, rfl⟩ hb
    · exact blocks_omEmb_wEmb _ _ l a

theorem aExt_mul_tMat (A C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (x : Ω) (m : Ψ ⊕ Ψ → ℕ)
    (hAT : ∀ s, A s * Ts s = (x ^ m s) • C s) (τ : Ψ) (s : Ψ ⊕ Ψ) (hs : s = .inl τ ∨ s = .inr τ) :
    aExt A s * tMat Ts τ = (x ^ m s) • aExt C s := by
  ext j b
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := BlockEmbeddings.sum_aExt_mul A (RingHom.id Ω) s j (fun a => tMat Ts τ a b)
  simp only [RingHom.id_apply] at h1
  rw [h1]
  by_cases hb : ∃ l', posOf p q s l' = b
  · obtain ⟨l', rfl⟩ := hb
    have h2 := congrFun (congrFun (hAT s) j) l'
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h2
    rw [aExt_posOf, ← h2]
    exact Finset.sum_congr rfl fun l _ => by rw [tMat_posOf Ts τ s hs]
  · rw [aExt_off C s j b hb, mul_zero]
    exact Finset.sum_eq_zero fun l _ => by rw [tMat_off Ts τ s hs l b hb, mul_zero]

theorem sum_cMin_minorIJ (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (t : StepIx Ψ p q)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (G : Matrix (Fin (p + q)) (Fin (p + q)) Ω)
    (S : Finset (Fin (p + q))) (hS : S.card = (t.2 : ℕ) + 1) :
    ∑ I, cMin C t J I * minorIJ G I S =
      ((aExt C t.1).submatrix J id * G.submatrix id (S.orderEmbOfFin hS)).det := by
  rw [BlockEmbeddings.det_mul_cols _ _ S hS]
  rfl

theorem sum_cMin_tMat_mul (A C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (x : Ω) (m : Ψ ⊕ Ψ → ℕ)
    (hAT : ∀ s, A s * Ts s = (x ^ m s) • C s) (τ : Ψ) (t : StepIx Ψ p q) (hs : t.1 = .inl τ ∨ t.1 = .inr τ)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω)
    (S : Finset (Fin (p + q))) (hS : S.card = (t.2 : ℕ) + 1) :
    ∑ I, cMin A t J I * minorIJ (tMat Ts τ * h) I S =
      x ^ (m t.1 * ((t.2 : ℕ) + 1)) * ∑ I, cMin C t J I * minorIJ h I S := by
  rw [sum_cMin_minorIJ A t J _ S hS, sum_cMin_minorIJ C t J _ S hS]
  have hm : (aExt A t.1).submatrix J id * (tMat Ts τ * h).submatrix id (S.orderEmbOfFin hS) =
      (x ^ m t.1) • ((aExt C t.1).submatrix J id * h.submatrix id (S.orderEmbOfFin hS)) := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← Matrix.mul_assoc, aExt_mul_tMat A C Ts x m hAT τ t.1 hs, Matrix.smul_mul]
    rfl
  rw [hm, Matrix.det_smul, Fintype.card_fin, pow_mul]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
