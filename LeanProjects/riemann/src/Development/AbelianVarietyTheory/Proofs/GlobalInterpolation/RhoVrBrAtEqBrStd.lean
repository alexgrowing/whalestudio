import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching

noncomputable section

namespace GlobalTheory.BranchBlock

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem isBlock_of_mulVec' {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} {c : E} (h1 : ∀ x, iniH hN (A' *ᵥ x) = A *ᵥ iniH hN x)
    (h2 : ∀ x, (A' *ᵥ x) (Br.iL hN) = c * x (Br.iL hN)) : BranchFormula.IsBlock hN A' A c := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, (Br.iC_inj hN).eq_iff]
    rw [e, mulVec_single_one, mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, mulVec_single_one, mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [mulVec_single_one, Pi.single_eq_of_ne (hne a).symm, mul_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [mulVec_single_one, Pi.single_eq_same, mul_one] at h
    exact h

theorem rhoVr_brAt_eq_brStd : ∀ {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] (emb : ι → E →+* K) {N n : ℕ}
    (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
    (∀ τ, Br.SameShift (lam τ) (sg τ)) → ∀ (t : E) (B' : GL (Fin n) E) (B : GL (Fin N) E),
    (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) →
    (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) →
    ∀ G : Formalism.L2.DIV.VV K lam, rhoVr emb sg B'⁻¹ (Br.brAt hN lam sg (fun τ => emb τ t) G) =
      Br.brStd hN lam sg (rhoVr emb lam B⁻¹ G) := by
  intro E K ι _ _ _ _ emb N n hN lam sg hI hS t B' B h1 h2 G
  have ht : t ≠ 0 := by
    intro h0
    have h := h2 (Pi.single (Br.iL hN) 1)
    rw [h0, zero_mul, Pi.single_eq_same] at h
    exact zero_ne_one h
  have hBA : ∀ x, (B : Matrix (Fin N) (Fin N) E) *ᵥ (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hAB : ∀ y, ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ ((B' : Matrix (Fin n) (Fin n) E) *ᵥ y) = y := by
    intro y
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hblk : BranchFormula.IsBlock hN ((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := by
    refine isBlock_of_mulVec' hN (fun x => ?_) (fun x => ?_)
    · have h := h1 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      rw [h, hAB]
    · have h := h2 (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      rw [hBA] at h
      exact h.symm
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (τ : ι) (a b : Fin m),
      ((invTrK (embGL emb g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
        emb τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g τ a b => rfl
  have key := BranchFormula.brAt_eq_pullback hN hI hS (invTrK (embGL emb B')) (invTrK (embGL emb B))
    (fun τ => emb τ t) (fun τ => (map_ne_zero _).2 ht) (fun τ => by
      refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;> simp only [e1]
      · rw [hblk.1]
      · rw [(hblk.2.1 a).2, map_zero]
      · rw [(hblk.2.1 a).1, map_zero]
      · rw [hblk.2.2]) G
  show rhoK sg (invTrK (embGL emb B'⁻¹)) _ = Br.brStd hN lam sg (rhoK lam (invTrK (embGL emb B⁻¹)) G)
  rw [map_inv (embGL emb), map_inv (embGL emb), map_inv invTrK, map_inv invTrK]
  exact key.symm

end GlobalTheory.BranchBlock
