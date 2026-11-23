import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

private theorem conj_apply_lemma (k : Type) [Field k] {N : ℕ} (w : Equiv.Perm (Fin N))
    (A : GL (Fin N) k) (u v : Fin N) :
    (↑(permGL k w * A * (permGL k w)⁻¹) : Matrix (Fin N) (Fin N) k) (w u) (w v) =
      (↑A : Matrix (Fin N) (Fin N) k) u v := by
  have hv : ∀ σ : Equiv.Perm (Fin N),
      (↑(permGL k σ) : Matrix (Fin N) (Fin N) k) = (σ⁻¹).toPEquiv.toMatrix := fun σ => rfl
  rw [← map_inv, Units.val_mul, Units.val_mul, hv, hv, inv_inv, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  simp [Matrix.submatrix_apply]

theorem GlobalTheory.CompanionTheory.GeomCell.innerMat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (e' : (Σ j, m' j) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (w : Equiv.Perm (Fin N)) (hcell : ∀ i j (t : c i j), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩) (p : Levi k m') (hp : p ∈ relParab k g) (hx : permGL k w * leviEmb k e' p * (permGL k w)⁻¹ ∈ blockUpper k N β), ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨_, hx⟩ : levi k N β) : GL (Fin N) k) = leviEmb k e (relEmb k f (swapBlocks k c (relProj k g ⟨p, hp⟩))) := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ m' _ _ c _ _ e β hβ e' f g w hcell p hp hx
  have key : ∀ a b : Fin N, β a = β b ↔ blk e a = blk e b := by
    intro a b
    constructor
    · intro h
      rcases lt_trichotomy (blk e a) (blk e b) with h' | h' | h'
      · exact absurd h (ne_of_lt ((hβ a b).mpr h'))
      · exact h'
      · exact absurd h (ne_of_gt ((hβ b a).mpr h'))
    · intro h
      rcases lt_trichotomy (β a) (β b) with h' | h' | h'
      · exact absurd h (ne_of_lt ((hβ a b).mp h'))
      · exact h'
      · exact absurd h (ne_of_gt ((hβ b a).mp h'))
  have hL : ∀ x y, (↑(↑((GroundTheory.Automorphic.Parabolic.leviProj k N β) ⟨_, hx⟩ : levi k N β) :
      GL (Fin N) k) : Matrix (Fin N) (Fin N) k) x y = if β x = β y then
      (↑(permGL k w * leviEmb k e' p * (permGL k w)⁻¹) : Matrix (Fin N) (Fin N) k) x y else 0 :=
    fun x y => rfl
  have hrel : ∀ (Q : ∀ i, Levi k (c i)) (i : α), relEmb k f Q i = leviEmb k (f i) (Q i) :=
    fun Q i => rfl
  have hsw : ∀ (R : ∀ j, Levi k (fun i => c i j)) (i : α) (j : β'), swapBlocks k c R i j = R j i :=
    fun R i j => rfl
  have hproj : ∀ (j : β') (i : α) (s s' : c i j),
      (↑((relProj k g ⟨p, hp⟩) j i) : Matrix (c i j) (c i j) k) s s' =
        (↑(p j) : Matrix (m' j) (m' j) k) (g j ⟨i, s⟩) (g j ⟨i, s'⟩) :=
    fun j i s s' => leviProj_apply k (g j) _ i s s'
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨j, t⟩, rfl⟩ := (f i).surjective a
  obtain ⟨⟨i', a'⟩, rfl⟩ := e.surjective y
  obtain ⟨⟨j', t'⟩, rfl⟩ := (f i').surjective a'
  rw [hL]
  by_cases hii : i = i'
  · subst hii
    rw [if_pos ((key _ _).mpr (by rw [blk_apply, blk_apply])), ← hcell i j t, ← hcell i j' t',
      conj_apply_lemma, hcell i j t, hcell i j' t', leviEmb_apply_same, hrel]
    by_cases hjj : j = j'
    · subst hjj
      rw [leviEmb_apply_same, leviEmb_apply_same, hsw, hproj]
    · rw [leviEmb_apply_ne k e' p hjj, leviEmb_apply_ne k (f i) _ hjj]
  · rw [if_neg (fun h => hii (by rw [key, blk_apply, blk_apply] at h; exact h)),
      leviEmb_apply_ne k e _ hii]
