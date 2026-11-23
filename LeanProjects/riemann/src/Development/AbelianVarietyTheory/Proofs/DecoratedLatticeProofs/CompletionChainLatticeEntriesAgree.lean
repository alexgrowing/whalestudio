import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.EntryBases

section Frames
variable {k : Type*} [Field k] {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

def ordExp : n ⊕ Fin c → ℤ := Sum.elim (fun _ => 0) (fun i => (i.val : ℤ) + 1)

theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (fun y : n ⊕ Fin c => (ϖ : k) ^ ordExp y) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, GlobalTheory.SplitFlip.diagGL, ordExp, diagonal, fromBlocks, Matrix.one_apply]
  split_ifs <;> simp [← zpow_natCast]

theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val = diagonal (fun y : n ⊕ Fin c => (ϖ : k) ^ (-ordExp y)) := by
  ext (i | i) (j | j) <;> simp [typeFrame, embA, GlobalTheory.SplitFlip.diagGL, ordExp, diagonal, fromBlocks, Matrix.one_apply]
  split_ifs <;> simp [← zpow_natCast]

theorem typeFrame_coords_apply (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (ord' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ ord).coords (typeFrame ϖ ord') x a b =
      (ϖ : k) ^ (ordExp (ord' b) - ordExp (ord a)) * x (ord a) (ord' b) := by
  simp only [LatFrame.coords, typeFrame_bas_val, typeFrame_bas_inv_val, submatrix_apply, diagonal_mul, mul_diagonal]
  dsimp only [typeFrame]
  rw [sub_eq_add_neg, zpow_add₀ (Units.ne_zero ϖ)]
  ring

end Frames

section Index

theorem fIdx_of_lt {κ c n v : ℕ} (h : v < κ) : LocE.fIdx κ c n v = v := by
  unfold LocE.fIdx; rw [if_pos h]

theorem fIdx_of_mid {κ c n v : ℕ} (h₁ : κ ≤ v) (h₂ : v < κ + c) : LocE.fIdx κ c n v = n + (v - κ) := by
  unfold LocE.fIdx; rw [if_neg (by omega), if_pos h₂]

theorem fIdx_of_ge {κ c n v : ℕ} (h : κ + c ≤ v) : LocE.fIdx κ c n v = v - c := by
  unfold LocE.fIdx; rw [if_neg (by omega), if_neg (by omega)]

theorem scE_of_lt {n v : ℕ} (ex : ℕ → ℕ) (h : v < n) : LocE.scE n ex v = 0 := by
  unfold LocE.scE; rw [if_pos h]

theorem scE_add (n i : ℕ) (ex : ℕ → ℕ) : LocE.scE n ex (n + i) = ex i := by
  unfold LocE.scE; rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem stdOrd_place {κ τ j c l n N : ℕ} (h : j + c = l) (hn : n = κ + j * (τ + 1))
    (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin N) (he : IsOrd (yPos xPos n) e) (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) :
    (e (stdOrd (Fin κ) (Fin τ) j c h a)).val = LocE.fIdx κ c n (zPos a) ∧
      ordExp (stdOrd (Fin κ) (Fin τ) j c h a) = LocE.scE n (fun i => i + 1) (LocE.fIdx κ c n (zPos a)) := by
  have hn' : n = κ + j * τ + j := by rw [hn]; ring
  rcases a with (i | ⟨i, hi⟩) | p
  · rw [stdOrd_eps, he]
    have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inl i) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = i.val := rfl
    rw [hz, fIdx_of_lt i.isLt, scE_of_lt _ (by omega)]
    exact ⟨rfl, rfl⟩
  · by_cases hic : i < c
    · have hs : stdOrd (Fin κ) (Fin τ) j c h (.inl (.inr ⟨i, hi⟩)) = .inr ⟨i, hic⟩ := standardOrderExtendedBasis_apply_low_block (Fin κ) (Fin τ) j c h ⟨i, hic⟩
      rw [hs, he]
      have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inr ⟨i, hi⟩) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + i := rfl
      rw [hz, fIdx_of_mid (by omega) (by omega), Nat.add_sub_cancel_left, scE_add]
      exact ⟨rfl, by simp [ordExp]⟩
    · obtain ⟨m, rfl⟩ : ∃ m, i = c + m := ⟨i - c, by omega⟩
      have hs : stdOrd (Fin κ) (Fin τ) j c h (.inl (.inr ⟨c + m, hi⟩)) = .inl (.inl (.inr ⟨m, by omega⟩)) :=
        stdOrd_f (Fin κ) (Fin τ) j c h ⟨m, by omega⟩
      rw [hs, he]
      have hz : zPos (κ := κ) (τ := τ) (j := j) (.inl (.inr ⟨c + m, hi⟩) : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + (c + m) := rfl
      rw [hz, fIdx_of_ge (by omega), scE_of_lt _ (by omega)]
      exact ⟨by simp [yPos, xPos]; omega, rfl⟩
  · rw [stdOrd_d, he]
    have hp : p.1.val * τ + p.2.val < j * τ := by
      have h1 : p.1.val * τ + p.2.val < (p.1.val + 1) * τ := by rw [add_mul, one_mul]; omega
      exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right τ p.1.isLt)
    have hz : zPos (κ := κ) (τ := τ) (j := j) (.inr p : Ix (Fin κ ⊕ Fin l) (Fin τ) j) = κ + l + p.1.val * τ + p.2.val := rfl
    rw [hz, fIdx_of_ge (by omega), scE_of_lt _ (by omega)]
    exact ⟨by simp [yPos, xPos]; omega, rfl⟩

end Index

section Main
variable {E k : Type} [Field E] [Field k]

theorem atN_val {N : ℕ} (v : Fin N → E) (i : Fin N) : Loc.atN v i.val = v i := by
  unfold Loc.atN; rw [dif_pos i.isLt]

theorem eN_val {N : ℕ} (i : Fin N) : Loc.eN E N i.val = Pi.single i 1 := by
  funext l; unfold Loc.eN; rw [Pi.single_apply]; simp [Fin.ext_iff]

theorem typeFrame_coords_toLoc (ι : E →+* k) (q : ℕ) (ϖ : kˣ) (hϖ : (ϖ : k) = ι (q : E))
    {κ τ l j c j' c' n N n' N' : ℕ} (h : j + c = l) (h' : j' + c' = l) (hn : n = κ + j * (τ + 1)) (hn' : n' = κ + j' * (τ + 1))
    (e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin N) (e' : XIx (Fin κ) (Fin τ) j' ⊕ Fin c' ≃ Fin N')
    (he : IsOrd (yPos xPos n) e) (he' : IsOrd (yPos xPos n') e') (x : (Fin N' → E) →ₗ[E] (Fin N → E))
    (a : Ix (Fin κ ⊕ Fin l) (Fin τ) j) (b : Ix (Fin κ ⊕ Fin l) (Fin τ) j') :
    (typeFrame ϖ (stdOrd (Fin κ) (Fin τ) j c h)).coords (typeFrame ϖ (stdOrd (Fin κ) (Fin τ) j' c' h')) (toLoc ι e e' x) a b =
      ι (LocE.entB q κ c' n' c n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  rw [map_natCast] at hϖ
  rw [typeFrame_coords_apply]
  obtain ⟨ha1, ha2⟩ := stdOrd_place h hn e he a
  obtain ⟨hb1, hb2⟩ := stdOrd_place h' hn' e' he' b
  simp only [LocE.entB, toLoc]
  rw [← ha2, ← hb2, ← ha1, ← hb1, eN_val, atN_val, map_mul, map_zpow₀, map_natCast, ← hϖ]
  ring

end Main

theorem entries_agree : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (τ j c : ℕ) (h : j + c = s) (n' c' n c₂ : ℕ), n' = κ + j * (τ + 1) → n = κ + (j + 1) * (τ + 1) → c' = c + 1 → c₂ = c → ∀ (e' : XIx (Fin κ) (Fin τ) j ⊕ Fin (c + 1) ≃ Fin (n' + c')) (e : XIx (Fin κ) (Fin τ) (j + 1) ⊕ Fin c ≃ Fin (n + c₂)), IsOrd (yPos xPos n') e' → IsOrd (yPos xPos n) e → ∀ (x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c₂) → E)) (a : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j), (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (j + 1) c (by omega))).coords (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) j (c + 1) (by omega))) (toLoc ι e e' x) a b = ι (LocE.entB q κ c' n' c₂ n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b)) := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT τ j c h n' c' n c₂ hn' hn hc' hc₂ e' e he' he x a b
  subst hc' hc₂
  exact typeFrame_coords_toLoc ι q S.ϖ hT.compl.unif _ _ hn hn' e e' he he' x a b

end GlobalTheory.SymBridge.EntryBases
