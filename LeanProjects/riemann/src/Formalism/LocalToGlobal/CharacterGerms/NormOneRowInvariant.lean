import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Atom

variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

def keyL (ℓ : Letter T r n) : T × ℕ × Fin n := (ℓ.1, ℓ.2.1.val, ℓ.2.2)

theorem keyL_inj : Function.Injective (keyL (T := T) (r := r) (n := n)) := by
  rintro ⟨σ, i, c⟩ ⟨σ', i', c'⟩ h
  simp only [keyL, Prod.mk.injEq] at h
  obtain ⟨rfl, hi, rfl⟩ := h
  obtain rfl : i = i' := Fin.ext hi
  rfl

theorem rowShift_X (σ : T) (i i' : Fin (r σ)) (t : C) (ℓ : Letter T r n) :
    rowShift r n C σ i i' t (X ℓ) =
      if keyL ℓ = (σ, i.val, ℓ.2.2) then X ℓ + MvPolynomial.C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ := by
  unfold rowShift
  simp only [MvPolynomial.aeval_X]
  have key : (∃ b, ℓ = ⟨σ, (i, b)⟩) ↔ keyL ℓ = (σ, ↑i, ℓ.snd.2) := by
    constructor
    · rintro ⟨b, rfl⟩
      rfl
    · intro h
      exact ⟨ℓ.snd.2, keyL_inj (show keyL ℓ = keyL ⟨σ, (i, ℓ.snd.2)⟩ from h)⟩
  by_cases h : keyL ℓ = (σ, ↑i, ℓ.snd.2)
  · rw [if_pos (key.mpr h), if_pos h]
  · rw [if_neg (mt key.mp h), if_neg h]

private theorem det_mapMatrix_shear_eq_det {K : ℕ} (A : Matrix (Fin K) (Fin K) (MvPolynomial (Letter T r n) C))
    (μ : Fin K → Fin K → Letter T r n) (hA : ∀ b c, A b c = X (μ b c)) (σ0 : T) (κ : Fin K → Fin n)
    (hμ : ∀ b c, keyL (μ b c) = (σ0, c.val, κ b)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    ((rowShift r n C σ i i' t).mapMatrix A).det = A.det := by
  have h3 : ∀ b c, (μ b c).snd.2 = κ b := fun b c => congrArg (fun p => p.2.2) (hμ b c)
  by_cases hc : σ = σ0 ∧ i.val < K
  · obtain ⟨hσ, hiK⟩ := hc
    subst σ0
    have hi'K : i'.val < K := lt_trans hi hiK
    let c0 : Fin K := ⟨i.val, hiK⟩
    let c1 : Fin K := ⟨i'.val, hi'K⟩
    have hne : c0 ≠ c1 := by
      intro h
      have h' := congrArg Fin.val h
      exact hi.ne' (Fin.ext h')
    have h1 : ∀ b, μ b c1 = ⟨σ, (i', κ b)⟩ := fun b =>
      keyL_inj (show keyL (μ b c1) = keyL ⟨σ, (i', κ b)⟩ from hμ b c1)
    have hmat : (rowShift r n C σ i i' t).mapMatrix A =
        A.updateCol c0 (fun b => A b c0 + (MvPolynomial.C t : MvPolynomial (Letter T r n) C) • A b c1) := by
      ext b c
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply, hA, rowShift_X, hμ, h3, h1]
      by_cases hcc : c = c0
      · have hv : (c : ℕ) = i.val := by rw [hcc]
        rw [if_pos (by rw [hv]), if_pos hcc, hcc, smul_eq_mul]
      · have hv : (c : ℕ) ≠ i.val := fun h => hcc (Fin.ext h)
        rw [if_neg (by simp [hv]), if_neg hcc]
    rw [hmat]
    exact Matrix.det_updateCol_add_smul_self A hne (MvPolynomial.C t : MvPolynomial (Letter T r n) C)
  · congr 1
    ext b c
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, hA, rowShift_X, hμ, h3]
    rw [if_neg]
    intro h
    simp only [Prod.mk.injEq] at h
    exact hc ⟨h.1.symm, by rw [← h.2.1]; exact c.isLt⟩

theorem rowShift_minor {N N' : ℕ} (lam : Fin N × Fin N' → Letter T r n) (σ0 : T) (col : Fin N → Fin n)
    (hlam : ∀ ρ c, keyL (lam (ρ, c)) = (σ0, c.val, col ρ)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (k : ℕ) :
    rowShift r n C σ i i' t (rename lam (minorK C N N' k)) = rename lam (minorK C N N' k) := by
  unfold minorK
  split_ifs with hk
  · rw [AlgHom.map_det, AlgHom.map_det]
    exact det_mapMatrix_shear_eq_det _ (fun b c => lam (Fin.castLE hk.1 b, Fin.castLE hk.2 c))
      (fun b c => by simp [rename_X]) σ0 (fun b => col (Fin.castLE hk.1 b))
      (fun b c => hlam (Fin.castLE hk.1 b) (Fin.castLE hk.2 c)) σ i i' hi t
  · simp

theorem rowShift_monP {N N' : ℕ} (lam : Fin N × Fin N' → Letter T r n) (σ0 : T) (col : Fin N → Fin n)
    (hlam : ∀ ρ c, keyL (lam (ρ, c)) = (σ0, c.val, col ρ)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (e : ℕ → ℕ) :
    rowShift r n C σ i i' t (rename lam (monP C N N' e)) = rename lam (monP C N N' e) := by
  unfold monP
  simp only [map_prod, map_pow, rowShift_minor lam σ0 col hlam σ i i' hi t]

end Atom

section Fam

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → Fin 2 → ZMod d → T} {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (IIof r tau o) (J o)} {F : ∀ o, Flag (X o)} {Z : Finset Orb}
  {ga : Orb → Fin 2 → ZMod d → ℕ → ℕ} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n}

def psiL (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (n : ℕ) (o : Orb) {N : ℕ} (col : Fin N → Fin n)
    (x : Fin N × WV (IIof r tau o)) : Letter T r n := phiL r tau n (col x.1, ⟨o, x.2⟩)

theorem ConjugatePairPlaceSetting.key_letter (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (t : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (ρ : Fin N) (q : Fin ((X o).rkF g t)) :
    keyL ((psiL r tau n o col ∘ (F o).letter g t) (ρ, q)) = (tau o g t, q.val, col ρ) := by
  simp only [Function.comp_apply, psiL, Flag.letter, phiL, keyL]
  have h1 : ((F o).en g t q).fst = t := by
    have h := (F o).3 g t q
    rw [H.hty] at h
    exact h
  rw [H.std o g t q, h1]

theorem ConjugatePairPlaceSetting.inv_minor (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col) (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k))) =
      rename (psiL r tau n o col) (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k)) := by
  rw [rename_rename]
  exact rowShift_minor _ (tau o g s) col (fun ρ c => H.key_letter o g s col ρ c) σ i i' hi t k

theorem ConjugatePairPlaceSetting.inv_mon (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (e : ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col) (rename ((F o).letter g s) (monP C N ((X o).rkF g s) e))) =
      rename (psiL r tau n o col) (rename ((F o).letter g s) (monP C N ((X o).rkF g s) e)) := by
  rw [rename_rename]
  exact rowShift_monP _ (tau o g s) col (fun ρ c => H.key_letter o g s col ρ c) σ i i' hi t e

theorem ConjugatePairPlaceSetting.inv_bi (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g g' : Fin 2) (s s' : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (k e1 e2 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col)
      (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C N ((X o).rkF g' s') k) ^ e2)) =
      rename (psiL r tau n o col)
      (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C N ((X o).rkF g' s') k) ^ e2) := by
  simp only [map_pow, map_mul, H.inv_minor o g s col k σ i i' hi t, H.inv_minor o g' s' col k σ i i' hi t]

theorem ConjugatePairPlaceSetting.inv_ch (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {N : ℕ}
    (col : Fin N → Fin n) (k e1 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col)
      (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1)) =
      rename (psiL r tau n o col) (rename ((F o).letter g s) (minorK C N ((X o).rkF g s) k) ^ e1) := by
  simp only [map_pow, H.inv_minor o g s col k σ i i' hi t]

theorem ConjugatePairPlaceSetting.inv_monAll (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (g : Fin 2) {N : ℕ}
    (col : Fin N → Fin n) (e : ZMod d → ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col)
      (∏ s : ZMod d, rename ((F o).letter g s) (monP C N ((X o).rkF g s) (e s)))) =
      rename (psiL r tau n o col) (∏ s : ZMod d, rename ((F o).letter g s) (monP C N ((X o).rkF g s) (e s))) := by
  simp only [map_prod]
  exact Finset.prod_congr rfl fun s _ => H.inv_mon o g s col (e s) σ i i' hi t

theorem ConjugatePairPlaceSetting.inv_poly (H : ConjugatePairPlaceSetting r cc a tau X F Z ga n L pl) (o : Orb) (b : GlobalTheory d) (col : Fin (b.what₂ (X o).n) → Fin n)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (rename (psiL r tau n o col) (b.poly (X o) (F o))) =
      rename (psiL r tau n o col) (b.poly (X o) (F o)) := by
  rcases b with ⟨g, a, j, y⟩ | ⟨g, a, u⟩ | ⟨g, e, N⟩
  · exact H.inv_bi o _ _ _ _ col _ _ _ σ i i' hi t
  · exact H.inv_ch o _ _ col _ _ σ i i' hi t
  · exact H.inv_monAll o _ col _ σ i i' hi t

end Fam

end Formalism.L2.FormalSeriesBounds.RF
