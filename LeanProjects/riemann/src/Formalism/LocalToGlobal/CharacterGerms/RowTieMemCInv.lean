import Formalism.LocalToGlobal.CharacterGerms.RowTieMemC
import Formalism.LocalToGlobal.CharacterGerms.NormOneRowInvariant

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Atom

variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

theorem rowShift_C (σ : T) (i i' : Fin (r σ)) (t z : C) :
    rowShift r n C σ i i' t (MvPolynomial.C z) = MvPolynomial.C z := (rowShift r n C σ i i' t).commutes z

variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)

theorem shift_same (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (t : C)
    (ρ : Fin N) (c : Fin N') (h : ¬ (σ = σ0 ∧ c.val = i.val)) :
    rowShift r n C σ i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) := by
  rw [hΦ, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, rowShift_C, rowShift_X, hlt, if_neg]
  intro e
  apply h
  exact ⟨(congrArg (fun x : T × ℕ × Fin n => x.1) e).symm, congrArg (fun x : T × ℕ × Fin n => x.2.1) e⟩

theorem shift_add (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (i i' : Fin (r σ0)) (t : C)
    (ρ : Fin N) (c c' : Fin N') (hc : c.val = i.val) (hc' : c'.val = i'.val) :
    rowShift r n C σ0 i i' t (Φ (X (ρ, c))) = Φ (X (ρ, c)) + MvPolynomial.C t * Φ (X (ρ, c')) := by
  rw [hΦ, hΦ, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h2 : (lt (ρ, c) q).2.2 = colf ρ q := congrArg (fun x : T × ℕ × Fin n => x.2.2) (hlt ρ c q)
  have h1 : keyL (lt (ρ, c) q) = (σ0, i.val, (lt (ρ, c) q).2.2) := by rw [hlt, hc, h2]
  rw [map_mul, rowShift_C, rowShift_X, if_pos h1]
  have h3 : (⟨σ0, i', (lt (ρ, c) q).2.2⟩ : Letter T r n) = lt (ρ, c') q := by
    apply keyL_inj
    rw [hlt, hc', h2]
    rfl
  rw [h3]
  ring

theorem rowShift_minor_lin (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (k : ℕ) :
    rowShift r n C σ i i' t (Φ (minorK C N N' k)) = Φ (minorK C N N' k) := by
  unfold minorK
  split_ifs with h
  · set A : Matrix (Fin k) (Fin k) (MvPolynomial (Letter T r n) C) :=
      Matrix.of fun b c => Φ (X (Fin.castLE h.1 b, Fin.castLE h.2 c)) with hA
    have e1 : Φ (Matrix.of fun b c : Fin k =>
        (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') C)).det = A.det := by
      rw [AlgHom.map_det]
      congr 1
    rw [e1, AlgHom.map_det]
    by_cases hc : σ = σ0 ∧ i.val < k
    · obtain ⟨rfl, hik⟩ := hc
      have hi' : i'.val < i.val := hi
      let ci : Fin k := ⟨i.val, hik⟩
      let ci' : Fin k := ⟨i'.val, lt_trans hi' hik⟩
      have hne : ci ≠ ci' := by
        intro e
        have h3 : ci.val = ci'.val := congrArg Fin.val e
        have h4 : i.val = i'.val := h3
        omega
      have e2 : (rowShift r n C σ i i' t).mapMatrix A =
          A.updateCol ci (fun b => A b ci + (MvPolynomial.C t : MvPolynomial (Letter T r n) C) • A b ci') := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply]
        simp only [hA, Matrix.of_apply]
        by_cases hcc : c = ci
        · subst hcc
          rw [if_pos rfl, smul_eq_mul]
          exact shift_add Φ σ w lt colf hΦ hlt i i' t _ _ _ rfl rfl
        · rw [if_neg hcc]
          refine shift_same Φ σ w lt colf hΦ hlt σ i i' t _ _ ?_
          rintro ⟨_, e⟩
          exact hcc (Fin.ext e)
      rw [e2, Matrix.det_updateCol_add_smul_self A hne]
    · have e2 : (rowShift r n C σ i i' t).mapMatrix A = A := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply]
        simp only [hA, Matrix.of_apply]
        refine shift_same Φ σ0 w lt colf hΦ hlt σ i i' t _ _ ?_
        rintro ⟨e0, e⟩
        apply hc
        refine ⟨e0, ?_⟩
        have : c.val = i.val := e
        omega
      rw [e2]
  · simp

theorem rowShift_monomial_eq_self (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C)
    (e : ℕ → ℕ) : rowShift r n C σ i i' t (Φ (monP C N N' e)) = Φ (monP C N N' e) := by
  unfold monP
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_pow, map_pow, rowShift_minor_lin Φ σ0 w lt colf hΦ hlt σ i i' hi t k]

end Atom

section Fam

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N} {n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

def trueT (g : Fin 2) (s : ZMod 2) : ZMod 2 := if g = 0 then s else s + 1

theorem SelfConjugatePlaceSetting.en_fst (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2)
    (q : Fin ((X o).rkF g s)) : ((F o).en g s q).1 = trueT g s := by
  have h1 := (F o).en_ty g s q
  rw [H.hty o g] at h1
  unfold trueT
  generalize ((F o).en g s q).1 = u at h1 ⊢
  split_ifs at h1 ⊢ with hg
  · exact h1
  · subst h1
    have h2 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [add_assoc, h2, add_zero]

variable (r tau gm) in

def PsiS (o : Orb) {M : ℕ} (col : Fin M → Fin N) :
    MvPolynomial (Fin M × WV fun _ => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  (subG r tau gm plc).comp (rename fun x : Fin M × WV fun _ => IIs r tau o =>
    ((col x.1, (⟨o, x.2⟩ : WVO fun o (_ : Fin 2) => IIs r tau o))))

theorem SelfConjugatePlaceSetting.inv_minor (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k)) := by
  refine rowShift_minor_lin ((PsiS r tau gm plc o col).comp (rename ((F o).letter g s))) (tau o (trueT g s))
    (fun _ q => gm o (trueT g s) q g)
    (fun x q => ⟨tau o ((F o).en g s x.2).1, ((F o).en g s x.2).2, plc (col x.1, q)⟩) (fun ρ q => plc (col ρ, q)) ?_ ?_
    σ i i' hi t k
  · intro x
    rw [AlgHom.comp_apply, rename_X]
    unfold PsiS
    rw [AlgHom.comp_apply, rename_X]
    unfold subG
    rw [aeval_X]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e2 : gm o ((F o).en g s x.2).1 q g = gm o (trueT g s) q g := by rw [H.en_fst]
    exact congrArg (fun z : C => MvPolynomial.C z * MvPolynomial.X
      (⟨tau o ((F o).en g s x.2).1, ((F o).en g s x.2).2, plc (col x.1, q)⟩ : Letter T r n)) e2
  · intro ρ c q
    show (tau o ((F o).en g s c).1, ((F o).en g s c).2.val, plc (col ρ, q)) = _
    simp only [Prod.mk.injEq]
    exact ⟨congrArg (tau o) (H.en_fst o g s c), H.std o g s c, trivial⟩

theorem SelfConjugatePlaceSetting.inv_mon (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (e : ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (monP C M ((X o).rkF g s) e))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (monP C M ((X o).rkF g s) e)) := by
  unfold monP
  simp only [map_prod, map_pow]
  exact Finset.prod_congr rfl fun k _ => by rw [H.inv_minor plc o g s col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_bi (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g g' : Fin 2) (s s' : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k e1 e2 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2)) =
      PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2) := by
  simp only [map_mul, map_pow]
  rw [H.inv_minor plc o g s col k σ i i' hi t, H.inv_minor plc o g' s' col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_ch (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod 2) {M : ℕ}
    (col : Fin M → Fin N) (k e1 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1)) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1) := by
  rw [map_pow, map_pow, H.inv_minor plc o g s col k σ i i' hi t]

theorem SelfConjugatePlaceSetting.inv_monAll (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) {M : ℕ}
    (col : Fin M → Fin N) (e : ZMod 2 → ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (∏ s : ZMod 2, rename ((F o).letter g s) (monP C M ((X o).rkF g s) (e s)))) =
      PsiS r tau gm plc o col (∏ s : ZMod 2, rename ((F o).letter g s) (monP C M ((X o).rkF g s) (e s))) := by
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun s _ => H.inv_mon plc o g s col (e s) σ i i' hi t

theorem SelfConjugatePlaceSetting.inv_poly (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) (b : GlobalTheory 2) (col : Fin (b.what₂ (X o).n) → Fin N)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (b.poly (X o) (F o))) = PsiS r tau gm plc o col (b.poly (X o) (F o)) := by
  cases b with
  | bi g s e y => exact H.inv_bi plc o g (1 - g) s (s + (e : ZMod 2)) col (X o).n _ _ σ i i' hi t
  | ch g s u => exact H.inv_ch plc o g s col (X o).n u σ i i' hi t
  | mon g e M => exact H.inv_monAll plc o g col e σ i i' hi t

theorem subG_blkProd :
    subG r tau gm plc (blkProd X F N L pl) =
      ∏ o, ∏ i, PsiS r tau gm plc o (fun ρ => plAt N pl o ⟨i, ρ⟩) ((blkAt L o i).poly (X o) (F o)) := by
  unfold blkProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun o _ => ?_
  unfold toAll prodAll
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rename_rename]
  rfl

end Fam

theorem isotropic_to_standard_substitution_invariant : IsotropicToStdSubstLineInvariant := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc σ i i' hi t
  rw [subG_blkProd, map_prod]
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => H.inv_poly plc o _ _ σ i i' hi t

end Formalism.L2.FormalSeriesBounds.RF
