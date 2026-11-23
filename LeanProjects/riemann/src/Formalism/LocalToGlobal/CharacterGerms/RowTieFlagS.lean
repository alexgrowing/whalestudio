import Formalism.LocalToGlobal.CharacterGerms.RowTieMainS

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Flag

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {m : ZMod d → ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

def idxS (hd : ZMod d) (g : Fin 2) (t : ZMod d) : ZMod d := if g = 0 then t else t - hd

theorem rkF_sigmaS (hd : ZMod d) (X : RowData C V d (fun _ => Σ a : ZMod d, Fin (m a)) J)
    (hty : ∀ (g : Fin 2) (x : Σ a : ZMod d, Fin (m a)), (X.G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd)
    (g : Fin 2) (t : ZMod d) : X.rkF g t = m (idxS hd g t) := by
  unfold RowData.rkF
  refine Finset.card_eq_of_equiv_fin
    ((Equiv.subtypeEquivRight fun c => ?_).trans (Equiv.sigmaSubtype (idxS hd g t)))
  rw [Finset.mem_filter, hty]
  simp only [Finset.mem_univ, true_and]
  unfold idxS
  by_cases hg : g = 0
  · simp only [if_pos hg]
  · simp only [if_neg hg]
    exact eq_sub_iff_add_eq.symm

def stdFlagS (hd : ZMod d) (X : RowData C V d (fun _ => Σ a : ZMod d, Fin (m a)) J)
    (hty : ∀ (g : Fin 2) (x : Σ a : ZMod d, Fin (m a)), (X.G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd) :
    Flag X where
  en := fun g t q => ⟨idxS hd g t, ⟨q.val, (rkF_sigmaS hd X hty g t) ▸ q.isLt⟩⟩
  en_inj := fun g t q q' h => by
    have h1 := eq_of_heq (Sigma.mk.inj h).2
    exact Fin.ext (Fin.mk.inj_iff.1 h1)
  en_ty := fun g t q => by
    rw [hty]
    unfold idxS
    by_cases hg : g = 0
    · simp [hg]
    · simp [hg]

end Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

theorem rowTieSelf_std (G : GeoInS Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E)))) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : LabS E C Orb 2}
    (ha : LabSArith V io ι lab) (hr : lab.RankOK Dw) :
    ∃ (X : ∀ o, RowData C V 2 (fun _ => lab.II Dw o) (JJ fun _ => lab.II Dw o)) (F : ∀ o, Flag (X o)),
      (∀ o, (X o).n = lab.n ∧ (X o).m = lab.j + lab.j' ∧ (X o).rh = 0 ∧ (∀ g b, (X o).big g b ↔ lab.big o g b) ∧
        ∀ g t, (X o).rkF g t = Dw.mult (lab.tau o (idxS lab.hd g t))) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a n →
        ∀ (N : ℕ) (_ : Fin N × Fin 2 ↪ Fin n) (nW : ℕ), nW ≤ 2 * N + 1 →
        ∀ gaC : Orb → ZMod 2 → ℕ → ℕ,
        (∀ o, (X o).Alt) → lab.j' < lab.n → (∀ o s q, gaC o s q ≠ 0 → 1 ≤ q ∧ q ≤ (X o).rkF 0 s) →
        WtTieC Dw.mult lab.tau gaC (fun τ i => a (τ, i)) →
        ValBlocksC X F nW gaC ν := by
  obtain ⟨X, hX, hV⟩ := rowTieSelf_main G hstar hι hd hY ha hr
  refine ⟨X, fun o => stdFlagS lab.hd (X o) (hX o).2.2.2.2, fun o => ⟨(hX o).1, (hX o).2.1, (hX o).2.2.1, (hX o).2.2.2.1,
    fun g t => rkF_sigmaS lab.hd (X o) (hX o).2.2.2.2 g t⟩, ?_⟩
  intro a n ν hν N pl nW hn gaC hA hj supp tie
  exact hV a n ν hν N pl _ nW hn gaC (fun _ _ _ _ => rfl) hA hj supp tie

end Formalism.L2.FormalSeriesBounds
