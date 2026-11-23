import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEnd

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal.MapSumDiagonal

theorem map_sum_of_pred {R Q α : Type} [AddCommMonoid R] [AddCommMonoid Q] (P : R → Prop) (f : R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (f0 : f 0 = 0)
    (fadd : ∀ a b, P a → P b → f (a + b) = f a + f b) (s : Finset α) (a : α → R) (ha : ∀ i, P (a i)) :
    P (∑ i ∈ s, a i) ∧ f (∑ i ∈ s, a i) = ∑ i ∈ s, f (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [P0, f0]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact ⟨Padd _ _ (ha i) ih.1, by rw [fadd _ _ (ha i) ih.1, ih.2]⟩

theorem split_abstract {R Q Orb : Type} [Ring R] [AddCommGroup Q] [Fintype Orb] (P : R → Prop) (h : R → R → Q)
    (P0 : P 0) (Padd : ∀ a b, P a → P b → P (a + b)) (Pmul : ∀ a b, P a → P b → P (a * b))
    (h0 : ∀ a, h a 0 = 0 ∧ h 0 a = 0)
    (hl : ∀ a a' b, P a → P a' → P b → h (a + a') b = h a b + h a' b)
    (hr : ∀ a a' b, P a → P a' → P b → h b (a + a') = h b a + h b a')
    (hs : ∀ a b, P a → P b → h b a = h a b)
    (W W' : R) (hW : P W) (hW' : P W') (hadj : ∀ a b, P a → P b → h (W * a) b = h a (W' * b))
    (hWW : W + W' = 1) (π : Orb → Fin 2 → R) (hπ : ∀ o g, P (π o g))
    (horth : ∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → h (π o g) (W * π o' g') = 0) :
    ∑ o, h (π o 0) (π o 1) = h (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) := by
  classical
  have hWπ : ∀ o g, P (W * π o g) := fun o g => Pmul _ _ hW (hπ o g)
  have e1 : (∑ o, ∑ g, π o g) = ∑ p : Orb × Fin 2, π p.1 p.2 := by rw [Fintype.sum_prod_type]
  have hB : P (∑ p : Orb × Fin 2, W * π p.1 p.2) :=
    (map_sum_of_pred P (fun _ => (0 : Q)) P0 Padd rfl (by simp) _ _ (fun p : Orb × Fin 2 => hWπ p.1 p.2)).1
  rw [e1, Finset.mul_sum]
  rw [(map_sum_of_pred P (fun a => h a (∑ p : Orb × Fin 2, W * π p.1 p.2)) P0 Padd (h0 _).2
    (fun a b ha hb => hl a b _ ha hb hB) Finset.univ (fun p : Orb × Fin 2 => π p.1 p.2)
    (fun p => hπ p.1 p.2)).2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun o _ => ?_
  have e2 : ∀ g, h (π o g) (∑ p : Orb × Fin 2, W * π p.1 p.2) = h (π o g) (W * π o (1 - g)) := by
    intro g
    rw [(map_sum_of_pred P (fun a => h (π o g) a) P0 Padd (h0 _).1
      (fun a b ha hb => hr a b _ ha hb (hπ o g)) Finset.univ (fun p : Orb × Fin 2 => W * π p.1 p.2)
      (fun p => hWπ p.1 p.2)).2]
    refine Finset.sum_eq_single (o, 1 - g) ?_ (by simp)
    intro p _ hp
    apply horth
    rintro ⟨h1, h2⟩
    exact hp (Prod.ext h1.symm h2)
  rw [Fin.sum_univ_two, e2, e2, sub_zero, sub_self, ← hs _ _ (hπ o 1) (hWπ o 0),
    hadj _ _ (hπ o 0) (hπ o 1), ← hr _ _ _ (hWπ o 1) (Pmul _ _ hW' (hπ o 1)) (hπ o 0), ← add_mul, hWW, one_mul]

theorem diagonal_split : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : RawChart C d I κ), RLaw X V → ∀ (Orb : Type) [Fintype Orb] (π : Orb → Fin 2 → Matrix κ κ C) (W W' : Matrix κ κ C), (∀ o g, IntEnd X V (π o g)) → IsEnd X V W W' → W + W' = 1 → (∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → hEnd X (π o g) (W * π o' g') ∈ logInt V κ) → (∑ o, hEnd X (π o 0) (π o 1)) - hEnd X (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ := by
  intro C _ _ V d I _ κ _ _ X hR Orb _ π W W' hπ hE hWW horth
  obtain ⟨P0, Padd, Pmul, h0, hadd, hs, hadj⟩ := GlobalTheory.RowVal.EndCalc.end_calc C V d I κ X hR
  let q := QuotientAddGroup.mk' (logInt V κ)
  have hq : ∀ a, q a = 0 ↔ a ∈ logInt V κ := fun a => QuotientAddGroup.eq_zero_iff a
  have key := split_abstract (IntEnd X V) (fun a b => q (hEnd X a b)) P0 Padd Pmul
    (fun a => ⟨by simp only [(h0 a).1, map_zero], by simp only [(h0 a).2, map_zero]⟩)
    (fun a a' b ha ha' hb => by
      have := (hq _).2 (hadd a a' b ha ha' hb).1
      rw [map_sub, map_add, sub_eq_zero] at this
      exact this.symm)
    (fun a a' b ha ha' hb => by
      have := (hq _).2 (hadd a a' b ha ha' hb).2
      rw [map_sub, map_add, sub_eq_zero] at this
      exact this.symm)
    (fun a b ha hb => by
      have := (hq _).2 (hs a b ha hb)
      rwa [map_sub, sub_eq_zero] at this)
    W W' hE.1 hE.2.1
    (fun a b ha hb => by
      have := (hq _).2 (hadj W W' a b hE ha hb)
      rwa [map_sub, sub_eq_zero] at this)
    hWW π hπ (fun o g o' g' hn => (hq _).2 (horth o g o' g' hn))
  rw [← hq, map_sub, map_sum, sub_eq_zero]
  exact key

end GlobalTheory.RowVal.MapSumDiagonal
