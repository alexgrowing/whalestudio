import Formalism.LocalToGlobal.CharacterGerms.CharacterHypothesisUnramified
import Formalism.LocalToGlobal.CharacterGerms.RowTieCharS

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I0 : Type} [Fintype I0]

def UPCharSelfSt (Y : FBChart C V OE dd) (p : SelfData Y d I0) (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) : Prop :=
  ∃ (h : Fin 2 → ℕ) (χ : ∀ g, Fin (h g) → Fin 2 → PS C 1 dd), (∀ g i col, Y.IsChar (χ g i col)) ∧
    ∀ g a, p.big g a →
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I0 // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        ((Y.rawSelf p).AltC →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' (gam V.l) : ℝ) : WithTop ℝ)) ∧
        ((∀ b, p.big g b) →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' 0 : ℝ) : WithTop ℝ))

theorem chStSelf_of_upChar (Y : FBChart C V OE dd) (p : SelfData Y d I0) (hr : (Y.rawSelf p).RankHyp)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (h : UPCharSelfSt Y p Hc) : RawChart.CHSt Hc := by
  obtain ⟨hh, χ, hχ, hUP⟩ := h
  exact CH_of_UP (fun g => RawChart.cart (Hc g)) p.n p.j p.j' p.big hr.big_compl hh
    (fun g i x => p.yOf g (χ g i) x) (fun g i x => p.yOf_int g (hχ g i) x) hUP
    (fun g i S t ht => charGermSelf_holds C V OE dd Y d I0 p Hc (χ g i) (hχ g i) g S t ht)

theorem isChar_one (Y : FBChart C V OE dd) : Y.IsChar (1 : PS C 1 dd) := by
  refine ⟨fun mu => ?_, map_one _, ?_⟩
  · rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · simp only [ev_one, mul_one]

theorem dlogC_one (i : Fin dd) : dlogC (1 : PS C 1 dd) i = 0 := by
  simp [dlogC, MvPowerSeries.coeff_one]

theorem lenCoker_smul {v : AddValuation C (WithTop ℝ)} {m h : ℕ} (B : Matrix (Fin m) (Fin h) C) {γ : C} (hγ : v γ = 0) :
    S4.lenCoker v (γ • B) = S4.lenCoker v B := by
  unfold S4.lenCoker
  congr 1
  funext g
  have e : (γ • B).submatrix id g = γ • B.submatrix id g := Matrix.ext fun i j => rfl
  rw [e, Matrix.det_smul, AddValuation.map_mul, AddValuation.map_pow, hγ, smul_zero, zero_add]

def rk0 {Y : FBChart C V OE dd} (p : SelfData Y d I0) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I0 => p.ty0 c = b).card

def rkS {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I0 => (Y.rawSelf p).ty g c = b).card

def a0Of {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a : ZMod d) : ZMod d := if g = 0 then a else a + p.hd

theorem ty_iff {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a : ZMod d) (c : I0) :
    (Y.rawSelf p).ty g c = a ↔ p.ty0 c = a0Of p g a := by
  show (if g = 0 then p.ty0 c else p.ty0 c + p.hd) = a ↔ p.ty0 c = (if g = 0 then a else a + p.hd)
  split_ifs with hg
  · exact Iff.rfl
  · constructor
    · intro h
      rw [← h, add_assoc, p.hd_two, add_zero]
    · intro h
      rw [h, add_assoc, p.hd_two, add_zero]

theorem rk_shift {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a k : ZMod d) :
    rk0 p (a0Of p g a + k + p.hd) = rkS p (1 - g) (a + k) := by
  have h : a0Of p g a + k + p.hd = a0Of p (1 - g) (a + k) := by
    have h2 := p.hd_two
    fin_cases g <;> simp [a0Of] <;> linear_combination h2
  unfold rk0 rkS
  simp only [ty_iff, h]

def AFBoundS (Y : FBChart C V OE dd) (p : SelfData Y d I0) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (FR : Fin dd → PS R 2 dd) : Prop :=
  ∀ a0 : ZMod d, ∃ (s : ℕ) (e : Fin s ≃ {x : I0 // p.ty0 x = a0}) (W : Fin s → Fin dd → R) (xs : NNReal),
    (∀ c i, algebraMap R C (W c i) = p.e (e c) i) ∧ HasAF vm FR W xs ∧
      vm (V.l : C) ^ (S4.frobSum V.l (fun b => rk0 p (b + p.hd)) a0) ≤ xs

theorem exists_unit_col {Y : FBChart C V OE dd} (p : SelfData Y d I0) (a0 : ZMod d) (g : Fin 2) :
    ∃ col : Fin 2, V.v (p.gm a0 col g) = 0 := by
  by_contra hno
  push Not at hno
  have hpos : ∀ col, V.MM (p.gm a0 col g) := fun col =>
    lt_of_le_of_ne (SelfConjugateGermZero.gm_int Y p a0 col g) (Ne.symm (hno col))
  have h1 := p.gm_hyp a0 (1 - g) g
  have hne : (1 - g : Fin 2) ≠ g := by fin_cases g <;> decide
  rw [if_neg hne] at h1
  have h2 : V.MM (∑ r, p.gm (a0 + p.hd) r (1 - g) * p.gm a0 r g) := by
    rw [Fin.sum_univ_two]
    have t : ∀ r, V.MM (p.gm (a0 + p.hd) r (1 - g) * p.gm a0 r g) := fun r => by
      unfold VF.MM
      rw [V.v.map_mul]
      exact lt_of_lt_of_le (hpos r) (le_add_of_nonneg_left (SelfConjugateGermZero.gm_int Y p _ r _))
    exact lt_of_lt_of_le (lt_min (t 0) (t 1)) (V.v.map_add _ _)
  rw [h1] at h2
  unfold VF.MM at h2
  rw [V.v.map_one] at h2
  exact lt_irrefl _ h2

theorem upCharS_of_afBound (Y : FBChart C V OE dd) (p : SelfData Y d I0) (hr : (Y.rawSelf p).RankHyp)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) (h : AFBoundS Y p vm R FR) : UPCharSelfSt Y p Hc := by
  have hR : ∀ x : R, V.Ge 0 (algebraMap R C x) := fun x => vA_nonneg hT hv h0 h1 x
  have hl1 : 1 < V.l := V.l_prime.one_lt
  have key : ∀ g a, ∃ (N : ℕ) (u : Fin N → Fin 2 → PS C 1 dd), (∀ k col, Y.IsChar (u k col)) ∧
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I0 // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        S4.lenCoker V.v (Matrix.of fun c k => p.yOf g (u k) (e c)) ≤
          ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
    intro g a
    obtain ⟨s, e0, W, xs, hW, ⟨N, u, hu, hx⟩, hS⟩ := h (a0Of p g a)
    let e1 : Fin s ≃ {x : I0 // (Y.rawSelf p).ty g x = a} :=
      e0.trans (Equiv.subtypeEquivRight fun x => (ty_iff p g a x).symm)
    have he1 : ∀ c, ((e1 c : {x : I0 // (Y.rawSelf p).ty g x = a}) : I0) = e0 c := fun _ => rfl
    have hs : s = pT (fun g => RawChart.cart (Hc g)) g a := by
      have := Fintype.card_congr e1
      rw [Fintype.card_fin, Fintype.card_subtype] at this
      exact this
    subst hs
    obtain ⟨col0, hcol⟩ := exists_unit_col p (a0Of p g a) g
    refine ⟨N, fun k col => if col = col0 then toC (u k) else 1, fun k col => ?_, e1, ?_⟩
    · show Y.IsChar (if col = col0 then toC (u k) else 1)
      split_ifs
      · exact isChar_of_isCh Y hR FR hF hF0 (hu k)
      · exact isChar_one Y
    · have hb := lenCoker_le_of_hasLen hT hv h0 h1 W u hx hS
      have hsum : S4.frobSum V.l (fun b => rk0 p (b + p.hd)) (a0Of p g a) = S4.frobSum V.l (rkS p (1 - g)) a := by
        unfold S4.frobSum
        exact tsum_congr fun k => by beta_reduce; rw [rk_shift]
      rw [hsum] at hb
      have hm : (Matrix.of fun c k => p.yOf g (fun col => if col = col0 then toC (u k) else 1) (e1 c)) =
          p.gm (a0Of p g a) col0 g •
            (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) := by
        ext c k
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
        unfold SelfData.yOf
        rw [Finset.sum_eq_single col0]
        · beta_reduce
          rw [if_pos rfl, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          show _ * (p.gm (p.ty0 (e1 c)) col0 g * p.e (e1 c) i) = _
          rw [he1, (e0 c).2, hW]
          ring
        · intro col _ hne
          beta_reduce
          rw [if_neg hne]
          exact Finset.sum_eq_zero fun i _ => by rw [dlogC_one, zero_mul]
        · intro hne
          exact absurd (Finset.mem_univ _) hne
      have hfin : S4.lenCoker V.v
          (Matrix.of fun c k => p.yOf g (fun col => if col = col0 then toC (u k) else 1) (e1 c)) ≤
          ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
        rw [hm, lenCoker_smul _ hcol]
        exact hb
      exact hfin
  choose N u hu e he using key
  let eq : ∀ g, (Σ a : ZMod d, Fin (N g a)) ≃ Fin (Fintype.card (Σ a : ZMod d, Fin (N g a))) := fun g => Fintype.equivFin _
  refine ⟨fun g => Fintype.card (Σ a : ZMod d, Fin (N g a)),
    fun g i => u g ((eq g).symm i).1 ((eq g).symm i).2, fun g i col => hu g _ _ col, fun g a hb => ?_⟩
  have hle' : S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e g a c)) ≤
      ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
    refine le_trans (lenCoker_mono V.v _ (fun k : Fin (N g a) => eq g ⟨a, k⟩)) ?_
    have e3 : (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e g a c)).submatrix id
        (fun k : Fin (N g a) => eq g ⟨a, k⟩) = Matrix.of fun c k => p.yOf g (u g a k) (e g a c) := by
      ext c k
      simp only [Matrix.submatrix_apply, Matrix.of_apply, id]
      rw [Equiv.symm_apply_apply]
    rw [e3]
    exact he g a
  have hc1 : ∀ b, p.big g b → rkS p (1 - g) b = p.j' := fun b hb' =>
    hr.rk_small (1 - g) b (fun hh => (hr.big_compl g b).mp hh hb')
  have hc2 : ∀ b, ¬ p.big g b → rkS p (1 - g) b = p.n + p.j := fun b hb' =>
    hr.rk_big (1 - g) b ((hr.big_compl g b).mpr hb')
  refine ⟨e g a, fun hA => ?_, fun hB => ?_⟩
  · rw [← frobSum_conj_alt hl1 p.n p.j p.j' (p.big g) (alt_step p.big hr.big_compl hA g) (rkS p (1 - g)) hc1 hc2 a hb]
    exact hle'
  · rw [← frobSum_conj_all hl1 p.n p.j p.j' (rkS p (1 - g)) (fun b => hc1 b (hB b)) a]
    exact hle'

end UpFBr

end Formalism.L2.FormalSeriesBounds
