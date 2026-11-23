import Formalism.LocalRingCardinality.DataKerI

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions MvPolynomial

section Det

theorem det_ind {p N : ℕ} (I : Fin p ↪o Fin N) {C : Type} [CommRing C] :
    (Matrix.of fun i k : Fin p => if (i : ℕ) = (I k : ℕ) then (1 : C) else 0).det =
      if ∀ k, (I k : ℕ) = k then 1 else 0 := by
  split_ifs with h
  · have : (Matrix.of fun i k : Fin p => if (i : ℕ) = (I k : ℕ) then (1 : C) else 0) = 1 := by
      ext i k
      simp only [Matrix.of_apply, Matrix.one_apply, h k, Fin.val_inj]
    rw [this, Matrix.det_one]
  · push Not at h
    obtain ⟨k, hk⟩ := h
    have hge : ∀ j : Fin p, (j : ℕ) ≤ (I j : ℕ) := fun j => by
      have := StrictMono.id_le (f := fun n : ℕ => if hn : n < p then (I ⟨n, hn⟩ : ℕ) + 0 else n + N) (by
        intro a b hab
        by_cases hb : b < p
        · have ha : a < p := lt_trans hab hb
          simp only [dif_pos ha, dif_pos hb, add_zero]
          exact I.strictMono (show (⟨a, ha⟩ : Fin p) < ⟨b, hb⟩ from hab)
        · simp only [dif_neg hb]
          by_cases ha : a < p
          · simp only [dif_pos ha, add_zero]
            have := (I ⟨a, ha⟩).2
            omega
          · simp only [dif_neg ha]; omega) j
      simpa [j.2] using this
    have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le _) k.2
    let last : Fin p := ⟨p - 1, by omega⟩
    have hlast : p ≤ (I last : ℕ) := by
      have h1 : (k : ℕ) < (I k : ℕ) := lt_of_le_of_ne (hge k) (Ne.symm hk)
      have h2 : ∀ n : ℕ, ∀ hn : (k : ℕ) + n < p, (I k : ℕ) + n ≤ (I ⟨k + n, hn⟩ : ℕ) := by
        intro n
        induction n with
        | zero => intro hn; simp
        | succ n ih =>
          intro hn
          have h3 := ih (by omega)
          have hlt : (I ⟨k + n, by omega⟩ : ℕ) < (I ⟨k + (n + 1), hn⟩ : ℕ) :=
            I.strictMono (show (⟨k + n, by omega⟩ : Fin p) < ⟨k + (n + 1), hn⟩ from by
              rw [Fin.lt_iff_val_lt_val]; simp)
          omega
      have h4 := h2 (p - 1 - k) (by omega)
      have e : (⟨k + (p - 1 - k), by omega⟩ : Fin p) = last := Fin.ext (by simp [last]; omega)
      rw [e] at h4
      omega
    refine Matrix.det_eq_zero_of_column_eq_zero last fun i => ?_
    simp only [Matrix.of_apply]
    rw [if_neg]
    have := i.2
    omega

end Det

section Eval

variable {Lt : Type} (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime]

def xS : Lt × ℕ × Fin N0 → ℂ_[l] := fun k => if k.2.1 = (k.2.2 : ℕ) then 1 else 0

def zS : Lt × Fin N0 × Fin N1 → ℂ_[l] := fun k => if (k.2.1 : ℕ) = (k.2.2 : ℕ) then 1 else 0

open Classical in

def ThE : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l] := fun μ =>
  if ∀ k ∈ μ.support, zS N0 N1 l k = 1 then (μ.prod fun _ n => (n.factorial : ℂ_[l]))⁻¹ else 0

open Classical in
theorem prod_ind {σ : Type} (t : σ → ℂ_[l]) (ht : ∀ k, t k = 0 ∨ t k = 1) (μ : σ →₀ ℕ) :
    (μ.prod fun k e => t k ^ e) = if ∀ k ∈ μ.support, t k = 1 then 1 else 0 := by
  split_ifs with h
  · exact Finset.prod_eq_one fun k hk => by show t k ^ μ k = 1; rw [h k hk, one_pow]
  · push Not at h
    obtain ⟨k, hk, hne⟩ := h
    have h0 : t k = 0 := (ht k).resolve_right hne
    exact Finset.prod_eq_zero hk (by show t k ^ μ k = 0; rw [h0, zero_pow (Finsupp.mem_support_iff.mp hk)])

theorem fac_ne (μ : (Lt × Fin N0 × Fin N1) →₀ ℕ) : (μ.prod fun _ n => (n.factorial : ℂ_[l])) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

open Classical in
theorem fac_ThE (μ : (Lt × Fin N0 × Fin N1) →₀ ℕ) :
    (μ.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff μ (ThE N0 N1 l) =
      μ.prod fun k e => zS N0 N1 l k ^ e := by
  rw [prod_ind l (zS N0 N1 l) (fun k => by unfold zS; split_ifs <;> simp) μ]
  show _ * ThE N0 N1 l μ = _
  unfold ThE
  split_ifs
  · exact mul_inv_cancel₀ (fac_ne N0 N1 l μ)
  · exact mul_zero _

theorem eval_applyAt0 (P : MvPolynomial (KM.XZ Lt N0 N1) ℤ) :
    MvPolynomial.eval (xS N0 l) (KM.applyAt0 N0 N1 l (ThE N0 N1 l) P) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l)) P := by
  unfold KM.applyAt0
  rw [map_sum, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  set e := Finsupp.sumFinsuppEquivProdFinsupp μ with he
  have hμ : μ = Finsupp.sumElim e.1 e.2 := by
    rw [he]
    ext k
    cases k <;> rfl
  have hprod : (∏ i ∈ μ.support, Sum.elim (xS N0 l) (zS N0 N1 l) i ^ μ i) =
      (e.1.prod fun k n => xS N0 l k ^ n) * (e.2.prod fun k n => zS N0 N1 l k ^ n) := by
    show μ.prod (fun i n => Sum.elim (xS N0 l) (zS N0 N1 l) i ^ n) = _
    conv_lhs => rw [hμ]
    rw [Finsupp.prod_sumElim]
    rfl
  rw [hprod, ← fac_ThE N0 N1 l e.2]
  simp only [eq_intCast, Int.cast_id]
  ring

theorem sum_xz {p : ℕ} (hp : p ≤ N0) (s : Lt) (i : Fin p) (b : Fin N1) :
    (∑ a : Fin N0, xS N0 l (s, (i : ℕ), a) * zS N0 N1 l (s, a, b)) = if (i : ℕ) = (b : ℕ) then 1 else 0 := by
  rw [Finset.sum_eq_single ⟨i, lt_of_lt_of_le i.2 hp⟩]
  · simp [xS, zS]
  · intro a _ ha
    have : (i : ℕ) ≠ (a : ℕ) := fun h => ha (Fin.ext h.symm)
    simp [xS, this]
  · simp

variable [Fintype Lt] [DecidableEq Lt]

open Classical in
theorem eval_Gxz (nu : Lt → YoungDiagram) (hnu : ∀ s c, (nu s).colLen c ≤ N0) (I : KM.ColChoice N1 nu) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l)) (KM.Gxz N0 N1 nu I) =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), if ∀ k, (I s c k : ℕ) = k then 1 else 0 := by
  unfold KM.Gxz
  rw [← MvPolynomial.coe_eval₂Hom, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold KM.minorXZ
  have hM : (MvPolynomial.eval₂Hom (Int.castRingHom ℂ_[l]) (Sum.elim (xS N0 l) (zS N0 N1 l))).mapMatrix
      (Matrix.of fun i k : Fin ((nu s).colLen c) => ∑ a : Fin N0,
        MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I s c k))) =
      Matrix.of fun i k : Fin ((nu s).colLen c) => if (i : ℕ) = (I s c k : ℕ) then (1 : ℂ_[l]) else 0 := by
    ext i k
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, map_sum]
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    exact sum_xz N0 N1 l (hnu s c) s i (I s c k)
  rw [RingHom.map_det, hM, det_ind]

open Classical in
theorem eval_nablaX (nu : Lt → YoungDiagram) (J : KM.ColChoice N0 nu) :
    MvPolynomial.eval (xS N0 l) (MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.nablaX N0 nu J)) =
      ∏ s, ∏ c : Fin ((nu s).rowLen 0), if ∀ k, (J s c k : ℕ) = k then 1 else 0 := by
  rw [MvPolynomial.eval_map]
  unfold KM.nablaX
  rw [← MvPolynomial.coe_eval₂Hom, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, ← det_ind (C := ℂ_[l]) (J s c)]
  congr 1
  ext i k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X, xS]

end Eval

end Formalism.BasicNotions.Examples₂.NZ
