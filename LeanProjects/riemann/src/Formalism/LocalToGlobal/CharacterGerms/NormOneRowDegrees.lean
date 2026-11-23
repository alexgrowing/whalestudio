import Formalism.LocalToGlobal.CharacterGerms.BlockMembershipNormOne

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

namespace WeightHomogeneousMinors

section WH

variable {R : Type} [CommRing R]

theorem isWH_rename {σ τ : Type} {w : τ → ℕ} (f : σ → τ) {p : MvPolynomial σ R} {D : ℕ}
    (h : IsWeightedHomogeneous (w ∘ f) p D) : IsWeightedHomogeneous w (rename f p) D := by
  intro dd hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero f p dd hd
  rw [← h hu, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  rfl

theorem isWH_of_zero {σ : Type} {w : σ → ℕ} (hw : ∀ x, w x = 0) (p : MvPolynomial σ R) :
    IsWeightedHomogeneous w p 0 := by
  intro dd _
  simp [Finsupp.weight_apply, hw]

theorem isWH_congr {σ : Type} {w w' : σ → ℕ} (h : ∀ x, w x = w' x) {p : MvPolynomial σ R} {D : ℕ}
    (hp : IsWeightedHomogeneous w' p D) : IsWeightedHomogeneous w p D := by
  obtain rfl : w = w' := funext h
  exact hp

theorem isWH_deg {σ : Type} {w : σ → ℕ} {p : MvPolynomial σ R} {D D' : ℕ}
    (hp : IsWeightedHomogeneous w p D) (e : D = D') : IsWeightedHomogeneous w p D' := by
  subst e; exact hp

theorem isWH_minorK_gen {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (v : Fin N' → ℕ) (hw : ∀ x, w x = v x.2)
    (h : k ≤ N ∧ k ≤ N') :
    IsWeightedHomogeneous w (minorK R N N' k) (∑ c : Fin k, v (Fin.castLE h.2 c)) := by
  unfold minorK
  rw [dif_pos h, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hprod : IsWeightedHomogeneous w (∏ i : Fin k, (Matrix.of fun b c : Fin k =>
      (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') R)) (σ i) i)
      (∑ c : Fin k, v (Fin.castLE h.2 c)) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => by
      simp only [Matrix.of_apply]
      have hx := isWeightedHomogeneous_X R w (Fin.castLE h.1 (σ i), Fin.castLE h.2 i)
      rwa [hw] at hx
  intro dd hdd
  apply hprod
  intro h0
  apply hdd
  rw [MvPolynomial.coeff_smul, h0, smul_zero]

theorem sum_fin_ite (k c0 : ℕ) : (∑ c : Fin k, if (c : ℕ) = c0 then 1 else 0) = if c0 < k then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨c0, h⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro hc; exact hb (Fin.ext hc)
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro hc
    exact h (by rw [← hc]; exact c.2)

theorem isWH_minorK_row {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (P : Prop) [Decidable P] (c0 : ℕ)
    (hw : ∀ x, w x = if P ∧ (x.2 : ℕ) = c0 then 1 else 0) :
    IsWeightedHomogeneous w (minorK R N N' k) (if k ≤ N ∧ k ≤ N' ∧ P ∧ c0 < k then 1 else 0) := by
  by_cases h : k ≤ N ∧ k ≤ N'
  · have hg := isWH_minorK_gen (R := R) (fun c : Fin N' => if P ∧ (c : ℕ) = c0 then 1 else 0) hw h
    refine isWH_deg hg ?_
    by_cases hP : P
    · simp only [hP, true_and, Fin.coe_castLE]
      rw [sum_fin_ite]
      simp [h.1, h.2, hP]
    · simp [hP]
  · unfold minorK
    rw [dif_neg h, if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]
    exact isWeightedHomogeneous_one R w

end WH

section Let

variable {T : Type} (r : T → ℕ) (n : ℕ)

def wLet (σ : T) (c0 : Fin (r σ)) (ℓ : Letter T r n) : ℕ := ∑ b : Fin n, if ℓ = ⟨σ, c0, b⟩ then 1 else 0

theorem weight_wLet (σ : T) (c0 : Fin (r σ)) (m : Letter T r n →₀ ℕ) :
    Finsupp.weight (wLet r n σ c0) m = ∑ b : Fin n, m ⟨σ, c0, b⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [wLet, smul_eq_mul, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Finsupp.mem_support_iff, not_not] at h
    exact h.symm

variable {r n}

theorem letEq {τ1 τ2 : T} {c1 : Fin (r τ1)} {c2 : Fin (r τ2)} {b1 b2 : Fin n} :
    ((⟨τ1, (c1, b1)⟩ : Letter T r n) = ⟨τ2, (c2, b2)⟩) ↔ ((⟨τ1, c1⟩ : Σ σ, Fin (r σ)) = ⟨τ2, c2⟩ ∧ b1 = b2) := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, rfl⟩
    cases h1
    rfl

theorem wLet_mk (σ : T) (c0 : Fin (r σ)) (τ : T) (c : Fin (r τ)) (ρ : Fin n) :
    wLet r n σ c0 ⟨τ, (c, ρ)⟩ = if (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0 := by
  unfold wLet
  simp only [letEq]
  by_cases h : (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩
  · simp only [h, true_and, if_true]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]

end Let

section Block

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ}
  {Orb : Type} {tau : Orb → Fin 2 → ZMod d → T} {o0 : Orb} {J0 : Fin 2 → Type} [∀ g, Fintype (J0 g)]

def wRow (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (o0 : Orb) {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ)
    (x : Fin N × WV (IIof r tau o0)) : ℕ :=
  if x.2.1 = g0 ∧ x.2.2.1 = t0 ∧ (x.2.2.2 : ℕ) = c0 then 1 else 0

variable (X : RowData C V d (IIof r tau o0) J0) (F : Flag X)
  (hty : ∀ g (x : IIof r tau o0 g), (X.G g).ty (Sum.inl x) = x.1)
  (std : ∀ g t (c : Fin (X.rkF g t)), ((F.en g t c).2 : ℕ) = c.val)

include hty in
theorem en_fst (g : Fin 2) (t : ZMod d) (c : Fin (X.rkF g t)) : (F.en g t c).1 = t := by
  rw [← hty g (F.en g t c)]
  exact F.en_ty g t c

include hty in
theorem rkF_eq (g : Fin 2) (t : ZMod d) : X.rkF g t = r (tau o0 g t) := by
  unfold RowData.rkF
  have hc : (Finset.univ : Finset (Fin (r (tau o0 g t)))).card = r (tau o0 g t) := by simp
  rw [← hc]
  symm
  apply Finset.card_bij (fun c _ => (⟨t, c⟩ : IIof r tau o0 g))
  · intro c _; simp [hty]
  · intro c1 _ c2 _ h; simpa using h
  · rintro ⟨t', c⟩ hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hty] at hc'
    subst hc'
    exact ⟨c, Finset.mem_univ _, rfl⟩

include hty std in
theorem wRow_letter {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d)
    (x : Fin N × Fin (X.rkF g t)) :
    wRow r tau o0 g0 t0 c0 (F.letter g t x) = if (g = g0 ∧ t = t0) ∧ (x.2 : ℕ) = c0 then 1 else 0 := by
  unfold wRow Flag.letter
  simp only [en_fst X F hty, std]
  simp only [and_assoc]

include hty std in
theorem isWH_letter_minorK {N k : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) :
    IsWeightedHomogeneous (wRow r tau o0 (N := N) g0 t0 c0) (rename (F.letter g t) (minorK C N (X.rkF g t) k))
      (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0) := by
  apply isWH_rename
  exact isWH_minorK_row (R := C) (g = g0 ∧ t = t0) c0 (fun x => wRow_letter X F hty std g0 t0 c0 g t x)

include hty in
theorem num_ch (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) (u : ℕ) :
    u • (if X.n ≤ X.n ∧ X.n ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < X.n then 1 else 0) =
      ∑ k ∈ Finset.Icc (c0 + 1) (r (tau o0 g0 t0)), (if g0 = g ∧ t0 = t ∧ k = X.n then u else 0) := by
  by_cases hg : g0 = g ∧ t0 = t
  · obtain ⟨rfl, rfl⟩ := hg
    rw [rkF_eq X hty]
    simp only [le_refl, true_and, eq_self_iff_true]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_Icc]
    by_cases hc : X.n ≤ r (tau o0 g0 t0) ∧ c0 < X.n
    · rw [if_pos hc, if_pos ⟨by omega, hc.1⟩, smul_eq_mul, mul_one]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h.2, by omega⟩), smul_zero]
  · rw [Finset.sum_eq_zero (fun k _ => if_neg (fun h => hg ⟨h.1, h.2.1⟩))]
    rw [if_neg (fun h => hg ⟨h.2.2.1.1.symm, h.2.2.1.2.symm⟩), smul_zero]

include hty in
theorem num_mon (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    (∑ t : ZMod d, ∑ k ∈ Finset.Icc 1 (min N (X.rkF g t)),
      e t k • (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0)) =
      ∑ k ∈ Finset.Icc (c0 + 1) (r (tau o0 g0 t0)),
        (if g0 = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g t0) then e t0 k else 0) := by
  by_cases hg : g = g0
  · subst hg
    rw [Finset.sum_eq_single t0]
    · rw [rkF_eq X hty]
      have hL : ∀ k ∈ Finset.Icc 1 (min N (r (tau o0 g t0))),
          e t0 k • (if k ≤ N ∧ k ≤ r (tau o0 g t0) ∧ (g = g ∧ t0 = t0) ∧ c0 < k then 1 else 0) =
            if c0 < k then e t0 k else 0 := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        by_cases hc : c0 < k
        · rw [if_pos ⟨by omega, by omega, ⟨rfl, rfl⟩, hc⟩, if_pos hc, smul_eq_mul, mul_one]
        · rw [if_neg (fun h => hc h.2.2.2), if_neg hc, smul_zero]
      rw [Finset.sum_congr rfl hL, ← Finset.sum_filter, ← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, eq_self_iff_true, true_and]
      omega
    · intro t _ ht
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (fun h => ht h.2.2.1.2), smul_zero]
    · simp
  · trans 0
    · exact Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun k _ => by
        rw [if_neg (fun h => hg h.2.2.1.1), smul_zero]
    · exact (Finset.sum_eq_zero fun k _ => if_neg (fun h => hg h.1.symm)).symm

end Block

end WeightHomogeneousMinors

end Formalism.L2.FormalSeriesBounds.RF
