import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussRec

variable {R : Type} [CommRing R]

theorem sum_comp_surj {A B : Type} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (π : A →+ B) (hπ : Function.Surjective π) (c : ℕ)
    (hc : Fintype.card A = c * Fintype.card B) (G : B → ℂ) :
    ∑ x, G (π x) = (c : ℂ) * ∑ y, G y := by
  classical
  have hn : ∀ b, (Finset.univ.filter fun x => π x = b).card
      = (Finset.univ.filter fun x => π x = 0).card := by
    intro b
    obtain ⟨x0, rfl⟩ := hπ b
    refine Finset.card_equiv (Equiv.subRight x0) ?_
    intro i
    simp [map_sub, sub_eq_zero]
  have hcard : Fintype.card A
      = (Finset.univ.filter fun x => π x = 0).card * Fintype.card B := by
    have h1 := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset A))
      (t := (Finset.univ : Finset B)) (f := π) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Finset.card_univ] at h1
    rw [h1, Finset.sum_congr rfl (fun b _ => hn b)]
    simp [mul_comm]
  have hpos : 0 < Fintype.card B := Fintype.card_pos
  have hc' : (Finset.univ.filter fun x => π x = 0).card = c := by
    have : (Finset.univ.filter fun x => π x = 0).card * Fintype.card B = c * Fintype.card B := by
      rw [← hcard, hc]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := π) (f := fun x => G (π x)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : ∀ x ∈ Finset.univ.filter (fun x => π x = b), G (π x) = G b := by
    intro x hx
    rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, hn b, hc', nsmul_eq_mul]

def gaussTerm (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (a : R)
    (k : ℕ) (w : R ⧸ lev ϖ k) : ℂ :=
  ψ k (Ideal.Quotient.mk (lev ϖ k) a * (barσ σ ϖ hfix k w * w))

theorem gaussTerm_mk (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ)
    (a : R) (k : ℕ) (x : R) :
    gaussTerm σ ϖ hfix ψ a k (Ideal.Quotient.mk _ x)
      = ψ k (Ideal.Quotient.mk _ (a * (σ x * x))) := by
  simp only [gaussTerm, barσ_mk, map_mul]

def traceChar (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (c : R) :
    AddChar (R ⧸ lev ϖ 1) ℂ :=
  (ψ 1).compAddMonoidHom (AddMonoidHom.mk'
    (fun t => Ideal.Quotient.mk (lev ϖ 1) c * t + barσ σ ϖ hfix 1 (Ideal.Quotient.mk (lev ϖ 1) c * t))
    (by intro x y; simp only [mul_add, map_add]; abel))

theorem traceChar_mk (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ)
    (c y : R) :
    traceChar σ ϖ hfix ψ c (Ideal.Quotient.mk _ y)
      = ψ 1 (Ideal.Quotient.mk _ (c * y + σ (c * y))) := by
  show ψ 1 (Ideal.Quotient.mk (lev ϖ 1) c * Ideal.Quotient.mk _ y
    + barσ σ ϖ hfix 1 (Ideal.Quotient.mk (lev ϖ 1) c * Ideal.Quotient.mk _ y)) = _
  rw [← map_mul, barσ_mk, ← map_add]

theorem sum_traceChar {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [Fintype (R ⧸ lev ϖ 1)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (c : R)
    [Decidable (c ∈ lev ϖ 1)] :
    ∑ t, traceChar σ ϖ hR.fix_ϖ ψ c t
      = if c ∈ lev ϖ 1 then (Fintype.card (R ⧸ lev ϖ 1) : ℂ) else 0 := by
  split_ifs with hc
  · have h1 : ∀ t, traceChar σ ϖ hR.fix_ϖ ψ c t = 1 := by
      intro t
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
      rw [traceChar_mk]
      have : Ideal.Quotient.mk (lev ϖ 1) (c * y + σ (c * y)) = 0 := by
        have h0 : Ideal.Quotient.mk (lev ϖ 1) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
        rw [map_add, ← barσ_mk σ ϖ hR.fix_ϖ, map_mul, h0]
        simp
      rw [this, AddChar.map_zero_eq_one]
    simp [h1]
  · have hne : traceChar σ ϖ hR.fix_ϖ ψ c ≠ 1 := by
      intro h0
      apply hc
      refine trace_nondeg hR hψ 1 c (fun t => ?_)
      have h1 := traceChar_mk σ ϖ hR.fix_ϖ ψ c t
      rw [h0, AddChar.one_apply] at h1
      rw [mul_comm t c]
      exact h1.symm
    exact AddChar.sum_eq_zero_of_ne_one hne

theorem gaussTerm_shift {σ : R →+* R} {ϖ : R} (hinv : ∀ a, σ (σ a) = a) (hfix : σ ϖ = ϖ)
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (j : ℕ) {a : R} (ha : σ a = a)
    (x y : R) :
    gaussTerm σ ϖ hfix ψ a (j + 2) (Ideal.Quotient.mk _ x + Ideal.Quotient.mk _ (ϖ ^ (j + 1) * y))
      = gaussTerm σ ϖ hfix ψ a (j + 2) (Ideal.Quotient.mk _ x)
        * traceChar σ ϖ hfix ψ (a * σ x) (Ideal.Quotient.mk _ y) := by
  have hp := psi_pow hψ 1 (j + 1) (a * σ x * y + σ (a * σ x * y))
  rw [show 1 + (j + 1) = j + 2 by omega] at hp
  rw [← map_add, gaussTerm_mk, gaussTerm_mk, traceChar_mk, ← hp, ← AddChar.map_add_eq_mul,
    ← map_add]
  congr 1
  rw [Ideal.Quotient.eq]
  refine mem_lev_iff.2 ⟨ϖ ^ j * (a * σ y * y), ?_⟩
  simp only [map_mul, map_add, map_pow, hfix, ha, hinv]
  ring

theorem mem_lev_one_iff {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε) {a : R}
    (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) (x : R) : a * σ x ∈ lev ϖ 1 ↔ x ∈ lev ϖ 1 := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (hR.fixLocal a ha ha1).exists_left_inv
    have h1 : σ x ∈ lev ϖ 1 := by
      have : σ x = v * (a * σ x) := by rw [← mul_assoc, hv, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ h
    obtain ⟨c, hc⟩ := mem_lev_iff.1 h1
    refine mem_lev_iff.2 ⟨σ c, ?_⟩
    have := congrArg σ hc
    simpa [hR.inv, hR.fix_ϖ] using this
  · intro h
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 h
    refine mem_lev_iff.2 ⟨a * σ c, ?_⟩
    simp only [map_mul, map_pow, hR.fix_ϖ]
    ring

def lft (ϖ : R) (k : ℕ) (w : R ⧸ lev ϖ k) : R :=
  Function.surjInv (Ideal.Quotient.mk_surjective (I := lev ϖ k)) w

@[simp] theorem mk_lft (ϖ : R) (k : ℕ) (w : R ⧸ lev ϖ k) :
    Ideal.Quotient.mk (lev ϖ k) (lft ϖ k w) = w :=
  Function.surjInv_eq _ w

theorem sum_stationary {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (j : ℕ) {a : R} (ha : σ a = a) [DecidablePred fun c => c ∈ lev ϖ 1] :
    ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
      = ∑ w, if a * σ (lft ϖ (j + 2) w) ∈ lev ϖ 1 then gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w else 0 := by
  have shift : ∀ t : R ⧸ lev ϖ 1, ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
      = ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
          * traceChar σ ϖ hR.fix_ϖ ψ (a * σ (lft ϖ (j + 2) w)) t := by
    intro t
    rw [← Equiv.sum_comp (Equiv.addRight (Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ ^ (j + 1) * lft ϖ 1 t)))]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h := gaussTerm_shift hR.inv hR.fix_ϖ hψ j ha (lft ϖ (j + 2) w) (lft ϖ 1 t)
    rw [mk_lft, mk_lft] at h
    exact h
  have hcard : (Fintype.card (R ⧸ lev ϖ 1) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  calc (Fintype.card (R ⧸ lev ϖ 1) : ℂ) * ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
      = ∑ t : R ⧸ lev ϖ 1, ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ t : R ⧸ lev ϖ 1, ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
          * traceChar σ ϖ hR.fix_ϖ ψ (a * σ (lft ϖ (j + 2) w)) t :=
        Finset.sum_congr rfl fun t _ => shift t
    _ = ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
          * ∑ t, traceChar σ ϖ hR.fix_ϖ ψ (a * σ (lft ϖ (j + 2) w)) t := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [sum_traceChar hR hψ]
        split_ifs <;> ring

theorem mk_mul_eq (ϖ : R) (j : ℕ) {x y : R}
    (h : Ideal.Quotient.mk (lev ϖ (j + 1)) x = Ideal.Quotient.mk (lev ϖ (j + 1)) y) :
    Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * x) = Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * y) := by
  rw [Ideal.Quotient.eq] at h ⊢
  obtain ⟨c, hc⟩ := mem_lev_iff.1 h
  refine mem_lev_iff.2 ⟨c, ?_⟩
  rw [← mul_sub, hc]
  ring

theorem mk_of_mul_eq {ϖ : R} (hreg : IsSMulRegular R ϖ) (j : ℕ) {x y : R}
    (h : Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * x) = Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * y)) :
    Ideal.Quotient.mk (lev ϖ (j + 1)) x = Ideal.Quotient.mk (lev ϖ (j + 1)) y := by
  rw [Ideal.Quotient.eq] at h ⊢
  obtain ⟨c, hc⟩ := mem_lev_iff.1 h
  refine mem_lev_iff.2 ⟨c, hreg ?_⟩
  simp only [smul_eq_mul]
  rw [mul_sub, hc]
  ring

theorem gaussTerm_mul {σ : R →+* R} {ϖ : R} (hfix : σ ϖ = ϖ)
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (j : ℕ) (a x : R) :
    gaussTerm σ ϖ hfix ψ a (j + 2) (Ideal.Quotient.mk _ (ϖ * x))
      = gaussTerm σ ϖ hfix ψ a j (Ideal.Quotient.mk _ x) := by
  rw [gaussTerm_mk, gaussTerm_mk, ← psi_pow hψ j 2 (a * (σ x * x))]
  congr 2
  simp only [map_mul, hfix]
  ring

theorem sum_filter_eq {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (j : ℕ) {a : R} (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) [DecidablePred fun c => c ∈ lev ϖ 1] :
    (∑ w, if a * σ (lft ϖ (j + 2) w) ∈ lev ϖ 1 then gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w else 0)
      = ∑ w' : R ⧸ lev ϖ (j + 1), gaussTerm σ ϖ hR.fix_ϖ ψ a j
          (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Nat.le_succ j))) w') := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun w' => Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * lft ϖ (j + 1) w'))
    ?_ ?_ ?_ ?_
  · intro w' _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_lev_one_iff hR ha ha1 _).2 ?_⟩
    have h := mk_lft ϖ (j + 2) (Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * lft ϖ (j + 1) w'))
    rw [Ideal.Quotient.eq] at h
    obtain ⟨c, hc⟩ := mem_lev_iff.1 h
    rw [sub_eq_iff_eq_add] at hc
    rw [hc]
    refine mem_lev_iff.2 ⟨ϖ ^ (j + 1) * c + lft ϖ (j + 1) w', ?_⟩
    ring
  · intro x _ y _ h
    have := mk_of_mul_eq hR.reg j h
    simpa using this
  · intro w hw
    have hw' := (mem_lev_one_iff hR ha ha1 _).1 (Finset.mem_filter.1 hw).2
    obtain ⟨c, hc⟩ := mem_lev_iff.1 hw'
    refine ⟨Ideal.Quotient.mk _ c, by simp, ?_⟩
    have h1 := mk_mul_eq ϖ j (mk_lft ϖ (j + 1) (Ideal.Quotient.mk _ c))
    simp only
    rw [h1, ← mk_lft ϖ (j + 2) w, hc, pow_one]
  · intro w' _
    conv_lhs => rw [← mk_lft ϖ (j + 1) w']
    rw [Ideal.Quotient.factor_mk, gaussTerm_mul hR.fix_ϖ hψ]

end GlobalTheory.CompanionTheory.GaussRec

open GlobalTheory.CompanionTheory.GaussRec in
theorem GlobalTheory.CompanionTheory.GaussRec.gauss_recursion : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ (j + 2), ψ (j + 2) (Ideal.Quotient.mk (lev ϖ (j + 2)) a * (barσ σ ϖ hR.fix_ϖ (j + 2) w * w))) = (q : ℂ) ^ 2 * ∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w)) := by
  intro R _ σ ϖ q ε hR _ ψ hψ j a ha ha1
  classical
  have hle : lev ϖ (j + 1) ≤ lev ϖ j :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Nat.le_succ j))
  have h1 := sum_stationary hR hψ j ha
  rw [sum_filter_eq hR hψ j ha ha1] at h1
  have hc : Fintype.card (R ⧸ lev ϖ (j + 1)) = q ^ 2 * Fintype.card (R ⧸ lev ϖ j) := by
    have e1 := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR (j + 1)
    have e2 := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR j
    rw [Nat.card_eq_fintype_card] at e1 e2
    rw [e1, e2, ← pow_add]
    congr 1
    ring
  have h2 := sum_comp_surj (Ideal.Quotient.factor hle).toAddMonoidHom
    (Ideal.Quotient.factor_surjective hle) (q ^ 2) hc (gaussTerm σ ϖ hR.fix_ϖ ψ a j)
  have h3 : (∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w) = ((q ^ 2 : ℕ) : ℂ) * ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a j w :=
    h1.trans h2
  simpa [gaussTerm] using h3

end
