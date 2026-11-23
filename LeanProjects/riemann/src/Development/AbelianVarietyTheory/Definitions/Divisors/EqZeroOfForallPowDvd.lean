import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

set_option autoImplicit false

noncomputable section

open MvPowerSeries TensorProduct

namespace GlobalTheory.QLog

open GlobalTheory.Katz GlobalTheory.PDivGroup GlobalTheory.Sandwich

section Frame

variable (p : ℕ) {B O : Type} (Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q]

structure IsFrame (θ : B →+* O) : Prop where

  surj : Function.Surjective θ

  inj : Function.Injective (algebraMap B Q)

  denom : ∀ q : Q, ∃ (k : ℕ) (b : B), (p : Q) ^ k * q = algebraMap B Q b

  unit_p : IsUnit (p : Q)

  unit_coprime : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)

  pd : ∀ x, θ x = 0 → ∃ y, θ y = 0 ∧ x ^ p = p * y

  sat : ∀ a : O, p * a = 0 → a = 0

  complete : IsAdicComplete (Ideal.span {(p : B)}) B

variable {Q} {σ : Type} {d : ℕ}

def In (N : Ideal B) (f : MvPowerSeries σ Q) : Prop :=
  ∀ α, ∃ b ∈ N, coeff α f = algebraMap B Q b

def DIn (N : Ideal B) (f : MvPowerSeries σ Q) : Prop :=
  ∀ α i, ∃ b ∈ N, (α i : Q) * coeff α f = algebraMap B Q b

variable (Q) in

def up {ι : Type} (u : ι → MvPowerSeries σ B) : ι → MvPowerSeries σ Q :=
  fun i => map (algebraMap B Q) (u i)

structure IsLift (θ : B →+* O) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) : Prop where

  const : ∀ i, constantCoeff (μ i) = 0

  unit : op μ (fun i => (X i : MvPowerSeries (Fin d) B)) (fun _ => 0) = fun i => X i

  comm : ∀ i, swap (μ i) = μ i

  law : IsLaw fun i => map θ (μ i)

def QL (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (N : Ideal B) (f : MvPowerSeries (Fin d) Q) :
    Prop :=
  constantCoeff f = 0 ∧ (∀ i, ∃ b ∈ N, lin f i = algebraMap B Q b) ∧ In N (cob1 (up Q μ) f)

def comb {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) : MvPowerSeries σ Q :=
  ∑ i, algebraMap B Q (b i) • e i

def IsBasis (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {ι : Type} [Fintype ι]
    (e : ι → MvPowerSeries (Fin d) Q) : Prop :=
  (∀ i, QL μ ⊤ (e i)) ∧ ∀ f, QL μ ⊤ f → ∃! b : ι → B, In (⊤ : Ideal B) (f - comb b e)

def IsAdapted (θ : B →+* O) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) {c : ℕ}
    (e : Fin d ⊕ Fin c → MvPowerSeries (Fin d) Q) : Prop :=
  ∀ i, In (RingHom.ker θ) (cob1 (up Q μ) (e (Sum.inl i))) ∧ lin (e (Sum.inl i)) = Pi.single i 1

def IsStep (θ : B →+* O) (N' N : Ideal B) : Prop :=
  ∃ (n : B) (a : O), a ∣ p ∧ N = N' ⊔ Ideal.span {n} ∧ ∀ b, b * n ∈ N' ↔ a ∣ θ b

def nmul {R : Type} [CommRing R] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    Fin d → MvPowerSeries (Fin d) R :=
  (fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n] fun _ => 0

def defect (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (n : ℕ) (f : MvPowerSeries (Fin d) Q) :
    MvPowerSeries (Fin d) Q := (n : Q) • f - subst (up Q (nmul μ n)) f

def frob (s : Q →+* Q) (f : MvPowerSeries σ Q) : MvPowerSeries σ Q :=
  subst (fun i => (X i : MvPowerSeries σ Q) ^ p) (map s f)

def IsEval {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (x : σ → A)
    (E : MvPowerSeries σ R →ₐ[R] A) : Prop :=
  (∀ i, E (X i) = x i) ∧ ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) →
    (p : A) ^ m ∣ E f

def HasVal [Fintype σ] [DecidableEq σ] (z : σ → B) (f : MvPowerSeries σ Q) (q : Q) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ N' ≥ N, ∃ b : B, q - MvPolynomial.eval (fun i => algebraMap B Q (z i))
    (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N') f) = algebraMap B Q (p ^ m * b)

variable {p} {θ : B →+* O}

theorem In.top_iff {f : MvPowerSeries σ Q} :
    In (⊤ : Ideal B) f ↔ ∃ s : MvPowerSeries σ B, map (algebraMap B Q) s = f := by
  constructor
  · intro h
    choose b _ hb using h
    refine ⟨(show MvPowerSeries σ B from fun α => b α), ?_⟩
    ext α
    rw [coeff_map, hb α]
    rfl
  · rintro ⟨s, rfl⟩ α
    exact ⟨_, trivial, coeff_map ..⟩

theorem hasSubst_up_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) : HasSubst (up Q (nmul μ n)) := by
  have h0 : ∀ n i, constantCoeff (nmul μ n i) = 0 := by
    intro n
    induction n with
    | zero => intro i; simp [nmul]
    | succ n ih =>
      intro i
      rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
      have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
          (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
        rintro (j | j) <;> simp [ih]
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)
  exact hasSubst_of_constantCoeff_zero fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]

theorem IsFrame.eq_zero_of_forall_pow_dvd (h : IsFrame p Q θ) {x : B}
    (hx : ∀ n : ℕ, (p : B) ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus h.complete.toIsHausdorff x fun n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
    exact hx n

theorem HasVal.unique [Fintype σ] [DecidableEq σ] (h : IsFrame p Q θ) {z : σ → B}
    {f : MvPowerSeries σ Q} {q q' : Q} (h1 : HasVal p z f q) (h2 : HasVal p z f q') : q = q' := by
  have key : ∀ m : ℕ, ∃ b : B, q - q' = algebraMap B Q (p ^ m * b) := fun m => by
    obtain ⟨N, hN⟩ := h1 m
    obtain ⟨N', hN'⟩ := h2 m
    obtain ⟨b, hb⟩ := hN _ (le_max_left N N')
    obtain ⟨b', hb'⟩ := hN' _ (le_max_right N N')
    exact ⟨b - b', by rw [mul_sub, map_sub, ← hb, ← hb']; ring⟩
  obtain ⟨b, hb⟩ := key 0
  have : (p : B) ^ 0 * b = 0 := h.eq_zero_of_forall_pow_dvd fun m => by
    obtain ⟨c, hc⟩ := key m
    exact ⟨c, h.inj (hb.symm.trans hc)⟩
  rw [this, map_zero, sub_eq_zero] at hb
  exact hb

theorem HasVal.var [Fintype σ] [DecidableEq σ] (z : σ → B) (i : σ) :
    HasVal p z (X i : MvPowerSeries σ Q) (algebraMap B Q (z i)) := by
  refine fun m => ⟨1, fun N hN => ⟨0, ?_⟩⟩
  have : trunc' Q (Finsupp.equivFunOnFinite.symm fun _ : σ => N) (X i) =
      MvPolynomial.X i := by
    ext α
    rw [coeff_trunc', coeff_X, MvPolynomial.coeff_X']
    by_cases h : α = Finsupp.single i 1
    · subst h
      rw [if_pos rfl, if_pos]
      intro j
      refine le_trans ?_ hN
      rw [Finsupp.single_apply]; split_ifs <;> simp
    · simp [h, Ne.symm h]
  rw [this]; simp

end Frame

structure Chart {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O) (d : ℕ) where

  x : ∀ n, Fin d → G.A n

  ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n

  ev₂ : ∀ n, MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n ⊗[O] G.A n

  μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O

  nil : ∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N

  isEval : ∀ n, IsEval p (x n) (ev n)

  isEval₂ : ∀ n, IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] 1) fun i => 1 ⊗ₜ[O] x n i) (ev₂ n)

  res : ∀ n i, G.res n (x (n + 1) i) = x n i

  aug : ∀ n i, Coalgebra.counit (R := O) (x n i) = 0

  surj : ∀ n, Function.Surjective (ev n)

  ker : ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f

  isLaw : IsLaw μ

  comul : ∀ n i, ev₂ n (μ i) = Coalgebra.comul (R := O) (x n i)

namespace Chart

variable {p : ℕ} {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q] {G : PDivGroup p O} {d : ℕ}
  (c : Chart G d)

def form (i : Fin d) : G.omega :=
  ⟨fun n => PDiv.dUnit O (c.x n i), fun n =>
    (PDiv.cotMap_d (G.res n) _).trans (congrArg (PDiv.dUnit O) (c.res n i))⟩

def HasPeriod [Algebra B Q] (θ : B →+* O) (t : G.Tate) (f : MvPowerSeries (Fin d) Q) (y : B) : Prop :=
  (∀ (n : ℕ) (z : Fin d → B), (∀ i, θ (z i) = t.pt n (c.x n i)) → ∃ q : Q, HasVal p z f q) ∧
  ∀ (n : ℕ) (z : Fin d → B) (q : Q), (∀ i, θ (z i) = t.pt n (c.x n i)) → HasVal p z f q →
    ∃ b : B, (p : Q) ^ n * q = algebraMap B Q (y + p ^ n * b)

def IsLie [Algebra O Q] (f : MvPowerSeries (Fin d) Q) (l : G.dual.Lie) : Prop :=
  (∀ n : ℕ, In (⊤ : Ideal O) (defect c.μ (p ^ n) f)) ∧
  ∀ (n : ℕ) (w : G.dual.omega) (φ : CartierDual O (G.A n)) (s : MvPowerSeries (Fin d) O),
    PDiv.dUnit O φ = w.1 n → map (algebraMap O Q) s = defect c.μ (p ^ n) f →
      (p : O) ^ n ∣ l w - φ (c.ev n s)

theorem hasPeriod_iff [Algebra B Q] {θ : B →+* O} (h : IsFrame p Q θ) (t : G.Tate)
    (f : MvPowerSeries (Fin d) Q) (y : B) :
    c.HasPeriod θ t f y ↔ ∀ (n : ℕ) (z : Fin d → B), (∀ i, θ (z i) = t.pt n (c.x n i)) →
      ∃ q : Q, HasVal p z f q ∧ ∃ b : B, (p : Q) ^ n * q = algebraMap B Q (y + p ^ n * b) := by
  refine ⟨fun H n z hz => ?_, fun H => ⟨fun n z hz => (H n z hz).imp fun _ hq => hq.1,
    fun n z q hz hq => ?_⟩⟩
  · obtain ⟨q, hq⟩ := H.1 n z hz
    exact ⟨q, hq, H.2 n z q hz hq⟩
  · obtain ⟨q', hq', hb⟩ := H n z hz
    rwa [HasVal.unique h hq hq']

variable {c} in

theorem HasPeriod.unique [Algebra B Q] {θ : B →+* O} (h : IsFrame p Q θ) {t : G.Tate}
    {f : MvPowerSeries (Fin d) Q} {y y' : B} (h1 : c.HasPeriod θ t f y) (h2 : c.HasPeriod θ t f y') :
    y = y' := by
  refine sub_eq_zero.1 (h.eq_zero_of_forall_pow_dvd fun n => ?_)
  choose z hz using fun j => h.surj (t.pt n (c.x n j))
  obtain ⟨q, hq⟩ := h1.1 n z hz
  obtain ⟨b, hb⟩ := h1.2 n z q hz hq
  obtain ⟨b', hb'⟩ := h2.2 n z q hz hq
  exact ⟨b' - b, by linear_combination h.inj (hb.symm.trans hb')⟩

theorem hasPeriod_X_iff [Algebra B Q] {θ : B →+* O} (h : IsFrame p Q θ) (t : G.Tate) (i : Fin d)
    (y : B) : c.HasPeriod θ t (X i : MvPowerSeries (Fin d) Q) y ↔ y = 0 := by
  have h0 : c.HasPeriod θ t (X i : MvPowerSeries (Fin d) Q) (0 : B) :=
    (c.hasPeriod_iff h t _ 0).2 fun n z _ => ⟨_, HasVal.var z i, z i, by simp⟩
  exact ⟨fun H => H.unique h h0, fun H => H ▸ h0⟩

theorem isLie_iff [Algebra O Q] (h : Function.Injective (algebraMap O Q))
    (f : MvPowerSeries (Fin d) Q) (l : G.dual.Lie) :
    c.IsLie f l ↔ ∀ n : ℕ, ∃ s : MvPowerSeries (Fin d) O,
      map (algebraMap O Q) s = defect c.μ (p ^ n) f ∧
        ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), PDiv.dUnit O φ = w.1 n →
          (p : O) ^ n ∣ l w - φ (c.ev n s) := by
  refine ⟨fun H n => ?_, fun H => ⟨fun n => In.top_iff.2 ((H n).imp fun _ hs => hs.1),
    fun n w φ s hφ hs => ?_⟩⟩
  · obtain ⟨s, hs⟩ := In.top_iff.1 (H.1 n)
    exact ⟨s, hs, fun w φ hφ => H.2 n w φ s hφ hs⟩
  · obtain ⟨s', hs', H'⟩ := H n
    have : s = s' := by
      ext α
      exact h (by simpa [coeff_map] using congrArg (coeff α) (hs.trans hs'.symm))
    exact this ▸ H' w φ hφ

variable {c} in

theorem IsLie.unique [Algebra O Q] [IsHausdorff (Ideal.span {(p : O)}) O]
    {f : MvPowerSeries (Fin d) Q} {l l' : G.dual.Lie} (h1 : c.IsLie f l) (h2 : c.IsLie f l') :
    l = l' := by
  refine LinearMap.ext fun w => sub_eq_zero.1
    (IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ fun n => ?_)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 n)
  obtain ⟨s, hs⟩ := In.top_iff.1 (h1.1 n)
  have := dvd_sub (h1.2 n w φ s hφ hs) (h2.2 n w φ s hφ hs)
  rwa [sub_sub_sub_cancel_right] at this

theorem isLie_zero [Algebra O Q] (h : Function.Injective (algebraMap O Q)) :
    c.IsLie (0 : MvPowerSeries (Fin d) Q) 0 :=
  (c.isLie_iff h 0 0).2 fun n => ⟨0, by
    rw [defect, ← coe_substAlgHom (hasSubst_up_nmul c.isLaw.const _), map_zero, map_zero, smul_zero,
      sub_zero], fun w φ _ => by simp⟩

end Chart

structure BFrame {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) : Type 1 where

  B : Type

  Q : Type
  [ringB : CommRing B]
  [ringQ : CommRing Q]
  [alg : Algebra B Q]

  a : Ainf p O →+* B

  θ : B →+* O

  σ : B →+* B

  s : Q →+* Q

  τ : B

  frame : IsFrame p Q θ

  θ_a : ∀ x, θ (a x) = WittVector.fontaineTheta O p x

  σ_a : ∀ x, σ (a x) = a (WittVector.frobenius x)

  s_alg : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)

  σ_pow : ∀ b, (p : B) ∣ σ b - b ^ p

  p_τ : p * τ = a (Sandwich.mu ε)

  τ_sq : τ * τ = 0

  gen : ∀ b, ∃ x y, b = a x + τ * a y

  τ_mul : ∀ y, τ * a y = 0 ↔ Sandwich.mu ε ∣ y

  a_dvd : ∀ x, τ ∣ a x ↔ Sandwich.mu ε ∣ x

attribute [instance] BFrame.ringB BFrame.ringQ BFrame.alg

def blk {R : Type} [CommRing R] (d c : ℕ) (u v : R) : Matrix (Fin d ⊕ Fin c) (Fin d ⊕ Fin c) R :=
  Matrix.diagonal (Sum.elim (fun _ => u) fun _ => v)

def IsNil {B O ι : Type} [CommRing B] [CommRing O] [Fintype ι] (θ : B →+* O) (σ : B →+* B)
    (M : Matrix ι ι B) : Prop :=
  ∃ N : ℕ, ∀ (v : ι → B) (i : ι), ¬IsUnit (θ ((fun w : ι → B => M.mulVec fun j => σ (w j))^[N] v i))

theorem isFrame_padic (p : ℕ) [Fact p.Prime] : IsFrame p ℚ_[p] (RingHom.id ℤ_[p]) where
  surj := Function.surjective_id
  inj := Subtype.val_injective
  denom q := by
    obtain ⟨⟨a, ⟨b, hb⟩⟩, h⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[p]) q
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨b.valuation, (PadicInt.unitCoeff hb0)⁻¹.val * a, ?_⟩
    have h1 := congrArg (algebraMap ℤ_[p] ℚ_[p]) (PadicInt.unitCoeff_spec hb0)
    have h2 : algebraMap ℤ_[p] ℚ_[p] (PadicInt.unitCoeff hb0)⁻¹.val *
        algebraMap ℤ_[p] ℚ_[p] (PadicInt.unitCoeff hb0).val = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    simp only [map_mul, map_pow, map_natCast] at h1 h ⊢
    rw [← h, h1]
    linear_combination (-(p : ℚ_[p]) ^ b.valuation * q) * h2
  unit_p := (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero).isUnit
  unit_coprime n h := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hl => ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := p) n).1 (by simpa using hl)
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.1 h.symm (Int.natCast_dvd_natCast.1 this)
  pd x hx := ⟨0, rfl, by
    rw [show x = 0 from hx, zero_pow (Fact.out : p.Prime).ne_zero, mul_zero]⟩
  sat a h := (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  complete := PadicInt.maximalIdeal_eq_span_p (p := p) ▸ inferInstance

example (p : ℕ) [hp : Fact p.Prime] (G : PDivGroup p ℤ_[p]) (d : ℕ) (c : Chart G d)
    (l : G.dual.Lie) : ¬c.IsLie (C (p : ℚ_[p])⁻¹ : MvPowerSeries (Fin d) ℚ_[p]) l := by
  intro h
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  obtain ⟨b, -, hb⟩ := h.1 1 0
  rw [defect, subst_C] at hb
  simp only [pow_one, map_sub, map_smul, coeff_zero_C, smul_eq_mul, mul_inv_cancel₀ hp0] at hb
  have h1 : (p : ℚ_[p])⁻¹ = algebraMap ℤ_[p] ℚ_[p] (1 - b) := by rw [map_sub, map_one, ← hb]; ring
  have h2 : ‖((p : ℚ_[p])⁻¹)‖ ≤ 1 := by rw [h1]; exact (1 - b).2
  rw [norm_inv, Padic.norm_p, inv_inv] at h2
  exact absurd (by exact_mod_cast h2) hp.out.one_lt.not_ge

example (p : ℕ) [Fact p.Prime] :
    IsStep p (RingHom.id ℤ_[p]) (Ideal.span {(p : ℤ_[p])}) ⊤ :=
  ⟨1, p, dvd_rfl, by simp, fun b => by simp [Ideal.mem_span_singleton]⟩

end GlobalTheory.QLog
