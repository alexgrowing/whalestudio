import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup

noncomputable section

open Matrix Formalism.UG Formalism.L2.DIV

namespace GlobalTheory.LevNorm

def edgeVal {k : Type} [CommRing k] {n : ℕ} (ρ κ : ℕ) (a : Fin n → Fin n → k) (M : GL (Fin n) k) : k :=
  ∑ i, ∑ j, if symEdge ρ κ i j then a i j * (M : Matrix (Fin n) (Fin n) k) i j else 0

def midDiag {k : Type} [CommRing k] (n ρ κ : ℕ) (s c : k) : Matrix (Fin n) (Fin n) k :=
  Matrix.diagonal fun i => if ρ ≤ i.val ∧ i.val < ρ + κ then c else s

def IsScal {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K) : Prop :=
  ∃ (c : Kˣ) (x : GL (Fin n) O), (m : Matrix (Fin n) (Fin n) K) = (c : K) • ((bc O.subtype x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem edgeVal_one {k : Type} [CommRing k] {n : ℕ} (ρ κ : ℕ) (a : Fin n → Fin n → k) : edgeVal ρ κ a 1 = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · have : i ≠ j := fun e => by unfold symEdge at h; rw [e] at h; omega
    simp [Matrix.one_apply_ne this]
  · rfl

structure PlaceSys (A : Type) [CommRing A] (S : Subring A) (P : Type) (k : P → Type) [∀ Q, Field (k Q)]
    (r : ∀ Q, S →+* k Q) : Type 1 where

  K : P → Type
  [fK : ∀ Q, Field (K Q)]

  O : ∀ Q, ValuationSubring (K Q)

  p : ∀ Q, A →+* K Q

  e : P → A
  surj : ∀ Q, Function.Surjective (p Q)
  e_self : ∀ Q, p Q (e Q) = 1
  e_ne : ∀ Q Q', Q' ≠ Q → p Q' (e Q) = 0
  ext : ∀ a, (∀ Q, p Q a = 0) → a = 0
  int : ∀ a, a ∈ S ↔ ∀ Q, p Q a ∈ O Q
  fin : ∀ a, {Q | p Q a ∉ O Q}.Finite
  r_surj : ∀ Q, Function.Surjective (r Q)
  r_ker : ∀ Q (s : S), r Q s = 0 ↔ (O Q).valuation (p Q s) < 1

attribute [instance] PlaceSys.fK

namespace PlaceSys

variable {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type} [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q}
  (Z : PlaceSys A S P k r)

theorem ext' {a b : A} (h : ∀ Q, Z.p Q a = Z.p Q b) : a = b :=
  sub_eq_zero.1 (Z.ext _ fun Q => by rw [map_sub, h Q, sub_self])

theorem e_mem (Q : P) : Z.e Q ∈ S := (Z.int _).2 fun Q' => by
  by_cases h : Q' = Q
  · subst h; rw [Z.e_self]; exact one_mem _
  · rw [Z.e_ne Q Q' h]; exact zero_mem _

theorem e_mul_eq_iff (Q : P) (a b : A) : Z.e Q * a = Z.e Q * b ↔ Z.p Q a = Z.p Q b := by
  refine ⟨fun h => by simpa [Z.e_self] using congrArg (Z.p Q) h, fun h => Z.ext' fun Q' => ?_⟩
  by_cases h' : Q' = Q
  · subst h'; rw [map_mul, map_mul, h]
  · rw [map_mul, map_mul, Z.e_ne Q Q' h', zero_mul, zero_mul]

theorem e_idem (Q : P) : Z.e Q * Z.e Q = Z.e Q := by
  have := (Z.e_mul_eq_iff Q (Z.e Q) 1).2 (by rw [Z.e_self, map_one])
  rwa [mul_one] at this

theorem e_mul_mem_iff (Q : P) (a : A) : Z.e Q * a ∈ S ↔ Z.p Q a ∈ Z.O Q := by
  refine ⟨fun h => by simpa [Z.e_self] using (Z.int _).1 h Q, fun h => (Z.int _).2 fun Q' => ?_⟩
  by_cases h' : Q' = Q
  · subst h'; rwa [map_mul, Z.e_self, one_mul]
  · rw [map_mul, Z.e_ne Q Q' h', zero_mul]; exact zero_mem _

theorem e_injective : Function.Injective Z.e := fun Q Q' h => by
  by_contra hne
  have h1 := Z.e_self Q
  rw [h, Z.e_ne Q' Q hne] at h1
  exact zero_ne_one h1

theorem exists_single (Q : P) (x : Z.K Q) : ∃ a : A, Z.p Q a = x ∧ ∀ Q', Q' ≠ Q → Z.p Q' a = 0 := by
  obtain ⟨b, hb⟩ := Z.surj Q x
  exact ⟨Z.e Q * b, by rw [map_mul, Z.e_self, one_mul, hb], fun Q' h => by rw [map_mul, Z.e_ne Q Q' h, zero_mul]⟩

def pO (Q : P) : S →+* Z.O Q :=
  ((Z.p Q).comp S.subtype).codRestrict (Z.O Q) fun s => (Z.int _).1 s.2 Q

theorem pO_coe (Q : P) (s : S) : (Z.pO Q s : Z.K Q) = Z.p Q s := rfl

theorem pO_surj (Q : P) : Function.Surjective (Z.pO Q) := fun x => by
  obtain ⟨a, h1, h2⟩ := Z.exists_single Q x
  refine ⟨⟨a, (Z.int _).2 fun Q' => ?_⟩, Subtype.ext h1⟩
  by_cases h' : Q' = Q
  · subst h'; rw [h1]; exact x.2
  · rw [h2 Q' h']; exact zero_mem _

theorem exists_res (Q : P) : ∃ ρ : Z.O Q →+* k Q, Function.Surjective ρ ∧ ∀ s, ρ (Z.pO Q s) = r Q s := by
  have hk : RingHom.ker (Z.pO Q) ≤ RingHom.ker (r Q) := fun s hs => by
    have h0 : Z.p Q s = 0 := congrArg Subtype.val (RingHom.mem_ker.1 hs)
    rw [RingHom.mem_ker, Z.r_ker, h0, map_zero]
    exact zero_lt_one
  refine ⟨(Z.pO Q).liftOfSurjective (Z.pO_surj Q) ⟨r Q, hk⟩, fun y => ?_, fun s => RingHom.liftOfSurjective_comp_apply _ _ _ _⟩
  obtain ⟨s, rfl⟩ := Z.r_surj Q y
  exact ⟨Z.pO Q s, RingHom.liftOfSurjective_comp_apply _ _ _ _⟩

theorem r_congr (Q : P) {s t : S} (h : Z.p Q s = Z.p Q t) : r Q s = r Q t := by
  obtain ⟨ρ, -, hρ⟩ := Z.exists_res Q
  rw [← hρ, ← hρ, show Z.pO Q s = Z.pO Q t from Subtype.ext h]

theorem gl_ext {n : ℕ} {x y : GL (Fin n) A} (h : ∀ Q, bc (Z.p Q) x = bc (Z.p Q) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => Z.ext' fun Q => ?_)
  exact congrArg (fun g : GL (Fin n) (Z.K Q) => (g : Matrix (Fin n) (Fin n) (Z.K Q)) i j) (h Q)

theorem gl_int {n : ℕ} {x : GL (Fin n) A} (h : ∀ Q, ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) x) :
    ∃ y : GL (Fin n) S, bc S.subtype y = x := by
  have key : ∀ {x : GL (Fin n) A}, (∀ Q, ∃ y : GL (Fin n) (Z.O Q), bc (Z.O Q).subtype y = bc (Z.p Q) x) →
      ∀ i j, (x : Matrix (Fin n) (Fin n) A) i j ∈ S := fun {x} h i j => (Z.int _).2 fun Q => by
    obtain ⟨y, hy⟩ := h Q
    have := congrArg (fun g : GL (Fin n) (Z.K Q) => (g : Matrix (Fin n) (Fin n) (Z.K Q)) i j) hy
    exact (show _ = Z.p Q _ from this) ▸ ((y : Matrix (Fin n) (Fin n) (Z.O Q)) i j).2
  have h1 := key h
  have h2 := key (x := x⁻¹) fun Q => by
    obtain ⟨y, hy⟩ := h Q
    exact ⟨y⁻¹, by rw [map_inv, map_inv, hy]⟩
  have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) S => M.map S.subtype := Matrix.map_injective S.subtype_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem gl_single {n : ℕ} (Q : P) (y : GL (Fin n) (Z.K Q)) :
    ∃ x : GL (Fin n) A, bc (Z.p Q) x = y ∧ ∀ Q', Q' ≠ Q → bc (Z.p Q') x = 1 := by
  choose j hj hj' using Z.exists_single Q
  let g : Matrix (Fin n) (Fin n) (Z.K Q) → Matrix (Fin n) (Fin n) A := fun M => 1 + (M - 1).map j
  have g1 : ∀ M, (Z.p Q).mapMatrix (g M) = M := fun M => by
    rw [map_add, map_one]
    have : (Z.p Q).mapMatrix ((M - 1).map j) = M - 1 := by ext a b; exact hj _
    rw [this, add_sub_cancel]
  have g2 : ∀ M Q', Q' ≠ Q → (Z.p Q').mapMatrix (g M) = 1 := fun M Q' h => by
    rw [map_add, map_one]
    have : (Z.p Q').mapMatrix ((M - 1).map j) = 0 := by ext a b; exact hj' _ Q' h
    rw [this, add_zero]
  have gm : ∀ M N, M * N = 1 → g M * g N = 1 := fun M N h => Matrix.ext fun a b => Z.ext' fun Q' => by
    have : (Z.p Q').mapMatrix (g M * g N) = (Z.p Q').mapMatrix 1 := by
      rw [map_mul, map_one]
      by_cases h' : Q' = Q
      · subst h'; rw [g1, g1, h]
      · rw [g2 _ _ h', g2 _ _ h', one_mul]
    exact congrFun (congrFun this a) b
  exact ⟨⟨g y.1, g (y⁻¹).1, gm _ _ y.mul_inv, gm _ _ y.inv_mul⟩, Units.ext (g1 _), fun Q' h => Units.ext (g2 _ Q' h)⟩

variable {σ : A →+* A}

theorem exists_bar (hσ : ∀ a, σ (σ a) = a) (Q : P) : ∃ Q', σ (Z.e Q) = Z.e Q' := by
  have h0 : ∀ Q, σ (Z.e Q) ≠ 0 := fun Q h => by
    have h1 := Z.e_self Q
    rw [← hσ (Z.e Q), h, map_zero, map_zero] at h1
    exact zero_ne_one h1
  have h01 : ∀ Q Q', Z.p Q' (σ (Z.e Q)) ≠ 0 → Z.p Q' (σ (Z.e Q)) = 1 := fun Q Q' h =>
    mul_left_cancel₀ h (by rw [← map_mul, ← map_mul, Z.e_idem, mul_one])
  obtain ⟨Q', hQ'⟩ : ∃ Q', Z.p Q' (σ (Z.e Q)) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 Q (Z.ext _ hc)
  have e1 : Z.e Q' * σ (Z.e Q) = Z.e Q' * 1 := (Z.e_mul_eq_iff _ _ _).2 (by rw [h01 _ _ hQ', map_one])
  have e2 : σ (Z.e Q') * Z.e Q = σ (Z.e Q') := by simpa [hσ] using congrArg σ e1
  have e3 : ∀ Q'', Q'' ≠ Q → Z.p Q'' (σ (Z.e Q')) = 0 := fun Q'' h => by
    rw [← e2, map_mul, Z.e_ne Q Q'' h, mul_zero]
  have e4 : Z.p Q (σ (Z.e Q')) = 1 := h01 _ _ fun h => h0 Q' (Z.ext _ fun Q'' => by
    by_cases h' : Q'' = Q
    · subst h'; exact h
    · exact e3 _ h')
  refine ⟨Q', ?_⟩
  rw [← hσ (Z.e Q')]
  congr 1
  refine Z.ext' fun Q'' => ?_
  by_cases h' : Q'' = Q
  · subst h'; rw [e4, Z.e_self]
  · rw [e3 _ h', Z.e_ne Q Q'' h']

theorem exists_conj (hS : ∀ a ∈ S, σ a ∈ S) {Q Q' : P} (h : σ (Z.e Q) = Z.e Q') :
    ∃ s : Z.K Q →+* Z.K Q', (∀ a, s (Z.p Q a) = Z.p Q' (σ a)) ∧ ∀ x ∈ Z.O Q, s x ∈ Z.O Q' := by
  have hk : RingHom.ker (Z.p Q) ≤ RingHom.ker ((Z.p Q').comp σ) := fun a ha => by
    have h1 : Z.e Q * a = Z.e Q * 0 := (Z.e_mul_eq_iff _ _ _).2 (by rw [RingHom.mem_ker.1 ha, map_zero])
    have h2 : Z.e Q' * σ a = Z.e Q' * 0 := by simpa [h] using congrArg σ h1
    simpa using (Z.e_mul_eq_iff _ _ _).1 h2
  have hs : ∀ a, (Z.p Q).liftOfSurjective (Z.surj Q) ⟨(Z.p Q').comp σ, hk⟩ (Z.p Q a) = Z.p Q' (σ a) :=
    fun a => RingHom.liftOfSurjective_comp_apply _ _ _ _
  refine ⟨_, hs, fun x hx => ?_⟩
  obtain ⟨a, rfl⟩ := Z.surj Q x
  rw [hs, ← Z.e_mul_mem_iff, ← h, ← map_mul]
  exact hS _ ((Z.e_mul_mem_iff _ _).2 hx)

theorem r_conj (hσ : ∀ a, σ (σ a) = a) (hS : ∀ a ∈ S, σ a ∈ S) {Q Q' : P} (h : σ (Z.e Q) = Z.e Q') (s : S) (hs : r Q s = 0) :
    r Q' ⟨σ s, hS _ s.2⟩ = 0 := by
  obtain ⟨t, ht, htO⟩ := Z.exists_conj hS (Q := Q') (Q' := Q) (by rw [← h, hσ])
  rw [Z.r_ker] at hs ⊢
  by_contra hc
  have hm : Z.p Q' (σ s) ∈ Z.O Q' := (Z.int _).1 (hS _ s.2) Q'
  have h1 : (Z.O Q').valuation (Z.p Q' (σ s)) = 1 := le_antisymm (((Z.O Q').valuation_le_one_iff _).2 hm) (not_lt.1 hc)
  have h0 : Z.p Q' (σ s) ≠ 0 := fun e => by rw [e, map_zero] at h1; exact zero_ne_one h1
  have h2 : (Z.p Q' (σ s))⁻¹ ∈ Z.O Q' := by rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, h1, inv_one]
  have h3 := htO _ h2
  rw [map_inv₀, ht, hσ, ← ValuationSubring.valuation_le_one_iff, map_inv₀] at h3
  have h4 : Z.p Q s ≠ 0 := by rw [← hσ s, ← ht]; exact (map_ne_zero t).2 h0
  have h5 : 0 < (Z.O Q).valuation (Z.p Q s) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h4)
  exact absurd hs (not_lt.2 ((inv_le_one₀ h5).1 h3))

end PlaceSys

end GlobalTheory.LevNorm

end
