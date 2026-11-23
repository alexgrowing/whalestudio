import Development.EtaleCohomology.EtaleSheaves.DomCoverPf

noncomputable section
open CategoryTheory

namespace LateralTheory.E.IdemCoverPf

variable (C : Type) [CommRing C]

abbrev P := ∀ p : PrimeSpectrum C, C ⧸ p.asIdeal

open Classical in

def e (c : C) : P C := fun p => if c ∈ p.asIdeal then 1 else 0

abbrev D := Algebra.adjoin C (Set.range (e C))

variable {C}

def Ei (c : C) : D C := ⟨e C c, Algebra.subset_adjoin ⟨c, rfl⟩⟩

theorem coord_alg (c : C) (p : PrimeSpectrum C) :
    ((algebraMap C (D C) c : D C) : P C) p = Ideal.Quotient.mk p.asIdeal c := rfl

theorem E_mul_one_sub (c : C) : Ei c * (1 - Ei c) = 0 := by
  apply Subtype.ext; funext p
  show e C c p * (1 - e C c p) = 0
  unfold e; split_ifs <;> simp

theorem E_mul_alg (c : C) : Ei c * algebraMap C (D C) c = 0 := by
  apply Subtype.ext; funext p
  show e C c p * Ideal.Quotient.mk p.asIdeal c = 0
  unfold e; split_ifs with h
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 h, mul_zero]
  · simp

theorem one_sub_E_mul (a b : C) : 1 - Ei (a * b) = (1 - Ei a) * (1 - Ei b) := by
  apply Subtype.ext; funext p
  show 1 - e C (a * b) p = (1 - e C a p) * (1 - e C b p)
  unfold e
  have := p.isPrime.mul_mem_iff_mem_or_mem (x := a) (y := b)
  split_ifs <;> simp_all

theorem ann_alg (t : D C) (c : C) (h : t * algebraMap C (D C) c = 0) : t * (1 - Ei c) = 0 := by
  apply Subtype.ext; funext p
  have hp := congrArg (fun x : D C => (x : P C) p) h
  simp only [Subalgebra.coe_mul, Pi.mul_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at hp
  show (t : P C) p * (1 - e C c p) = 0
  unfold e; split_ifs with hc
  · simp
  · rw [coord_alg] at hp
    have hne : Ideal.Quotient.mk p.asIdeal c ≠ 0 := fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    rw [mul_eq_zero] at hp
    simp [hp.resolve_right hne]

theorem integral : Algebra.IsIntegral C (D C) := by
  apply Algebra.IsIntegral.adjoin
  rintro _ ⟨c, rfl⟩
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_one]
  funext p; simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]; unfold e; split_ifs <;> simp

theorem approx (r : Ideal (D C)) [r.IsPrime] (s : D C) :
    ∃ ε : D C, ε ∉ r ∧ ∃ c : C, ε * s = ε * algebraMap C (D C) c := by
  obtain ⟨x, hx⟩ := s
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    by_cases hc : Ei c ∈ r
    · refine ⟨1 - Ei c, fun h => r.ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance) ?_, 0, ?_⟩
      · have := r.add_mem h hc; simpa using this
      · rw [map_zero, mul_zero, mul_comm]; exact E_mul_one_sub c
    · refine ⟨Ei c, hc, 1, ?_⟩
      rw [map_one, mul_one]
      apply Subtype.ext; funext p
      show e C c p * e C c p = e C c p
      unfold e; split_ifs <;> simp
  | algebraMap c => exact ⟨1, fun h => (Ideal.IsPrime.ne_top inferInstance) (r.eq_top_of_isUnit_mem h isUnit_one), c, rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨ε1, h1, c1, e1⟩ := ihx
    obtain ⟨ε2, h2, c2, e2⟩ := ihy
    refine ⟨ε1 * ε2, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim h1 h2, c1 + c2, ?_⟩
    have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : D C) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add]
    linear_combination ε2 * e1 + ε1 * e2
  | mul x y hx hy ihx ihy =>
    obtain ⟨ε1, h1, c1, e1⟩ := ihx
    obtain ⟨ε2, h2, c2, e2⟩ := ihy
    refine ⟨ε1 * ε2, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim h1 h2, c1 * c2, ?_⟩
    have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : D C) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul]
    linear_combination (ε2 * ⟨y, hy⟩) * e1 + (ε1 * algebraMap C (D C) c1) * e2

section Loc
variable (r : Ideal (D C)) [r.IsPrime]
local notation "L" => Localization.AtPrime r

theorem unit_of (x : D C) (hx : x ∉ r) : IsUnit (algebraMap (D C) L x) :=
  IsLocalization.map_units L (⟨x, hx⟩ : r.primeCompl)

theorem eq_of_approx (s : D C) : ∃ c : C, algebraMap (D C) L s = algebraMap (D C) L (algebraMap C (D C) c) := by
  obtain ⟨ε, hε, c, h⟩ := approx r s
  refine ⟨c, ?_⟩
  have h' := congrArg (algebraMap (D C) L) h
  rw [map_mul, map_mul] at h'
  exact (unit_of r ε hε).mul_left_cancel h'

theorem frac (z : L) : ∃ a b : C, IsUnit (algebraMap (D C) L (algebraMap C (D C) b)) ∧
    z * algebraMap (D C) L (algebraMap C (D C) b) = algebraMap (D C) L (algebraMap C (D C) a) := by
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective r.primeCompl z
  obtain ⟨a, ha⟩ := eq_of_approx r x
  obtain ⟨b, hb⟩ := eq_of_approx r (t : D C)
  refine ⟨a, b, hb ▸ unit_of r t t.2, ?_⟩
  simp only
  rw [← hb, ← ha, IsLocalization.mk'_spec]

theorem zero_of_E (a : C) (h : Ei a ∉ r) : algebraMap (D C) L (algebraMap C (D C) a) = 0 := by
  have h' := congrArg (algebraMap (D C) L) (E_mul_alg a)
  rw [map_mul, map_zero] at h'
  exact (unit_of r _ h).mul_right_eq_zero.1 h'

theorem domain : IsDomain L := by
  have key : ∀ a b : C, algebraMap (D C) L (algebraMap C (D C) (a * b)) = 0 →
      algebraMap (D C) L (algebraMap C (D C) a) = 0 ∨ algebraMap (D C) L (algebraMap C (D C) b) = 0 := by
    intro a b h
    obtain ⟨⟨t, ht⟩, h0⟩ := (IsLocalization.map_eq_zero_iff r.primeCompl L _).1 h
    have h1 := ann_alg t (a * b) h0
    have hm : t * (1 - Ei (a * b)) ∈ r := h1 ▸ r.zero_mem
    have h2 : 1 - Ei (a * b) ∈ r := (Ideal.IsPrime.mem_or_mem inferInstance hm).resolve_left ht
    rw [one_sub_E_mul] at h2
    have hne : ∀ c : C, 1 - Ei c ∈ r → Ei c ∉ r := fun c h3 h4 =>
      (Ideal.IsPrime.ne_top inferInstance) (r.eq_top_iff_one.2 (by simpa using r.add_mem h3 h4))
    rcases Ideal.IsPrime.mem_or_mem inferInstance h2 with h3 | h3
    · exact Or.inl (zero_of_E r a (hne a h3))
    · exact Or.inr (zero_of_E r b (hne b h3))
  haveI : NoZeroDivisors L := ⟨fun {x y} hxy => by
    obtain ⟨a, b, hb, hx⟩ := frac r x
    obtain ⟨a', b', hb', hy⟩ := frac r y
    have : algebraMap (D C) L (algebraMap C (D C) (a * a')) = 0 := by
      rw [map_mul, map_mul, ← hx, ← hy]
      calc x * _ * (y * _) = x * y * (algebraMap (D C) L (algebraMap C (D C) b) *
          algebraMap (D C) L (algebraMap C (D C) b')) := by ring
        _ = 0 := by rw [hxy, zero_mul]
    rcases key a a' this with h | h
    · left; rw [← hx] at h; exact hb.mul_left_eq_zero.1 h
    · right; rw [← hy] at h; exact hb'.mul_left_eq_zero.1 h⟩
  exact NoZeroDivisors.to_isDomain L

end Loc

theorem spS (q : Ideal C) (hq : q.IsPrime) : ∃ Q : Ideal (D C), Q.IsPrime ∧ Q.comap (algebraMap C (D C)) = q := by
  let φ : D C →+* C ⧸ q := (Pi.evalRingHom (fun p : PrimeSpectrum C => C ⧸ p.asIdeal) ⟨q, hq⟩).comp
    (D C).val.toRingHom
  haveI := hq
  refine ⟨RingHom.ker φ, RingHom.ker_isPrime φ, ?_⟩
  rw [RingHom.comap_ker]
  have : φ.comp (algebraMap C (D C)) = Ideal.Quotient.mk q := by ext c; rfl
  rw [this, Ideal.mk_ker]

theorem IdemCover_of : LateralTheory.E.DomCoverPf.IdemCover := by
  intro C0
  haveI : Algebra.IsIntegral C0 (D C0) := integral
  refine ⟨CommRingCat.of (D C0), CommRingCat.ofHom (algebraMap C0 (D C0)), ?_, ?_, ?_⟩
  · intro x; exact Algebra.IsIntegral.isIntegral (R := C0) (x : D C0)
  · intro q hq; exact spS q hq
  · intro r _
    exact ⟨domain r, frac r⟩

end LateralTheory.E.IdemCoverPf
