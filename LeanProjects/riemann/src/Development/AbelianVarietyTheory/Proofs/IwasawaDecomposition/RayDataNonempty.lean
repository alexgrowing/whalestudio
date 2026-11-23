import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero

noncomputable section

namespace GlobalTheory.Mem.RayEx

open NumberField IsDedekindDomain

section General

variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)

def S : Submonoid (Ideal R) where
  carrier := {I | IsCoprime I m}
  mul_mem' := fun ha hb => IsCoprime.mul_left ha hb
  one_mem' := isCoprime_one_left

def Rel (I J : Ideal R) : Prop :=
  ∃ a b : R, a - 1 ∈ m ∧ b - 1 ∈ m ∧ Ideal.span {a} * I = Ideal.span {b} * J

variable {m}

theorem mul_sub_one_mem {a b : R} (ha : a - 1 ∈ m) (hb : b - 1 ∈ m) : a * b - 1 ∈ m := by
  have : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [this]
  exact m.add_mem (m.mul_mem_left _ hb) ha

theorem ne_zero_of_sub_one_mem (hm : m ≠ ⊤) {a : R} (ha : a - 1 ∈ m) : a ≠ 0 := by
  rintro rfl
  apply hm
  rw [Ideal.eq_top_iff_one]
  simpa using m.neg_mem ha

theorem ne_bot_of_isCoprime (hm : m ≠ ⊤) {I : Ideal R} (h : IsCoprime I m) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at h
  exact hm h

theorem exists_mem_sub_one {I : Ideal R} (h : IsCoprime I m) : ∃ a ∈ I, a - 1 ∈ m := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp h
  refine ⟨a, ha, ?_⟩
  have : a - 1 = -b := by rw [← hab]; ring
  rw [this]
  exact m.neg_mem hb

theorem isCoprime_span {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m := by
  refine Ideal.isCoprime_iff_exists.mpr ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, by ring⟩

theorem Rel.refl (I : Ideal R) : Rel m I I := ⟨1, 1, by simp, by simp, rfl⟩

theorem Rel.symm {I J : Ideal R} (h : Rel m I J) : Rel m J I := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  exact ⟨b, a, hb, ha, h.symm⟩

theorem Rel.mul {I J I' J' : Ideal R} (h : Rel m I J) (h' : Rel m I' J') : Rel m (I * I') (J * J') := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨c, d, hc, hd, h'⟩ := h'
  refine ⟨a * c, b * d, mul_sub_one_mem ha hc, mul_sub_one_mem hb hd, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    mul_mul_mul_comm, h, h', mul_mul_mul_comm]

theorem Rel.trans {I J L : Ideal R} (h : Rel m I J) (h' : Rel m J L) : Rel m I L := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  obtain ⟨c, d, hc, hd, h'⟩ := h'
  refine ⟨c * a, b * d, mul_sub_one_mem hc ha, mul_sub_one_mem hb hd, ?_⟩
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    mul_assoc, h, mul_left_comm, h', mul_assoc]

variable (m) in

def con : Con (S m) where
  r I J := Rel m I.1 J.1
  iseqv := ⟨fun I => Rel.refl _, Rel.symm, Rel.trans⟩
  mul' := fun h h' => Rel.mul h h'

theorem isUnit_quot (x : (con m).Quotient) : IsUnit x := by
  obtain ⟨⟨I, hI⟩, rfl⟩ := Con.mk'_surjective (c := con m) x
  obtain ⟨a, haI, ha⟩ := exists_mem_sub_one hI
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr haI
  have hJ' : IsCoprime J m := by
    have := isCoprime_span ha
    rw [hJ] at this
    exact this.of_mul_left_right
  refine IsUnit.of_mul_eq_one ((con m).mk' ⟨J, hJ'⟩) ?_
  rw [← map_mul, ← map_one (con m).mk']
  refine (Con.eq _).mpr ?_
  refine ⟨1, a, by simp, ha, ?_⟩
  simp [hJ]

theorem exists_good {I J : Ideal R} (hI : IsCoprime I m) (hJ : IsCoprime J m) {x y : R} (hy : y ≠ 0)
    (h : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ b : R, IsCoprime (Ideal.span {b}) m ∧ Rel m I (Ideal.span {b} * J) := by
  obtain ⟨a, haJ, ha⟩ := exists_mem_sub_one hJ
  have h1 : y * a ∈ Ideal.span {x} * I := by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) haJ
  obtain ⟨b, -, hb⟩ := Ideal.mem_span_singleton_mul.mp h1
  have h2 : Ideal.span {a} * I = Ideal.span {b} * J := by
    have hy' : (Ideal.span {y} : Ideal R) ≠ 0 := by simpa using hy
    apply mul_left_cancel₀ hy'
    rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← hb, mul_left_comm, ← h, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, mul_comm b x]
  refine ⟨b, ?_, a, 1, ha, by simp, by simp [h2]⟩
  have := (isCoprime_span ha).mul_left hI
  rw [h2] at this
  exact this.of_mul_left_left

theorem rel_span {b c : R} (hb : IsCoprime (Ideal.span {b}) m) (h : b - c ∈ m) :
    Rel m (Ideal.span {b}) (Ideal.span {c}) := by
  obtain ⟨a, haI, ha⟩ := exists_mem_sub_one hb
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp haI
  refine ⟨u * c, u * b, ?_, ha, ?_⟩
  · have : u * c - 1 = (u * b - 1) - u * (b - c) := by ring
    rw [this]
    exact m.sub_mem ha (m.mul_mem_left _ h)
  · rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    congr 2
    ring

theorem finite_quot (hm : m ≠ ⊤) [Finite (R ⧸ m)] [Finite (ClassGroup R)] : Finite (con m).Quotient := by
  let cl : S m → ClassGroup R := fun I =>
    ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_zero (ne_bot_of_isCoprime hm I.2)⟩
  have key : ∀ I : S m, ∃ b : R, IsCoprime (Ideal.span {b}) m ∧
      Rel m I.1 (Ideal.span {b} * (Function.invFun cl (cl I)).1) := by
    intro I
    have h : cl I = cl (Function.invFun cl (cl I)) := (Function.invFun_eq ⟨I, rfl⟩).symm
    obtain ⟨x, y, -, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    exact exists_good I.2 (Function.invFun cl (cl I)).2 hy hxy
  choose b hb hrel using key
  let F : (con m).Quotient → ClassGroup R × (R ⧸ m) := fun x =>
    (cl (Quotient.out x), Ideal.Quotient.mk m (b (Quotient.out x)))
  refine Finite.of_injective F ?_
  intro x y hxy
  obtain ⟨h1, h2⟩ := Prod.mk.inj hxy
  rw [Ideal.Quotient.eq] at h2
  refine Quotient.out_equiv_out.mp ?_
  have h3 := hrel (Quotient.out y)
  rw [← h1] at h3
  exact ((hrel _).trans ((rel_span (hb _) h2).mul (Rel.refl _))).trans h3.symm

theorem exists_group (hm : m ≠ ⊤) [Finite (R ⧸ m)] [Finite (ClassGroup R)] :
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (φ : S m →* G), Function.Surjective φ ∧
      ∀ I J, φ I = φ J ↔ Rel m I.1 J.1 := by
  haveI : Finite (con m).Quotient := finite_quot hm
  exact ⟨(con m).Quotient, commGroupOfIsUnit isUnit_quot, Fintype.ofFinite _, (con m).mk',
    Con.mk'_surjective, fun I J => Con.eq _⟩

theorem map_mul_mk {G : Type} [CommGroup G] (φ : S m →* G) {I J : Ideal R} (hI : IsCoprime I m)
    (hJ : IsCoprime J m) : φ ⟨I * J, hI.mul_left hJ⟩ = φ ⟨I, hI⟩ * φ ⟨J, hJ⟩ := by
  have h : (⟨I * J, hI.mul_left hJ⟩ : S m) = (⟨I, hI⟩ : S m) * (⟨J, hJ⟩ : S m) :=
    Subtype.ext (Submonoid.coe_mul (S m) ⟨I, hI⟩ ⟨J, hJ⟩).symm
  rw [h, map_mul]

end General

open Classical in

theorem nonempty_rayData (K : Type) [Field K] [NumberField K] (M : ℕ) (hM : 2 ≤ M) : Nonempty (RayData K M) := by
  set m : Ideal (𝓞 K) := Ideal.span {(M : 𝓞 K)} with hmdef
  have hm0 : m ≠ ⊥ := by
    rw [hmdef, Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hm : m ≠ ⊤ := by
    rw [hmdef, Ne, Ideal.span_singleton_eq_top]
    intro h
    have h' : IsUnit (algebraMap ℤ (𝓞 K) (M : ℤ)) := by simpa using h
    have := (isUnit_map_iff (algebraMap ℤ (𝓞 K)) _).mp h'
    rw [Int.isUnit_iff] at this
    omega
  haveI : Finite (𝓞 K ⧸ m) := Ideal.finiteQuotientOfFreeOfNeBot m hm0
  obtain ⟨G, _, _, φ, hs, he⟩ := exists_group hm
  refine ⟨{ G := G
            cls := fun I => if h : IsCoprime I m then φ ⟨I, h⟩ else 1
            cls_mul := ?_, cls_surj := ?_, cls_eq := ?_ }⟩
  · intro I J hI hJ _ _
    rw [dif_pos hI, dif_pos hJ, dif_pos (hI.mul_left hJ)]
    exact map_mul_mk φ hI hJ
  · intro c
    obtain ⟨⟨I, hI⟩, rfl⟩ := hs c
    exact ⟨I, hI, ne_bot_of_isCoprime hm hI, dif_pos hI⟩
  · intro I J hI hJ _ _
    rw [dif_pos hI, dif_pos hJ, he]
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨a, b, ne_zero_of_sub_one_mem hm ha, ne_zero_of_sub_one_mem hm hb, ha, hb, h⟩
    · rintro ⟨a, b, -, -, ha, hb, h⟩
      exact ⟨a, b, ha, hb, h⟩

end GlobalTheory.Mem.RayEx

end
