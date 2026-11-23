import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TenFin

theorem finite_quot_of_gen {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal R)
    (f : A →+* R) (g : B →+* R) (J₁ : Ideal A) (J₂ : Ideal B) (h₁ : J₁.map f ≤ I) (h₂ : J₂.map g ≤ I)
    [Finite (A ⧸ J₁)] [Finite (B ⧸ J₂)] (hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (hI : (n : R) ∈ I) : Finite (R ⧸ I) := by
  let π := Ideal.Quotient.mk I
  let fa : A ⧸ J₁ →+* R ⧸ I := Ideal.Quotient.lift J₁ (π.comp f) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (h₁ (Ideal.mem_map_of_mem f ha)))
  let gb : B ⧸ J₂ →+* R ⧸ I := Ideal.Quotient.lift J₂ (π.comp g) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (h₂ (Ideal.mem_map_of_mem g ha)))
  have hfa : ∀ a, π (f a) = fa (Ideal.Quotient.mk J₁ a) := fun a => rfl
  have hgb : ∀ b, π (g b) = gb (Ideal.Quotient.mk J₂ b) := fun b => rfl
  let S : Set (R ⧸ I) := Set.image2 (· * ·) (Set.range fa) (Set.range gb)
  have hS : S.Finite := (Set.finite_range fa).image2 _ (Set.finite_range gb)
  let M : Submonoid (R ⧸ I) :=
    { carrier := S
      one_mem' := ⟨1, ⟨1, map_one _⟩, 1, ⟨1, map_one _⟩, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ ⟨_, ⟨a', rfl⟩, _, ⟨b', rfl⟩, rfl⟩
        refine ⟨fa (a * a'), ⟨_, rfl⟩, gb (b * b'), ⟨_, rfl⟩, ?_⟩
        simp only [map_mul]; ring }
  have hsub : π '' (Set.range f ∪ Set.range g) ⊆ (M : Set (R ⧸ I)) := by
    rintro _ ⟨_, ⟨a, rfl⟩ | ⟨b, rfl⟩, rfl⟩
    · exact ⟨fa (Ideal.Quotient.mk J₁ a), ⟨_, rfl⟩, 1, ⟨1, map_one _⟩, (mul_one _).trans (hfa a).symm⟩
    · exact ⟨1, ⟨1, map_one _⟩, gb (Ideal.Quotient.mk J₂ b), ⟨_, rfl⟩, (one_mul _).trans (hgb b).symm⟩
  have htop : AddSubgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subring.closure (π '' (Set.range f ∪ Set.range g)) := by
      rw [← RingHom.map_closure, hgen, ← RingHom.range_eq_map]
      exact Ideal.Quotient.mk_surjective x
    rw [Subring.mem_closure_iff] at hx
    refine AddSubgroup.closure_mono ?_ hx
    exact Submonoid.closure_le.2 hsub
  haveI : AddGroup.FG (R ⧸ I) := ⟨⟨hS.toFinset, by rw [Set.Finite.coe_toFinset]; exact htop⟩⟩
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  rw [nsmul_eq_mul]
  have : (n : R ⧸ I) = 0 := by
    rw [← map_natCast π]; exact Ideal.Quotient.eq_zero_iff_mem.2 hI
  rw [this, zero_mul]

theorem finite_intKQ_quot : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r m : ℕ),
    Finite (GlobalTheory.LKLoc.intK p K ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m}) →
    Finite (GlobalTheory.LKLoc.intK p (Qr p r) ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) →
    Finite (intKQ p K r ⧸ Ideal.span {(p : intKQ p K r) ^ m}) := by
  intro p _ K r m hA hB
  let f : GlobalTheory.LKLoc.intK p K →+* intKQ p K r :=
    ((inclK p K r).toRingHom.comp (GlobalTheory.LKLoc.intK p K).subtype).codRestrict (intKQ p K r)
      (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩))
  let g : GlobalTheory.LKLoc.intK p (Qr p r) →+* intKQ p K r :=
    ((inclQ p K r).toRingHom.comp (GlobalTheory.LKLoc.intK p (Qr p r)).subtype).codRestrict (intKQ p K r)
      (fun b => Subring.subset_closure (Or.inr ⟨⟨b.1, b.2⟩, rfl⟩))
  have hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨⟨b.1, b.2⟩, rfl⟩)
    | zero => exact zero_mem _
    | one => exact one_mem _
    | add y z _ _ h1 h2 => exact add_mem h1 h2
    | neg y _ h => exact neg_mem h
    | mul y z _ _ h1 h2 => exact mul_mem h1 h2
  refine finite_quot_of_gen (J₁ := Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m})
    (J₂ := Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) _ f g ?_ ?_ hgen (p ^ m) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) ?_
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · rw [Nat.cast_pow]; exact Ideal.subset_span rfl

end GlobalTheory.TenFin
