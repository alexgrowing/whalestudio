import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

namespace BaseC

theorem inv_uniq {R : Type*} [CommRing R] {a b c : R} (ha : a * c = 1) (hb : b * c = 1) : a = b :=
  calc a = a * (b * c) := by rw [hb, mul_one]
    _ = (a * c) * b := by ring
    _ = b := by rw [ha, one_mul]

variable {l : ℕ} [Fact l.Prime]

theorem ι_eq : ι l = PositivityTheory.LocInh.ιCD l :=
  PositivityTheory.LocInh.bcris_hom_ext fun x =>
    (Loc2.lift_mk₀ (iC l) (isUnit_iC_l l) (isUnit_image_period l) x).trans (PositivityTheory.LocInh.ιCD_cB x).symm

theorem qB_eq : qB l = PositivityTheory.LocInh.qB l :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => by
    rw [RingHom.comp_apply, RingHom.comp_apply, qB, IsLocalization.lift_eq]
    exact (PositivityTheory.LocInh.qB_coe z).symm)

theorem aB_ainfMap (a : WittVector l (PreTilt ↥(PadicComplexInt l) l)) :
    aB l (ainfMap l a) = Formalism.Per6.aB l a := rfl

theorem aB_injective : Function.Injective (aB l) := by
  intro a b h
  obtain ⟨a, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) b
  rw [aB_ainfMap, aB_ainfMap] at h
  rw [PositivityTheory.LocInh.aB_injective h]

theorem φ_aB (a : AInf ℂ_[l] l) : φ l (aB l a) = aB l (WittVector.frobenius a) := by
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  rw [← PositivityTheory.LocInh.frob_ainfMap_frobenius, aB_ainfMap, aB_ainfMap]
  exact (PositivityTheory.LocInh.aB_frobenius b).symm

theorem σ_aB (g : GQ l) (a : AInf ℂ_[l] l) : ∃ a' : AInf ℂ_[l] l, σB g (aB l a) = aB l a' := by
  obtain ⟨b, rfl⟩ := PositivityTheory.LocInh.ainfMap_surjective (l := l) a
  refine ⟨ainfMap l (WittVector.map (PositivityTheory.LocInh.galT g) b), ?_⟩
  rw [aB_ainfMap, aB_ainfMap]
  exact (PositivityTheory.LocInh.aB_act g b).symm

abbrev u (l : ℕ) [Fact l.Prime] : B l := qB l ((l : ℚ_[l])⁻¹)

theorem u_mul : u l * (l : B l) = 1 := by
  rw [u, ← map_natCast (qB l) l, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), map_one]

theorem map_u (f : B l →+* B l) : f (u l) = u l := by
  refine inv_uniq (c := (l : B l)) ?_ u_mul
  rw [← map_natCast f l, ← map_mul, u_mul, map_one]

theorem aB_mem (a : AInf ℂ_[l] l) : aB l a ∈ Ainf' l :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem u_mem : u l ∈ Ainf' l :=
  Subring.subset_closure (Or.inr rfl)

theorem map_mem {f : B l →+* B l} (h1 : ∀ a, f (aB l a) ∈ Ainf' l) :
    ∀ x ∈ Ainf' l, f x ∈ Ainf' l := fun x hx =>
  (Subring.closure_le (t := (Ainf' l).comap f)).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · exact h1 a
    · rw [Set.mem_singleton_iff.1 hy]
      show f (u l) ∈ Ainf' l
      rw [map_u]
      exact u_mem) hx

theorem pow_u (y : B l) (n : ℕ) : y * (l : B l) ^ n * u l ^ n = y := by
  rw [mul_assoc, ← mul_pow, mul_comm (l : B l), u_mul, one_pow, mul_one]

def rep (l : ℕ) [Fact l.Prime] : Subring (B l) where
  carrier := {x | ∃ (a : AInf ℂ_[l] l) (k : ℕ), x = aB l a * u l ^ k}
  mul_mem' := by
    rintro _ _ ⟨a, k, rfl⟩ ⟨b, j, rfl⟩
    exact ⟨a * b, k + j, by rw [map_mul, pow_add]; ring⟩
  one_mem' := ⟨1, 0, by rw [map_one, pow_zero, mul_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, k, rfl⟩ ⟨b, j, rfl⟩
    refine ⟨a * (l : AInf ℂ_[l] l) ^ j + b * (l : AInf ℂ_[l] l) ^ k, k + j, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
    calc aB l a * u l ^ k + aB l b * u l ^ j =
        aB l a * (l : B l) ^ j * u l ^ j * u l ^ k + aB l b * (l : B l) ^ k * u l ^ k * u l ^ j := by
          rw [pow_u, pow_u]
      _ = _ := by ring
  zero_mem' := ⟨0, 0, by rw [map_zero, zero_mul]⟩
  neg_mem' := by
    rintro _ ⟨a, k, rfl⟩
    exact ⟨-a, k, by rw [map_neg, neg_mul]⟩

theorem mem_rep {x : B l} (hx : x ∈ Ainf' l) : ∃ (a : AInf ℂ_[l] l) (k : ℕ), x = aB l a * u l ^ k :=
  (Subring.closure_le (t := rep l)).2 (by
    rintro y (⟨a, rfl⟩ | hy)
    · exact ⟨a, 0, by rw [pow_zero, mul_one]⟩
    · rw [Set.mem_singleton_iff.1 hy]
      exact ⟨1, 1, by rw [map_one, one_mul, pow_one]⟩) hx

end BaseC

end period_ring_base
