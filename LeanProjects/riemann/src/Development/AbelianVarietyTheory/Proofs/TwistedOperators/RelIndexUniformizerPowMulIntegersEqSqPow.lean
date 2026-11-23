import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnramIntIndex

theorem le_exp_neg_one_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) :
    a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne a 0 with rfl | h
  · exact zero_le'
  · obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha
    rw [WithZero.coe_le_coe]
    have h1 : Multiplicative.toAdd m < 0 := ha
    show Multiplicative.toAdd m ≤ -1
    omega

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_maximalIdeal_iff (y : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) :
    y ∈ IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring ↔
      Valued.v (y : L) < 1 := by
  have hy : Valued.v (y : L) ≤ 1 := y.2
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hn
    refine lt_of_le_of_ne hy fun h1 => hn ?_
    have h0 : (y : L) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    have hinv : Valued.v ((y : L)⁻¹) ≤ 1 := by rw [map_inv₀, h1, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(y : L)⁻¹, hinv⟩ : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) ?_
    exact Subtype.ext (mul_inv_cancel₀ h0)
  · rintro hlt ⟨u, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, (u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) * z = 1 :=
      ⟨_, u.mul_inv⟩
    have h11 : (((u : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) : L)) * (z : L) = 1 :=
      congrArg Subtype.val hz
    have h1 := congrArg Valued.v h11
    rw [map_mul, map_one] at h1
    have h2 : Valued.v (z : L) ≤ 1 := z.2
    exact absurd h1 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt))

theorem relIndex_mul_uniformizer (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) :
    ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).relIndex
      (Formalism.UG.intL L).toAddSubgroup = q ^ 2 := by
  obtain ⟨-, -, -, h4, -, -, h7⟩ := h
  set V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring with hV
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hlt : Valued.v ϖ < 1 := by
    rw [h4, ← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    omega
  have hI : (IsLocalRing.maximalIdeal V).toAddSubgroup.index = q ^ 2 := h7
  let f : V →+ L := V.subtype.toAddMonoidHom
  have hf : Function.Injective f := Subtype.val_injective
  have e1 : (IsLocalRing.maximalIdeal V).toAddSubgroup.map f =
      (Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ) := by
    ext x
    simp only [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : Valued.v (y : L) < 1 := (mem_maximalIdeal_iff y).1 hy
      have hle := le_exp_neg_one_of_lt_one hy'
      refine ⟨ϖ⁻¹ * (y : L), ?_, ?_⟩
      · show Valued.v (ϖ⁻¹ * (y : L)) ≤ 1
        rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.mpr (by simpa using h0)), mul_one, h4]
        exact hle
      · show ϖ * (ϖ⁻¹ * (y : L)) = (y : L)
        field_simp
    · rintro ⟨o, ho, rfl⟩
      have ho' : Valued.v o ≤ 1 := ho
      have hm : Valued.v (ϖ * o) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' ho') hlt
      exact ⟨⟨ϖ * o, hm.le⟩, (mem_maximalIdeal_iff _).2 hm, rfl⟩
  have e2 : (⊤ : AddSubgroup V).map f = (Formalism.UG.intL L).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← e1, ← e2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  exact hI

theorem relIndex_mul_uniformizer_pow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) (e : ℕ) :
    ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex
      (Formalism.UG.intL L).toAddSubgroup = (q ^ 2) ^ e := by
  have hbase := relIndex_mul_uniformizer ϖ c q h
  obtain ⟨-, -, -, h4, -⟩ := h
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hϖ : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [h4, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  set O := (Formalism.UG.intL L).toAddSubgroup with hO
  have hmulle : ∀ a ∈ Formalism.UG.intL L, O.map (AddMonoidHom.mulLeft a) ≤ O := by
    rintro a ha _ ⟨o, ho, rfl⟩
    exact (Formalism.UG.intL L).mul_mem ha ho
  induction e with
  | zero =>
    have : O.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = O := by
      ext x
      simp [AddSubgroup.mem_map]
    rw [this]
    simp
  | succ e ih =>
    have hinj : Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) :=
      mul_right_injective₀ (pow_ne_zero e h0)
    have hcomp : O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) =
        (O.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨o, ho, by rw [pow_succ, mul_assoc]⟩
    have hstep : (O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex
        (O.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q ^ 2 := by
      rw [hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]
      exact hbase
    have hle1 : O.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ O.map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      rw [hcomp]
      exact AddSubgroup.map_mono (hmulle ϖ hϖ)
    have hle2 := hmulle (ϖ ^ e) (pow_mem hϖ e)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, hstep, ih]
    exact (pow_succ' _ _).symm

end GlobalTheory.UnramIntIndex
