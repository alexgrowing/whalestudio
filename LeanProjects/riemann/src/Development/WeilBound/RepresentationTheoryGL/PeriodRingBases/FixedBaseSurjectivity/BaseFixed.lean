import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FrobAinfMapFrobenius
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.ThetaAlgebraMap.ThAlgebraMap

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst PfDRPst Matrix

namespace BaseA

variable {l : ℕ} [Fact l.Prime]

open GroundTheory.PAdicHodge.ACris in
theorem uB_root {ζ : PadicAlgCl l} {m : ℕ} (hm : 0 < m) (hc : m.Coprime l) (hζ : ζ ^ m = 1)
    (h : ζ ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) : PositivityTheory.LocInh.uB l ⟨ζ, h⟩ ∈ Ainf' l := by
  obtain ⟨T, hT, hθT⟩ := exists_teichmuller_rootOfUnity hm hc hζ
  have hζ0 : (ζ : ℂ_[l]) ≠ 0 := by
    intro h0
    have := norm_eq_one_of_pow_eq_one hm (show (ζ : ℂ_[l]) ^ m = 1 by
      rw [PadicComplex.coe_eq, ← map_pow, hζ, map_one])
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hx : iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) T) = algClToBdR l ζ := by
    apply eq_of_pow_eq_one_of_theta_eq hm
    · rw [← map_pow, ← map_pow, hT, map_one, map_one]
    · rw [← map_pow, hζ, map_one]
    · rw [thetaAlgHom_apply, thetaField_iota, theta_algebraMap, hθT, thetaAlgHom_algClToBdR]
    · rw [thetaAlgHom_algClToBdR]; exact hζ0
  have e : aB l T = PositivityTheory.LocInh.uB l ⟨ζ, h⟩ := by
    apply base_ι_inj l
    have e1 : ι l (aB l T) = algebraMap (BdRp l) (BdR l)
        (iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) T)) := ι_cB l _
    rw [e1, hx, ι_eq, PositivityTheory.LocInh.ιCD_uB, PositivityTheory.LocInh.GaloisCommutant.oD_apply]
  rw [← e]
  exact Subring.subset_closure (Or.inl ⟨T, rfl⟩)

theorem uB_mem (c : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) : PositivityTheory.LocInh.uB l c ∈ Ainf' l := by
  obtain ⟨c, hc⟩ := c
  have e : (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra =
      Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1} :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  have adj : ∀ x, x ∈ Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1} →
      x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l := fun x hx => by
    have : x ∈ (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra := e ▸ hx
    exact this
  have key : ∀ x ∈ Algebra.adjoin ℚ_[l] {x : PadicAlgCl l | ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m = 1},
      ∀ h : x ∈ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l, PositivityTheory.LocInh.uB l ⟨x, h⟩ ∈ Ainf' l := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      intro h
      obtain ⟨m, hm, hl, hxm⟩ := hx
      exact uB_root hm (Nat.Coprime.symm (((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl)) hxm h
    | algebraMap r =>
      intro h
      have : (⟨algebraMap ℚ_[l] (PadicAlgCl l) r, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) =
          algebraMap ℚ_[l] ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) r := rfl
      rw [this, PositivityTheory.LocInh.uB_algebraMap, ← qB_eq]
      exact EstT.qB_mem_ainf r
    | add x y hx hy ihx ihy =>
      intro h
      have : (⟨x + y, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) = ⟨x, adj x hx⟩ + ⟨y, adj y hy⟩ := rfl
      rw [this, map_add]
      exact Subring.add_mem _ (ihx (adj x hx)) (ihy (adj y hy))
    | mul x y hx hy ihx ihy =>
      intro h
      have : (⟨x * y, h⟩ : ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l)) = ⟨x, adj x hx⟩ * ⟨y, adj y hy⟩ := rfl
      rw [this, map_mul]
      exact Subring.mul_mem _ (ihx (adj x hx)) (ihy (adj y hy))
  exact key c (by have : c ∈ (Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l).toSubalgebra := hc; rwa [e] at this) hc

end BaseA

open BaseA

theorem base_fixed' (l : ℕ) [Fact l.Prime] : ∀ L : Fld l, FiniteDimensional ℚ_[l] L →
    ∃ (f : ℕ) (b : Fin f → B l),
    (∀ i, b i ∈ Ainf' l ∧ ∀ σ ∈ L.fixingSubgroup, σB σ (b i) = b i) ∧
    ∀ x, (∀ σ ∈ L.fixingSubgroup, σB σ x = x) → ∃ q : Fin f → ℚ_[l], x = ∑ i, qB l (q i) * b i := by
  intro L hL
  let L0 : IntermediateField ℚ_[l] (PadicAlgCl l) := L ⊓ Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l
  have : FiniteDimensional ℚ_[l] L0 := by
    have : FiniteDimensional ℚ_[l] L.toSubalgebra.toSubmodule := hL
    exact Submodule.finiteDimensional_of_le (S₂ := L.toSubalgebra.toSubmodule)
      (S₁ := L0.toSubalgebra.toSubmodule) fun x hx => (IntermediateField.mem_inf.1 hx).1
  let bas := Module.finBasis ℚ_[l] L0
  let c : Fin (Module.finrank ℚ_[l] L0) → ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) :=
    fun i => ⟨(bas i : PadicAlgCl l), (IntermediateField.mem_inf.1 (bas i).2).2⟩
  refine ⟨_, fun i => PositivityTheory.LocInh.uB l (c i), fun i => ⟨uB_mem _, fun σ hσ => ?_⟩, fun x hx => ?_⟩
  · apply base_ι_inj l
    rw [base_ι_σ, ι_eq, PositivityTheory.LocInh.ιCD_uB, PositivityTheory.LocInh.σD_oD]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (IntermediateField.mem_inf.1 (bas i).2).1
  · obtain ⟨k, hkL, hk⟩ := PositivityTheory.LocInh.invB ⟨L, hL⟩ x fun g hg => hx g hg
    let k0 : L0 := ⟨k, IntermediateField.mem_inf.2 ⟨hkL, k.2⟩⟩
    refine ⟨fun i => bas.repr k0 i, ?_⟩
    rw [← hk]
    have hsum := congrArg (fun y : L0 => (y : PadicAlgCl l)) (bas.sum_repr k0).symm
    have hk' : k = ∑ i, algebraMap ℚ_[l] ↥(Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l) (bas.repr k0 i) * c i := by
      apply Subtype.ext
      refine hsum.trans ?_
      simp only [IntermediateField.coe_sum, Algebra.smul_def, IntermediateField.coe_mul, c]
      rfl
    rw [hk', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, PositivityTheory.LocInh.uB_algebraMap, qB_eq]

end period_ring_base
