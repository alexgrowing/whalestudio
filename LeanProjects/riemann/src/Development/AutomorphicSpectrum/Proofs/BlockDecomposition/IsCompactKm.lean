import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open Filter Topology ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.KmTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_Km_iff (N m : ℕ) (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j) ∈ 𝒪[k] := by
  have ha : ((Zls.unifU k : k) ^ m) = algebraMap 𝒪[k] k (Zls.unif k ^ m) := by
    simp [Zls.unifU]
  have ha0 : ((Zls.unifU k : k) ^ m) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    have h1 : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) (u.val i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) := by
      have h2 := congrArg (fun w => w.val i j) (MonoidHom.mem_ker.1 hu)
      simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
    have h3 : (Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val i j -
        (1 : Matrix (Fin N) (Fin N) k) i j = algebraMap 𝒪[k] k (c * Zls.unif k ^ m) := by
      rw [hc, map_sub]
      simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h3, map_mul, ← ha, mul_comm (algebraMap 𝒪[k] k c), inv_mul_cancel_left₀ ha0]
    exact c.2
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 ?_, rfl⟩
    refine Units.ext ?_
    ext i j
    have h1 := h i j
    let c : 𝒪[k] := ⟨_, h1⟩
    have h2 : algebraMap 𝒪[k] k (u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) =
        algebraMap 𝒪[k] k (c * Zls.unif k ^ m) := by
      rw [map_mul, ← ha, map_sub]
      show _ = ((Zls.unifU k : k) ^ m)⁻¹ * _ * _
      rw [mul_comm, mul_inv_cancel_left₀ ha0]
      simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h3 := IsFractionRing.injective 𝒪[k] k h2
    have h4 : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) (u.val i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m}) ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨c, h3.symm⟩)
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]
    rw [h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem continuous_entry (N m : ℕ) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k =>
      ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j) := by
  have h : Continuous fun g : GL (Fin N) k => g.val i j :=
    (continuous_id.matrix_elem i j).comp Units.continuous_val
  exact continuous_const.mul (h.sub continuous_const)

theorem coe_Km_eq (N m : ℕ) : (Zls.Km k N m : Set (GL (Fin N) k)) =
    (KO k (Fin N) : Set (GL (Fin N) k)) ∩ ⋂ i, ⋂ j, (fun g : GL (Fin N) k =>
      ((Zls.unifU k : k) ^ m)⁻¹ * (g.val i j - (1 : Matrix (Fin N) (Fin N) k) i j)) ⁻¹' (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    GlobalTheory.SplitWeil.Model.isOpen_int.preimage (continuous_entry N m i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  refine GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j => ?_)
  exact (GlobalTheory.SplitWeil.Model.isCompact_int.isClosed).preimage (continuous_entry N m i j)

end GlobalTheory.CompanionTheory.KmTop
