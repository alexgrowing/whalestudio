import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ModelC

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ValuativeRel Function ReciprocityTheory.Neutral.Cmp

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] {p : ℕ} [Fact p.Prime] (m : Model K p)

theorem Model.E_algebraMap_integer (c : 𝒪[K]) :
    m.E (algebraMap 𝒪[K] (AlgebraicClosure K) c) = (m.e (c : K) : PadicAlgCl p) := m.comm _

theorem Model.mem_integral_closure_iff_norm (x : AlgebraicClosure K) : x ∈ integersBar K ↔ ‖m.E x‖ ≤ 1 := by
  constructor
  · rintro ⟨P, hPm, hP⟩
    let f : 𝒪[K] →+* PadicAlgCl p :=
      (m.E : AlgebraicClosure K →+* PadicAlgCl p).comp (algebraMap 𝒪[K] (AlgebraicClosure K))
    refine norm_le_one_of_monic_root (P.map f) (hPm.map f) (fun i => ?_) ?_
    · rw [Polynomial.coeff_map]
      show ‖m.E (algebraMap 𝒪[K] (AlgebraicClosure K) (P.coeff i))‖ ≤ 1
      rw [m.E_algebraMap_integer]
      exact (m.int _).1 (P.coeff i).2
    · have := congrArg (m.E : AlgebraicClosure K →+* PadicAlgCl p) hP
      rw [map_zero, Polynomial.hom_eval₂] at this
      rw [Polynomial.eval_map]
      exact this
  · intro hy
    obtain ⟨q, hqm, hq⟩ := (norm_le_one_iff_isIntegral (m.E x)).1 hy
    let ψ : PadicInt.subring p →+* 𝒪[K] :=
      ((m.e.symm : m.K' →+* K).comp ((algebraMap ℚ_[p] m.K').comp (PadicInt.subring p).subtype)).codRestrict
        𝒪[K] (fun c => (m.int _).2 (by
          show ‖((m.e (m.e.symm (algebraMap ℚ_[p] m.K' (c : ℚ_[p]))) : m.K') : PadicAlgCl p)‖ ≤ 1
          rw [RingEquiv.apply_symm_apply]
          show ‖algebraMap ℚ_[p] (PadicAlgCl p) (c : ℚ_[p])‖ ≤ 1
          rw [norm_algebraMap']
          exact c.2))
    refine ⟨q.map ψ, hqm.map ψ, ?_⟩
    apply m.E.injective
    rw [Polynomial.eval₂_map, map_zero]
    have := Polynomial.hom_eval₂ q ((algebraMap 𝒪[K] (AlgebraicClosure K)).comp ψ)
      (m.E : AlgebraicClosure K →+* PadicAlgCl p) x
    change (m.E : AlgebraicClosure K →+* PadicAlgCl p) _ = 0
    rw [this, ← hq]
    congr 1
    ext c
    show m.E (algebraMap 𝒪[K] (AlgebraicClosure K) (ψ c)) = _
    rw [m.E_algebraMap_integer]
    show ((m.e (m.e.symm (algebraMap ℚ_[p] m.K' (c : ℚ_[p]))) : m.K') : PadicAlgCl p) = _
    rw [RingEquiv.apply_symm_apply]
    rfl

theorem Model.mem_maximal_ideal_closure_iff_norm (x : AlgebraicClosure K) : x ∈ maxIdealBar K ↔ ‖m.E x‖ < 1 := by
  show (x ∈ integersBar K ∧ (x = 0 ∨ x⁻¹ ∉ integersBar K)) ↔ _
  rw [m.mem_integral_closure_iff_norm, m.mem_integral_closure_iff_norm]
  by_cases h0 : x = 0
  · simp [h0]
  · have hn : 0 < ‖m.E x‖ := norm_pos_iff.2 (by simpa using h0)
    rw [map_inv₀, norm_inv]
    simp only [h0, false_or, not_le]
    rw [one_lt_inv_iff₀]
    exact ⟨fun h => h.2.2, fun h => ⟨h.le, hn, h⟩⟩

noncomputable def Model.toOK : 𝒪[K] →+* OK p m.K' :=
  ((m.e : K →+* m.K').comp 𝒪[K].subtype).codRestrict _ (fun c => (mem_OK_iff p m.K' _).2 ((m.int _).1 c.2))

theorem Model.toOK_surjective : Surjective m.toOK := by
  intro y
  refine ⟨⟨m.e.symm y, (m.int _).2 ?_⟩, ?_⟩
  · rw [RingEquiv.apply_symm_apply]
    exact (mem_OK_iff p m.K' _).1 y.2
  · apply Subtype.ext
    show m.e (m.e.symm y) = y
    rw [RingEquiv.apply_symm_apply]

theorem Model.card_residue_field_model [IsNonarchimedeanLocalField K] : Nat.card 𝓀[K] = qK p m.K' := by
  let f : 𝒪[K] →+* resK p m.K' := (redK p m.K').comp m.toOK
  have hf : Surjective f := (redK_surjective p m.K').comp m.toOK_surjective
  have hker : RingHom.ker f = IsLocalRing.maximalIdeal 𝒪[K] :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f hf)
  rw [qK]
  exact Nat.card_congr ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)).toEquiv

theorem Model.mem_integer_iff_vK (x : Kˣ) : (x : K) ∈ 𝒪[K] ↔ 0 ≤ vK p m.K' (m.eU x) := by
  rw [m.int, ← norm_le_one_iff_vK p m.K' m.fin]
  rfl

theorem Model.isUnit_integer_iff (x : Kˣ) (hx : (x : K) ∈ 𝒪[K]) :
    IsUnit (⟨x, hx⟩ : 𝒪[K]) ↔ vK p m.K' (m.eU x) = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]).1 = ((x⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val]
      apply eq_inv_of_mul_eq_one_left
      have h2 : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (u : 𝒪[K]) = 1 := u.inv_mul
      rw [hu] at h2
      exact congrArg Subtype.val h2
    have h3 : ((x⁻¹ : Kˣ) : K) ∈ 𝒪[K] := h1 ▸ ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]).2
    rw [m.mem_integer_iff_vK, map_inv, vK_inv] at h3
    rw [m.mem_integer_iff_vK] at hx
    omega
  · intro h
    have h3 : ((x⁻¹ : Kˣ) : K) ∈ 𝒪[K] := by
      rw [m.mem_integer_iff_vK, map_inv, vK_inv, h]; simp
    exact IsUnit.of_mul_eq_one ⟨_, h3⟩ (Subtype.ext (by simp))

theorem Model.isUniformiser_iff_valuation_one (π : Kˣ) : IsUniformiser K (π : K) ↔ vK p m.K' (m.eU π) = 1 := by
  constructor
  · rintro ⟨hπ, hirr⟩
    obtain ⟨ϖ', hϖ'⟩ := exists_vK_eq_one p m.K' m.fin
    obtain ⟨ϖ, rfl⟩ := m.eU.surjective ϖ'
    have h0 := (m.mem_integer_iff_vK π).1 hπ
    have h1 : vK p m.K' (m.eU π) ≠ 0 := fun h => hirr.not_isUnit ((m.isUnit_integer_iff π hπ).2 h)
    have hϖ : (ϖ : K) ∈ 𝒪[K] := by rw [m.mem_integer_iff_vK, hϖ']; exact zero_le_one
    have hv : vK p m.K' (m.eU (ϖ⁻¹ * π)) = vK p m.K' (m.eU π) - 1 := by
      rw [map_mul, vK_mul, map_inv, vK_inv, hϖ']; ring
    have hq : ((ϖ⁻¹ * π : Kˣ) : K) ∈ 𝒪[K] := by
      rw [m.mem_integer_iff_vK, hv]; omega
    have hmul : (⟨π, hπ⟩ : 𝒪[K]) = ⟨ϖ, hϖ⟩ * ⟨_, hq⟩ := Subtype.ext (by simp)
    rcases hirr.isUnit_or_isUnit hmul with h | h
    · rw [m.isUnit_integer_iff, hϖ'] at h; omega
    · rw [m.isUnit_integer_iff, hv] at h; omega
  · intro h
    have hπ : (π : K) ∈ 𝒪[K] := by rw [m.mem_integer_iff_vK, h]; exact zero_le_one
    refine ⟨hπ, ?_, ?_⟩
    · rw [m.isUnit_integer_iff, h]; omega
    · intro a b hab
      have hab' : (π : K) = a.1 * b.1 := congrArg Subtype.val hab
      have ha0 : a.1 ≠ 0 := fun h0 => π.ne_zero (by rw [hab', h0, zero_mul])
      have hb0 : b.1 ≠ 0 := fun h0 => π.ne_zero (by rw [hab', h0, mul_zero])
      have hπab : π = Units.mk0 a.1 ha0 * Units.mk0 b.1 hb0 := Units.ext hab'
      have ha := (m.mem_integer_iff_vK (Units.mk0 a.1 ha0)).1 a.2
      have hb := (m.mem_integer_iff_vK (Units.mk0 b.1 hb0)).1 b.2
      rw [hπab, map_mul, vK_mul] at h
      have h2 : vK p m.K' (m.eU (Units.mk0 a.1 ha0)) = 0 ∨ vK p m.K' (m.eU (Units.mk0 b.1 hb0)) = 0 := by omega
      exact h2.imp (fun h => (m.isUnit_integer_iff (Units.mk0 a.1 ha0) a.2).2 h)
        (fun h => (m.isUnit_integer_iff (Units.mk0 b.1 hb0) b.2).2 h)

theorem Model.isHomeomorph_units_model : IsHomeomorph m.eU := by
  have h1 : Continuous m.eU := Continuous.units_map (m.e : K →* m.K') m.homeo.continuous
  have h2 : Continuous m.eU.symm :=
    Continuous.units_map (m.e.symm : m.K' →* K) (m.e.toEquiv.toHomeomorphOfContinuousOpen m.homeo.continuous m.homeo.isOpenMap).symm.continuous
  exact (Homeomorph.mk m.eU.toEquiv h1 h2).isHomeomorph

end ReciprocityTheory.DiscreteGroups.LocalClassField
