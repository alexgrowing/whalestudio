import Mathlib
import GroundTheory.LocalFields.NormCorrespondence
import GroundTheory.LocalFields.Existence
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
import GroundTheory.ProfiniteCohomology.PoincareDuality.Torsion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open IntermediateField GroundTheory.LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {Ω : Type*} [Field Ω] [Algebra F Ω] [IsSepClosure F Ω]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Ω] in

theorem exists_norm_iff_mem_range_normUnits (E : IntermediateField F Ω) [FiniteDimensional F E]
    (a : Fˣ) : (∃ y : E, Algebra.norm F y = (a : F)) ↔ a ∈ (normUnits F E).range := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hy
      exact a.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simp [hy])⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, rfl⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSepClosure F Ω] in

theorem exists_norm_of_eq {E₁ E₂ : IntermediateField F Ω} (h : E₁ = E₂) {a : F}
    (hy : ∃ y : E₁, Algebra.norm F y = a) : ∃ y : E₂, Algebra.norm F y = a := by
  subst h
  exact hy

theorem eq_top_of_forall_exists_norm (H : Subgroup Gal(Ω/F)) [H.Normal]
    (hH : IsOpen (H : Set Gal(Ω/F))) (hcomm : ∀ σ τ : Gal(Ω/F), σ * τ * σ⁻¹ * τ⁻¹ ∈ H)
    (h : ∀ a : Fˣ, ∃ y : fixedField H, Algebra.norm F y = (a : F)) : H = ⊤ := by
  set E := fixedField H with hE
  have hfix : E.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
  have hfin : FiniteDimensional F E :=
    (InfiniteGalois.isOpen_iff_finite E).1 (by rw [hfix]; exact hH)
  have hgal : IsGalois F E :=
    (InfiniteGalois.normal_iff_isGalois E).1 (by rw [hfix]; infer_instance)
  have hc : ∀ σ' τ' : Gal(E/F), σ' * τ' = τ' * σ' := by
    intro σ' τ'
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) σ'
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) τ'
    have hk : σ * τ * σ⁻¹ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom E).ker := by
      rw [E.restrictNormalHom_ker, hfix]
      exact hcomm σ τ
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
    have key : ∀ {M : Type _} [Group M] (x y : M), x * y * x⁻¹ * y⁻¹ = 1 → x * y = y * x := by
      intro M _ x y hxy
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [hxy, one_mul]
    exact key _ _ hk
  have : IsAbelianGalois F E := { toIsGalois := hgal, toIsMulCommutative := ⟨⟨hc⟩⟩ }
  have hidx := index_range_normUnits_of_isAbelianGalois (Ω := Ω) E
  have htop : (normUnits F E).range = ⊤ :=
    eq_top_iff.2 fun a _ => (exists_norm_iff_mem_range_normUnits E a).1 (h a)
  rw [htop, Subgroup.index_top] at hidx
  have hbot : E = ⊥ := IntermediateField.finrank_eq_one_iff.1 hidx.symm
  rw [← hfix, hbot, IntermediateField.fixingSubgroup_bot]

theorem exists_zmod_char_not_norm {n : ℕ} (hn : (n : F) ≠ 0) (a : Fˣ) (ha : ∀ b : Fˣ, b ^ n ≠ a) :
    ∃ ψ : Gal(Ω/F) →* Multiplicative (ZMod n), IsOpen (ψ.ker : Set Gal(Ω/F)) ∧
      ¬ ∃ y : fixedField ψ.ker, Algebra.norm F y = (a : F) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  have : NeZero n := ⟨hn0⟩
  set P := (powMonoidHom n : Fˣ →* Fˣ).range with hP
  have hPopen : IsOpen (P : Set Fˣ) := isOpen_range_pow hn
  have hPfin : Finite (Fˣ ⧸ P) := finite_quotient_range_pow hn
  have : P.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hkill : ∀ q : Additive (Fˣ ⧸ P), n • q = 0 := by
    intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    have hq : q = Additive.ofMul (x : Fˣ ⧸ P) := by rw [hx]; rfl
    rw [hq, ← ofMul_pow, ← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff (x ^ n)).2 (MonoidHom.mem_range.2 ⟨x, rfl⟩),
      ofMul_one]
  have hane : Additive.ofMul (a : Fˣ ⧸ P) ≠ 0 := by
    intro h0
    have h1 : (a : Fˣ ⧸ P) = 1 := congrArg Additive.toMul h0
    obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).1 h1
    exact ha b hb
  obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero (A := Additive (Fˣ ⧸ P)) hkill hane
  let φ : Fˣ →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicativeRight χ).comp (QuotientGroup.mk' P)
  have hφ : ∀ x : Fˣ, φ x = Multiplicative.ofAdd (χ (Additive.ofMul (x : Fˣ ⧸ P))) := fun _ => rfl
  have hPle : P ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hφ, (QuotientGroup.eq_one_iff _).2 hx, ofMul_one, map_zero, ofAdd_zero]
  have hH'open : IsOpen (φ.ker : Set Fˣ) := Subgroup.isOpen_mono hPle hPopen
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hPle
  have haH' : a ∉ φ.ker := by
    rw [MonoidHom.mem_ker, hφ]
    intro h1
    exact hχ (Multiplicative.ofAdd.injective h1)
  obtain ⟨E, hEfin, hEab, hEH⟩ := exists_isAbelianGalois_range_normUnits_eq (Ω := Ω) φ.ker hH'open
  have := hEfin
  have := hEab
  let φbar : Fˣ ⧸ (normUnits F E).range →* Multiplicative (ZMod n) :=
    QuotientGroup.lift _ φ (le_of_eq hEH)
  have hφbar : Function.Injective φbar := by
    refine (injective_iff_map_eq_one φbar).2 fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : x ∈ φ.ker := hq
      rw [← hEH] at hx
      exact (QuotientGroup.eq_one_iff _).2 hx
  let ψ : Gal(Ω/F) →* Multiplicative (ZMod n) :=
    (φbar.comp (localReciprocityAbelian E).toMonoidHom).comp (AlgEquiv.restrictNormalHom E)
  have hker : ψ.ker = E.fixingSubgroup := by
    rw [← E.restrictNormalHom_ker]
    ext σ
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : (localReciprocityAbelian E) (AlgEquiv.restrictNormalHom E σ) = 1 :=
        hφbar (h1.trans (map_one φbar).symm)
      exact (MulEquiv.map_eq_one_iff _).1 h2
    · intro h1
      change φbar ((localReciprocityAbelian E) (AlgEquiv.restrictNormalHom E σ)) = 1
      rw [h1, map_one, map_one]
  refine ⟨ψ, ?_, ?_⟩
  · rw [hker]
    exact IntermediateField.fixingSubgroup_isOpen E
  · have hfE : fixedField ψ.ker = E := by
      rw [hker]
      exact InfiniteGalois.fixedField_fixingSubgroup E
    intro hy
    have := (exists_norm_iff_mem_range_normUnits E a).1 (exists_norm_of_eq hfE hy)
    rw [hEH] at this
    exact haH' this

end GroundTheory.ProfCoh
