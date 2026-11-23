import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.UnitsPowers
import GroundTheory.LocalFields.UnramifiedRootsOfUnity

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IntermediateField

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ} {ζ : L}

theorem algebra_adjoin_eq_top_of_adjoin_eq_top (htop : K⟮ζ⟯ = ⊤) : Algebra.adjoin K {ζ} = ⊤ :=
  (IntermediateField.adjoin_eq_top_iff (F := K) (E := L)).mp htop

theorem algEquiv_eq_one_of_apply_eq (htop : K⟮ζ⟯ = ⊤) {σ : L ≃ₐ[K] L} (hσ : σ ζ = ζ) : σ = 1 := by
  have h := AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop)
    (φ₁ := σ.toAlgHom) (φ₂ := AlgHom.id K L) (by simpa using hσ)
  ext x
  exact DFunLike.congr_fun h x

theorem isGalois_of_adjoin_eq_top (hζ : IsPrimitiveRoot ζ m)
    (hm : (m : K) ≠ 0) (htop : K⟮ζ⟯ = ⊤) : IsGalois K L := by
  have : NeZero m := ⟨by rintro rfl; simp at hm⟩
  have : IsCyclotomicExtension {m} K L := by
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨ζ, hζ⟩, fun x ↦ ?_⟩
    have hle : Algebra.adjoin K {ζ} ≤ Algebra.adjoin K {b : L | b ^ m = 1} :=
      Algebra.adjoin_mono (by simpa using hζ.pow_eq_one)
    exact hle (by rw [algebra_adjoin_eq_top_of_adjoin_eq_top htop]; trivial)
  exact IsCyclotomicExtension.isGalois {m} K L

end Generic

section PrimitiveResidue

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem isPrimitiveRoot_residue {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {ζ : 𝒪[L]}
    (hζ : IsPrimitiveRoot ζ m) : IsPrimitiveRoot (IsLocalRing.residue 𝒪[L] ζ) m := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl ↦ hζ.dvd_of_pow_eq_one l ?_⟩
  refine eq_of_pow_eq_one_of_residue_eq hm ?_ (one_pow m) (by rw [map_pow, hl, map_one])
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem natCast_ne_zero_of_residueField {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) : (m : L) ≠ 0 := by
  intro h
  apply hm
  have : (m : 𝒪[L]) = 0 := Subtype.ext (by simpa using h)
  rw [← map_natCast (IsLocalRing.residue 𝒪[L]), this, map_zero]

end PrimitiveResidue

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Residue

variable (L) in

theorem natCast_residueField_ne_zero {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) : (m : 𝓀[L]) ≠ 0 := by
  rw [← map_natCast (algebraMap 𝓀[K] 𝓀[L])]
  exact (map_ne_zero_iff _ (algebraMap 𝓀[K] 𝓀[L]).injective).mpr hm

end Residue

section Cyclotomic

variable {m : ℕ} {ζ : L}

private def rootInteger (hm : m ≠ 0) (hζ : ζ ^ m = 1) : 𝒪[L] :=
  ⟨ζ, mem_integer_of_pow_eq_one hm hζ⟩

variable (K L) in

theorem residueAlgEquiv_injective_of_adjoin_eq_top (hm : (m : 𝓀[K]) ≠ 0) (hζ : ζ ^ m = 1)
    (htop : K⟮ζ⟯ = ⊤) : Function.Injective (residueAlgEquiv K L) := by
  have hmL := natCast_residueField_ne_zero L hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply algEquiv_eq_one_of_apply_eq htop
  set z := rootInteger hm0 hζ
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z, rootInteger] using hζ)
  have key : integerAlgEquiv K L σ z = z := by
    refine eq_of_pow_eq_one_of_residue_eq hmL (by rw [← map_pow, hz, map_one]) hz ?_
    rw [← residueAlgEquiv_residue, hσ, AlgEquiv.one_apply]
  simpa [z, rootInteger] using congrArg Subtype.val key

theorem ramificationIndex_eq_one_of_adjoin_eq_top (hζ : IsPrimitiveRoot ζ m) (hm : (m : 𝓀[K]) ≠ 0)
    (htop : K⟮ζ⟯ = ⊤) : ramificationIndex K L = 1 := by
  have := isGalois_of_adjoin_eq_top hζ (natCast_ne_zero_of_residueField (L := K) hm) htop
  have hinj := residueAlgEquiv_injective_of_adjoin_eq_top K L hm hζ.pow_eq_one htop
  have hcard : Module.finrank K L ≤ residueDegree K L := by
    rw [← IsGalois.card_aut_eq_finrank, residueDegree_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_le_card_of_injective _ hinj
  have hf := residueDegree_pos K L
  rw [← ramificationIndex_mul_residueDegree K L] at hcard
  have he := ramificationIndex_pos K L
  nlinarith

end Cyclotomic

section Unramified

variable (K L)

theorem residueDegree_eq_finrank_of_unramified (h : ramificationIndex K L = 1) :
    residueDegree K L = Module.finrank K L := by
  rw [← ramificationIndex_mul_residueDegree K L, h, one_mul]

theorem exists_isPrimitiveRoot_adjoin_eq_top_of_unramified (h : ramificationIndex K L = 1) :
    ∃ ζ : L, IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) ∧ K⟮ζ⟯ = ⊤ := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := L)
  refine ⟨z, hz.map_of_injective (f := (𝒪[L]).subtype) Subtype.val_injective, ?_⟩
  have hres := isPrimitiveRoot_residue (natCast_card_residueField_sub_one_ne_zero L) hz
  have htop' : 𝓀[K]⟮IsLocalRing.residue 𝒪[L] z⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    by_cases hy : y = 0
    · rw [hy]
      exact zero_mem _
    · have := Fintype.ofFinite 𝓀[L]
      have : NeZero (Nat.card 𝓀[L] - 1) := ⟨fun h0 ↦
        natCast_card_residueField_sub_one_ne_zero L (by rw [h0, Nat.cast_zero])⟩
      have hy1 : y ^ (Nat.card 𝓀[L] - 1) = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one y hy
      obtain ⟨i, -, rfl⟩ := hres.eq_pow_of_pow_eq_one hy1
      exact pow_mem (mem_adjoin_simple_self _ _) _
  refine eq_of_le_of_finrank_le le_top ?_
  rw [finrank_top', adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    ← residueDegree_eq_finrank_of_unramified K L h, residueDegree_eq_finrank]
  calc Module.finrank 𝓀[K] 𝓀[L] = Module.finrank 𝓀[K] 𝓀[K]⟮IsLocalRing.residue 𝒪[L] z⟯ := by
        rw [htop', finrank_top']
    _ = (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] z)).natDegree :=
        adjoin.finrank (Algebra.IsIntegral.isIntegral _)
    _ ≤ _ := natDegree_minpoly_residue_le z

theorem isGalois_of_unramified (h : ramificationIndex K L = 1) : IsGalois K L := by
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hm := natCast_ne_zero_of_residueField (natCast_card_residueField_sub_one_ne_zero L)
  refine isGalois_of_adjoin_eq_top hζ (fun h0 ↦ hm ?_) htop
  rw [← map_natCast (algebraMap K L), h0, map_zero]

theorem residueAlgEquiv_injective_of_unramified (h : ramificationIndex K L = 1) :
    Function.Injective (residueAlgEquiv K L) := by
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hm := natCast_card_residueField_sub_one_ne_zero L
  refine residueAlgEquiv_injective_of_adjoin_eq_top K L (m := Nat.card 𝓀[L] - 1) (fun h0 ↦ hm ?_)
    hζ.pow_eq_one htop
  rw [← map_natCast (algebraMap 𝓀[K] 𝓀[L]), h0, map_zero]

theorem card_algEquiv_of_unramified (h : ramificationIndex K L = 1) :
    Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
  have := isGalois_of_unramified K L h
  exact IsGalois.card_aut_eq_finrank K L

theorem residueAlgEquiv_bijective_of_unramified (h : ramificationIndex K L = 1) :
    Function.Bijective (residueAlgEquiv K L) := by
  refine (residueAlgEquiv_injective_of_unramified K L h).bijective_of_nat_card_le ?_
  rw [card_algEquiv_of_unramified K L h, IsGalois.card_aut_eq_finrank, ← residueDegree_eq_finrank,
    residueDegree_eq_finrank_of_unramified K L h]

def galoisEquivResidue (h : ramificationIndex K L = 1) :
    (L ≃ₐ[K] L) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulEquiv.ofBijective (residueAlgEquiv K L) (residueAlgEquiv_bijective_of_unramified K L h)

@[simp]
theorem galoisEquivResidue_apply (h : ramificationIndex K L = 1) (σ : L ≃ₐ[K] L) :
    galoisEquivResidue K L h σ = residueAlgEquiv K L σ :=
  rfl

theorem isCyclic_of_unramified (h : ramificationIndex K L = 1) : IsCyclic (L ≃ₐ[K] L) :=
  isCyclic_of_surjective (galoisEquivResidue K L h).symm.toMonoidHom
    (galoisEquivResidue K L h).symm.surjective

def frobenius (h : ramificationIndex K L = 1) : L ≃ₐ[K] L :=
  letI := Fintype.ofFinite 𝓀[K]
  (galoisEquivResidue K L h).symm (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L])

theorem residueAlgEquiv_frobenius_apply (h : ramificationIndex K L = 1) (y : 𝓀[L]) :
    residueAlgEquiv K L (frobenius K L h) y = y ^ Nat.card 𝓀[K] := by
  let := Fintype.ofFinite 𝓀[K]
  have : residueAlgEquiv K L (frobenius K L h) =
      FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L] :=
    (galoisEquivResidue K L h).apply_symm_apply _
  rw [this, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Fintype.card_eq_nat_card]

theorem residue_frobenius_apply (h : ramificationIndex K L = 1) (x : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L] (integerAlgEquiv K L (frobenius K L h) x) =
      IsLocalRing.residue 𝒪[L] x ^ Nat.card 𝓀[K] := by
  rw [← residueAlgEquiv_residue, residueAlgEquiv_frobenius_apply]

theorem frobenius_sub_pow_mem_maximalIdeal (h : ramificationIndex K L = 1) (x : 𝒪[L]) :
    integerAlgEquiv K L (frobenius K L h) x - x ^ Nat.card 𝓀[K] ∈ 𝓂[L] := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, residue_frobenius_apply, sub_self]

theorem orderOf_frobenius (h : ramificationIndex K L = 1) :
    orderOf (frobenius K L h) = Module.finrank K L := by
  let := Fintype.ofFinite 𝓀[K]
  rw [frobenius, MulEquiv.orderOf_eq, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
    ← residueDegree_eq_finrank, residueDegree_eq_finrank_of_unramified K L h]

theorem zpowers_frobenius (h : ramificationIndex K L = 1) :
    Subgroup.zpowers (frobenius K L h) = ⊤ := by
  let := Fintype.ofFinite 𝓀[K]
  rw [eq_top_iff]
  intro σ _
  obtain ⟨k, hk⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[K] 𝓀[L]).2
    (galoisEquivResidue K L h σ)
  refine ⟨(k : ℕ), ?_⟩
  apply (galoisEquivResidue K L h).injective
  simp only [zpow_natCast, map_pow]
  rw [← hk, frobenius, MulEquiv.apply_symm_apply]

variable {K L}

theorem frobenius_apply_of_pow_eq_one (h : ramificationIndex K L = 1) {m : ℕ}
    (hm : (m : 𝓀[K]) ≠ 0) {ξ : L} (hξ : ξ ^ m = 1) :
    frobenius K L h ξ = ξ ^ Nat.card 𝓀[K] := by
  have hmL := natCast_residueField_ne_zero L hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set z : 𝒪[L] := ⟨ξ, mem_integer_of_pow_eq_one hm0 hξ⟩
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z] using hξ)
  have key : integerAlgEquiv K L (frobenius K L h) z = z ^ Nat.card 𝓀[K] := by
    refine eq_of_pow_eq_one_of_residue_eq hmL (by rw [← map_pow, hz, map_one]) ?_ ?_
    · rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
    · rw [residue_frobenius_apply, map_pow]
  simpa [z] using congrArg Subtype.val key

theorem natCast_card_pow_sub_one_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
  have := Fintype.ofFinite 𝓀[K]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos), Nat.cast_pow, Nat.card_eq_fintype_card,
    FiniteField.cast_card_eq_zero, zero_pow hn, Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

theorem finrank_eq_of_adjoin_eq_top {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (htop : K⟮ζ⟯ = ⊤) :
    Module.finrank K L = n := by
  set q := Nat.card 𝓀[K] with hq_def
  have hq : 1 < q := one_lt_card_residueField K
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have h := ramificationIndex_eq_one_of_adjoin_eq_top hζ hm htop
  set F := frobenius K L h
  have hF : F ζ = ζ ^ q := frobenius_apply_of_pow_eq_one h hm hζ.pow_eq_one
  have hFk : ∀ k : ℕ, (F ^ k) ζ = ζ ^ (q ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hF, ← pow_mul, ← pow_succ']
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by
    have : 1 < q ^ n := Nat.one_lt_pow hn hq
    omega)
  have hpow : ∀ k : ℕ, ζ ^ (q ^ k) = ζ ↔ ζ ^ (q ^ k - 1) = 1 := by
    intro k
    have h1 : q ^ k = q ^ k - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    conv_lhs => rw [h1, pow_succ]
    constructor
    · intro h2
      exact mul_left_cancel₀ hζ0 (by rw [mul_one, mul_comm]; exact h2)
    · intro h2
      rw [h2, one_mul]
  have hd := orderOf_frobenius K L h
  have hfin := Module.finrank_pos (R := K) (M := L)
  apply le_antisymm
  ·
    have hFn : F ^ n = 1 := by
      apply algEquiv_eq_one_of_apply_eq htop
      rw [hFk, hpow]
      exact hζ.pow_eq_one
    rw [← hd]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (orderOf_dvd_of_pow_eq_one hFn)
  ·
    have h1 : ζ ^ (q ^ Module.finrank K L - 1) = 1 := by
      rw [← hpow, ← hFk, ← hd, pow_orderOf_eq_one, AlgEquiv.one_apply]
    have hdvd := hζ.dvd_of_pow_eq_one _ h1
    have hlt : 1 < q ^ Module.finrank K L := Nat.one_lt_pow hfin.ne' hq
    have hle := Nat.le_of_dvd (by omega) hdvd
    have : q ^ n ≤ q ^ Module.finrank K L := by
      have := Nat.one_le_pow n q (by omega)
      omega
    exact (Nat.pow_le_pow_iff_right hq).mp this

end Unramified

end GroundTheory.LocalField
