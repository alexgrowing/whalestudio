import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAuxiliaryPlacesSquarePatternsSUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FirstInequalitySUnitsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoPowLeIndexLocalNormsSqrtExtensionStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsLocalSquaresFiniteRealPlacesLeStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupLocalSquaresEqTop

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup {G : Type} [CommGroup G] (U W : Subgroup G) :
    W.index = W.relIndex U * (U ⊔ W).index := by
  rw [← Subgroup.relIndex_mul_index (le_sup_right : W ≤ U ⊔ W), Subgroup.relIndex_sup_right]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.sqs_le_locSq (F : Type) [Field F] [NumberField F]
    (U : Subgroup Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    _root_.GlobalTheory.QNorm.sqs U ≤ _root_.GlobalTheory.QNorm.locSq F S := by
  intro x hx
  unfold _root_.GlobalTheory.QNorm.sqs at hx
  obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.mp hx
  unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq
  rw [Subgroup.mem_inf]
  simp only [Subgroup.mem_iInf, _root_.GlobalTheory.QNorm.mem_sqSub, powMonoidHom_apply,
    Units.val_pow_eq_pow_val, map_pow]
  exact ⟨fun v _ => ⟨_, sq _⟩, fun σ => ⟨_, sq _⟩⟩

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma eq_one_of_mul_self_eq_one_withZero (a : WithZero (Multiplicative ℤ))
    (h : a * a = 1) : a = 1 := by
  induction a using WithZero.recZeroCoe with
  | zero => simp at h
  | coe m =>
    have h1 : m * m = 1 := by exact_mod_cast h
    have h2 : Multiplicative.toAdd m + Multiplicative.toAdd m = 0 := by
      rw [← toAdd_mul, h1, toAdd_one]
    have h3 : Multiplicative.toAdd m = 0 := by omega
    have h4 : m = 1 := by rw [← ofAdd_toAdd m, h3, ofAdd_zero]
    rw [h4, WithZero.coe_one]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Fˣ) (hy : y ∈ _root_.GlobalTheory.QNorm.sUnits F S)
    (h : IsSquare (y : F)) : y ∈ _root_.GlobalTheory.QNorm.sqs (_root_.GlobalTheory.QNorm.sUnits F S) := by
  obtain ⟨s, hs⟩ := h
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact y.ne_zero hs
  unfold _root_.GlobalTheory.QNorm.sqs
  refine Subgroup.mem_map.mpr ⟨Units.mk0 s hs0, ?_, ?_⟩
  · rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hy ⊢
    intro v hv
    have h1 := hy v hv
    rw [hs, map_mul] at h1
    exact eq_one_of_mul_self_eq_one_withZero _ h1
  · ext
    simp [hs, sq]

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma sqs_le_self {G : Type} [CommGroup G] (U : Subgroup G) :
    _root_.GlobalTheory.QNorm.sqs U ≤ U := by
  intro y hy
  unfold _root_.GlobalTheory.QNorm.sqs at hy
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
  rw [powMonoidHom_apply]
  exact U.pow_mem hs 2

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), _root_.GlobalTheory.QNorm.admitted F S → δ ∈ _root_.GlobalTheory.QNorm.sUnits F S → ¬ IsSquare (δ : F) → ∀ x ∈ _root_.GlobalTheory.QNorm.sUnits F S, x ∈ _root_.GlobalTheory.QNorm.locNorm F δ S → x ∈ _root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) := by
  intro F _ _ δ S hS hδ hns x hx hxN
  classical
  obtain ⟨T, hST, hcard, hδT, hpat⟩ :=
    _root_.GlobalTheory.QNorm.exists_auxiliary_places F δ S hS hδ hns
  have htop := _root_.GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top F S T hS hST hpat
  have hS' := hS.mono (Finset.subset_union_left (s₂ := T))
  have hUU : _root_.GlobalTheory.QNorm.sUnits F S ≤ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) := by
    intro z hz
    rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hz ⊢
    intro v hv
    exact hz v (fun h => hv (Finset.mem_union_left _ h))
  have hsq_eq : _root_.GlobalTheory.QNorm.locSq F S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) =
      _root_.GlobalTheory.QNorm.sqs (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) := by
    apply le_antisymm
    · rintro y ⟨hyL, hyU⟩
      exact _root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare F _ y hyU
        (_root_.GlobalTheory.QNorm.isSquare_of_mem_locSq F S T hS htop y hyU hyL)
    · exact le_inf (_root_.GlobalTheory.QNorm.sqs_le_locSq F _ S) (sqs_le_self _)
  obtain ⟨hL0, hL⟩ := _root_.GlobalTheory.QNorm.index_locSq_le F S
  have hrel := _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits F (S ∪ T)
  have hL' := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locSq F S)
  rw [← Subgroup.inf_relIndex_right, hsq_eq, hrel, Finset.card_union_of_disjoint hST] at hL'
  have hJ0 : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).index ≠ 0 := by
    rw [hL'] at hL0
    exact right_ne_zero_of_mul hL0
  have hJ : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).index ≤ 2 := by
    have h4 : (4 : ℕ) ^ (S.card + Fintype.card (InfinitePlace F)) =
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]
      congr 1
      omega
    rw [hL', h4] at hL
    exact le_of_mul_le_mul_left hL (by positivity)
  have hLN : _root_.GlobalTheory.QNorm.locSq F S ≤ _root_.GlobalTheory.QNorm.locNorm F δ S := by
    intro y hy
    unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq at hy
    unfold _root_.GlobalTheory.QNorm.locNorm
    rw [Subgroup.mem_inf] at hy ⊢
    simp only [Subgroup.mem_iInf] at hy ⊢
    exact ⟨fun v hv => _root_.GlobalTheory.QNorm.sqSub_le_normSub _ _ (hy.1 v hv),
      fun σ => _root_.GlobalTheory.QNorm.sqSub_le_normSub _ _ (hy.2 σ)⟩
  haveI : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locSq F S).FiniteIndex :=
    ⟨hJ0⟩
  have hK : (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T) ⊔ _root_.GlobalTheory.QNorm.locNorm F δ S).index ≤ 2 :=
    le_trans (Subgroup.index_antitone (sup_le_sup_left hLN _)) hJ
  obtain ⟨hR0, hR⟩ := _root_.GlobalTheory.QNorm.first_inequality_sUnits F δ (S ∪ T) hS' (hUU hδ) hns
  obtain ⟨-, hN⟩ := _root_.GlobalTheory.QNorm.two_pow_le_index_locNorm F (δ : F) S δ.ne_zero
  have hcnt : _root_.GlobalTheory.QNorm.tFin F δ (S ∪ T) = _root_.GlobalTheory.QNorm.tFin F δ S := by
    unfold _root_.GlobalTheory.QNorm.tFin
    congr 1
    ext v
    simp only [Set.mem_setOf_eq, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, h⟩
      · exact ⟨hv, h⟩
      · exact absurd (hδT v hv) h
    · rintro ⟨hv, h⟩
      exact ⟨Or.inl hv, h⟩
  have hNidx := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locNorm F δ S)
  have hGN := _root_.GlobalTheory.QNorm.normSub_id_le_locNorm F (δ : F) S
  have hRle : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F)).relIndex
      (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≤
      (_root_.GlobalTheory.QNorm.locNorm F δ S).relIndex (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) := by
    have h2 : 2 * (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F)).relIndex
        (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≤
        (_root_.GlobalTheory.QNorm.locNorm F δ S).relIndex (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) * 2 := by
      calc _ ≤ _ := hR
        _ = 2 ^ (_root_.GlobalTheory.QNorm.tFin F δ S + _root_.GlobalTheory.QNorm.tReal F δ) := by rw [hcnt]
        _ ≤ _ := hN
        _ = _ := hNidx
        _ ≤ _ := Nat.mul_le_mul_left _ hK
    omega
  have hchain := Subgroup.relIndex_mul_relIndex
    (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T))
    (_root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) (inf_le_inf_right _ hGN) inf_le_right
  rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right] at hchain
  have hne : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)).relIndex
      (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hchain
    exact hR0 hchain.symm
  have hNpos := lt_of_lt_of_le (Nat.pos_of_ne_zero hR0) hRle
  have hone : (_root_.GlobalTheory.QNorm.normSub (RingHom.id F) (δ : F) ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)).relIndex
      (_root_.GlobalTheory.QNorm.locNorm F δ S ⊓ _root_.GlobalTheory.QNorm.sUnits F (S ∪ T)) = 1 := by
    have hle1 := hchain.le.trans hRle
    have h3 := le_of_mul_le_mul_right (hle1.trans (one_mul _).symm.le) hNpos
    omega
  exact (Subgroup.relIndex_eq_one.mp hone ⟨hxN, hUU hx⟩).1

end GlobalTheory.QNorm
