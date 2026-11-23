import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.IndBasic

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.Ind

open PI.KLW

theorem exists_refl {K : Type} [Field K] (c : K →+* K) (hc : ∀ x, c (c x) = x) {ι : Type}
    [Fintype ι] (e0 e : ι → K) (h0 : hf c e0 e0 = 1) (h1 : hf c e e = 1) (hne : hf c e0 e ≠ 1) :
    ∃ σ : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c σ ∧ σ e0 = e := by
  obtain ⟨w, hw⟩ : ∃ w, w = e0 - e := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t, t = hf c e0 w := ⟨_, rfl⟩
  have ht : t = 1 - hf c e0 e := by rw [htdef, hw, hf_sub_right, h0]
  have ht0 : t ≠ 0 := by rw [ht]; exact sub_ne_zero.mpr (Ne.symm hne)
  have hct : c t = 1 - hf c e e0 := by rw [htdef, hf_conj c hc, hw, hf_sub_left, h0]
  have hww : hf c w w = t + c t := by
    rw [hct, ht, hw, hf_sub_left, hf_sub_right, hf_sub_right, h0, h1]
    ring
  have hct0 : c t ≠ 0 := (map_ne_zero c).mpr ht0
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = t⁻¹ := ⟨_, rfl⟩
  have key : γ + c γ = γ * c γ * hf c w w := by
    rw [hww, hγ, map_inv₀]
    field_simp
    ring
  let φ : (ι → K) →ₗ[K] K :=
    { toFun := fun v => γ * hf c v w
      map_add' := fun a b => by rw [hf_add_left, mul_add]
      map_smul' := fun k a => by rw [hf_smul_left, RingHom.id_apply, smul_eq_mul]; ring }
  let σL : (ι → K) →ₗ[K] (ι → K) := LinearMap.id - φ.smulRight w
  have hσ : ∀ v, σL v = v - (γ * hf c v w) • w := fun v => rfl
  have iso : ∀ v v', hf c (σL v) (σL v') = hf c v v' := by
    intro v v'
    rw [hσ, hσ]
    simp only [hf_sub_left, hf_sub_right, hf_smul_left, hf_smul_right, map_mul]
    rw [← hf_conj c hc v' w]
    linear_combination (-(hf c v w * c (hf c v' w))) * key
  refine ⟨mkU c σL iso, mkU_unitary c σL iso, ?_⟩
  rw [mkU_apply, hσ, ← htdef, hγ, inv_mul_cancel₀ ht0, one_smul, hw, sub_sub_cancel]

theorem unimod_preimage {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] {σ : (ι → K) ≃ₗ[K] (ι → K)} (hσ : IsUnitary c σ) {L : Set (ι → K)}
    (hL : Unimod K c p L) : Unimod K c p (σ ⁻¹' L) := by
  intro v
  constructor
  · intro hv w hw
    rw [← hσ]
    exact (hL (σ v)).1 hv (σ w) hw
  · intro h
    show σ v ∈ L
    rw [hL]
    intro w hw
    have h' := h (σ.symm w) (by show σ (σ.symm w) ∈ L; rw [LinearEquiv.apply_symm_apply]; exact hw)
    rwa [← hσ, LinearEquiv.apply_symm_apply] at h'

theorem spans_preimage {K : Type} [Field K] {ι : Type} {σ : (ι → K) ≃ₗ[K] (ι → K)}
    {L : Set (ι → K)} (hS : Spans K L) : Spans K (σ ⁻¹' L) := fun v => by
  obtain ⟨N, hN, h⟩ := hS (σ v)
  exact ⟨N, hN, by show σ _ ∈ L; rw [map_smul]; exact h⟩

def extL {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι) :
    ({i // i ≠ i0} → K) →ₗ[K] (ι → K) where
  toFun w i := if h : i = i0 then 0 else w ⟨i, h⟩
  map_add' a b := by
    funext i
    by_cases h : i = i0 <;> simp [h]
  map_smul' k a := by
    funext i
    by_cases h : i = i0 <;> simp [h]

def resL {K : Type} [Field K] {ι : Type} (i0 : ι) : (ι → K) →ₗ[K] ({i // i ≠ i0} → K) :=
  LinearMap.funLeft K K Subtype.val

theorem extL_self {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι)
    (w : {i // i ≠ i0} → K) : extL i0 w i0 = 0 := by
  simp [extL]

theorem extL_ne {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι)
    (w : {i // i ≠ i0} → K) (j : {i // i ≠ i0}) : extL i0 w j.1 = w j := by
  simp [extL, j.2]

theorem resL_apply {K : Type} [Field K] {ι : Type} (i0 : ι) (v : ι → K) (j : {i // i ≠ i0}) :
    resL i0 v j = v j.1 := rfl

theorem decomp {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι) (v : ι → K) :
    v = extL i0 (resL i0 v) + v i0 • Pi.single i0 1 := by
  funext i
  by_cases h : i = i0
  · subst h
    simp [extL_self]
  · have := extL_ne i0 (resL i0 v) ⟨i, h⟩
    simp only at this
    simp [this, resL_apply, Pi.single_eq_of_ne h]

theorem hf_ext_ext {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (a b : {i // i ≠ i0} → K) : hf c (extL i0 a) (extL i0 b) = hf c a b := by
  unfold hf
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i0]
  simp only [extL_self, extL_ne, zero_mul, zero_add]

theorem hf_decomp {K : Type} [Field K] (c : K →+* K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i0 : ι) (a b : {i // i ≠ i0} → K) (x y : K) :
    hf c (extL i0 a + x • Pi.single i0 1) (extL i0 b + y • Pi.single i0 1)
      = hf c a b + x * c y := by
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hf_ext_ext,
    hf_single_right, hf_single_left, extL_self, map_zero, Pi.add_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, mul_one, zero_add]
  ring

theorem split_step {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (i0 : ι) (L : Set (ι → K)) (hL : Unimod K c p L)
    (hS : Spans K L) (he : Pi.single i0 (1 : K) ∈ L)
    (hrec : ∀ L' : Set ({i // i ≠ i0} → K), Unimod K c p L' → Spans K L' →
      ∃ u : ({i // i ≠ i0} → K) ≃ₗ[K] ({i // i ≠ i0} → K),
        IsUnitary c u ∧ ∀ v, v ∈ L' ↔ ∀ j, Rp K p (u v j)) :
    ∃ u : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c u ∧ ∀ v, v ∈ L ↔ ∀ i, Rp K p (u v i) := by
  have hv0 : ∀ v ∈ L, Rp K p (v i0) := fun v hv => by
    have := (hL v).1 hv _ he
    rwa [hf_single_right] at this
  have hres : ∀ v ∈ L, extL i0 (resL i0 v) ∈ L := fun v hv => by
    have e1 : extL i0 (resL i0 v) = v + (-(v i0)) • Pi.single i0 1 := by
      rw [neg_smul, ← sub_eq_add_neg]
      exact eq_sub_iff_add_eq.mpr (decomp i0 v).symm
    rw [e1]
    exact add_smul_mem hL hv he (rp_neg (hv0 v hv))
  let L' : Set ({i // i ≠ i0} → K) := {a | extL i0 a ∈ L}
  have hL' : Unimod K c p L' := by
    intro a
    constructor
    · intro ha b hb
      rw [← hf_ext_ext c i0]
      exact (hL _).1 ha _ hb
    · intro h
      show extL i0 a ∈ L
      rw [hL]
      intro x hx
      rw [decomp i0 x, hf_add_right, hf_smul_right, hf_single_right, extL_self, mul_zero,
        add_zero, hf_ext_ext]
      exact h _ (hres x hx)
  have hS' : Spans K L' := fun a => by
    obtain ⟨N, hN, h⟩ := hS (extL i0 a)
    exact ⟨N, hN, by show extL i0 _ ∈ L; rw [map_smul]; exact h⟩
  obtain ⟨u', hu', hmem'⟩ := hrec L' hL' hS'
  let U : (ι → K) →ₗ[K] (ι → K) :=
    extL i0 ∘ₗ (u'.toLinearMap ∘ₗ resL i0) + (LinearMap.proj i0).smulRight (Pi.single i0 1)
  have hU : ∀ v, U v = extL i0 (u' (resL i0 v)) + v i0 • Pi.single i0 1 := fun v => rfl
  have iso : ∀ v w, hf c (U v) (U w) = hf c v w := by
    intro v w
    rw [hU, hU, hf_decomp, hu']
    conv_rhs => rw [decomp i0 v, decomp i0 w]
    rw [hf_decomp]
  refine ⟨mkU c U iso, mkU_unitary c U iso, fun v => ?_⟩
  simp only [mkU_apply]
  have hUi0 : U v i0 = v i0 := by
    rw [hU]
    simp [extL_self]
  have hUj : ∀ j : {i // i ≠ i0}, U v j.1 = u' (resL i0 v) j := fun j => by
    rw [hU, Pi.add_apply, extL_ne, Pi.smul_apply, Pi.single_eq_of_ne j.2, smul_zero, add_zero]
  constructor
  · intro hv i
    by_cases h : i = i0
    · subst h
      rw [hUi0]
      exact hv0 v hv
    · have := hUj ⟨i, h⟩
      simp only at this
      rw [this]
      exact (hmem' _).1 (hres v hv) _
  · intro h
    have h0 : Rp K p (v i0) := hUi0 ▸ h i0
    have h1 : resL i0 v ∈ L' := (hmem' _).2 fun j => hUj j ▸ h j.1
    rw [decomp i0 v]
    exact add_smul_mem hL h1 he h0

theorem card_ne_sub {ι : Type} [Fintype ι] [DecidableEq ι] (i0 : ι) (k : ℕ)
    (hk : Fintype.card ι = k + 1) : Fintype.card {i // i ≠ i0} = k := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, hk, Nat.add_sub_cancel]

theorem latIso_card (hN : NormOne) {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ)
    (hK : Module.finrank ℚ K = 2) (hc : ∀ x, c (c x) = x) (hp : p.Prime) (hs : SplitK c p) :
    ∀ (k : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = k → ∀ L : Set (ι → K),
      Unimod K c p L → Spans K L →
        ∃ u : (ι → K) ≃ₗ[K] (ι → K), IsUnitary c u ∧ ∀ v, v ∈ L ↔ ∀ i, Rp K p (u v i) := by
  intro k
  induction k with
  | zero =>
    intro ι _ hk L hL _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hk
    refine ⟨LinearEquiv.refl K _, fun v w => rfl, fun v => ?_⟩
    have h0 := zero_mem_of hL
    constructor
    · intro _ i
      exact isEmptyElim i
    · intro _
      rwa [Subsingleton.elim v 0]
  | succ k ih =>
    intro ι _ hk L hL hS
    classical
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i0⟩ := ‹Nonempty ι›
    obtain ⟨e, heL, hee⟩ := hN K c p ι L hK hc hp hs hL hS
    obtain ⟨e1, he1L, he1, hne⟩ :
        ∃ e1 ∈ L, hf c e1 e1 = 1 ∧ hf c (Pi.single i0 1) e1 ≠ 1 := by
      by_cases h1 : hf c (Pi.single i0 1) e = 1
      · refine ⟨-e, neg_mem_of hL heL, by rw [hf_neg_left, hf_neg_right, neg_neg, hee], ?_⟩
        rw [hf_neg_right, h1]
        norm_num
      · exact ⟨e, heL, hee, h1⟩
    obtain ⟨σ, hσ, hσe⟩ :=
      exists_refl c hc (Pi.single i0 1) e1 (hf_single_single c i0) he1 hne
    obtain ⟨u'', hu'', hmem''⟩ := split_step c p i0 (σ ⁻¹' L) (unimod_preimage c p hσ hL)
      (spans_preimage hS) (by show σ _ ∈ L; rw [hσe]; exact he1L)
      (fun L' hL' hS' => ih _ (card_ne_sub i0 k hk) L' hL' hS')
    refine ⟨σ.symm.trans u'', unitary_trans (unitary_symm hσ) hu'', fun v => ?_⟩
    have h := hmem'' (σ.symm v)
    have hm : σ.symm v ∈ σ ⁻¹' L ↔ v ∈ L := by
      show σ (σ.symm v) ∈ L ↔ v ∈ L
      rw [LinearEquiv.apply_symm_apply]
    rw [hm] at h
    simpa only [LinearEquiv.trans_apply] using h

theorem lattice_from_norm_one_induction : LatticeFromNormOne := by
  intro hN K _ _ c p ι _ L hK hc hp hs hL hS
  exact latIso_card hN c p hK hc hp hs _ ι rfl L hL hS

end PI.KLW.Ind

namespace PI.KLW

theorem lattice_from_norm_one : LatticeFromNormOne := Ind.lattice_from_norm_one_induction

end PI.KLW
