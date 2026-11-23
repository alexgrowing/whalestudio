import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueSum

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.DelParam

theorem algHom_eq_subst {O : Type} [CommRing O] (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (hj : (X : O⟦X⟧) ∣ j X)
    (a : O⟦X⟧) : j a = a.subst (j X) := by
  have hs : HasSubst (j X) := HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 hj)
  have := algHom_ext_X j (substAlgHom hs) hj (by rw [coe_substAlgHom, subst_X hs])
  rw [← coe_substAlgHom hs, ← this]

theorem dvd_coeff_of_aeval {O : Type} [CommRing O] (a : O) (ξ w : O⟦X⟧) (s e : ℕ) (hs : 0 < s)
    (hw : IsUnit w) (hξ : ξ = w * X ^ s) (E : Polynomial O) (b c : O⟦X⟧)
    (h : Polynomial.aeval ξ E = X ^ (e * s) * b + C a * c) : ∀ k < e, a ∣ E.coeff k := by
  induction e generalizing E b c with
  | zero => intro k hk; omega
  | succ e ih =>
    have hE := Polynomial.X_mul_divX_add E
    have h0 : a ∣ E.coeff 0 := by
      have h1 := congrArg constantCoeff h
      rw [← hE] at h1
      simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hξ, map_pow,
        constantCoeff_X, zero_pow hs.ne', zero_pow (Nat.mul_pos e.succ_pos hs).ne', mul_zero,
        zero_mul, zero_add, constantCoeff_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply] at h1
      exact ⟨_, h1⟩
    obtain ⟨d, hd⟩ := h0
    obtain ⟨w', hw'⟩ := hw.exists_right_inv
    have h2 : X ^ s * (w * Polynomial.aeval ξ E.divX - X ^ (e * s) * b) = C a * (c - C d) := by
      rw [← hE, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hd] at h
      have hC : algebraMap O O⟦X⟧ (a * d) = C a * C d := by rw [← map_mul]; rfl
      rw [hC] at h
      nth_rewrite 1 [hξ] at h
      linear_combination h
    have h3 : ∃ c', w * Polynomial.aeval ξ E.divX - X ^ (e * s) * b = C a * c' := by
      refine ⟨PowerSeries.mk fun k => coeff (k + s) (c - C d), ?_⟩
      ext k
      rw [coeff_C_mul, coeff_mk, ← coeff_C_mul, ← h2, coeff_X_pow_mul]
    obtain ⟨c', hc'⟩ := h3
    have h4 := ih E.divX (w' * b) (w' * c') (by
      linear_combination w' * hc' - Polynomial.aeval ξ E.divX * hw')
    intro k hk
    cases k with
    | zero => exact ⟨d, hd⟩
    | succ k => rw [← Polynomial.coeff_divX]; exact h4 k (by omega)

theorem prod_one_root {O : Type} [CommRing O] (ϖ : Fin 1 → O) (a : O) (E : Polynomial O)
    (hE : E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))) (h : ϖ 0 = -a) :
    E = Polynomial.X + Polynomial.C a := by
  rw [hE, Fin.prod_univ_one, h, map_neg, sub_neg_eq_add]

theorem lvl_zero_mod {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] :
    ∃ r : O⟦X⟧, lvl l O 0 = X ^ (l - 1) + C (l : O) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (1 : O⟦X⟧) X
  have h1 := mul_lvl (l := l) (O := O) 0
  simp only [pow_zero, pow_one, zero_add, add_sub_cancel_left] at h1
  refine ⟨r, mul_left_cancel₀ (X_ne_zero (R := O)) ?_⟩
  have h2 : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : l.Prime).one_le]
  rw [h1, hr, map_natCast, h2]; ring

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O]
    (hp : PD.p = l)

def EisAt (l e : ℕ) (ξ : O⟦X⟧) (E : Polynomial O) : Prop :=
  E.Monic ∧ E.natDegree = e ∧ (∀ k < e, (l : O) ∣ E.coeff k) ∧
    Associated (E.coeff 0) (l : O) ∧ Associated (Polynomial.aeval ξ E) W.q₀ ∧
    (∃ c : O⟦X⟧, IsUnit c ∧ W.φ₀ ξ = c.subst ξ * ξ * Polynomial.aeval ξ E ^ W.DelF.card) ∧
    ∃ c : O⟦X⟧, IsUnit c ∧ W.γ₀ W.gam ξ - ξ = c.subst ξ * ξ * Polynomial.aeval ξ E

def HasEis (l e : ℕ) (ξ : O⟦X⟧) : Prop :=
  ∃ (E : Polynomial O) (ϖ : Fin e → O), E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ)) ∧
    (∀ τ, Associated (ϖ τ ^ e) (l : O)) ∧
    (∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ ξ - C (ϖ τ)) ∧
    Function.Injective ϖ ∧ EisAt W l e ξ E

include hp

theorem free_and_invariants_gen [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hu : ¬ IsUnit (l : O))
    (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O)) (ξ : O⟦X⟧)
    (hξ : Associated ξ (X ^ W.DelF.card)) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    (∀ b : O⟦X⟧, ∃! G : Fin W.DelF.card → O⟦X⟧,
      b = ∑ k : Fin W.DelF.card, X ^ (k : ℕ) * (G k).subst ξ) ∧
    ∀ b : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ b = b) ↔ ∃ g : O⟦X⟧, b = g.subst ξ := by
  classical
  have hγ : ∀ g, W.γ₀ g = GlobalTheory.Cyc.act l O (χ g : ℤ_[l]) := fun g => by
    rw [γ₀_eq W hp χ hχ g]
    refine algHom_ext_X _ _ (X_dvd_act_X _) ?_
    rw [act_X, GlobalTheory.Cyc.Series.act_X, GlobalTheory.Cyc.Series.cyc_eq]
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  have : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  let _ : Fintype Δ := Fintype.ofFinite _
  have hcard : Fintype.card Δ = W.DelF.card := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  obtain ⟨w, hw⟩ := hξ.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.Cyc.invariants_param l O
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hu Δ ξ w w.isUnit
    (by rw [hcard, ← hw, mul_comm])
    (fun d => (hfa fun d => GlobalTheory.Cyc.act l O (d : ℤ_[l]) ξ = ξ).2 (fun δ hδ => by
      rw [← hγ]; exact hinv δ hδ) d d.2)
  refine ⟨hcard ▸ h1, fun b => ?_⟩
  rw [← h2, Subtype.forall, hfa fun d => GlobalTheory.Cyc.act l O (d : ℤ_[l]) b = b]
  simp only [hγ]

theorem eisenstein_gen (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (ht : FrTie W R j)
    (E : Polynomial O) (hEd : E = ∏ τ, (Polynomial.X - Polynomial.C (R.ϖ τ))) :
    Function.Injective R.ϖ ∧ EisAt W l R.e (j X) E := by
  subst hEd
  obtain ⟨-, -, hφ, hγ, -, hs, hX, hE⟩ := ht
  have hes := R.es
  have h2l := (Fact.out : l.Prime).two_le
  have hs0 : 0 < R.s := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hes; omega
  have he0 : R.e ≠ 0 := fun h0 => by rw [h0] at hes; omega
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hj : (X : O⟦X⟧) ∣ j X := (dvd_pow_self X hs0.ne').trans hX.symm.dvd
  have hq := (φ₀_eq W hp).2
  rw [EisAt, ← hs]
  have hjE : Polynomial.aeval (j X) (∏ τ, (Polynomial.X - Polynomial.C (R.ϖ τ))) = j R.E := by
    rw [R.E_def, map_prod, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_sub, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algHom_C]
  refine ⟨fun τ τ' hτ => ?_,
    Polynomial.monic_prod_of_monic _ _ fun τ _ => Polynomial.monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hne
    have h1 := R.ϖ_sub τ τ' hne
    rw [hτ, sub_self, ← hτ] at h1
    have h2 := R.ϖ_val τ
    rw [(associated_zero_iff_eq_zero _).1 h1.symm, zero_pow he0] at h2
    exact hl0 ((associated_zero_iff_eq_zero _).1 h2.symm)
  · rw [Polynomial.natDegree_prod_of_monic _ _ fun τ _ => Polynomial.monic_X_sub_C _]
    simp
  · obtain ⟨w, hw⟩ := hX.symm
    obtain ⟨u, hu⟩ := hE.symm
    obtain ⟨r, hr⟩ := lvl_zero_mod (l := l) O
    refine dvd_coeff_of_aeval _ (j X) w R.s R.e hs0 w.isUnit (by rw [← hw, mul_comm]) _ u (r * u) ?_
    rw [hjE, ← hu, hq, hr, hes]; ring
  · obtain ⟨u, hu⟩ := hE.symm
    have h1 := congrArg constantCoeff hu
    rw [map_mul, hq, constantCoeff_lvl, constantCoeff_algHom j hj, R.E_def, map_prod] at h1
    rw [Polynomial.coeff_zero_prod]
    simp only [map_sub, constantCoeff_X, constantCoeff_C] at h1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero]
    rw [← h1]
    exact associated_mul_unit_left _ _ (u.isUnit.map _)
  · rw [hjE]; exact hE
  · refine ⟨R.u, R.u.isUnit, ?_⟩
    rw [← hφ, R.φ_X, map_mul, map_mul, map_pow, hjE, algHom_eq_subst j hj R.u]
  · refine ⟨R.κ, R.κ.isUnit, ?_⟩
    rw [← hγ, R.γ_X, map_mul, map_add, map_one, map_mul, hjE, algHom_eq_subst j hj R.κ]
    ring

omit hp [CharZero O] [Algebra ℤ_[l] O] in

theorem eisAt_one [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hu : ¬ IsUnit (l : O)) (ξ : O⟦X⟧) (hq : lvl l O 0 ∣ ξ + (l : O⟦X⟧)) (e₀ : ℕ) (he₀ : e₀ = 1)
    (hA : HasEis W l e₀ ξ) : EisAt W l 1 ξ (Polynomial.X + Polynomial.C (l : O)) := by
  obtain ⟨E, ϖ, hE, -, hr, -, hA⟩ := hA
  subst he₀
  obtain ⟨ζ, hζ, hd⟩ := hr 0
  rwa [prod_one_root ϖ _ E hE (eq_neg_of_root hu _ _ ζ hζ hd hq)] at hA

end Generic

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
  (h : Good K 1 LL) (hl : l ≠ 2)
include hl

theorem card_eq : (H.W K 1 LL h).DelF.card = (l - 1) / Module.finrank ↥(K0 K) ↥K.1 := by
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
  have h2l := (Fact.out : l.Prime).two_le
  have h0 : 0 < Module.finrank ↥(K0 K) ↥K.1 := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hc; omega
  rw [← hc, Nat.mul_div_cancel _ h0]

omit hl in

theorem free_and_invariants (ξ : (↥(OL LL))⟦X⟧)
    (hξ : Associated ξ (X ^ (H.W K 1 LL h).DelF.card))
    (hinv : ∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ ξ = ξ) :
    (∀ b : (↥(OL LL))⟦X⟧, ∃! G : Fin (H.W K 1 LL h).DelF.card → (↥(OL LL))⟦X⟧,
      b = ∑ k : Fin (H.W K 1 LL h).DelF.card, X ^ (k : ℕ) * (G k).subst ξ) ∧
    ∀ b : (↥(OL LL))⟦X⟧, (∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ b = b) ↔
      ∃ g : (↥(OL LL))⟦X⟧, b = g.subst ξ := by
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL (H.W K 1 LL h)
  exact free_and_invariants_gen (H.W K 1 LL h) (P.PD_p K) hu χ hχ ξ hξ hinv

theorem exists_eisenstein (ξ : (↥(OL LL))⟦X⟧)
    (hξ : Associated ξ (X ^ (H.W K 1 LL h).DelF.card))
    (hinv : ∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ ξ = ξ) :
    HasEis (H.W K 1 LL h) l (Module.finrank ↥(K0 K) ↥K.1) ξ := by
  obtain ⟨R, j, jE, hj, he, ht, -, hr, -⟩ := exists_attached H h hl ξ hξ hinv
  have h1 : HasEis (H.W K 1 LL h) l R.e (j X) :=
    ⟨_, R.ϖ, rfl, R.ϖ_val, hr, eisenstein_gen (H.W K 1 LL h) (P.PD_p K) R j ht _ rfl⟩
  rwa [hj, he] at h1

set_option maxHeartbeats 800000 in

theorem trace_param (h1 : Module.finrank ↥(K0 K) ↥K.1 = 1) :
    (H.W K 1 LL h).DelF.card = l - 1 ∧
    Associated (H.W K 1 LL h).π₀₁ (X ^ (H.W K 1 LL h).DelF.card) ∧
    (∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ (H.W K 1 LL h).π₀₁ = (H.W K 1 LL h).π₀₁) ∧
    EisAt (H.W K 1 LL h) l 1 (H.W K 1 LL h).π₀₁
      (Polynomial.X + Polynomial.C ((l : ℕ) : ↥(OL LL))) := by
  have hc := card_eq H h hl
  rw [h1, Nat.div_one] at hc
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL (H.W K 1 LL h)
  obtain ⟨p2, p3, p4⟩ := π₀₁_spec (H.W K 1 LL h) (P.PD_p K) χ hχ hl hc
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  exact ⟨hc, p2, p3, eisAt_one (H.W K 1 LL h) hu _ p4 _ h1 (exists_eisenstein H h hl _ p2 p3)⟩

end GlobalTheory.DelParam
