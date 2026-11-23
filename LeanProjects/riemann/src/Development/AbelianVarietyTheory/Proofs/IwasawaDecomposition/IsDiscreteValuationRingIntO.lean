import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier

open IsLocalRing Cardinal
open Formalism.MainNotions.DIV.Cons (SCF intO BigT)

namespace GlobalTheory.LocM.Cht.CompletedClosure

theorem isDiscreteValuationRing_intO {K : Type} [NormedField K] [IsUltrametricDist K] (π : K) (h0 : π ≠ 0)
    (h1 : ‖π‖ < 1) (h : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n) : IsDiscreteValuationRing ↥(intO K) := by
  have hpos : 0 < ‖π‖ := norm_pos_iff.2 h0
  have hunit : ∀ x : ↥(intO K), IsUnit x ↔ ‖(x : K)‖ = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hx.exists_right_inv
      have e : ‖(x : K)‖ * ‖(y : K)‖ = 1 := by
        rw [← norm_mul, ← Subring.coe_mul, hy, Subring.coe_one, norm_one]
      have hx1 : ‖(x : K)‖ ≤ 1 := x.2
      have hy1 : ‖(y : K)‖ ≤ 1 := y.2
      nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]
    · intro hx
      have hx0 : (x : K) ≠ 0 := fun h' => by simp [h'] at hx
      refine IsUnit.of_mul_eq_one (⟨(x : K)⁻¹, show ‖(x : K)⁻¹‖ ≤ 1 by simp [hx]⟩ : ↥(intO K)) (Subtype.ext ?_)
      exact mul_inv_cancel₀ hx0
  have hnat : ∀ x : ↥(intO K), x ≠ 0 → ∃ n : ℕ, ‖(x : K)‖ = ‖π‖ ^ n := by
    intro x hx
    obtain ⟨n, hn⟩ := h x (fun h' => hx (Subtype.ext h'))
    have hx1 : ‖(x : K)‖ ≤ 1 := x.2
    have hn0 : 0 ≤ n := by
      rw [hn] at hx1
      exact (zpow_le_one_iff_right_of_lt_one₀ hpos h1).1 hx1
    lift n to ℕ using hn0
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  let ϖ : ↥(intO K) := ⟨π, h1.le⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, ⟨?_, ?_⟩, ?_⟩
  · rw [hunit]; exact h1.ne
  · intro a b hab
    have e : π = (a : K) * b := congrArg Subtype.val hab
    have ha : a ≠ 0 := fun h' => h0 (by rw [e, h']; simp)
    have hb : b ≠ 0 := fun h' => h0 (by rw [e, h']; simp)
    obtain ⟨m, hm⟩ := hnat a ha
    obtain ⟨n, hn⟩ := hnat b hb
    have e2 : ‖π‖ ^ 1 = ‖π‖ ^ (m + n) := by
      rw [pow_add, ← hm, ← hn, ← norm_mul, ← e, pow_one]
    have e3 : 1 = m + n := (pow_right_strictAnti₀ hpos h1).injective e2
    rw [hunit, hunit, hm, hn]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · left; simp
    · right
      have : n = 0 := by omega
      simp [this]
  · intro x hx
    obtain ⟨n, hn⟩ := hnat x hx
    have hnorm : ‖(x : K) / π ^ n‖ = 1 := by
      rw [norm_div, norm_pow, hn, div_self (pow_pos hpos n).ne']
    let u : ↥(intO K) := ⟨(x : K) / π ^ n, hnorm.le⟩
    have hu : IsUnit u := (hunit u).2 hnorm
    refine ⟨n, hu.unit, Subtype.ext ?_⟩
    change π ^ n * ((x : K) / π ^ n) = x
    exact mul_div_cancel₀ _ (pow_ne_zero n h0)

theorem exists_scf_equiv {p : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] [CharZero C] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) (hC : #C ≤ 𝔠) :
    ∃ (D : SCF p) (e : C →+* ↥D.S), (∀ x, ‖e x‖ = ‖x‖) ∧ Function.Surjective e := by
  have hle : #C ≤ #BigT := by
    refine hC.trans ?_
    rw [mk_set, mk_set, mk_real]
    exact (cantor _).le.trans (cantor _).le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hle
  let S : Set BigT := Set.range j
  let e : S ≃ C := (Equiv.ofInjective j j.injective).symm
  letI : Field S := e.field
  let r : S ≃+* C := e.ringEquiv
  letI : NormedField S := NormedField.induced S C r r.injective
  have hn : ∀ x : S, ‖x‖ = ‖r x‖ := fun _ => rfl
  have hn' : ∀ x : C, ‖r.symm x‖ = ‖x‖ := fun x => by rw [hn, r.apply_symm_apply]
  letI : NontriviallyNormedField S :=
    { (inferInstance : NormedField S) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
        exact ⟨r.symm x, (hn' x).symm ▸ hx⟩ }
  haveI : IsUltrametricDist S :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hn, hn, hn, map_add]; exact IsUltrametricDist.norm_add_le_max _ _
  haveI : IsAlgClosed S := IsAlgClosed.of_ringEquiv C S r.symm
  have hiso : Isometry r := AddMonoidHomClass.isometry_of_norm r fun x => (hn x).symm
  haveI : CompleteSpace S :=
    (hiso.isUniformInducing.completeSpace_congr r.surjective).2 inferInstance
  haveI : CharZero S := charZero_of_injective_ringHom (f := r.symm.toRingHom) r.symm.injective
  exact ⟨{ S := S, norm_p := by rw [hn, map_natCast, hp] }, r.symm.toRingHom, hn', r.symm.surjective⟩

theorem exists_scf_dense {p : ℕ} {F C : Type} [Field F] [CharZero F] [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra F C] (hF : #F ≤ 𝔠)
    (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) {x : F} (hx : 1 < ‖algebraMap F C x‖) :
    ∃ (D : SCF p) (i : F →+* ↥D.S), (∀ y, ‖i y‖ = ‖algebraMap F C y‖) ∧
      Dense {z : ↥D.S | ∃ q : Polynomial F, q ≠ 0 ∧ q.eval₂ i z = 0} := by
  let A := algebraicClosure F C
  let L : Subfield C := A.toSubfield.topologicalClosure
  have hAL : A.toSubfield ≤ L := A.toSubfield.le_topologicalClosure
  have hKL : ∀ y : F, algebraMap F C y ∈ L := fun y => hAL (A.algebraMap_mem y)
  have hcl : IsClosed (L : Set C) := A.toSubfield.isClosed_topologicalClosure
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL x⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  letI : Algebra A L := (Subfield.inclusion hAL : A.toSubfield →+* L).toAlgebra
  have hd : DenseRange (algebraMap A L) :=
    (denseRange_inclusion_iff (s := (A.toSubfield : Set C)) (t := (L : Set C)) hAL).2 subset_rfl
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosed L := isAlgClosed_of_denseRange hd
  have hL : #L ≤ 𝔠 := by
    refine (GlobalTheory.SmallClosedField.mk_le_of_denseRange _ hd).trans ?_
    have hA : #A ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max F A).trans (max_le hF aleph0_le_continuum)
    exact (power_le_power_right hA).trans continuum_power_aleph0.le
  let i : F →+* L := (algebraMap F C).codRestrict L hKL
  have hi : ∀ y, ‖i y‖ = ‖algebraMap F C y‖ := fun _ => rfl
  haveI : CharZero L := charZero_of_injective_ringHom i.injective
  have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast i, hi, map_natCast, hp]
  obtain ⟨D, e, he, hs⟩ := exists_scf_equiv hLp hL
  refine ⟨D, e.comp i, fun y => by rw [RingHom.comp_apply, he, hi], ?_⟩
  have hc : Continuous e := (AddMonoidHomClass.isometry_of_norm e he).continuous
  refine Dense.mono ?_ (hs.denseRange.comp hd hc)
  rintro _ ⟨a, rfl⟩
  obtain ⟨q, hq, hqa⟩ : IsAlgebraic F (a : C) := mem_algebraicClosure_iff.1 a.2
  refine ⟨q, hq, ?_⟩
  have h2 : q.eval₂ i (algebraMap A L a) = 0 := by
    apply L.subtype.injective
    rw [Polynomial.hom_eval₂, map_zero]
    exact hqa
  rw [Function.comp_apply, ← Polynomial.hom_eval₂, h2, map_zero]

theorem fieldSt : GlobalTheory.LocM.Cht.FieldSt := by
  intro p R _ _ _ _ _ hp hpm
  let F := FractionRing R
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing R F hp0 hpm
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  have hF : #F ≤ 𝔠 :=
    (IsLocalization.cardinalMk_le (nonZeroDivisors R)).trans (mk_le_aleph0.trans aleph0_le_continuum)
  have hx : 1 < ‖algebraMap F C (algebraMap R F p)⁻¹‖ := by
    rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
  haveI : CharZero F := charZero_of_injective_ringHom (IsFractionRing.injective R F)
  obtain ⟨D, i, hi, hd⟩ := exists_scf_dense hF (by rw [← hCp, map_natCast, map_natCast]) hx
  let g : R →+* ↥D.S := i.comp (algebraMap R F)
  have hginj : Function.Injective g := i.injective.comp (IsFractionRing.injective R F)
  have hle : ∀ a : R, ‖g a‖ ≤ 1 := fun a => by
    rw [RingHom.comp_apply, hi]; exact (hC _).2 ⟨a, rfl⟩
  have hlt : ∀ a ∈ maximalIdeal R, ‖g a‖ < 1 := fun a ha => by
    refine GlobalTheory.SmallClosedField.norm_lt_one_of_mem_maximalIdeal g hle hp0 ?_ ha
    rw [map_natCast, D.norm_p]
    exact inv_lt_one_of_one_lt₀ h1
  have hone : ∀ a b : R, a * b = 1 → ‖g a‖ = 1 := fun a b hab => by
    have e : ‖g a‖ * ‖g b‖ = 1 := by rw [← norm_mul, ← map_mul, hab, map_one, norm_one]
    nlinarith [norm_nonneg (g a), norm_nonneg (g b), hle a, hle b]
  let f : R →+* ↥(intO ↥D.S) := g.codRestrict (intO ↥D.S) hle
  let K₀ : Subfield ↥D.S := Subfield.closure (Set.range fun a => ((f a : ↥(intO ↥D.S)) : ↥D.S))
  have hK₀ : K₀ = i.fieldRange := by
    refine le_antisymm (Subfield.closure_le.2 ?_) ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap R F a, rfl⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) y
      rw [map_div₀]
      exact div_mem (Subfield.subset_closure ⟨a, rfl⟩) (Subfield.subset_closure ⟨b, rfl⟩)
  have hmem : ∀ y : F, i y ∈ K₀.topologicalClosure := fun y =>
    K₀.le_topologicalClosure (hK₀ ▸ ⟨y, rfl⟩)
  refine ⟨D, f, K₀.topologicalClosure, fun a b h => hginj (congrArg Subtype.val h), ⟨fun a ha => ?_⟩, rfl, ?_, ?_⟩
  · by_contra hna
    obtain ⟨y, hy⟩ := ha.exists_right_inv
    have e : ‖g a‖ * ‖(y : ↥D.S)‖ = 1 := by
      rw [← norm_mul, ← norm_one (α := ↥D.S)]
      exact congrArg (fun t : ↥(intO ↥D.S) => ‖(t : ↥D.S)‖) hy
    have hy1 : ‖(y : ↥D.S)‖ ≤ 1 := y.2
    nlinarith [norm_nonneg (g a), norm_nonneg (y : ↥D.S), hlt a hna]
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hπ0 : g π ≠ 0 := (map_ne_zero_iff g hginj).2 hπ.ne_zero
    have hR : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ‖g a‖ = ‖g π‖ ^ n := fun a ha => by
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
      exact ⟨n, by rw [map_mul, norm_mul, hone _ _ u.mul_inv, one_mul, map_pow, norm_pow]⟩
    refine isDiscreteValuationRing_intO (K := ↥K₀.topologicalClosure) ⟨g π, hmem _⟩
      (fun h => hπ0 (congrArg Subtype.val h)) (hlt π hπ.not_isUnit) fun x hx0 => ?_
    have hx1 : (x : ↥D.S) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxc : (x : ↥D.S) ∈ closure (K₀ : Set ↥D.S) := x.2
    obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hxc ‖(x : ↥D.S)‖ (norm_pos_iff.2 hx1)
    rw [dist_eq_norm] at hxz
    have hzn : ‖z‖ = ‖(x : ↥D.S)‖ := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (x : ↥D.S)) (y := -((x : ↥D.S) - z))
        (by rw [norm_neg]; exact hxz.ne')
      rw [norm_neg, max_eq_left hxz.le] at this
      rw [← this]; congr 1; ring
    rw [hK₀] at hz
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) y
    have ha : a ≠ 0 := by
      rintro rfl
      exact hx1 (norm_eq_zero.1 (by rw [← hzn]; simp))
    obtain ⟨m, hm⟩ := hR a ha
    obtain ⟨n, hn⟩ := hR b (nonZeroDivisors.ne_zero hb)
    refine ⟨(m : ℤ) - n, ?_⟩
    change ‖(x : ↥D.S)‖ = ‖g π‖ ^ ((m : ℤ) - n)
    rw [zpow_sub₀ (norm_ne_zero_iff.2 hπ0), zpow_natCast, zpow_natCast, ← hm, ← hn, ← hzn, map_div₀, norm_div]
    rfl
  · refine hd.mono ?_
    rintro z ⟨q, hq, hqz⟩
    let j : F →+* ↥K₀.topologicalClosure := i.codRestrict _ hmem
    refine ⟨q.map j, (Polynomial.map_ne_zero_iff j.injective).2 hq, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact hqz

end GlobalTheory.LocM.Cht.CompletedClosure
