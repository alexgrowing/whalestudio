import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix MeasureTheory
open scoped Topology

namespace GlobalTheory.LocGL

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

theorem exists_continuous_addChar_ne_one : ∃ ψ : AddChar k Circle, Continuous ψ ∧ ψ ≠ 1 := by
  obtain ⟨ψ, hψ⟩ := exists_hasConductor_one k
  exact ⟨ψ, hψ.continuous, hψ.ne_one⟩

private theorem cball_subset_cball_of_valuation_le {s t : kˣ} (h : valuation k (t : k) ≤ valuation k (s : k)) :
    cball t ⊆ cball s := fun x (hx : valuation k x ≤ valuation k (t : k)) => le_trans hx h

private theorem exists_shift_of_conductor_of_trivial_on_cball {ψ ψ' : AddChar k Circle} {c t s : kˣ} (h : HasConductor ψ c)
    (ht : ∀ z ∈ cball t, ψ' z = 1) (hts : cball t ⊆ cball s) :
    ∃ y ∈ cball (c * t⁻¹), ∀ x ∈ cball s, ψ (x * y) = ψ' x := by
  let _ : MeasurableSpace k := borel k
  have _ : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν, hν1⟩ := exists_isUnitVol k
  have _ := hν
  have h0s : (0 : k) ∈ cball s := by simp [cball]
  set f : k → ℂ := (cball s).indicator fun x => (ψ' x : ℂ) with hf
  have hfinv : ∀ z ∈ cball t, ∀ x, f (x + z) = f x := by
    intro z hz x
    have hzs : z ∈ cball s := hts hz
    by_cases hx : x ∈ cball s
    · have hxz : x + z ∈ cball s := add_mem_cball hx hzs
      simp only [hf, Set.indicator_of_mem hx, Set.indicator_of_mem hxz, AddChar.map_add_eq_mul,
        ht z hz, mul_one]
    · have hxz : x + z ∉ cball s := fun hxz => hx (by simpa using add_mem_cball hxz (neg_mem_cball hzs))
      simp only [hf, Set.indicator_of_notMem hx, Set.indicator_of_notMem hxz]
  have hSB : f ∈ SB k := by
    refine ⟨?_, ?_⟩
    · rw [IsLocallyConstant.iff_exists_open]
      intro x
      refine ⟨(· - x) ⁻¹' cball t, (isOpen_cball t).preimage (continuous_id.sub continuous_const),
        ?_, fun x' hx' => ?_⟩
      · simp [cball]
      · have e := hfinv (x' - x) hx' x
        rwa [add_sub_cancel] at e
    · refine HasCompactSupport.intro (isCompact_cball s) fun x hx => ?_
      simp only [hf, Set.indicator_of_notMem hx]
  have hf0 : f 0 = 1 := by
    simp only [hf, Set.indicator_of_mem h0s, AddChar.map_zero_eq_one, Circle.coe_one]
  obtain ⟨y, hy⟩ : ∃ y, ∫ x, f x * (ψ (x * y) : ℂ) ∂ν ≠ 0 := by
    by_contra hne
    have hall : ∀ y, ∫ x, f x * (ψ (x * y) : ℂ) ∂ν = 0 := fun y => not_not.1 fun h => hne ⟨y, h⟩
    have hI : ∫ y, (∫ x, f x * (ψ (x * y) : ℂ) ∂ν) ∂ν = 0 := by simp [hall]
    rw [fourier_inversion ν h hSB, hf0, mul_one] at hI
    have hvol : ν.real (𝒪[k] : Set k) = 1 := by simp [Measure.real, hν1]
    have hpos : (0 : ℝ) < ν.real (𝒪[k] : Set k) ^ 2 * nabs k c := by
      rw [hvol, one_pow, one_mul]
      exact nabs_pos k c
    exact hpos.ne' (Complex.ofReal_eq_zero.1 hI)
  have hyc : y ∈ cball (c * t⁻¹) := by
    by_contra hyc
    exact hy (fourier_eq_zero ν h hfinv hyc)
  have key : ∀ x0 ∈ cball s, (ψ' x0 : ℂ) * (ψ (x0 * y) : ℂ) = 1 := by
    intro x0 hx0
    let g : k → ℂ := fun x => f x * (ψ (x * y) : ℂ)
    have hshift : ∀ x, g (x0 + x) = ((ψ' x0 : ℂ) * (ψ (x0 * y) : ℂ)) * g x := by
      intro x
      by_cases hx : x ∈ cball s
      · have hxx : x0 + x ∈ cball s := add_mem_cball hx0 hx
        simp only [g, hf, Set.indicator_of_mem hx, Set.indicator_of_mem hxx, add_mul,
          AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
      · have hxx : x0 + x ∉ cball s := fun hxx =>
          hx (by simpa using add_mem_cball (neg_mem_cball hx0) hxx)
        simp only [g, hf, Set.indicator_of_notMem hx, Set.indicator_of_notMem hxx, zero_mul, mul_zero]
    have hI : ∫ x, g x ∂ν = ((ψ' x0 : ℂ) * (ψ (x0 * y) : ℂ)) * ∫ x, g x ∂ν := by
      calc ∫ x, g x ∂ν = ∫ x, g (x0 + x) ∂ν := (integral_add_left_eq_self g x0).symm
        _ = ∫ x, ((ψ' x0 : ℂ) * (ψ (x0 * y) : ℂ)) * g x ∂ν := by simp_rw [hshift]
        _ = _ := integral_const_mul _ _
    exact mul_right_cancel₀ hy (hI.symm.trans (one_mul _).symm)
  refine ⟨-y, neg_mem_cball hyc, fun x hx => ?_⟩
  have e : ψ' x * ψ (x * y) = 1 := Circle.ext (by rw [Circle.coe_mul, Circle.coe_one]; exact key x hx)
  rw [mul_neg, AddChar.map_neg_eq_inv]
  exact (eq_inv_of_mul_eq_one_left e).symm

theorem exists_eq_mulShift {ψ ψ' : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1) (h' : Continuous ψ') :
    ∃ a : k, ψ' = ψ.mulShift a := by
  have _ : T2Space k := t2Space k
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  obtain ⟨t, ht⟩ := exists_cball_addChar_eq_one ψ' h'

  let Y : kˣ → Set k := fun s => cball (c * t⁻¹) ∩ {y | ∀ x ∈ cball s, ψ (x * y) = ψ' x}
  have hYc : ∀ s, IsClosed (Y s) := by
    intro s
    refine (isCompact_cball _).isClosed.inter ?_
    have e : {y | ∀ x ∈ cball s, ψ (x * y) = ψ' x} = ⋂ x ∈ cball s, {y | ψ (x * y) = ψ' x} := by
      ext y
      simp
    rw [e]
    exact isClosed_biInter fun x _ =>
      isClosed_eq (f := fun y => ψ (x * y)) (hψ.comp (continuous_const_mul x)) continuous_const
  have hYk : ∀ s, IsCompact (Y s) := fun s =>
    (isCompact_cball _).of_isClosed_subset (hYc s) Set.inter_subset_left
  have hYn : ∀ s, (Y s).Nonempty := by
    intro s
    rcases le_total (valuation k (t : k)) (valuation k (s : k)) with hle | hle
    · obtain ⟨y, hy, hy'⟩ := exists_shift_of_conductor_of_trivial_on_cball hc ht (cball_subset_cball_of_valuation_le hle)
      exact ⟨y, hy, hy'⟩
    · obtain ⟨y, hy, hy'⟩ := exists_shift_of_conductor_of_trivial_on_cball (s := t) hc ht subset_rfl
      exact ⟨y, hy, fun x hx => hy' x (cball_subset_cball_of_valuation_le hle hx)⟩
  have hYd : Directed (· ⊇ ·) Y := by
    intro s₁ s₂
    rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with hle | hle
    · exact ⟨s₂, fun y hy => ⟨hy.1, fun x hx => hy.2 x (cball_subset_cball_of_valuation_le hle hx)⟩, subset_rfl⟩
    · exact ⟨s₁, subset_rfl, fun y hy => ⟨hy.1, fun x hx => hy.2 x (cball_subset_cball_of_valuation_le hle hx)⟩⟩
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed Y hYd hYn hYk hYc
  rw [Set.mem_iInter] at hy
  refine ⟨y, ?_⟩
  ext x
  rw [AddChar.mulShift_apply, mul_comm]
  by_cases hx : x = 0
  · simp [hx]
  · have hxx : x ∈ cball (Units.mk0 x hx) := by simp [cball]
    rw [(hy (Units.mk0 x hx)).2 x hxx]

theorem exists_unit_eq_mulShift {ψ ψ' : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1) (h' : Continuous ψ')
    (h1' : ψ' ≠ 1) : ∃ a : kˣ, ψ' = ψ.mulShift (a : k) := by
  obtain ⟨a, ha⟩ := exists_eq_mulShift hψ h1 h'
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h1' (by rw [ha, AddChar.mulShift_zero])
  exact ⟨Units.mk0 a ha0, by rw [Units.val_mk0]; exact ha⟩

end Chars

section Generic

variable {k : Type} [Field k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

theorem nontrivial_twJacquet_of_surjective {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {U : Subgroup G} {θ θ' : U →* ℂˣ} (T : V →ₗ[ℂ] W) (hT : Function.Surjective T)
    (h : ∀ (u : U) v, T (ρ u v - (θ u : ℂ) • v) ∈ twKer σ U θ') (H : Nontrivial (TwJacquet σ U θ')) :
    Nontrivial (TwJacquet ρ U θ) := by
  have hle : twKer ρ U θ ≤ (twKer σ U θ').comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact h u v
  have hs : Function.Surjective ((twKer ρ U θ).mapQ (twKer σ U θ') T hle) := by
    intro q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨v, rfl⟩ := hT w
    exact ⟨Submodule.Quotient.mk v, Submodule.mapQ_apply _ _ _ _⟩
  exact hs.nontrivial

def powTorus (N : ℕ) (a : kˣ) : GL (Fin N) k :=
  ⟨diagonal fun i => (a : k) ^ (i : ℕ), diagonal fun i => ((a⁻¹ : kˣ) : k) ^ (i : ℕ),
    by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩

theorem powTorus_conj_apply (a : kˣ) (g : GL (Fin N) k) (i j : Fin N) :
    ((powTorus N a)⁻¹ * g * powTorus N a).val i j = ((a⁻¹ : kˣ) : k) ^ (i : ℕ) * g.val i j * (a : k) ^ (j : ℕ) := by
  simp [powTorus, Matrix.diagonal_mul, Matrix.mul_diagonal]

private theorem sub_smul_mem_twKer' {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (U : Subgroup G) (θ : U →* ℂˣ) (g : G) (hg : g ∈ U) (v : X) :
    ρ g v - (θ ⟨g, hg⟩ : ℂ) • v ∈ twKer ρ U θ :=
  Submodule.subset_span ⟨⟨g, hg⟩, v, rfl⟩

theorem IsGenericFor.mulShift {ψ : AddChar k Circle} {π : Representation ℂ (GL (Fin N) k) V} (h : IsGenericFor ψ π)
    (a : kˣ) : IsGenericFor (ψ.mulShift (a : k)) π := by
  unfold IsGenericFor at h ⊢
  set t := powTorus N a with ht
  have hmem : ∀ u : unipB k (Fin N), t⁻¹ * (u : GL (Fin N) k) * t ∈ unipB k (Fin N) := by
    intro u
    obtain ⟨hl, hd⟩ := (mem_unipB (R := k)).1 u.2
    refine (mem_unipB (R := k)).2 ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [ht, powTorus_conj_apply, hl i j hji, mul_zero, zero_mul]
    · rw [ht, powTorus_conj_apply, hd i, mul_one, ← mul_pow, Units.inv_mul, one_pow]
  have hchar : ∀ u : unipB k (Fin N),
      whitChar ψ N ⟨_, hmem u⟩ = whitChar (ψ.mulShift (a : k)) N u := by
    intro u
    simp only [whitChar, MonoidHom.coe_mk, OneHom.coe_mk, AddChar.mulShift_apply]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hp).2
    have e : ((a⁻¹ : kˣ) : k) ^ (p.1 : ℕ) * (a : k) ^ (p.1 : ℕ) = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    show ((t⁻¹ * (u : GL (Fin N) k) * t : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = _
    rw [ht, powTorus_conj_apply, hp2, pow_succ]
    linear_combination ((a : k) * (u : GL (Fin N) k).val p.1 p.2) * e
  refine nontrivial_twJacquet_of_surjective (π t⁻¹) (fun v => ⟨π t v, ?_⟩) (fun u v => ?_) h
  · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · have e : π t⁻¹ (π (u : GL (Fin N) k) v) = π (t⁻¹ * u * t) (π t⁻¹ v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc _ t,
        mul_inv_cancel, mul_one]
    rw [map_sub, LinearMap.map_smul, e, ← hchar u]
    exact sub_smul_mem_twKer' π _ _ _ (hmem u) _

theorem isGenericFor_mulShift_iff {ψ : AddChar k Circle} {π : Representation ℂ (GL (Fin N) k) V} (a : kˣ) :
    IsGenericFor (ψ.mulShift (a : k)) π ↔ IsGenericFor ψ π := by
  refine ⟨fun h => ?_, fun h => h.mulShift a⟩
  have h' := h.mulShift a⁻¹
  rwa [AddChar.mulShift_mulShift, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    AddChar.mulShift_one] at h'

theorem IsGenericFor.of_equiv {ψ : AddChar k Circle} {π : Representation ℂ (GL (Fin N) k) V}
    {σ : Representation ℂ (GL (Fin N) k) W} (h : IsGenericFor ψ π) (φ : π.Equiv σ) : IsGenericFor ψ σ := by
  unfold IsGenericFor at h ⊢
  refine nontrivial_twJacquet_of_surjective (ρ := σ) (σ := π) φ.symm.toLinearEquiv.toLinearMap
    φ.symm.toLinearEquiv.surjective (fun u w => ?_) h
  have e : φ.symm.toLinearEquiv.toLinearMap (σ (u : GL (Fin N) k) w) =
      π u (φ.symm.toLinearEquiv.toLinearMap w) :=
    Representation.IntertwiningMap.isIntertwining σ π φ.symm.toIntertwiningMap (u : GL (Fin N) k) w
  rw [map_sub, LinearMap.map_smul, e]
  exact sub_smul_mem_twKer' π _ _ _ u.2 _

theorem isGenericFor_congr {ψ : AddChar k Circle} {π : Representation ℂ (GL (Fin N) k) V}
    {σ : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv σ) : IsGenericFor ψ π ↔ IsGenericFor ψ σ := by
  exact ⟨fun h => h.of_equiv φ, fun h => h.of_equiv φ.symm⟩

theorem isGenericFor_twist_iff {ψ : AddChar k Circle} {π : Representation ℂ (GL (Fin N) k) V} (χ : kˣ →* ℂˣ) :
    IsGenericFor ψ (twist π (detChar (Fin N) χ)) ↔ IsGenericFor ψ π := by
  have hdet : ∀ u : unipB k (Fin N), ((detChar (Fin N) χ (u : GL (Fin N) k) : ℂˣ) : ℂ) = 1 := by
    intro u
    rw [detChar_apply, det_eq_one_of_mem_unipRad k u.2, map_one, Units.val_one]
  unfold IsGenericFor
  constructor
  · intro h
    refine nontrivial_twJacquet_of_surjective (ρ := π) LinearMap.id Function.surjective_id
      (fun u v => ?_) h
    have e : π u v = twist π (detChar (Fin N) χ) u v := by rw [twist_apply, hdet u, one_smul]
    rw [LinearMap.id_apply, e]
    exact sub_smul_mem_twKer' _ _ _ _ u.2 _
  · intro h
    refine nontrivial_twJacquet_of_surjective (σ := π) LinearMap.id Function.surjective_id
      (fun u v => ?_) h
    have e : twist π (detChar (Fin N) χ) u v = π u v := by rw [twist_apply, hdet u, one_smul]
    rw [LinearMap.id_apply, e]
    exact sub_smul_mem_twKer' _ _ _ _ u.2 _

theorem not_isGenericFor_detRep {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (hN : 2 ≤ N) (χ : kˣ →* ℂˣ) :
    ¬ IsGenericFor ψ (detRep (Fin N) χ) := by
  obtain ⟨z, hz⟩ := AddChar.ne_one_iff.1 hψ
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  have hlt : i0 < i1 := by simp [i0, i1, Fin.lt_def]
  have hne : i0 ≠ i1 := ne_of_lt hlt

  let g : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i0 i1 z)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have hg : ∀ i j, (g : Matrix (Fin N) (Fin N) k) i j =
      (if i = j then 1 else 0) + (if i0 = i ∧ i1 = j then z else 0) := by
    intro i j
    simp [g, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  have hgU : g ∈ unipB k (Fin N) := by
    refine (mem_unipB (R := k)).2 ⟨fun i j hji => ?_, fun i => ?_⟩
    · have h1 : i ≠ j := ne_of_gt hji
      have h2 : ¬ (i0 = i ∧ i1 = j) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hlt hji
      rw [hg, if_neg h1, if_neg h2, add_zero]
    · have h2 : ¬ (i0 = i ∧ i1 = i) := by
        rintro ⟨rfl, h⟩
        exact hne h.symm
      rw [hg, if_pos rfl, if_neg h2, add_zero]
  have hsum : ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, (g : Matrix (Fin N) (Fin N) k) p.1 p.2 = z := by
    rw [Finset.sum_eq_single (i0, i1)]
    · rw [hg, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
    · intro p hp hpne
      have hp2 : (p.2 : ℕ) = p.1 + 1 := (Finset.mem_filter.1 hp).2
      have h1 : p.1 ≠ p.2 := by
        intro h
        rw [h] at hp2
        omega
      have h2 : ¬ (i0 = p.1 ∧ i1 = p.2) := fun h => hpne (Prod.ext h.1.symm h.2.symm)
      rw [hg, if_neg h1, if_neg h2, add_zero]
    · intro h
      exact (h (by simp [i0, i1])).elim
  have hθ : ((whitChar ψ N ⟨g, hgU⟩ : ℂˣ) : ℂ) = (ψ z : ℂ) := by
    show ((Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1,
      (g : Matrix (Fin N) (Fin N) k) p.1 p.2)) : ℂˣ) : ℂ) = _
    rw [hsum, Circle.toUnits_apply, Units.val_mk0]
  have hd : detRep (Fin N) χ g 1 = 1 := by
    rw [detRep, ofChar_apply, detChar_apply, det_eq_one_of_mem_unipRad k hgU, map_one, Units.val_one,
      mul_one]
  have hw : (1 - (ψ z : ℂ)) ∈ twKer (detRep (Fin N) χ) (unipB k (Fin N)) (whitChar ψ N) := by
    have h := sub_smul_mem_twKer' (detRep (Fin N) χ) (unipB k (Fin N)) (whitChar ψ N) g hgU 1
    rwa [hd, hθ, smul_eq_mul, mul_one] at h
  have hne1 : (1 - (ψ z : ℂ)) ≠ 0 := by
    intro h0
    exact hz (Circle.ext ((sub_eq_zero.1 h0).symm.trans Circle.coe_one.symm))
  have htop : ∀ x : ℂ, x ∈ twKer (detRep (Fin N) χ) (unipB k (Fin N)) (whitChar ψ N) := by
    intro x
    have h := Submodule.smul_mem _ (x / (1 - (ψ z : ℂ))) hw
    rwa [smul_eq_mul, div_mul_cancel₀ _ hne1] at h
  intro H
  unfold IsGenericFor at H
  obtain ⟨p, q, hpq⟩ := H.exists_pair_ne
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact hpq (by rw [(Submodule.Quotient.mk_eq_zero _).2 (htop x), (Submodule.Quotient.mk_eq_zero _).2 (htop y)])

variable [TopologicalSpace k]

theorem isGeneric_congr {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (φ : π.Equiv σ) : IsGeneric π ↔ IsGeneric σ := by
  unfold IsGeneric
  exact exists_congr fun ψ => and_congr_right fun _ => and_congr_right fun _ => isGenericFor_congr φ

theorem isGeneric_twist_iff {π : Representation ℂ (GL (Fin N) k) V} (χ : kˣ →* ℂˣ) :
    IsGeneric (twist π (detChar (Fin N) χ)) ↔ IsGeneric π := by
  unfold IsGeneric
  exact exists_congr fun ψ => and_congr_right fun _ => and_congr_right fun _ => isGenericFor_twist_iff χ

theorem not_isGeneric_detRep (hN : 2 ≤ N) (χ : kˣ →* ℂˣ) : ¬ IsGeneric (detRep (Fin N) χ) := by
  unfold IsGeneric
  rintro ⟨ψ, -, h1, h⟩
  exact not_isGenericFor_detRep h1 hN χ h

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

theorem isGenericFor_iff_of_continuous {ψ ψ' : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1) (h' : Continuous ψ')
    (h1' : ψ' ≠ 1) (π : Representation ℂ (GL (Fin N) k) V) : IsGenericFor ψ π ↔ IsGenericFor ψ' π := by
  obtain ⟨a, rfl⟩ := exists_unit_eq_mulShift hψ h1 h' h1'
  exact (isGenericFor_mulShift_iff a).symm

theorem isGeneric_iff_isGenericFor {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) : IsGeneric π ↔ IsGenericFor ψ π := by
  unfold IsGeneric
  constructor
  · rintro ⟨ψ', h', h1', hg⟩
    exact (isGenericFor_iff_of_continuous hψ h1 h' h1' π).2 hg
  · intro h
    exact ⟨ψ, hψ, h1, h⟩

theorem isGeneric_detRep_one (χ : kˣ →* ℂˣ) : IsGeneric (detRep (Fin 1) χ) := by
  obtain ⟨ψ, hψ, h1⟩ := exists_continuous_addChar_ne_one k
  exact ⟨ψ, hψ, h1, isGenericFor_one ψ χ⟩

end Generic

end GlobalTheory.LocGL
