import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameBound
open NumberField IsDedekindDomain
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec

noncomputable section

namespace ModelDimension.Read

section Point

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_ratio (y : (Σ k, ι k) → Ω) (cc : ∀ k, ι k) (f : MRing ι) :
    MvPolynomial.aeval (fun q : Σ k, ι k => y q / y ⟨q.1, cc q.1⟩) f =
      MvPolynomial.eval (fun k => (y ⟨k, cc k⟩)⁻¹) (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, hf]
    simp [mConeMap, div_eq_mul_inv]

theorem aeval_ratio_form (y : (Σ k, ι k) → Ω) (cc : ∀ k, ι k) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    MvPolynomial.aeval (fun q : Σ k, ι k => y q / y ⟨q.1, cc q.1⟩) f =
      (∏ k, (y ⟨k, cc k⟩)⁻¹ ^ d k) * MvPolynomial.aeval y f := by
  rw [aeval_ratio, GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form y hf]
  rw [map_mul, MvPolynomial.eval_C, map_prod]
  simp only [map_pow, MvPolynomial.eval_X]

theorem point [CharZero Ω] (y : (Σ k, ι k) → Ω) (hb : Birational y) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (B : Finset Ω) :
    ∃ B₂ : Finset Ω, ∀ (A : Subring Ω), (↑B₂ : Set Ω) ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) →
      ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (ev : A →+* 𝕜), ∃ z ∈ Small.ptsOver 𝕜 (mCoordIdeal y),
        (∀ q, ∃ a : A, z q = ev a) ∧ ∃ (A₂ : Subring Ω) (hle : A₂ ≤ A), (↑B : Set Ω) ⊆ A₂ ∧
          (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A₂) ∧ ∀ x : A₂, Small.HasVal y 0 (x : Ω) z (ev ⟨x, hle x.2⟩) := by
  classical
  choose cc hcc using hy
  choose d g h hg hh hy0 he using hb
  let ρ : (Σ k, ι k) → Ω := fun q => y q / y ⟨q.1, cc q.1⟩
  refine ⟨B ∪ Finset.univ.image ρ ∪ B.image fun b => (MvPolynomial.aeval ρ (h b))⁻¹, fun A hA hn 𝕜 _ _ ev => ?_⟩
  have hρ : ∀ q, ρ q ∈ A := fun q => hA (by simp)
  have hBA : ∀ b ∈ B, b ∈ A := fun b hb => hA (by simp [hb])
  have hiA : ∀ b ∈ B, (MvPolynomial.aeval ρ (h b))⁻¹ ∈ A := fun b hb =>
    hA (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)))
  let ρA : (Σ k, ι k) → A := fun q => ⟨ρ q, hρ q⟩
  let z : (Σ k, ι k) → 𝕜 := fun q => ev (ρA q)
  have h1 : ∀ f : MRing ι, ((MvPolynomial.aeval ρA f : A) : Ω) = MvPolynomial.aeval ρ f := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, Subring.coe_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, Subring.coe_mul, hf, MvPolynomial.aeval_X]; rfl
  have h2 : ∀ f : MRing ι, MvPolynomial.aeval z f = ev (MvPolynomial.aeval ρA f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, hf, MvPolynomial.aeval_X]; rfl
  have hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) := by
    refine ⟨fun k => ⟨cc k, ?_⟩, fun f hf => ?_⟩
    · have : ρA ⟨k, cc k⟩ = 1 := Subtype.ext (div_self (hcc k))
      show ev _ ≠ 0
      rw [this, map_one]; exact one_ne_zero
    · have h0 : mConeMap y f = 0 := hf
      have : MvPolynomial.aeval ρA f = 0 := Subtype.ext (by rw [h1, aeval_ratio, h0, map_zero]; rfl)
      rw [h2, this, map_zero]
  have hval : ∀ x ∈ A ⊓ FinRd.ValSub.valRing y z, ∀ hx : x ∈ A, Small.HasVal y 0 x z (ev ⟨x, hx⟩) := by
    rintro x ⟨-, w, dg, dh, g', h', hg', hh', hd, e, hz0, -⟩ hx
    obtain rfl : dg = dh := funext fun k => by simpa using hd k
    refine ⟨dg, dg, g', h', hg', hh', hd, e, hz0, ?_⟩
    have : MvPolynomial.aeval ρA g' = ⟨x, hx⟩ * MvPolynomial.aeval ρA h' := Subtype.ext (by
      rw [Subring.coe_mul, h1, h1, aeval_ratio_form y cc hg', aeval_ratio_form y cc hh', e]; ring)
    rw [h2, h2, this, map_mul]
  refine ⟨z, hz, fun q => ⟨_, rfl⟩, A ⊓ FinRd.ValSub.valRing y z, inf_le_left, fun b hb => ⟨hBA b hb, ?_⟩,
    fun n hn0 => ⟨hn n hn0, _, FinRd.ValSub.hv_natInv hn0⟩, fun x => hval x x.2 _⟩
  have hne : MvPolynomial.aeval ρ (h b) ≠ 0 := by
    rw [aeval_ratio_form y cc (hh b)]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hcc k))) (hy0 b)
  have hu : MvPolynomial.aeval ρA (h b) * ⟨_, hiA b hb⟩ = 1 := Subtype.ext (by
    rw [Subring.coe_mul, h1]; exact mul_inv_cancel₀ hne)
  have hz0 : MvPolynomial.aeval z (h b) ≠ 0 := by
    rw [h2]
    intro h0
    have := congrArg ev hu
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  exact ⟨_, FinRd.ValSub.hv_quot (hg b) (hh b) (he b) hz0⟩

end Point

section Ext

variable {p : ℕ} [hp : Fact p.Prime]

theorem vV_nonneg (T : CDVR) (a : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
  by_cases h : algebraMap T.V T.Fr a = 0
  · simp [h, vV]
  have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one a
  have := (WithZero.log_le_log (valV_ne_zero h) one_ne_zero).2 h1
  rw [WithZero.log_one] at this
  simp only [vV]; omega

theorem range_le (T : CDVR) (hT : T.FinRes) (ι : T.Fr →+* PadicAlgCl p) (N : ℝ) (hN : 0 < N)
    (hι : ∀ x, x ≠ 0 → ‖ι x‖ = (p : ℝ) ^ (-((vV T.V x : ℝ) / N))) :
    ∃ S : Set (PadicAlgCl p), S.Finite ∧ ∀ L : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] L →
      S ⊆ L → ∀ x, ι x ∈ L := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  choose rep hrep using IsLocalRing.residue_surjective (R := T.V)
  haveI : Finite (IsLocalRing.ResidueField T.V) := hT
  let f : T.V →+* PadicAlgCl p := ι.comp (algebraMap T.V T.Fr)
  have hle : ∀ a, ‖f a‖ ≤ 1 := fun a => by
    by_cases h : algebraMap T.V T.Fr a = 0
    · show ‖ι _‖ ≤ 1
      rw [h, map_zero, norm_zero]; exact zero_le_one
    show ‖ι _‖ ≤ 1
    rw [hι _ h]
    refine Real.rpow_le_one_of_one_le_of_nonpos hp1.le (neg_nonpos.2 (div_nonneg ?_ hN.le))
    exact_mod_cast vV_nonneg T a
  have hlt : ‖f ϖ‖ < 1 := by
    have h : algebraMap T.V T.Fr ϖ ≠ 0 := by simpa using hϖ.ne_zero
    show ‖ι _‖ < 1
    rw [hι _ h]
    refine Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos (div_pos ?_ hN))
    have h1 : valV T.V (algebraMap T.V T.Fr ϖ) < 1 :=
      ((IsDiscreteValuationRing.maximalIdeal T.V).valuation_lt_one_iff_mem ϖ).2 hϖ.not_isUnit
    have := (WithZero.log_lt_log (valV_ne_zero h) one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    have h2 : 0 < vV T.V (algebraMap T.V T.Fr ϖ) := by simp only [vV]; omega
    exact_mod_cast h2
  refine ⟨insert (f ϖ) (Set.range fun k => f (rep k)), (Set.finite_range _).insert _, fun L hL hS => ?_⟩
  have hϖL : f ϖ ∈ L := hS (Set.mem_insert _ _)
  have hrL : ∀ k, f (rep k) ∈ L := fun k => hS (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have happ : ∀ (n : ℕ) (a : T.V), ∃ b ∈ L, ‖f a - b‖ ≤ ‖f ϖ‖ ^ n := by
    intro n
    induction n with
    | zero => exact fun a => ⟨0, L.zero_mem, by simpa using hle a⟩
    | succ n ih =>
      intro a
      have hm : a - rep (IsLocalRing.residue T.V a) ∈ IsLocalRing.maximalIdeal T.V := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hrep, sub_self]
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hm
      obtain ⟨a', ha'⟩ := hm
      obtain ⟨b, hb, hab⟩ := ih a'
      refine ⟨f (rep (IsLocalRing.residue T.V a)) + f ϖ * b, L.add_mem (hrL _) (L.mul_mem hϖL hb), ?_⟩
      have : f a - (f (rep (IsLocalRing.residue T.V a)) + f ϖ * b) = f ϖ * (f a' - b) := by
        have := congrArg f ha'
        rw [map_sub, map_mul] at this
        linear_combination this
      rw [this, norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left hab (norm_nonneg _)
  have hcl : IsClosed (L : Set (PadicAlgCl p)) := by
    haveI : FiniteDimensional ℚ_[p] L.toSubalgebra.toSubmodule := hL
    exact L.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  have hV : ∀ a, f a ∈ L := fun a => by
    refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    obtain ⟨b, hb, hab⟩ := happ n a
    exact ⟨b, hb, by rw [dist_eq_norm]; exact hab.trans_lt hn⟩
  intro x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := T.V) x
  rw [map_div₀]
  exact L.div_mem (hV a) (hV b)

theorem ext (T : CDVR) (hT : T.FinRes) (ι : T.Fr →+* PadicAlgCl p) (N : ℝ) (hN : 0 < N)
    (hι : ∀ x, x ≠ 0 → ‖ι x‖ = (p : ℝ) ^ (-((vV T.V x : ℝ) / N))) {σ : Type} [Finite σ] (z : σ → PadicAlgCl p) :
    ∃ (T₀ : CDVR) (j : T₀.Fr →+* PadicAlgCl p) (iT : T.Fr →+* T₀.Fr) (r : ℕ)
      (L : IntermediateField ℚ_[p] (PadicAlgCl p)), T₀.FinRes ∧ 0 < r ∧ (∀ x, j (iT x) = ι x) ∧
      (∀ x, vV T₀.V (iT x) = (r : ℤ) * vV T.V x) ∧ (∀ i, z i ∈ L) ∧ (∀ x ∈ L, x ∈ Set.range j) ∧
      ∀ x, x ≠ 0 → ‖j x‖ = (p : ℝ) ^ (-((vV T₀.V x : ℝ) / (r * N))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  obtain ⟨S, hS, hSL⟩ := range_le T hT ι N hN hι
  let L := IntermediateField.adjoin ℚ_[p] (S ∪ Set.range z)
  haveI : Finite (S ∪ Set.range z : Set _) := (hS.union (Set.finite_range z)).to_subtype
  haveI hL : FiniteDimensional ℚ_[p] L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hιL := hSL L hL (fun x hx => IntermediateField.subset_adjoin _ _ (Or.inl hx))
  obtain ⟨T₀, j, hfin, -, hLj, hnorm⟩ := FinRd.Pt.exists_cdvr L
  choose f hf using fun x => hLj _ (hιL x)
  have hinj : Function.Injective j := j.injective
  let iT : T.Fr →+* T₀.Fr :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hf, map_add, map_add, hf, hf]) }
  have hiT : ∀ x, j (iT x) = ι x := hf
  set m : ℤ := vV T₀.V ((p : ℕ) : T₀.Fr) with hm
  have hrel : ∀ x, x ≠ 0 → (vV T₀.V (iT x) : ℝ) / m = (vV T.V x : ℝ) / N := fun x hx => by
    have h1 := hnorm (iT x) ((map_ne_zero iT).2 hx)
    rw [hiT, hι x hx] at h1
    have h2 := congrArg Real.log h1
    rw [Real.log_rpow (by linarith), Real.log_rpow (by linarith)] at h2
    have := mul_right_cancel₀ (Real.log_pos hp1).ne' h2
    linarith
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal T.V).valuation_exists_uniformizer T.Fr
  have hπ1 : vV T.V π = 1 := by simp [vV, valV, hπ]
  have hπ0 : π ≠ 0 := fun h => by simp [h, vV] at hπ1
  have h1 := hrel π hπ0
  rw [hπ1, Int.cast_one] at h1
  have hm0 : 0 ≤ m := by
    have := vV_nonneg T₀ (p : ℕ)
    rwa [map_natCast] at this
  have hmne : (m : ℝ) ≠ 0 := fun h0 => by
    rw [h0, div_zero] at h1
    exact (one_div_pos.2 hN).ne h1
  have hmpos : (0 : ℝ) < m := lt_of_le_of_ne (by exact_mod_cast hm0) hmne.symm
  have h2 : (vV T₀.V (iT π) : ℝ) * N = m := by field_simp at h1; linarith
  have h3 : (0 : ℝ) < vV T₀.V (iT π) := by
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) hN.le
    linarith
  have h4 : 0 < vV T₀.V (iT π) := by exact_mod_cast h3
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le h4.le
  rw [hr, Int.cast_natCast] at h2
  refine ⟨T₀, j, iT, r, L, hfin, by omega, hiT, fun x => ?_,
    fun i => IntermediateField.subset_adjoin _ _ (Or.inr ⟨i, rfl⟩), hLj, fun x hx => by rw [hnorm x hx, h2]⟩
  by_cases hx : x = 0
  · simp [hx, vV]
  have h5 := hrel x hx
  rw [← h2] at h5
  have hr0 : (r : ℝ) ≠ 0 := by rw [hr] at h3; exact_mod_cast h3.ne'
  field_simp at h5
  have : (vV T₀.V (iT x) : ℝ) = r * vV T.V x := by linarith
  exact_mod_cast this

end Ext

end ModelDimension.Read
