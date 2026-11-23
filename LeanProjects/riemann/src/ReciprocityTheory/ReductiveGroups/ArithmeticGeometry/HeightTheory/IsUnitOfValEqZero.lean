import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.SemistableReduction.AlgAll

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsLocalRing

namespace ValuationResidueLemmas

theorem wt_add_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe x =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe y =>
      have hx : (0 : ℤ) ≤ x := by exact_mod_cast ha
      have hy : (0 : ℤ) ≤ y := by exact_mod_cast hb
      have hxy : x + y = 0 := by exact_mod_cast h
      have hx0 : x = 0 := by omega
      rw [hx0]
      rfl

theorem wt_pos {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  calc (0 : WithTop ℤ) < b := hb
    _ = 0 + b := (zero_add b).symm
    _ ≤ a + b := by
      first
        | exact add_le_add_right ha b
        | exact add_le_add_left ha b
        | gcongr

theorem wt_nonneg_of_add {a b c : WithTop ℤ} (hb : b ≠ ⊤) (h : a + b = c) (hc : b ≤ c) : 0 ≤ a := by
  induction b using WithTop.recTopCoe with
  | top => exact absurd rfl hb
  | coe y =>
    induction a using WithTop.recTopCoe with
    | top => exact le_top
    | coe x =>
      rw [← h] at hc
      have hyx : y ≤ x + y := by exact_mod_cast hc
      have hx : (0 : ℤ) ≤ x := by omega
      exact_mod_cast hx

section
variable {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))

private lemma mem_iff_lemma (y : F) : y ∈ vRing v ↔ 0 ≤ v y := by
  first
    | exact Iff.rfl
    | exact Valuation.mem_valuationSubring_iff _ _

theorem val_eq_zero_of_isUnit (x : vRing v) (hx : IsUnit x) : v (x : F) = 0 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hxy : (x : F) * (y : F) = 1 := by
    have h1 := congrArg (fun z : vRing v => (z : F)) hy
    simpa using h1
  have h1 : v ((x : F) * (y : F)) = 0 := by
    rw [hxy, AddValuation.map_one]
  rw [AddValuation.map_mul] at h1
  exact wt_add_eq_zero ((mem_iff_lemma v _).1 x.2) ((mem_iff_lemma v _).1 y.2) h1

theorem isUnit_of_val_eq_zero (x : vRing v) (hx : v (x : F) = 0) : IsUnit x := by
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hx
    simp at hx
  have h2 : v ((x : F)⁻¹) = 0 := by
    have h3 := AddValuation.map_mul v ((x : F)⁻¹) x
    rw [inv_mul_cancel₀ hx0, AddValuation.map_one, hx, add_zero] at h3
    exact h3.symm
  have hinv : (x : F)⁻¹ ∈ vRing v := (mem_iff_lemma v _).2 (le_of_eq h2.symm)
  have hmul : x * ⟨(x : F)⁻¹, hinv⟩ = 1 := by
    apply Subtype.ext
    show (x : F) * (x : F)⁻¹ = 1
    exact mul_inv_cancel₀ hx0
  first
    | exact IsUnit.of_mul_eq_one _ hmul
    | exact isUnit_of_mul_eq_one x _ hmul
    | exact ⟨⟨x, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

theorem mem_max_iff (x : vRing v) : x ∈ maximalIdeal (vRing v) ↔ 0 < v (x : F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have h0 : 0 ≤ v (x : F) := (mem_iff_lemma v _).1 x.2
  constructor
  · intro h
    exact lt_of_le_of_ne h0 (fun he => h (isUnit_of_val_eq_zero v x he.symm))
  · intro h hu
    exact h.ne' (val_eq_zero_of_isUnit v x hu)

theorem residue_ne_zero_iff (x : vRing v) : residue (vRing v) x ≠ 0 ↔ v (x : F) = 0 := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff, mem_max_iff]
  have h0 : 0 ≤ v (x : F) := (mem_iff_lemma v _).1 x.2
  constructor
  · intro h
    exact (eq_of_le_of_not_lt h0 h).symm
  · intro h hlt
    rw [h] at hlt
    exact lt_irrefl _ hlt
end

end ValuationResidueLemmas

namespace ValuationResidueLemmas

theorem val_eval_eq_zero {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (P : MvPolynomial σ Ω) (hP : ∀ β, 0 ≤ w (algebraMap Ω U (P.coeff β))) (α : σ →₀ ℕ)
    (h1 : P.coeff α = 1) :
    w (MvPolynomial.aeval t P) = 0 := by
  letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)

  have hc : ∀ β, P.coeff β ∈ (vRing w).comap (algebraMap Ω U) := fun β =>
    ValuationSubring.mem_comap.2 ((mem_iff_lemma w _).2 (hP β))
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : MvPolynomial σ ((vRing w).comap (algebraMap Ω U)),
      MvPolynomial.map ((vRing w).comap (algebraMap Ω U)).subtype P₀ = P := by
    first
      | (refine ⟨∑ β ∈ P.support, MvPolynomial.monomial β
            (⟨P.coeff β, hc β⟩ : (vRing w).comap (algebraMap Ω U)), ?_⟩
         rw [map_sum]
         simp only [MvPolynomial.map_monomial]
         conv_rhs => rw [P.as_sum]
         rfl)
      | exact MvPolynomial.mem_range_map_iff_coeffs_subset.2 (fun c hc' => by
          obtain ⟨β, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc'
          exact ⟨⟨_, hc β⟩, rfl⟩)

  have hQ1 : ((MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U))
      (fun s => (⟨t s, ht s⟩ : vRing w)) P₀ : vRing w) : U) = MvPolynomial.aeval t P := by
    rw [← hP₀, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have h2 := MvPolynomial.eval₂_comp_left (vRing w).subtype
      (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U)) (fun s => (⟨t s, ht s⟩ : vRing w)) P₀
    first
      | exact h2
      | (rw [← h2]; rfl)
  have hhom : (residue (vRing w)).comp (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U)) =
      (algebraMap (ResidueField ((vRing w).comap (algebraMap Ω U))) (ResidueField (vRing w))).comp
        (residue ((vRing w).comap (algebraMap Ω U))) := by
    ext x
    first
      | rfl
      | exact (IsLocalRing.ResidueField.map_residue _ _).symm
  have hkey : MvPolynomial.aeval (fun s => residue (vRing w) ⟨t s, ht s⟩)
      (MvPolynomial.map (residue ((vRing w).comap (algebraMap Ω U))) P₀) =
      residue (vRing w) (MvPolynomial.eval₂ (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U))
        (fun s => (⟨t s, ht s⟩ : vRing w)) P₀) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left, hhom]
    rfl
  have hα : P₀.coeff α = 1 := by
    apply Subtype.ext
    have h3 := congrArg (MvPolynomial.coeff α) hP₀
    rw [MvPolynomial.coeff_map, h1] at h3
    exact h3
  have hne0 : MvPolynomial.map (residue ((vRing w).comap (algebraMap Ω U))) P₀ ≠ 0 := by
    intro h0
    have h4 := congrArg (MvPolynomial.coeff α) h0
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, hα, map_one] at h4
    exact one_ne_zero h4
  have hne : residue (vRing w) (MvPolynomial.eval₂
      (ReciprocityTheory.MultiplicativeHeights.comapInclusion (vRing w) (algebraMap Ω U))
      (fun s => (⟨t s, ht s⟩ : vRing w)) P₀) ≠ 0 := by
    rw [← hkey]
    intro h0
    apply hne0
    first
      | exact algebraicIndependent_iff.1 hind _ h0
      | exact hind (by rw [h0, map_zero])
  have h5 := (residue_ne_zero_iff w _).1 hne
  rw [hQ1] at h5
  exact h5

theorem exists_val_coeff {Ω U σ : Type} [Field Ω] [Field U] [Algebra Ω U]
    (w : AddValuation U (WithTop ℤ)) (t : σ → U) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
      AlgebraicIndependent (ResidueField ((vRing w).comap (algebraMap Ω U)))
        (fun s => residue (vRing w) ⟨t s, ht s⟩))
    (P : MvPolynomial σ Ω) (hP : P ≠ 0) :
    ∃ c : Ω, c ≠ 0 ∧ w (MvPolynomial.aeval t P) = w (algebraMap Ω U c) := by
  classical
  have hsupp : P.support.Nonempty := by
    first
      | exact Finsupp.support_nonempty_iff.2 hP
      | (rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]; exact hP)

  obtain ⟨β₀, hβ₀, hmin⟩ := Finset.exists_min_image P.support
    (fun β => w (algebraMap Ω U (P.coeff β))) hsupp
  have hc0 : P.coeff β₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hβ₀
  refine ⟨P.coeff β₀, hc0, ?_⟩
  have hfc : w (algebraMap Ω U (P.coeff β₀)) ≠ ⊤ := by
    intro h
    rw [AddValuation.top_iff] at h
    exact hc0 ((algebraMap Ω U).injective (h.trans (map_zero _).symm))

  have hQ : ∀ β, 0 ≤ w (algebraMap Ω U ((MvPolynomial.C (P.coeff β₀)⁻¹ * P).coeff β)) := by
    intro β
    rw [MvPolynomial.coeff_C_mul]
    by_cases hβ : β ∈ P.support
    · have e : algebraMap Ω U ((P.coeff β₀)⁻¹ * P.coeff β) * algebraMap Ω U (P.coeff β₀) =
          algebraMap Ω U (P.coeff β) := by
        rw [← map_mul]
        congr 1
        field_simp
      exact wt_nonneg_of_add hfc (by rw [← AddValuation.map_mul, e]) (hmin β hβ)
    · rw [MvPolynomial.notMem_support_iff.1 hβ, mul_zero, map_zero, AddValuation.map_zero]
      exact le_top
  have hQ1 : (MvPolynomial.C (P.coeff β₀)⁻¹ * P).coeff β₀ = 1 := by
    rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc0]
  have h1 := val_eval_eq_zero w t ht hind _ hQ β₀ hQ1
  rw [map_mul, MvPolynomial.aeval_C, AddValuation.map_mul] at h1
  have h2 : w (algebraMap Ω U (P.coeff β₀)⁻¹) + w (algebraMap Ω U (P.coeff β₀)) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, inv_mul_cancel₀ hc0, map_one, AddValuation.map_one]
  have ha : w (algebraMap Ω U (P.coeff β₀)⁻¹) ≠ ⊤ := by
    intro h
    rw [AddValuation.top_iff] at h
    exact (inv_ne_zero hc0) ((algebraMap Ω U).injective (h.trans (map_zero _).symm))
  generalize w (algebraMap Ω U (P.coeff β₀)⁻¹) = a at ha h1 h2
  generalize w (MvPolynomial.aeval t P) = X at h1 ⊢
  generalize w (algebraMap Ω U (P.coeff β₀)) = Y at h2 ⊢
  induction a using WithTop.recTopCoe with
  | top => exact absurd rfl ha
  | coe a =>
    induction X using WithTop.recTopCoe with
    | top => simp at h1
    | coe X =>
      induction Y using WithTop.recTopCoe with
      | top => simp at h2
      | coe Y =>
        have e1 : a + X = 0 := by exact_mod_cast h1
        have e2 : a + Y = 0 := by exact_mod_cast h2
        have e3 : X = Y := by omega
        rw [e3]

end ValuationResidueLemmas

namespace ValuationResidueLemmas

theorem surj_res {K : Type} [Field K] [NumberField K] (ν : AddValuation K (WithTop ℤ))
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hnn : ∀ a : 𝓞 K, algebraMap (𝓞 K) K a ∈ vRing ν)
    (hpos : ∀ a : 𝓞 K, 0 < ν (algebraMap (𝓞 K) K a) ↔ a ∈ la.asIdeal) :
    Function.Surjective ((residue (vRing ν)).comp
      ((algebraMap (𝓞 K) K).codRestrict (vRing ν) hnn)) := by
  intro z
  obtain ⟨c, rfl⟩ := residue_surjective z
  have hc : 0 ≤ ν (c : K) := c.2
  have hz : ∀ a : 𝓞 K, a ∉ la.asIdeal → ν (algebraMap (𝓞 K) K a) = 0 := fun a ha =>
    le_antisymm (not_lt.mp (fun h => ha ((hpos a).mp h))) (hnn a)
  obtain ⟨n, d, hd, hnd⟩ : ∃ n d : 𝓞 K, d ∉ la.asIdeal ∧
      (c : K) * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n := by
    obtain ⟨n, d, h | h⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq la (c : K)
    · exact ⟨n, d, d.2, h⟩
    · refine ⟨d, n, ?_, h⟩
      intro hn
      have h1 : ν ((c : K) * algebraMap (𝓞 K) K n) = ν (algebraMap (𝓞 K) K d) := by rw [h]
      rw [AddValuation.map_mul, hz d d.2] at h1
      have h2 := wt_pos hc ((hpos n).mpr hn)
      rw [h1] at h2
      exact lt_irrefl _ h2
  obtain ⟨y, i, hi, hyi⟩ := la.isMaximal.exists_inv hd
  refine ⟨n * y, ?_⟩
  rw [RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_max_iff]
  have hval : ν ((c : K) - algebraMap (𝓞 K) K (n * y)) + ν (algebraMap (𝓞 K) K d) =
      ν (algebraMap (𝓞 K) K n) + ν (algebraMap (𝓞 K) K i) := by
    rw [← AddValuation.map_mul, ← AddValuation.map_mul, ← map_mul]
    congr 1
    rw [sub_mul, hnd, ← map_mul, ← map_sub]
    congr 1
    linear_combination (-n) * hyi
  rw [hz d hd, add_zero] at hval
  show 0 < ν ((c : K) - algebraMap (𝓞 K) K (n * y))
  rw [hval]
  exact wt_pos (hnn n) ((hpos i).mpr hi)

theorem indep_u {K Ω U τ : Type} [Field K] [NumberField K] [Field Ω] [Field U] [Algebra K Ω]
    [Algebra Ω U] (w : AddValuation U (WithTop ℤ)) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (u : τ → vRing w)
    (h0 : ∀ P : MvPolynomial τ (𝓞 K), 0 < w (MvPolynomial.eval₂ ((algebraMap Ω U).comp
      ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun j => (u j : U)) P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ a : 𝓞 K, 0 ≤ w (((algebraMap Ω U).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) a)) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra ((vRing w).comap (algebraMap Ω U)) (algebraMap K Ω)
    letI : Algebra (ResidueField (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω)))
        (ResidueField (vRing w)) :=
      ((algebraMap _ (ResidueField (vRing w))).comp
        (algebraMap _ (ResidueField ((vRing w).comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent (ResidueField (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => residue (vRing w) (u j)) := by
  classical
  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
  letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra ((vRing w).comap (algebraMap Ω U)) (algebraMap K Ω)
  letI : Algebra (ResidueField (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (ResidueField (vRing w)) :=
    ((algebraMap _ (ResidueField (vRing w))).comp
      (algebraMap _ (ResidueField ((vRing w).comap (algebraMap Ω U))))).toAlgebra
  let ν : AddValuation K (WithTop ℤ) := (w.comap (algebraMap Ω U)).comap (algebraMap K Ω)
  have hpos : ∀ a : 𝓞 K, 0 < ν (algebraMap (𝓞 K) K a) ↔ a ∈ la.asIdeal := by
    intro a
    have := h0 (MvPolynomial.C a)
    simp only [MvPolynomial.eval₂_C] at this
    refine this.trans ?_
    constructor
    · intro h; simpa using h 0
    · intro h α; rw [MvPolynomial.coeff_C]; split_ifs <;> simp [h]
  have h1' : ∀ a : 𝓞 K, algebraMap (𝓞 K) K a ∈ vRing ν := h1
  have h1o : ∀ a : 𝓞 K, algebraMap (𝓞 K) K a ∈ ((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω) := h1
  have hsurj : Function.Surjective ((residue (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω))).comp
      ((algebraMap (𝓞 K) K).codRestrict _ h1o)) := surj_res ν la h1' hpos
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨P', rfl⟩ := MvPolynomial.map_surjective _ hsurj P
  obtain ⟨α, hα⟩ : ∃ α, P'.coeff α ∉ la.asIdeal := by
    by_contra hall
    push Not at hall
    apply hne
    ext α
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, RingHom.comp_apply, residue_eq_zero_iff]
    exact (mem_max_iff ν _).mpr ((hpos _).mpr (hall α))
  have hw0 : ¬ 0 < w (MvPolynomial.eval₂ ((algebraMap Ω U).comp
      ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun j => (u j : U)) P') := by
    rw [h0]; intro h; exact hα (h α)
  let ψ : 𝓞 K →+* vRing w :=
    ((algebraMap Ω U).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))).codRestrict (vRing w) h1
  let y : vRing w := MvPolynomial.eval₂ ψ u P'
  have hy : (y : U) = MvPolynomial.eval₂ ((algebraMap Ω U).comp
      ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun j => (u j : U)) P' :=
    MvPolynomial.eval₂_comp_left (vRing w).subtype ψ u P'
  have hres : residue (vRing w) y = 0 := by
    have e := MvPolynomial.eval₂_comp_left (residue (vRing w)) ψ u P'
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at hP
    refine e.trans (Eq.trans ?_ hP)
    congr 1
  rw [residue_eq_zero_iff, mem_max_iff, hy] at hres
  exact hw0 hres

end ValuationResidueLemmas
end ReciprocityTheory.ChartRestriction.G.T0
