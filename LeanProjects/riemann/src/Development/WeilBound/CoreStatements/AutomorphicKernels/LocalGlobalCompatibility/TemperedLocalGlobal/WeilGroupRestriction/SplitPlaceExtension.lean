import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains

noncomputable section

open scoped Pointwise

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

namespace PositivityTheory.Pf1.CLGD.K.SplitPlaceExtension

section Place

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

theorem val_int_le_one (A : ValuationSubring Ω) (c : 𝓞 K) : A.valuation (algebraMap K Ω (c : K)) ≤ 1 := by
  refine (A.valuation_le_one_iff _).2 ?_
  have hi : IsIntegral ℤ (algebraMap K Ω (c : K)) := c.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom
  have h1 : IsIntegral A (algebraMap K Ω (c : K)) := hi.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem exists_isPlaceOver (A : ValuationSubring Ω) (x₀ : 𝓞 K) (hx₀ : x₀ ≠ 0)
    (hv : A.valuation (algebraMap K Ω (x₀ : K)) < 1) : ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v := by
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A
    (fun c => (A.valuation_le_one_iff _).1 (val_int_le_one A c))
  have key : ∀ c : 𝓞 K, f c ∈ IsLocalRing.maximalIdeal A ↔ A.valuation (algebraMap K Ω (c : K)) < 1 :=
    fun c => A.valuation_lt_one_iff (f c)
  haveI : (IsLocalRing.maximalIdeal A).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, Ideal.comap_isPrime _ _, ?_⟩, fun c => ?_⟩
  · intro h0
    have hx : x₀ ∈ (IsLocalRing.maximalIdeal A).comap f := by rw [Ideal.mem_comap, key]; exact hv
    rw [h0, Ideal.mem_bot] at hx
    exact hx₀ hx
  · show _ ↔ c ∈ (IsLocalRing.maximalIdeal A).comap f
    rw [Ideal.mem_comap, key]

end Place

section Tower

variable {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω]
  [Algebra E M] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 M)}

theorem algebraMap_int (x : 𝓞 E) :
    algebraMap M Ω ((algebraMap (𝓞 E) (𝓞 M) x : 𝓞 M) : M) = algebraMap E Ω (x : E) := by
  rw [IsScalarTower.algebraMap_apply E M Ω]
  rfl

theorem exists_place (h : IsPlaceOver A w) : ∃ w'' : HeightOneSpectrum (𝓞 M), IsPlaceOver A w'' := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  refine exists_isPlaceOver A (algebraMap (𝓞 E) (𝓞 M) x) ?_ ?_
  · intro h0
    apply hx0
    have h1 : ((algebraMap (𝓞 E) (𝓞 M) x : 𝓞 M) : M) = 0 := by rw [h0]; simp
    have h2 : algebraMap E M (x : E) = 0 := h1
    rw [map_eq_zero_iff _ (algebraMap E M).injective] at h2
    simpa using h2
  · rw [algebraMap_int]
    exact (h x).2 hx

theorem mem_iff (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (x : 𝓞 E) :
    x ∈ w.asIdeal ↔ algebraMap (𝓞 E) (𝓞 M) x ∈ w'.asIdeal := by
  rw [← h x, ← h' (algebraMap (𝓞 E) (𝓞 M) x), algebraMap_int]

theorem natCast_mem_iff (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (p : ℕ) :
    ((p : ℕ) : 𝓞 M) ∈ w'.asIdeal ↔ ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  rw [mem_iff h h', map_natCast]

theorem mem_Dec_of_resG {τ : G M Ω} (hτ : resG E τ ∈ Dec (F := E) A) : τ ∈ Dec (F := M) A := by
  have h1 : resG E τ • A = A := hτ
  show τ • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  rfl

theorem actsAs_of_resG {τ : G M Ω} {q a b : ℕ} (hτ : ActsAs A q (resG E τ) a b) : ActsAs A q τ a b :=
  ⟨mem_Dec_of_resG hτ.1, fun x hx => hτ.2 x hx⟩

end Tower

section ActsAs

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω}

theorem actsAs_shift {q a b : ℕ} {σ : G K Ω} (hσ : ActsAs A q σ a b) (n : ℕ) : ActsAs A q σ (a + n) (b + n) := by
  refine ⟨hσ.1, fun x hx => ?_⟩
  have h1 := cong_pow (val_pow_le_one (val_apply_le_one hσ.1 hx) _) (val_pow_le_one hx _) (hσ.2 x hx) (q ^ n)
  rwa [← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at h1

theorem actsAs_pow {q f a b : ℕ} {σ : G K Ω} (hσ : ActsAs A q σ (f * a) (f * b)) : ActsAs A (q ^ f) σ a b := by
  refine ⟨hσ.1, fun x hx => ?_⟩
  rw [← pow_mul, ← pow_mul]
  exact hσ.2 x hx

end ActsAs

theorem dvd_sub_of_pow_eq {k : Type*} [Field k] [Fintype k] {q f m n : ℕ} (hq : 1 < q)
    (hk : Fintype.card k = q ^ f) (hmn : m ≤ n) (h : ∀ y : k, y ^ (q ^ n) = y ^ (q ^ m)) : f ∣ n - m := by
  classical
  have hf : f ≠ 0 := by
    rintro rfl
    have h0 := Fintype.one_lt_card (α := k)
    rw [hk, pow_zero] at h0
    exact lt_irrefl _ h0
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf g = q ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    simp only [Nat.card_eq_fintype_card]
    rw [Fintype.card_units, hk]
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : (g ^ (q ^ m)) ^ (q ^ d) = g ^ (q ^ m) := by
    apply Units.ext
    push_cast
    rw [← pow_mul, ← pow_add]
    exact h g
  have hd1 : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
  have h2 : g ^ (q ^ m * (q ^ d - 1)) = 1 := by
    have h3 : (g ^ (q ^ m)) ^ (q ^ d - 1) * g ^ (q ^ m) = g ^ (q ^ m) := by
      rw [← pow_succ, Nat.sub_add_cancel hd1, h1]
    rw [pow_mul]
    exact mul_eq_right.mp h3
  have h3 : q ^ f - 1 ∣ q ^ m * (q ^ d - 1) := hord ▸ orderOf_dvd_of_pow_eq_one h2
  have hq1 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
  have hcop : Nat.Coprime (q ^ f - 1) (q ^ m) := by
    have c1 : Nat.Coprime (q ^ f - 1) (q ^ f) := by
      obtain ⟨N, hN⟩ : ∃ N, q ^ f = N + 1 := ⟨q ^ f - 1, by omega⟩
      rw [hN, Nat.add_sub_cancel]
      exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right N)
    exact (c1.coprime_dvd_right (dvd_pow_self q hf)).pow_right m
  have h4 : q ^ f - 1 ∣ q ^ d - 1 := hcop.dvd_of_dvd_mul_left h3
  have h5 : Nat.gcd (q ^ f - 1) (q ^ d - 1) = q ^ f - 1 := Nat.gcd_eq_left h4
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at h5
  have h6 : q ^ Nat.gcd f d = q ^ f := by
    have := Nat.one_le_pow (Nat.gcd f d) q (by omega)
    omega
  have h7 : Nat.gcd f d = f := Nat.pow_right_injective hq h6
  exact h7 ▸ Nat.gcd_dvd_right f d

section Weil

variable {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω]
  [Algebra E M] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 M)}

theorem mem_Weil_of_resG (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (τ : G M Ω) (hσ : resG E τ ∈ Weil h) :
    τ ∈ Weil h' := by
  classical
  obtain ⟨a, b, hab⟩ := (mem_Weil h).1 hσ
  obtain ⟨f, hf⟩ := exists_normV_pow h h'
  have hq : 1 < normV w := one_lt_normV w
  have hres : ∀ y : 𝓞 M, y ^ (normV w ^ b) - y ^ (normV w ^ a) ∈ w'.asIdeal := by
    intro y
    rw [← h']
    have hy := hab.2 (algebraMap M Ω (y : M)) (val_int_le_one A y)
    rw [resG_apply, AlgEquiv.commutes] at hy
    simpa using hy
  haveI := w'.isMaximal
  letI := Ideal.Quotient.field w'.asIdeal
  haveI : Finite (𝓞 M ⧸ w'.asIdeal) := w'.asIdeal.finiteQuotientOfFreeOfNeBot w'.ne_bot
  letI := Fintype.ofFinite (𝓞 M ⧸ w'.asIdeal)
  have hcard : Fintype.card (𝓞 M ⧸ w'.asIdeal) = normV w ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hf
  have hpow : ∀ z : 𝓞 M ⧸ w'.asIdeal, z ^ (normV w ^ b) = z ^ (normV w ^ a) := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq]
    exact hres y
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h0 := one_lt_normV w'
    rw [hf, pow_zero] at h0
    exact lt_irrefl _ h0
  rw [mem_Weil, hf]
  rcases le_total b a with hba | hab'
  · obtain ⟨k, hk⟩ := dvd_sub_of_pow_eq hq hcard hba (fun z => (hpow z).symm)
    refine ⟨b + k, b, actsAs_pow (actsAs_of_resG (E := E) ?_)⟩
    have hfb : b ≤ f * b := Nat.le_mul_of_pos_left b (Nat.pos_of_ne_zero hf0)
    have e1 : a + (f * b - b) = f * (b + k) := by
      rw [mul_add, ← hk]
      generalize f * b = X at hfb ⊢
      omega
    have e2 : b + (f * b - b) = f * b := by omega
    have h1 := actsAs_shift hab (f * b - b)
    rwa [e1, e2] at h1
  · obtain ⟨k, hk⟩ := dvd_sub_of_pow_eq hq hcard hab' hpow
    refine ⟨a, a + k, actsAs_pow (actsAs_of_resG (E := E) ?_)⟩
    have hfa : a ≤ f * a := Nat.le_mul_of_pos_left a (Nat.pos_of_ne_zero hf0)
    have e1 : b + (f * a - a) = f * (a + k) := by
      rw [mul_add, ← hk]
      generalize f * a = X at hfa ⊢
      omega
    have e2 : a + (f * a - a) = f * a := by omega
    have h1 := actsAs_shift hab (f * a - a)
    rwa [e1, e2] at h1

theorem mem_range_resW_iff (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (σ : Weil h) :
    σ ∈ (resW h h').range ↔ (σ : G E Ω) ∈ (resG E (E' := M) (Ω := Ω)).range := by
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨(τ : G M Ω), rfl⟩
  · rintro ⟨τ, hτ⟩
    have hm : τ ∈ Weil h' := mem_Weil_of_resG h h' τ (hτ ▸ σ.2)
    exact ⟨⟨τ, hm⟩, Subtype.ext hτ⟩

end Weil

section Split

theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M]
    [IsCMField M] [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  let φ : M →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h1 := IsCMField.complexEmbedding_complexConj (K := M) φ (algebraMap E M x)
  have h2 := IsCMField.complexEmbedding_complexConj (K := E) (φ.comp (algebraMap E M)) x
  simp only [RingHom.comp_apply] at h2
  rw [h1, h2]

theorem le_of_under_le {E : Type} [Field E] [NumberField E] [IsCMField E] (P : Ideal (𝓞 E)) [hP : P.IsPrime]
    (h : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ P → x ∈ P) (Q : Ideal (𝓞 E))
    (hQ : Q.under (𝓞 (maximalRealSubfield E)) ≤ P.under (𝓞 (maximalRealSubfield E))) : Q ≤ P := by
  intro y hy
  obtain ⟨s, hs⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E
    (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by
      rw [map_mul, mul_comm]
      congr 1
      ext; simp)
  have h1 : s ∈ Q.under (𝓞 (maximalRealSubfield E)) := by
    rw [Ideal.under_def, Ideal.mem_comap, hs]
    exact Q.mul_mem_right _ hy
  have h2 := hQ h1
  rw [Ideal.under_def, Ideal.mem_comap, hs] at h2
  exact (hP.mem_or_mem h2).elim id (h y)

variable {E M Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Field Ω]
  [Algebra E M] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 M)}

theorem isSplitAt_of (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (hs : IsSplitAt w) : IsSplitAt w' := by
  obtain ⟨u, hne, hu⟩ := hs
  have hcE : ∀ x : 𝓞 E, algebraMap (𝓞 E) (𝓞 M) (IsCMField.ringOfIntegersComplexConj E x) =
      IsCMField.ringOfIntegersComplexConj M (algebraMap (𝓞 E) (𝓞 M) x) := fun x => by
    apply RingOfIntegers.ext
    exact (conj_algebraMap (x : E)).symm
  haveI := w'.isPrime
  refine ⟨⟨Ideal.comap (IsCMField.ringOfIntegersComplexConj M) w'.asIdeal, Ideal.comap_isPrime _ _, ?_⟩, ?_, ?_⟩
  · intro h0
    apply w'.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have hx' : (IsCMField.ringOfIntegersComplexConj M).symm x ∈
        Ideal.comap (IsCMField.ringOfIntegersComplexConj M) w'.asIdeal := by
      rw [Ideal.mem_comap, AlgEquiv.apply_symm_apply]
      exact hx
    rw [h0, Ideal.mem_bot] at hx'
    rw [Ideal.mem_bot]
    simpa using congrArg (IsCMField.ringOfIntegersComplexConj M) hx'
  · intro heq
    have hst : ∀ x : 𝓞 M, IsCMField.ringOfIntegersComplexConj M x ∈ w'.asIdeal → x ∈ w'.asIdeal := by
      intro x hx
      have hx' : x ∈ Ideal.comap (IsCMField.ringOfIntegersComplexConj M) w'.asIdeal := Ideal.mem_comap.2 hx
      have e := congrArg HeightOneSpectrum.asIdeal heq
      simp only at e
      rwa [e] at hx'
    have hwst : ∀ x : 𝓞 E, IsCMField.ringOfIntegersComplexConj E x ∈ w.asIdeal → x ∈ w.asIdeal := by
      intro x hx
      rw [mem_iff h h'] at hx ⊢
      rw [hcE] at hx
      exact hst _ hx
    haveI := w.isPrime
    have hle : u.asIdeal ≤ w.asIdeal :=
      le_of_under_le w.asIdeal hwst u.asIdeal (congrArg HeightOneSpectrum.asIdeal hu).le
    exact hne (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top hle))
  · apply HeightOneSpectrum.ext
    ext x
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
    rw [AlgEquiv.commutes]

end Split

end PositivityTheory.Pf1.CLGD.K.SplitPlaceExtension

namespace PositivityTheory.Pf1.CLGD.K

open SplitPlaceExtension in

theorem split_places_weil_galois : ContinuousInvariantCoefficients := by
  intro E Ω _ _ _ _ _ _ A w h X
  obtain ⟨w', h'⟩ := exists_place (M := X.M) h
  exact ⟨w', h', isSplitAt_of h h', natCast_mem_iff h h', mem_range_resW_iff h h'⟩

end PositivityTheory.Pf1.CLGD.K

end
