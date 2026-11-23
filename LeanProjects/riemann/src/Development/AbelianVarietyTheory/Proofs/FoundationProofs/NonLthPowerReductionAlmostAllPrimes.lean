import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationExtensionUniqueBertiniNoetherStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.LthPowRed

open Polynomial

theorem exists_comap_eq {K L : Type} [Field K] [Field L] (f : K →+* L) (U : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = U := by
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)
  have key : ∀ x ∈ U.nonunits, f x ∈ W.nonunits := by
    intro x hx
    obtain ⟨hxU, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hx
    refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2 ⟨hW ⟨x, hxU⟩, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
    exact fun hu => hm (hloc.map_nonunit ⟨x, hxU⟩ hu)
  refine ⟨W, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxU
    have h0 : x ≠ 0 := by rintro rfl; exact hxU U.zero_mem
    have h1 : x⁻¹ ∈ U.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, map_inv₀]
      have : 1 < U.valuation x := by
        rw [← not_le, ValuationSubring.valuation_le_one_iff]; exact hxU
      exact inv_lt_one_of_one_lt₀ this
    have h2 := key _ h1
    rw [ValuationSubring.mem_nonunits_iff, map_inv₀, map_inv₀] at h2
    have h3 : W.valuation (f x) ≤ 1 := (W.valuation_le_one_iff _).2 hx
    have h4 : 0 < W.valuation (f x) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact (map_ne_zero f).2 h0
    exact absurd ((inv_lt_one₀ h4).1 h2) (not_lt.2 h3)
  · intro x hx
    exact hW ⟨x, hx⟩

theorem mem_nonunits_iff_of_mem_iff {K L : Type} [Field K] [Field L] (f : K →+* L)
    {A : ValuationSubring K} {B : ValuationSubring L} (hAB : ∀ a, f a ∈ B ↔ a ∈ A) (a : K) :
    f a ∈ B.nonunits ↔ a ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, hAB,
    map_eq_zero]

theorem val_eq_one_iff {L : Type} [Field L] (A : ValuationSubring L) (x : L) :
    A.valuation x = 1 ↔ x ∈ A ∧ x ∉ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, ← ValuationSubring.valuation_le_one_iff]
  constructor
  · intro h; rw [h]; exact ⟨le_rfl, lt_irrefl _⟩
  · rintro ⟨h1, h2⟩; exact le_antisymm h1 (not_lt.1 h2)

theorem val_eq_one_iff_of_mem_iff {K L : Type} [Field K] [Field L] (f : K →+* L)
    {A : ValuationSubring K} {B : ValuationSubring L} (hAB : ∀ a, f a ∈ B ↔ a ∈ A) (a : K) :
    B.valuation (f a) = 1 ↔ A.valuation a = 1 := by
  rw [val_eq_one_iff, val_eq_one_iff, hAB, mem_nonunits_iff_of_mem_iff f hAB]

theorem val_eq_one_of_pow {L : Type} [Field L] (A : ValuationSubring L) {x : L} {n : ℕ} (hn : n ≠ 0)
    (h : A.valuation (x ^ n) = 1) : A.valuation x = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' h1 hn))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hn))

theorem not_both_nonunits {F : Type} [Field F] (V : ValuationSubring F) {q l : ℕ} (hq : q.Prime)
    (hl : l.Prime) (hql : q ≠ l) (h1 : (q : F) ∈ V.nonunits) (h2 : (l : F) ∈ V.nonunits) : False := by
  have hcop : IsCoprime (q : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hl).2 hql)
  obtain ⟨a, b, hab⟩ := hcop
  have hab' : (a : F) * q + (b : F) * l = 1 := by
    have := congrArg (Int.cast : ℤ → F) hab; push_cast at this; exact this
  rw [ValuationSubring.mem_nonunits_iff] at h1 h2
  have ha : V.valuation (a : F) ≤ 1 := (V.valuation_le_one_iff _).2 (intCast_mem V a)
  have hb : V.valuation (b : F) ≤ 1 := (V.valuation_le_one_iff _).2 (intCast_mem V b)
  have : V.valuation ((a : F) * q + (b : F) * l) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) h1
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hb) h2
  rw [hab', map_one] at this
  exact lt_irrefl _ this

theorem natCast_mem_nonunits_of_primitive {F : Type} [Field F] (V : ValuationSubring F) {l : ℕ}
    (hl : 1 < l) {ζ : F} (hζ : IsPrimitiveRoot ζ l) (hV : ζ - 1 ∈ V.nonunits) :
    (l : F) ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hV ⊢
  have hζV : ζ ∈ V := by
    have h1 : ζ - 1 ∈ V := (V.valuation_le_one_iff _).1 (le_of_lt hV)
    have : ζ = (ζ - 1) + 1 := by ring
    rw [this]; exact add_mem h1 V.one_mem
  have hsum : ∑ i ∈ Finset.range l, ζ ^ i = 0 := hζ.geom_sum_eq_zero hl
  have hl' : (l : F) = ∑ i ∈ Finset.range l, (1 - ζ ^ i) := by
    rw [Finset.sum_sub_distrib, hsum]; simp
  rw [hl']
  refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
  have hg : (∑ j ∈ Finset.range i, ζ ^ j) * (ζ - 1) = ζ ^ i - 1 := geom_sum_mul ζ i
  have hgV : V.valuation (∑ j ∈ Finset.range i, ζ ^ j) ≤ 1 :=
    (V.valuation_le_one_iff _).2 (Subring.sum_mem _ fun j _ => V.pow_mem hζV j)
  rw [← neg_sub, Valuation.map_neg, ← hg, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hgV) hV

end GlobalTheory.LthPowRed

namespace GlobalTheory.LthPowRed

open Polynomial

theorem finiteDimensional_adjoin_map {F K L : Type} [Field F] [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] (hKL : FiniteDimensional K L) (t : K)
    (ht : FiniteDimensional (IntermediateField.adjoin F {t}) K) :
    FiniteDimensional (IntermediateField.adjoin F {algebraMap K L t}) L := by
  set E := IntermediateField.adjoin F {t}
  set E' := IntermediateField.adjoin F {algebraMap K L t}
  have h1 : E.map (IsScalarTower.toAlgHom F K L) = E' := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
  have hmem : ∀ e : E, algebraMap K L (e : K) ∈ E' := by
    intro e
    rw [← h1]
    exact ⟨e, e.2, rfl⟩
  let g : E →+* E' :=
    { toFun := fun e => ⟨algebraMap K L e, hmem e⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  letI : Algebra E E' := g.toAlgebra
  haveI : IsScalarTower E E' L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite E L := Module.Finite.trans K L
  exact Module.Finite.of_restrictScalars_finite E E' L

def GaussOver {F L : Type} [Field F] [Field L] [Algebra F L] (V : ValuationSubring F) (t : L)
    (W : ValuationSubring L) : Prop :=
  (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) →
    (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)

theorem core {F K L : Type} [Field F] [IsAlgClosed F] [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (t : K) {l : ℕ} (hl : l.Prime) {ζ₀ : F}
    (hζ₀ : IsPrimitiveRoot ζ₀ l) (s : K) (θ : L) (hθ : θ ^ l = algebraMap K L s) (τ : L →ₐ[K] L)
    (hτ : τ θ = algebraMap F L ζ₀ * θ) (V : ValuationSubring F) {q : ℕ} (hq : q.Prime) (hql : q ≠ l)
    (hqV : (q : F) ∈ V.nonunits)
    (huniq : ∀ W₁ W₂ : ValuationSubring L, GaussOver V (algebraMap K L t) W₁ →
      GaussOver V (algebraMap K L t) W₂ → W₁ = W₂)
    (W : ValuationSubring K) (hW : GaussOver V t W) (h : K) (c : F) (hc0 : c ≠ 0) (hcV : c ∈ V)
    (hciV : c⁻¹ ∈ V) : ¬ W.valuation (s * h ^ l - algebraMap F K c) < 1 := by
  intro hlt
  obtain ⟨W', hW'⟩ := exists_comap_eq (algebraMap K L) W
  have hKL : ∀ y : K, algebraMap K L y ∈ W' ↔ y ∈ W := fun y => by
    rw [← hW', ValuationSubring.mem_comap]
  have hFL : ∀ a : F, algebraMap F L a ∈ W' ↔ a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply F K L, hKL]; exact hW.1 a
  have hG' : GaussOver V (algebraMap K L t) W' := by
    refine ⟨hFL, fun P h1 h2 => ?_⟩
    rw [Polynomial.aeval_algebraMap_apply, val_eq_one_iff_of_mem_iff (algebraMap K L) hKL]
    exact hW.2 P h1 h2
  have hτK : ∀ y : K, τ (algebraMap K L y) = algebraMap K L y := τ.commutes
  have hτF : ∀ a : F, τ (algebraMap F L a) = algebraMap F L a := fun a => by
    rw [IsScalarTower.algebraMap_apply F K L, hτK]
  set W'' := W'.comap (τ : L →+* L) with hW''
  have hτmem : ∀ y : L, (τ : L →+* L) y ∈ W' ↔ y ∈ W'' := fun y => by
    rw [hW'', ValuationSubring.mem_comap]
  have hKL'' : ∀ y : K, algebraMap K L y ∈ W'' ↔ y ∈ W := fun y => by
    rw [← hτmem]; simp only [AlgHom.coe_toRingHom]; rw [hτK, hKL]
  have hG'' : GaussOver V (algebraMap K L t) W'' := by
    refine ⟨fun a => ?_, fun P h1 h2 => ?_⟩
    · rw [IsScalarTower.algebraMap_apply F K L, hKL'']; exact hW.1 a
    · rw [Polynomial.aeval_algebraMap_apply, val_eq_one_iff_of_mem_iff (algebraMap K L) hKL'']
      exact hW.2 P h1 h2
  have hEq : W'' = W' := huniq _ _ hG'' hG'
  have hτnon : ∀ x : L, x ∈ W'.nonunits → τ x ∈ W'.nonunits := by
    intro x hx
    rw [← hEq] at hx
    exact (mem_nonunits_iff_of_mem_iff (τ : L →+* L) hτmem x).2 hx
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hl.pos
  have hcval : V.valuation c = 1 := by
    rw [val_eq_one_iff, ValuationSubring.mem_nonunits_iff_or]
    push_neg
    exact ⟨hcV, hc0, hciV⟩
  have hcW : W'.valuation (algebraMap F L c) = 1 :=
    (val_eq_one_iff_of_mem_iff (algebraMap F L) hFL c).2 hcval
  have hζW : W'.valuation (algebraMap F L ζ₀) = 1 :=
    val_eq_one_of_pow W' hl.ne_zero (by rw [← map_pow, hζ₀.pow_eq_one, map_one, map_one])
  have hcL0 : algebraMap F L c ≠ 0 := (_root_.map_ne_zero _).2 hc0
  have hdl : (algebraMap F L d) ^ l = algebraMap F L c := by rw [← map_pow, hd]
  set x := θ * algebraMap K L h with hx
  set y := x * (algebraMap F L d)⁻¹ with hy
  have hxl : x ^ l - algebraMap F L c = algebraMap K L (s * h ^ l - algebraMap F K c) := by
    rw [hx, mul_pow, hθ, map_sub, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  have hx1 : W'.valuation (x ^ l - algebraMap F L c) < 1 := by
    rw [hxl, ← ValuationSubring.mem_nonunits_iff, mem_nonunits_iff_of_mem_iff (algebraMap K L) hKL,
      ValuationSubring.mem_nonunits_iff]
    exact hlt
  have hy1 : W'.valuation (y ^ l - 1) < 1 := by
    have : y ^ l - 1 = (x ^ l - algebraMap F L c) * (algebraMap F L c)⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hcL0, hy, mul_pow, inv_pow, hdl]
    rw [this, map_mul, map_inv₀, hcW, inv_one, mul_one]
    exact hx1
  have hprod : y ^ l - 1 = ∏ ζ ∈ nthRootsFinset l (1 : F), (y - algebraMap F L ζ) := by
    have := congrArg (Polynomial.aeval y) (X_pow_sub_one_eq_prod hl.pos hζ₀)
    simpa [map_prod] using this
  obtain ⟨ζ, hζm, hζ⟩ : ∃ ζ ∈ nthRootsFinset l (1 : F), W'.valuation (y - algebraMap F L ζ) < 1 := by
    by_contra hne
    push_neg at hne
    have : 1 ≤ W'.valuation (y ^ l - 1) := by
      rw [hprod, map_prod]; exact Finset.one_le_prod' hne
    exact absurd hy1 (not_lt.2 this)
  have hζpow : ζ ^ l = 1 := (mem_nthRootsFinset hl.pos _).1 hζm
  have hτy : τ y = algebraMap F L ζ₀ * y := by
    rw [hy, hx, map_mul, map_mul, map_inv₀, hτ, hτK, hτF]; ring
  have h2 : W'.valuation (algebraMap F L ζ₀ * y - algebraMap F L ζ) < 1 := by
    have := hτnon _ ((ValuationSubring.mem_nonunits_iff _).2 hζ)
    rw [map_sub, hτy, hτF, ValuationSubring.mem_nonunits_iff] at this
    exact this
  have h3 : W'.valuation (algebraMap F L ζ₀ * y - algebraMap F L ζ₀ * algebraMap F L ζ) < 1 := by
    rw [← mul_sub, map_mul, hζW, one_mul]; exact hζ
  have h4 : W'.valuation (algebraMap F L (ζ * (ζ₀ - 1))) < 1 := by
    have : algebraMap F L (ζ * (ζ₀ - 1)) = (algebraMap F L ζ₀ * y - algebraMap F L ζ) -
        (algebraMap F L ζ₀ * y - algebraMap F L ζ₀ * algebraMap F L ζ) := by
      simp only [map_mul, map_sub, map_one]; ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 h3)
  have hζ1 : W'.valuation (algebraMap F L ζ) = 1 :=
    val_eq_one_of_pow W' hl.ne_zero (by rw [← map_pow, hζpow, map_one, map_one])
  have h5 : W'.valuation (algebraMap F L (ζ₀ - 1)) < 1 := by
    rw [map_mul, map_mul, hζ1, one_mul] at h4; exact h4
  have h6 : ζ₀ - 1 ∈ V.nonunits := by
    rw [← mem_nonunits_iff_of_mem_iff (algebraMap F L) hFL, ValuationSubring.mem_nonunits_iff]
    exact h5
  exact not_both_nonunits V hq hl hql hqV (natCast_mem_nonunits_of_primitive V hl.one_lt hζ₀ h6)

end GlobalTheory.LthPowRed

namespace GlobalTheory.LthPowRed

open Polynomial

theorem not_valuation_lt_one : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F]
    {K : Type} [Field K] [Algebra F K] (t : K), Transcendental F t →
    FiniteDimensional (IntermediateField.adjoin F {t}) K → ∀ (l : ℕ), l.Prime → ∀ (s : K),
    (∀ u : K, u ^ l ≠ s) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F,
    ((q : ℕ) : F) ∈ V.nonunits → ∀ W : ValuationSubring K, ((∀ a : F, algebraMap F K a ∈ W ↔ a ∈ V) ∧
    (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) →
    W.valuation (Polynomial.aeval t P) = 1)) → ∀ (h : K) (c : F), h ≠ 0 → c ≠ 0 → c ∈ V → c⁻¹ ∈ V →
    ¬ W.valuation (s * h ^ l - algebraMap F K c) < 1 := by
  intro F _ _ _ _ K _ _ t ht hfin l hl s hs
  haveI : Fact (Irreducible (X ^ l - C s)) := ⟨X_pow_sub_C_irreducible_of_prime hl hs⟩
  have hf0 : (X ^ l - C s : K[X]) ≠ 0 := X_pow_sub_C_ne_zero hl.pos s
  have hKL : FiniteDimensional K (AdjoinRoot (X ^ l - C s)) := (AdjoinRoot.powerBasis hf0).finite
  haveI : NeZero (l : F) := ⟨Nat.cast_ne_zero.2 hl.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F l
  have htL : Transcendental F (algebraMap K (AdjoinRoot (X ^ l - C s)) t) :=
    (transcendental_algebraMap_iff (algebraMap K _).injective).2 ht
  have hfinL := finiteDimensional_adjoin_map (F := F) hKL t hfin
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.gauss_valuation_extension_unique_bertiniNoether _ htL hfinL
  refine ⟨insert l S₀, fun q hq hqS V hqV W hW h c _hh hc0 hcV hciV => ?_⟩
  have hql : q ≠ l := fun e => hqS (e ▸ Finset.mem_insert_self _ _)
  have hqS₀ : q ∉ S₀ := fun e => hqS (Finset.mem_insert_of_mem e)
  have hθ : AdjoinRoot.root (X ^ l - C s) ^ l = algebraMap K _ s := by
    have := AdjoinRoot.eval₂_root (X ^ l - C s)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    rw [AdjoinRoot.algebraMap_eq]; exact this
  have hτroot : aeval (algebraMap F _ ζ₀ * AdjoinRoot.root (X ^ l - C s)) (X ^ l - C s) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, mul_pow, hθ, ← map_pow, hζ₀.pow_eq_one, map_one, one_mul,
      sub_self]
  have hτ : AdjoinRoot.liftAlgHom (X ^ l - C s) (Algebra.ofId K _) _ hτroot
      (AdjoinRoot.root (X ^ l - C s)) = algebraMap F _ ζ₀ * AdjoinRoot.root (X ^ l - C s) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  exact core t hl hζ₀ s _ hθ _ hτ V hq hql hqV (hS₀ q hq hqS₀ V hqV) W hW h c hc0 hcV hciV

end GlobalTheory.LthPowRed
