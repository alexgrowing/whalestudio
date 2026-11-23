import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitMulPowOfKummerVanishesOnInertiaCurve
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfPowEqOne

open scoped MatrixGroups TensorProduct
open Polynomial

namespace GlobalTheory.KZ.UnRoot

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

theorem val_eq_one_iff {F : Type} [Field F] (T : ValuationSubring F) (y : F) :
    T.valuation y = 1 ↔ y ≠ 0 ∧ y ∈ T ∧ y⁻¹ ∈ T := by
  rw [← T.valuation_le_one_iff, ← T.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨fun h0 => ?_, h.le, by rw [h, inv_one]⟩
    rw [h0, map_zero] at h
    exact zero_ne_one h
  · rintro ⟨h0, h₁, h₂⟩
    have : 0 < T.valuation y := zero_lt_iff.2 ((_root_.map_ne_zero _).2 h0)
    exact le_antisymm h₁ ((inv_le_one₀ this).1 h₂)

theorem val_comap_eq_one {K K' : Type} [Field K] [Field K'] (f : K →+* K') (S : ValuationSubring K') (x : K) :
    (S.comap f).valuation x = 1 ↔ S.valuation (f x) = 1 := by
  rw [val_eq_one_iff, val_eq_one_iff, ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀,
    _root_.map_ne_zero]

theorem val_eq_one_of_pow {L : Type} [Field L] (A : ValuationSubring L) {x : L} {n : ℕ} (hn : n ≠ 0)
    (h : A.valuation (x ^ n) = 1) : A.valuation x = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' h1 hn))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hn))

theorem root_eq_one {F : Type} [Field F] (V : ValuationSubring F) {m : ℕ} (hm : V.valuation (m : F) = 1) {ζ : F}
    (hζ : ζ ^ m = 1) (hV : V.valuation (ζ - 1) < 1) : ζ = 1 := by
  first
  | exact @_root_.GlobalTheory.RootOfUnityEqOne.main
  | exact _root_.GlobalTheory.RootOfUnityEqOne.main
  | (apply _root_.GlobalTheory.RootOfUnityEqOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootOfUnityEqOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootOfUnityEqOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootOfUnityEqOne.main ..)

theorem fix_root {L : Type} [Field L] (B : ValuationSubring L) {m : ℕ} (hm0 : m ≠ 0) (hm : B.valuation (m : L) = 1)
    {y U g : L} (hy : y ^ m = U) (hg : g ≠ 0) (hu : B.valuation (U / g ^ m) = 1) (φ : L →+* L) (hU : φ U = U)
    (hφg : φ g = g) (hφ : ∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) : φ y = y := by
  have hz : B.valuation (y / g) = 1 := val_eq_one_of_pow B hm0 (by rw [div_pow, hy]; exact hu)
  have hz0 : y / g ≠ 0 := ((val_eq_one_iff B _).1 hz).1
  have hy0 : y ≠ 0 := fun h => hz0 (by rw [h, zero_div])
  have h1 : (φ y / y) ^ m = 1 := by
    rw [div_pow, ← map_pow, hy, hU, div_self]
    rw [← hy]; exact pow_ne_zero _ hy0
  have h2 := hφ _ hz.le
  have e : φ (y / g) - y / g = (φ y / y - 1) * (y / g) := by
    rw [map_div₀, hφg]; field_simp
  rw [e, map_mul, hz, mul_one] at h2
  have := root_eq_one B hm h1 h2
  exact (div_eq_one_iff_eq hy0).1 this

theorem fix_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (Q : (L →+* L) → Prop) (S : Set L)
    (hS : ∀ y ∈ S, ∃ T : Finset K, ∀ φ, Q φ → (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ y = y)
    {θ : L} (hθ : θ ∈ IntermediateField.adjoin K S) :
    ∃ T : Finset K, ∀ φ, Q φ → (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ θ = θ := by
  classical
  induction hθ using IntermediateField.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap x => exact ⟨{x}, fun φ _ h => h x (Finset.mem_singleton_self x)⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := hx
    obtain ⟨T', hT'⟩ := hy
    exact ⟨T ∪ T', fun φ hq h => by
      rw [map_add, hT φ hq fun t ht => h t (Finset.mem_union_left _ ht),
        hT' φ hq fun t ht => h t (Finset.mem_union_right _ ht)]⟩
  | inv x _ hx =>
    obtain ⟨T, hT⟩ := hx
    exact ⟨T, fun φ hq h => by rw [map_inv₀, hT φ hq h]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := hx
    obtain ⟨T', hT'⟩ := hy
    exact ⟨T ∪ T', fun φ hq h => by
      rw [map_mul, hT φ hq fun t ht => h t (Finset.mem_union_left _ ht),
        hT' φ hq fun t ht => h t (Finset.mem_union_right _ ht)]⟩

theorem core {k K L : Type} [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (B : ValuationSubring L) (hB : ∀ p : k[X], algebraMap K L (algebraMap k[X] K p) ∈ B) {l : ℕ} (hl : 0 < l)
    (f : K) (hf : f ≠ 0) (θ : L) (hθ : θ ^ l = algebraMap K L f) (T : Finset K)
    (hT : ∀ φ : L →+* L, (∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) →
      (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ θ = θ) :
    ∃ c : K, c ≠ 0 ∧ B.valuation (algebraMap K L (f / c ^ l)) = 1 := by
  classical
  let E : IntermediateField (RatFunc k) K := IntermediateField.adjoin (RatFunc k) ((insert f T : Finset K) : Set K)
  have hE : ∀ t ∈ insert f T, t ∈ E := fun t ht => IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 ht)
  haveI : FiniteDimensional (RatFunc k) E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic E K := inferInstance
  haveI : Module.IsTorsionFree E L := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E L := ⟨inferInstance, Algebra.IsAlgebraic.trans E K L⟩
  haveI : CharZero K := charZero_of_injective_ringHom (algebraMap (RatFunc k) K).injective
  haveI : CharZero L := charZero_of_injective_ringHom (algebraMap K L).injective
  haveI : NeZero (l : L) := ⟨Nat.cast_ne_zero.2 hl.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L l
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne'] at hθ
    exact hf ((map_eq_zero _).1 hθ.symm)
  obtain ⟨c, hc, hv⟩ := GlobalTheory.KumVal.exists_unit_of_kum_eq_zero k E L l ζ hl hζ ⟨f, hE f (Finset.mem_insert_self _ _)⟩ θ
    (fun h => hf (congrArg Subtype.val h)) hθ B (by
      intro x hx
      have hx' : IsIntegral k[X] x := hx
      obtain ⟨p, hp, hpx⟩ := hx'
      let ρ : k[X] →+* B := ((algebraMap K L).comp (algebraMap k[X] K)).codRestrict B hB
      have hi : IsIntegral B (algebraMap E L x) := by
        refine ⟨p.map ρ, hp.map ρ, ?_⟩
        rw [eval₂_map]
        have := congrArg (algebraMap E L) hpx
        rw [hom_eval₂, map_zero] at this
        exact this
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
      rw [← hy]; exact y.2)
    (fun g hg => GlobalTheory.NeedB.kum_eq_of hζ hθ0 0 (by
      have := hT (g : L →+* L) hg fun t ht => g.commutes ⟨t, hE t (Finset.mem_insert_of_mem ht)⟩
      simpa using this))
  refine ⟨c, fun h => hc (Subtype.ext h), ?_⟩
  exact hv

end GlobalTheory.KZ.UnRoot

open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.UnRoot

theorem mem_Un_of_root_mem_adjoin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (m l : ℕ), 0 < m → 0 < l → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), θ ∈ IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)} → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → f ∈ X.Un l := by
  intro Ω _ _ _ ε X m l hm hl θ f hθ hf W hW
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_ringHom (algebraMap ℚ Ω).injective
  obtain ⟨B, rfl⟩ := exists_comap_eq (algebraMap X.K (AlgebraicClosure X.K)) W
  let e := RatFunc.algEquivOfTranscendental X.jK (GlobalTheory.K4.jK_transcendental X)
  let ψ : RatFunc Ω →ₐ[Ω] X.K := (IntermediateField.val _).comp e.toAlgHom
  letI : Algebra (RatFunc Ω) X.K := ψ.toRingHom.toAlgebra
  letI : Algebra (Polynomial Ω) X.K := (ψ.toRingHom.comp (algebraMap (Polynomial Ω) (RatFunc Ω))).toAlgebra
  haveI : IsScalarTower (Polynomial Ω) (RatFunc Ω) X.K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := ⟨fun x => by
    refine (X.alg_j x).ringHom_of_comp_eq (e.symm : _ →+* RatFunc Ω) (RingHom.id _) e.symm.injective ?_
    ext a
    show ((e (e.symm a) : _) : X.K) = a
    rw [e.apply_symm_apply]⟩
  have hp : ∀ p : (Polynomial Ω), algebraMap (Polynomial Ω) X.K p ∈ B.comap (algebraMap X.K (AlgebraicClosure X.K)) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      have : algebraMap (Polynomial Ω) X.K (C a) = algebraMap Ω X.K a := by
        rw [← ψ.commutes a]; rfl
      rw [this]; exact hW.1 a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a h =>
      have : algebraMap (Polynomial Ω) X.K Polynomial.X = X.jK := by
        show ((e (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) : _) : X.K) = _
        rw [RatFunc.algebraMap_X, RatFunc.algEquivOfTranscendental_X]
      rw [pow_succ, ← mul_assoc, map_mul, this]
      exact mul_mem h hW.2
  have hmB : B.valuation (m : AlgebraicClosure X.K) = 1 := by
    have h1 : (B.comap (algebraMap X.K (AlgebraicClosure X.K))).valuation (algebraMap Ω X.K (m : Ω)) = 1 := by
      rw [val_eq_one_iff, ← map_inv₀]
      exact ⟨(_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hm.ne'), hW.1 _, hW.1 _⟩
    rw [val_comap_eq_one] at h1
    simpa using h1
  obtain ⟨T, hT⟩ := fix_adjoin (fun φ => ∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) _ (by
    rintro y ⟨U, hU, hy⟩
    obtain ⟨g, hg⟩ := hU _ hW
    rw [val_comap_eq_one, map_div₀, map_pow] at hg
    exact ⟨{(U : X.K), (g : X.K)}, fun φ hq h => fix_root B hm.ne' hmB hy ((_root_.map_ne_zero _).2 g.ne_zero) hg φ
      (h _ (by simp)) (h _ (by simp)) hq⟩) hθ
  obtain ⟨c, hc, hv⟩ := core (k := Ω) B hp hl (f : X.K) f.ne_zero θ hf T hT
  exact ⟨Units.mk0 c hc, (val_comap_eq_one _ _ _).2 hv⟩

end GlobalTheory.KZ.UnRoot
