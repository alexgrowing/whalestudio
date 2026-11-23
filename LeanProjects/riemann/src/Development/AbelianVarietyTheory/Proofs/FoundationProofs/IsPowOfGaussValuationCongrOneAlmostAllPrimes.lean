import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringGaloisStableOfKummerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RootFFiniteGaloisIsPGroupStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationUniqueOnLthRootLevelFieldsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularUnitsOfRootMemKummerAdjoinStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.Exact

theorem exists_ext {K L : Type} [Field K] [Field L] (φ : K →+* L) (W : ValuationSubring K) :
    ∃ W' : ValuationSubring L, ∀ x, φ x ∈ W' ↔ x ∈ W := by
  obtain ⟨A, h, hl⟩ := IsLocalRing.exists_factor_valuationRing (φ.comp W.subtype)
  refine ⟨A, fun x => ⟨fun hx => ?_, fun hx => h ⟨x, hx⟩⟩⟩
  by_contra hW
  have hx0 : x ≠ 0 := by rintro rfl; exact hW W.zero_mem
  have hi : x⁻¹ ∈ W := (W.mem_or_inv_mem x).resolve_left hW
  have hu : IsUnit (((φ.comp W.subtype).codRestrict A.toSubring h) ⟨x⁻¹, hi⟩) :=
    isUnit_iff_exists_inv.2 ⟨⟨φ x, hx⟩, Subtype.ext (by simp [hx0])⟩
  obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.1 (hl.1 _ hu)
  have : (z : K) = x := by simpa [Subtype.ext_iff, inv_mul_eq_iff_eq_mul₀ hx0] using hz
  exact hW (this ▸ z.2)

theorem lt_one_iff {K L : Type} [Field K] [Field L] (φ : K →+* L) {W : ValuationSubring K} {W' : ValuationSubring L}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) (x : K) : W'.valuation (φ x) < 1 ↔ W.valuation x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← map_inv₀, h, map_eq_zero]

theorem eq_one_iff {K L : Type} [Field K] [Field L] (φ : K →+* L) {W : ValuationSubring K} {W' : ValuationSubring L}
    (h : ∀ x, φ x ∈ W' ↔ x ∈ W) (x : K) : W'.valuation (φ x) = 1 ↔ W.valuation x = 1 := by
  have h1 := lt_one_iff φ h x
  have h2 := h x
  rw [← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff] at h2
  rw [← not_le, ← not_le, not_iff_not] at h1
  rw [le_antisymm_iff, le_antisymm_iff, h1, h2]

theorem gauss_map {F K L : Type} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] (φ : K →ₐ[F] L)
    {W : ValuationSubring K} {W' : ValuationSubring L} (h : ∀ x, φ x ∈ W' ↔ x ∈ W) (t : K) (V : ValuationSubring F) :
    Gauss (φ t) V W' ↔ Gauss t V W := by
  unfold Gauss
  refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun P => ?_)
  · rw [← φ.commutes, h]
  · rw [Polynomial.aeval_algHom_apply]
    exact imp_congr Iff.rfl (imp_congr Iff.rfl (eq_one_iff (φ : K →+* L) h _))

theorem fix_root {F L : Type} [Field F] [Field L] [Algebra F L] (W : ValuationSubring L) (τ : L ≃ₐ[F] L)
    (hst : ∀ x, τ x ∈ W ↔ x ∈ W) {m : ℕ} (hm : 0 < m) {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (hv : ¬ W.valuation (m : L) < 1) {y : L} (hy : W.valuation (y ^ m - 1) < 1) (hτ : τ (y ^ m) = y ^ m) :
    τ y = y := by
  have hζ' : IsPrimitiveRoot (algebraMap F L ζ) m := hζ.map_of_injective (algebraMap F L).injective
  have hp := congrArg (Polynomial.eval y) (X_pow_sub_C_eq_prod hζ' hm (one_pow m))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod,
    mul_one] at hp
  obtain ⟨i, hi⟩ : ∃ i : ℕ, W.valuation (y - algebraMap F L ζ ^ i) < 1 := by
    by_contra hc
    push Not at hc
    rw [hp, map_prod] at hy
    exact absurd hy (not_lt.2 (Finset.one_le_prod' fun i _ => hc i))
  have hi' := (lt_one_iff (τ : L →+* L) hst _).2 hi
  simp only [RingHom.coe_coe, map_sub, map_pow, AlgEquiv.commutes] at hi'
  have hd : W.valuation (τ y - y) < 1 := by
    have := W.valuation.map_sub_lt hi' hi
    simpa using this
  have hvy : W.valuation y = 1 := by
    have := W.valuation.map_one_add_of_lt hy
    rw [add_sub_cancel, map_pow] at this
    exact (pow_eq_one_iff_of_nonneg zero_le' hm.ne').1 this
  have hy0 : y ≠ 0 := by rintro rfl; simp at hvy
  set z := τ y / y with hz
  have hzm : z ^ m = 1 := by
    rw [hz, div_pow, ← map_pow, hτ, div_self (pow_ne_zero _ hy0)]
  have hz1 : W.valuation (z - 1) < 1 := by
    rw [hz, div_sub_one hy0, map_div₀, hvy, div_one]; exact hd
  have hvz : W.valuation z = 1 := by
    have := W.valuation.map_one_add_of_lt hz1
    rwa [add_sub_cancel] at this
  by_contra hne
  have hz1' : z - 1 ≠ 0 := by
    rw [sub_ne_zero, hz]; intro h; exact hne ((div_eq_one_iff_eq hy0).1 h)
  have hs : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := geom_sum_mul z m
    rw [hzm, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hz1'
  have hpow : ∀ i : ℕ, W.valuation (1 - z ^ i) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : 1 - z ^ (i + 1) = z * (1 - z ^ i) - (z - 1) := by ring
      rw [e]
      refine W.valuation.map_sub_lt ?_ hz1
      rw [map_mul, hvz, one_mul]; exact ih
  apply hv
  have e : (m : L) = ∑ i ∈ Finset.range m, (1 - z ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact W.valuation.map_sum_lt one_ne_zero fun i _ => hpow i

theorem not_lt_of_coprime {L : Type} [Field L] (W : ValuationSubring L) {q m : ℕ} (h : Nat.Coprime m q)
    (hq : W.valuation (q : L) < 1) : ¬ W.valuation (m : L) < 1 := by
  intro hm
  obtain ⟨a, b, hab⟩ : IsCoprime (m : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 h
  have e : (a : L) * m + (b : L) * q = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → L) hab
  have hi : ∀ c : ℤ, W.valuation (c : L) ≤ 1 := fun c => (W.valuation_le_one_iff _).2 (intCast_mem W c)
  have h1 : W.valuation ((a : L) * m + (b : L) * q) < 1 := by
    refine W.valuation.map_add_lt ?_ ?_ <;> rw [map_mul]
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hi a) zero_le' hm
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hi b) zero_le' hq
  rw [e, map_one] at h1
  exact lt_irrefl _ h1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def levK (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω X.K where
  carrier := {f | Lev X M f}
  mul_mem' ha hb γ hγ := by rw [map_mul, ha γ hγ, hb γ hγ]
  add_mem' ha hb γ hγ := by rw [map_add, ha γ hγ, hb γ hγ]
  algebraMap_mem' c γ _ := AlgEquiv.commutes _ c
  inv_mem' x hx γ hγ := by rw [map_inv₀, hx γ hγ]

theorem mem_levF (X : Tower Ω ε) (M : ℕ) (x : AlgebraicClosure X.K) :
    x ∈ levF X M ↔ ∃ f, Lev X M f ∧ algebraMap X.K (AlgebraicClosure X.K) f = x := by
  refine ⟨fun hx => ?_, fun hx => IntermediateField.subset_adjoin _ _ hx⟩
  have : levF X M ≤ (levK X M).map (IsScalarTower.toAlgHom Ω X.K (AlgebraicClosure X.K)) :=
    IntermediateField.adjoin_le_iff.2 fun z hz => hz
  exact this hx

theorem normal_levF (X : Tower Ω ε) (M : ℕ) : Normal (levF X M) (AlgebraicClosure X.K) := by
  let A := IntermediateField.adjoin Ω {X.jK}
  have hA : A ≤ levK X M := IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 (lev_jK X M))
  haveI : Algebra.IsAlgebraic A X.K := ⟨X.alg_j⟩
  haveI : Algebra.IsAlgebraic A (AlgebraicClosure X.K) := Algebra.IsAlgebraic.trans A X.K _
  let φ : A →+* levF X M := (algebraMap A (AlgebraicClosure X.K)).codRestrict (levF X M)
    fun a => (mem_levF X M _).2 ⟨a, hA a.2, rfl⟩
  haveI : Algebra.IsAlgebraic (levF X M) (AlgebraicClosure X.K) := ⟨fun x =>
    (IsIntegral.map_of_comp_eq φ (RingHom.id _) rfl (Algebra.IsIntegral.isIntegral (R := A) x)).isAlgebraic⟩
  haveI : IsAlgClosure (levF X M) (AlgebraicClosure X.K) := ⟨inferInstance, inferInstance⟩
  infer_instance

theorem lev_mono (X : Tower Ω ε) {M N : ℕ} (h : M ∣ N) {f : X.K} (hf : Lev X M f) : Lev X N f := by
  intro γ hγ
  refine hf γ ?_
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have c1 := congrArg (ZMod.castHom h (ZMod M)) h1
  have c2 := congrArg (ZMod.castHom h (ZMod M)) h2
  have c3 := congrArg (ZMod.castHom h (ZMod M)) h3
  have c4 := congrArg (ZMod.castHom h (ZMod M)) h4
  simp only [map_intCast, map_one, map_zero] at c1 c2 c3 c4
  exact ⟨c1, c2, c3, c4⟩

theorem rootF_le (X : Tower Ω ε) (hst : ∀ (g : GQ) (W : ValuationSubring X.K), X.OverY W →
      X.OverY (W.comap (X.sl g).toRingEquiv.toRingHom)) (M₀ M m : ℕ) (U : X.Kˣ) (hU : U ∈ X.Un m)
    (x : AlgebraicClosure X.K) (hx : x ∈ rootF X M₀ M m U) :
    x ∈ IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m,
      y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)} := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨f, _, rfl⟩ | ⟨γ, _, hγ⟩
    · exact IntermediateField.algebraMap_mem _ f
    · exact IntermediateField.subset_adjoin _ _ ⟨_, KmapA.un_map X _ (hst (ofSL γ)) m U hU, hγ⟩
  | algebraMap x =>
    obtain ⟨f, _, hf⟩ := (mem_levF X M₀ _).1 x.2
    have := IntermediateField.algebraMap_mem (IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m,
      y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)}) f
    rw [hf] at this
    exact this
  | add x y _ _ hx hy => exact add_mem hx hy
  | inv x _ hx => exact inv_mem hx
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem mem_of_fixed {F E : Type} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    [FiniteDimensional F L] [IsGalois F L] (T : Subfield E) (hT : ∀ a : F, algebraMap F E a ∈ T) (y : L)
    (hy : ∀ τ : L ≃ₐ[F] L, (∀ x : L, (x : E) ∈ T → τ x = x) → τ y = y) : (y : E) ∈ T := by
  let T' : IntermediateField F L := (T.toIntermediateField hT).comap L.val
  have : y ∈ T' := by
    rw [← IsGalois.fixedField_fixingSubgroup T', IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact hy τ fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x hx
  exact this

end GlobalTheory.KZ.ES.Exact

open GlobalTheory.KZ.ES.Exact in

theorem GlobalTheory.KZ.ES.pow_of_gauss_congr_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W : ValuationSubring X.K, Gauss X.jK V W → ∀ (n k : ℕ) (U : X.Kˣ), U ∈ X.Un (l ^ n) → Lev X (M₀ * l ^ k) U → W.valuation ((U : X.K) - 1) < 1 → ∃ g : X.Kˣ, U = g ^ (l ^ n) := by
  intro Ω _ _ _ ε X hhol l M₀ hl hM₀ hlM
  obtain ⟨S, hS⟩ := GlobalTheory.T.gaussValuation_unique_on_lthRoot_level_fields ε X hhol l M₀ hl hM₀
  refine ⟨insert l S, fun q hq hqS V hqV W hW n k U hU hlev hU1 => ?_⟩
  rw [Finset.mem_insert, not_or] at hqS
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hroot : ∀ m : ℕ, 0 < m → ∃ ζ : levF X M₀, IsPrimitiveRoot ζ m := fun m hm => by
    haveI : NeZero m := ⟨hm.ne'⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
    exact ⟨_, hζ.map_of_injective (algebraMap Ω (levF X M₀)).injective⟩
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨W', hW'⟩ := exists_ext (algebraMap X.K (AlgebraicClosure X.K)) W
  have hG : Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W' :=
    (gauss_map (IsScalarTower.toAlgHom Ω X.K (AlgebraicClosure X.K)) hW' X.jK V).2 hW
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.rootF_finiteDimensional_isGalois_isPGroup ε X l M₀ k n hl hM₀ hlM U hlev
  set L := rootF X M₀ (M₀ * l ^ k) (l ^ n) U with hL
  let WL : ValuationSubring L := W'.comap (algebraMap L (AlgebraicClosure X.K))
  have hWL : ∀ x : L, algebraMap L (AlgebraicClosure X.K) x ∈ W' ↔ x ∈ WL := fun x => Iff.rfl
  haveI := normal_levF X M₀
  have hstab : ∀ (τ : L ≃ₐ[levF X M₀] L) (x : L), τ x ∈ WL ↔ x ∈ WL := by
    refine GlobalTheory.T.mem_valuationSubring_galois_iff_of_kummer_stable l hl (levF X M₀) L h3 (hroot l hl.pos) WL ?_
    rintro θ hθ ⟨a, ha⟩ τ x hx
    obtain ⟨f, hf, hfa⟩ := (mem_levF X M₀ _).1 a.2
    have hθf : (θ : AlgebraicClosure X.K) ^ l = algebraMap X.K (AlgebraicClosure X.K) f := by
      rw [hfa]; exact (congrArg Subtype.val ha).symm
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [map_zero] at hθf
      exact hθ (Subtype.ext (pow_eq_zero_iff hl.ne_zero |>.1 hθf))
    have hfU : Units.mk0 f hf0 ∈ X.Un l := GlobalTheory.T.mem_modularUnits_of_root_mem_kummer_adjoin ε X (l ^ n) l hm hl.pos θ _
      (rootF_le X (fun g W hW => (GlobalTheory.T.overAffineJLine_comap_sl_gal ε X ε.injective hhol W hW).1 g) _ _ _ U hU θ θ.2) hθf
    let τ' := τ.liftNormal (AlgebraicClosure X.K)
    let σ : AlgebraicClosure X.K →ₐ[Ω] AlgebraicClosure X.K := (τ'.restrictScalars Ω : _ ≃ₐ[Ω] _)
    have hj : σ (algebraMap X.K (AlgebraicClosure X.K) X.jK) = algebraMap X.K (AlgebraicClosure X.K) X.jK :=
      τ'.commutes ⟨_, (mem_levF X M₀ _).2 ⟨_, lev_jK X M₀, rfl⟩⟩
    have hG2 : Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V (W'.comap σ.toRingHom) := by
      refine (gauss_map σ (W := W'.comap σ.toRingHom) (W' := W') (fun _ => ValuationSubring.mem_comap.symm) _ V).1 ?_
      rw [hj]; exact hG
    have hx' : (x : AlgebraicClosure X.K) ∈ IntermediateField.adjoin (levF X M₀) {(θ : AlgebraicClosure X.K)} := by
      have : L.val x ∈ (IntermediateField.adjoin (levF X M₀) {θ}).map L.val := ⟨x, hx, rfl⟩
      rwa [IntermediateField.adjoin_map, Set.image_singleton] at this
    have key := hS q hq hqS.2 V hqV _ _ hG2 hG θ _ hfU hf hθf x hx'
    rw [ValuationSubring.mem_comap] at key
    rw [← hWL, ← hWL, ← τ.liftNormal_commutes]
    exact key
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap X.K (AlgebraicClosure X.K) U) hm
  have hyL : y ∈ L := IntermediateField.subset_adjoin _ _
    (Or.inr ⟨1, one_mem _, by rw [map_one, X.sl_one]; exact hy⟩)
  obtain ⟨ζ, hζ⟩ := hroot _ hm
  have hqW : W'.valuation (q : AlgebraicClosure X.K) < 1 := by
    have := (lt_one_iff (algebraMap Ω (AlgebraicClosure X.K)) hG.1 q).2 (V.mem_nonunits_iff.1 hqV)
    rwa [map_natCast] at this
  have hqL : WL.valuation (q : L) < 1 := by
    rw [← lt_one_iff _ hWL, map_natCast]; exact hqW
  have hv : ¬ WL.valuation ((l ^ n : ℕ) : L) < 1 :=
    not_lt_of_coprime WL (Nat.Coprime.pow_left n ((Nat.coprime_primes hl hq).2 (Ne.symm hqS.1))) hqL
  have hy1 : WL.valuation ((⟨y, hyL⟩ : L) ^ (l ^ n) - 1) < 1 := by
    rw [← lt_one_iff _ hWL, map_sub, map_pow, map_one]
    have := (lt_one_iff _ hW' _).2 hU1
    rw [map_sub, map_one, ← hy] at this
    exact this
  have hyT : y ∈ (levF X (M₀ * l ^ k)).toSubfield := by
    refine mem_of_fixed L _ (fun a => ?_) ⟨y, hyL⟩ fun τ hτ => ?_
    · obtain ⟨f, hf, hfa⟩ := (mem_levF X M₀ _).1 a.2
      exact (mem_levF X _ _).2 ⟨f, lev_mono X (Dvd.intro _ rfl) hf, hfa⟩
    · refine fix_root WL τ (hstab τ) hm hζ hv hy1 (hτ _ ?_)
      exact (mem_levF X _ _).2 ⟨U, hlev, hy.symm⟩
  obtain ⟨g, -, hg⟩ := (mem_levF X _ _).1 hyT
  have hgU : g ^ (l ^ n) = U := (algebraMap X.K (AlgebraicClosure X.K)).injective (by rw [map_pow, hg, hy])
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hgU
    exact U.ne_zero hgU.symm
  exact ⟨Units.mk0 g hg0, Units.ext (by simp [hgU])⟩
