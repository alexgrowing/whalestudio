import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPow

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES IntermediateField

noncomputable section

namespace GlobalTheory.KZ.ES.RootGal

theorem exists_adjoin_eq_of_natDegree_le {F E : Type} [Field F] [Field E] [CharZero F] [Algebra F E]
    (L : IntermediateField F E) (B : ℕ) (key : ∀ y ∈ L, IsIntegral F y ∧ (minpoly F y).natDegree ≤ B) :
    ∃ x ∈ L, L ≤ F⟮x⟯ := by
  have hbound : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ B := by
    intro y hy
    rw [adjoin.finrank (key y hy).1]
    exact (key y hy).2
  let D : Set ℕ := {d | ∃ y ∈ L, Module.finrank F F⟮y⟯ = d}
  have hDne : D.Nonempty := ⟨_, 0, L.zero_mem, rfl⟩
  have hDbdd : BddAbove D := ⟨B, by rintro d ⟨y, hy, rfl⟩; exact hbound y hy⟩
  obtain ⟨x, hxL, hxmax⟩ := Nat.sSup_mem hDne hDbdd
  have hle : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ Module.finrank F F⟮x⟯ := by
    intro y hy
    rw [hxmax]
    exact le_csSup hDbdd ⟨y, hy, rfl⟩
  refine ⟨x, hxL, ?_⟩
  intro y hy
  have hx := key x hxL
  have hy' := key y hy
  haveI : FiniteDimensional F F⟮x, y⟯ := finiteDimensional_adjoin (by
    rintro z (rfl | rfl)
    · exact hx.1
    · exact hy'.1)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F F⟮x, y⟯
  have hz : F⟮(α : E)⟯ = F⟮x, y⟯ := by
    simpa only [lift_adjoin_simple, lift_top] using congr_arg lift hα
  have hKL : F⟮x, y⟯ ≤ L := by
    rw [adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact hxL
    · exact hy
  have hxK : F⟮x⟯ ≤ F⟮x, y⟯ := adjoin_simple_le_iff.2 (subset_adjoin F _ (by simp))
  have heq : F⟮x⟯ = F⟮x, y⟯ := by
    apply eq_of_le_of_finrank_le hxK
    rw [← hz]
    exact hle _ (hKL α.2)
  rw [heq]
  exact subset_adjoin F _ (by simp)

theorem aut_eq_one_of_fix {F E : Type} [Field F] [Field E] [Algebra F E] (S : Set E)
    (ρ : adjoin F S ≃ₐ[F] adjoin F S) (h : ∀ x : adjoin F S, (x : E) ∈ S → ρ x = x) : ρ = 1 := by
  ext ⟨x, hx⟩
  congr 1
  change ρ ⟨x, hx⟩ = ⟨x, hx⟩
  induction hx using adjoin_induction with
  | mem x hx => exact h _ hx
  | algebraMap c => exact ρ.commutes c
  | add x y hx hy ihx ihy =>
    change ρ (⟨x, hx⟩ + ⟨y, hy⟩) = ⟨x, hx⟩ + ⟨y, hy⟩
    rw [map_add, ihx, ihy]
  | inv x hx ihx =>
    change ρ (⟨x, hx⟩⁻¹) = ⟨x, hx⟩⁻¹
    rw [map_inv₀, ihx]
  | mul x y hx hy ihx ihy =>
    change ρ (⟨x, hx⟩ * ⟨y, hy⟩) = ⟨x, hx⟩ * ⟨y, hy⟩
    rw [map_mul, ihx, ihy]

theorem pow_apply_eq_of_fix_pow {F E : Type} [Field F] [Field E] [Algebra F E] (m : ℕ)
    (hμ : ∀ z : E, z ^ m = 1 → z ∈ (algebraMap F E).range) (ρ : E ≃ₐ[F] E) (y : E) (hy : ρ (y ^ m) = y ^ m) :
    (ρ ^ m) y = y := by
  by_cases h0 : y = 0
  · rw [h0, map_zero]
  have h1 : (ρ y / y) ^ m = 1 := by
    rw [div_pow, ← map_pow, hy, div_self (pow_ne_zero _ h0)]
  obtain ⟨c, hc⟩ := hμ _ h1
  have h2 : ρ y = algebraMap F E c * y := by rw [hc, div_mul_cancel₀ _ h0]
  have h3 : ∀ j : ℕ, (ρ ^ j) y = algebraMap F E c ^ j * y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, ρ.commutes, h2]
      ring
  rw [h3, hc, h1, one_mul]

theorem mem_rootSet_field {F E : Type} [Field F] [Field E] [Algebra F E] {p : Polynomial F} (hp : p ≠ 0) (y : E) :
    y ∈ p.rootSet E ↔ Polynomial.aeval y p = 0 := Polynomial.mem_rootSet_of_ne hp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def levSub (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω X.K where
  carrier := {f | Lev X M f}
  mul_mem' := fun ha hb γ hγ => by rw [map_mul, ha γ hγ, hb γ hγ]
  add_mem' := fun ha hb γ hγ => by rw [map_add, ha γ hγ, hb γ hγ]
  algebraMap_mem' := fun c γ _ => AlgEquiv.commutes _ c
  inv_mem' := fun x hx γ hγ => by rw [map_inv₀, hx γ hγ]

theorem mem_levF (X : Tower Ω ε) (M : ℕ) (y : AlgebraicClosure X.K) :
    y ∈ levF X M ↔ ∃ f, Lev X M f ∧ algebraMap X.K (AlgebraicClosure X.K) f = y := by
  have : levF X M = (levSub X M).map (IsScalarTower.toAlgHom Ω X.K (AlgebraicClosure X.K)) := by
    rw [← adjoin_self Ω ((levSub X M).map _)]; rfl
  rw [this]; rfl

theorem lev_sl (X : Tower Ω ε) {M : ℕ} {f : X.K} (hf : Lev X M f) (γ : SL(2, ℤ)) :
    Lev X M (X.sl (ofSL γ) f) := by
  intro δ hδ
  have h : γ * δ = (γ * δ * γ⁻¹) * γ := by group
  rw [← X.sl_mul, ← map_mul, h, map_mul, X.sl_mul, hf _ ((CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ)]

theorem charZero_levF (X : Tower Ω ε) (M : ℕ) : CharZero (levF X M) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  exact charZero_of_injective_algebraMap (algebraMap Ω (levF X M)).injective

theorem sl_eq_of_map_eq (X : Tower Ω ε) {M : ℕ} {f : X.K} (hf : Lev X M f) {γ δ : SL(2, ℤ)}
    (h : SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ) :
    X.sl (ofSL γ) f = X.sl (ofSL δ) f := by
  have h1 : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma M :=
    CongruenceSubgroup.Gamma_mem'.2 (by rw [map_mul, map_inv, h, mul_inv_cancel])
  have h2 : γ = γ * δ⁻¹ * δ := by group
  conv_lhs => rw [h2, map_mul, X.sl_mul, hf _ h1]

theorem exists_orbit_poly (X : Tower Ω ε) (M₀ M : ℕ) (hM : 0 < M) :
    ∃ B : ℕ, ∀ m : ℕ, 0 < m → ∀ f : X.K, Lev X M f → ∃ Q : Polynomial (levF X M₀), Q.Monic ∧ Q.natDegree ≤ B * m ∧
      ∀ y : AlgebraicClosure X.K, Polynomial.aeval y Q = 0 ↔
        ∃ γ ∈ CongruenceSubgroup.Gamma M₀, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) f) := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  let π : SL(2, ℤ) →* SL(2, ZMod M) := SpecialLinearGroup.map (Int.castRingHom (ZMod M))
  refine ⟨Fintype.card SL(2, ZMod M), fun m hm f hf => ?_⟩
  let g : SL(2, ZMod M) → X.K := fun x => X.sl (ofSL (Function.invFun π x)) f
  let S : Finset X.K := (Finset.univ.image g).filter
    (fun c => ∃ γ ∈ CongruenceSubgroup.Gamma M₀, X.sl (ofSL γ) f = c)
  have hS : ∀ c, c ∈ S ↔ ∃ γ ∈ CongruenceSubgroup.Gamma M₀, X.sl (ofSL γ) f = c := by
    intro c
    simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨γ, -, rfl⟩ := h
    exact ⟨π γ, sl_eq_of_map_eq X hf (Function.invFun_eq (f := π) ⟨γ, rfl⟩)⟩
  have hcard : S.card ≤ Fintype.card SL(2, ZMod M) :=
    (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (by simp))
  let p : Polynomial X.K := ∏ c ∈ S, (Polynomial.X ^ m - Polynomial.C c)
  have hpmon : p.Monic := Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_pow_sub_C c hm.ne'
  have hpdeg : p.natDegree = S.card * m := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun c _ => Polynomial.monic_X_pow_sub_C c hm.ne']
    simp [Polynomial.natDegree_X_pow_sub_C]
  have hpinv : ∀ δ ∈ CongruenceSubgroup.Gamma M₀, p.map (X.sl (ofSL δ) : X.K →+* X.K) = p := by
    intro δ hδ
    simp only [p, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    have himg : S.image (X.sl (ofSL δ)) = S := by
      ext y
      simp only [Finset.mem_image, hS]
      constructor
      · rintro ⟨z, ⟨γ, hγ, rfl⟩, rfl⟩
        exact ⟨γ * δ, mul_mem hγ hδ, by rw [map_mul, X.sl_mul]⟩
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨_, ⟨γ * δ⁻¹, mul_mem hγ (inv_mem hδ), rfl⟩, by
          rw [← X.sl_mul, ← map_mul, inv_mul_cancel_right]⟩
    conv_rhs => rw [← himg]
    rw [Finset.prod_image (fun a _ b _ h => (X.sl (ofSL δ)).injective h)]
    rfl
  have hlift : p.map (algebraMap X.K (AlgebraicClosure X.K)) ∈
      Polynomial.lifts (algebraMap (levF X M₀) (AlgebraicClosure X.K)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    refine ⟨⟨_, (mem_levF X M₀ _).2 ⟨p.coeff i, fun δ hδ => ?_, rfl⟩⟩, by rw [Polynomial.coeff_map]; rfl⟩
    conv_rhs => rw [← hpinv δ hδ]
    rw [Polynomial.coeff_map]
    rfl
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hpmon.map _)
  refine ⟨q, hqmon, ?_, fun y => ?_⟩
  · rw [hqdeg, Polynomial.natDegree_map, hpdeg]
    exact Nat.mul_le_mul_right _ hcard
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hqmap]
    simp only [p, Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, hS]
    constructor
    · rintro ⟨_, ⟨γ, hγ, rfl⟩, h⟩
      exact ⟨γ, hγ, h⟩
    · rintro ⟨γ, hγ, h⟩
      exact ⟨_, ⟨γ, hγ, rfl⟩, h⟩

theorem exists_primitive (X : Tower Ω ε) (M₀ M : ℕ) (hM : 0 < M) (hd : M₀ ∣ M) :
    ∃ f₀, Lev X M f₀ ∧ ∀ f, Lev X M f → algebraMap X.K (AlgebraicClosure X.K) f ∈
      (levF X M₀)⟮algebraMap X.K (AlgebraicClosure X.K) f₀⟯ := by
  obtain ⟨B, hB⟩ := exists_orbit_poly X M₀ M hM
  have hle : levF X M₀ ≤ levF X M := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := (mem_levF X M₀ y).1 hy
    exact (mem_levF X M _).2 ⟨f, fun γ hγ => hf γ (CongruenceDescent.Gamma_le_of_dvd hd hγ), rfl⟩
  haveI := charZero_levF X M₀
  obtain ⟨θ, hθ, h⟩ := exists_adjoin_eq_of_natDegree_le (extendScalars hle) (B * 1) (by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := (mem_levF X M y).1 hy
    obtain ⟨Q, hQ, hdeg, hroot⟩ := hB 1 one_pos f hf
    have h0 := (hroot (algebraMap X.K (AlgebraicClosure X.K) f)).2
      ⟨1, Subgroup.one_mem _, by rw [pow_one, map_one, X.sl_one]⟩
    exact ⟨⟨Q, hQ, h0⟩, (Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ h0) hQ.ne_zero).trans hdeg⟩)
  obtain ⟨f₀, hf₀, rfl⟩ := (mem_levF X M θ).1 hθ
  exact ⟨f₀, hf₀, fun f hf => h ((mem_levF X M _).2 ⟨f, hf, rfl⟩)⟩

theorem apply_eq_sl (X : Tower Ω ε) (M₀ : ℕ) (E : IntermediateField (levF X M₀) (AlgebraicClosure X.K))
    (τ : E ≃ₐ[levF X M₀] E) (f₀ : X.K) (h₀ : algebraMap X.K (AlgebraicClosure X.K) f₀ ∈ E)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M₀)
    (hτ : (τ ⟨_, h₀⟩ : AlgebraicClosure X.K) = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) f₀))
    (x : AlgebraicClosure X.K) (hx : x ∈ (levF X M₀)⟮algebraMap X.K (AlgebraicClosure X.K) f₀⟯) :
    ∃ (f : X.K) (h : x ∈ E), algebraMap X.K (AlgebraicClosure X.K) f = x ∧
      (τ ⟨x, h⟩ : AlgebraicClosure X.K) = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) f) := by
  induction hx using adjoin_induction with
  | mem x hx =>
    obtain rfl := hx
    exact ⟨f₀, h₀, rfl, hτ⟩
  | algebraMap c =>
    obtain ⟨f, hf, hc⟩ := (mem_levF X M₀ c).1 c.2
    refine ⟨f, E.algebraMap_mem c, hc, ?_⟩
    rw [hf γ hγ, hc]
    exact congrArg Subtype.val (τ.commutes c)
  | add x y _ _ ihx ihy =>
    obtain ⟨f, hx, rfl, h1⟩ := ihx
    obtain ⟨g, hy, rfl, h2⟩ := ihy
    refine ⟨f + g, E.add_mem hx hy, map_add _ _ _, ?_⟩
    rw [map_add (X.sl _), map_add (algebraMap X.K (AlgebraicClosure X.K)) (X.sl _ f), ← h1, ← h2]
    exact congrArg Subtype.val (map_add τ ⟨_, hx⟩ ⟨_, hy⟩)
  | inv x _ ihx =>
    obtain ⟨f, hx, rfl, h1⟩ := ihx
    refine ⟨f⁻¹, E.inv_mem hx, map_inv₀ _ _, ?_⟩
    rw [map_inv₀ (X.sl _), map_inv₀ (algebraMap X.K (AlgebraicClosure X.K)) (X.sl _ f), ← h1]
    exact congrArg Subtype.val (map_inv₀ τ ⟨_, hx⟩)
  | mul x y _ _ ihx ihy =>
    obtain ⟨f, hx, rfl, h1⟩ := ihx
    obtain ⟨g, hy, rfl, h2⟩ := ihy
    refine ⟨f * g, E.mul_mem hx hy, map_mul _ _ _, ?_⟩
    rw [map_mul (X.sl _), map_mul (algebraMap X.K (AlgebraicClosure X.K)) (X.sl _ f), ← h1, ← h2]
    exact congrArg Subtype.val (map_mul τ ⟨_, hx⟩ ⟨_, hy⟩)

theorem algebraMap_mem_rootF (X : Tower Ω ε) (M₀ M m : ℕ) (U : X.K) {f : X.K} (hf : Lev X M f) :
    algebraMap X.K (AlgebraicClosure X.K) f ∈ rootF X M₀ M m U :=
  subset_adjoin _ _ (Or.inl ⟨f, hf, rfl⟩)

theorem exists_isSplittingField (X : Tower Ω ε) (M₀ M m : ℕ) (hM : 0 < M) (hd : M₀ ∣ M) (hm : 0 < m) (U : X.K)
    (hU : Lev X M U) : ∃ Q : Polynomial (levF X M₀), Q.IsSplittingField (levF X M₀) (rootF X M₀ M m U) := by
  obtain ⟨B, hB⟩ := exists_orbit_poly X M₀ M hM
  obtain ⟨f₀, hf₀, hgen⟩ := exists_primitive X M₀ M hM hd
  obtain ⟨Q₁, hQ₁, -, hr₁⟩ := hB 1 one_pos f₀ hf₀
  obtain ⟨Q₂, hQ₂, -, hr₂⟩ := hB m hm U hU
  have hne : Q₁ * Q₂ ≠ 0 := (hQ₁.mul hQ₂).ne_zero
  have hE : rootF X M₀ M m U = adjoin (levF X M₀) ((Q₁ * Q₂).rootSet (AlgebraicClosure X.K)) := by
    apply le_antisymm
    · refine adjoin_le_iff.2 ?_
      rintro y (⟨f, hf, rfl⟩ | hy)
      · refine (adjoin_simple_le_iff.2 (subset_adjoin _ _ ?_)) (hgen f hf)
        refine (mem_rootSet_field hne _).2 ?_
        rw [map_mul, (hr₁ _).2 ⟨1, Subgroup.one_mem _, by rw [pow_one, map_one, X.sl_one]⟩, zero_mul]
      · refine subset_adjoin _ _ ((mem_rootSet_field hne _).2 ?_)
        rw [map_mul, (hr₂ _).2 hy, mul_zero]
    · refine adjoin_le_iff.2 ?_
      intro y hy
      have h := (mem_rootSet_field hne _).1 hy
      rw [map_mul, mul_eq_zero] at h
      rcases h with h | h
      · obtain ⟨γ, -, h⟩ := (hr₁ y).1 h
        rw [pow_one] at h
        rw [h]
        exact algebraMap_mem_rootF X M₀ M m U (lev_sl X hf₀ γ)
      · exact subset_adjoin _ _ (Or.inr ((hr₂ y).1 h))
  refine ⟨Q₁ * Q₂, ?_⟩
  rw [hE]
  exact adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

theorem exists_apply_eq_sl (X : Tower Ω ε) (M₀ M m : ℕ) (hM : 0 < M) (hd : M₀ ∣ M) (U : X.K)
    (τ : rootF X M₀ M m U ≃ₐ[levF X M₀] rootF X M₀ M m U) :
    ∃ γ ∈ CongruenceSubgroup.Gamma M₀, ∀ (j : ℕ) (f : X.K) (hf : Lev X M f),
      ((τ ^ j) ⟨_, algebraMap_mem_rootF X M₀ M m U hf⟩ : AlgebraicClosure X.K) =
        algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL (γ ^ j)) f) := by
  obtain ⟨B, hB⟩ := exists_orbit_poly X M₀ M hM
  obtain ⟨f₀, hf₀, hgen⟩ := exists_primitive X M₀ M hM hd
  obtain ⟨Q₁, hQ₁, -, hr₁⟩ := hB 1 one_pos f₀ hf₀
  have h₀ := algebraMap_mem_rootF X M₀ M m U hf₀
  have h1 : Polynomial.aeval (⟨_, h₀⟩ : rootF X M₀ M m U) Q₁ = 0 := by
    apply (algebraMap (rootF X M₀ M m U) (AlgebraicClosure X.K)).injective
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact (hr₁ _).2 ⟨1, Subgroup.one_mem _, by rw [pow_one, map_one, X.sl_one]; rfl⟩
  have h2 : Polynomial.aeval (τ ⟨_, h₀⟩ : AlgebraicClosure X.K) Q₁ = 0 := by
    have h3 : Polynomial.aeval (τ ⟨_, h₀⟩) Q₁ = 0 := by
      rw [Polynomial.aeval_algHom_apply, h1, map_zero]
    have h4 := congrArg (algebraMap (rootF X M₀ M m U) (AlgebraicClosure X.K)) h3
    rwa [← Polynomial.aeval_algebraMap_apply, map_zero] at h4
  obtain ⟨γ, hγ, h⟩ := (hr₁ _).1 h2
  rw [pow_one] at h
  have hone : ∀ (f : X.K) (hf : Lev X M f),
      τ ⟨_, algebraMap_mem_rootF X M₀ M m U hf⟩ = ⟨_, algebraMap_mem_rootF X M₀ M m U (lev_sl X hf γ)⟩ := by
    intro f hf
    obtain ⟨g, _, hg, h5⟩ := apply_eq_sl X M₀ _ τ f₀ h₀ γ hγ h _ (hgen f hf)
    obtain rfl := (algebraMap X.K (AlgebraicClosure X.K)).injective hg
    exact Subtype.ext h5
  refine ⟨γ, hγ, fun j => ?_⟩
  induction j with
  | zero => intro f hf; rw [pow_zero, pow_zero, map_one, X.sl_one]; rfl
  | succ j ih =>
    intro f hf
    rw [pow_succ, AlgEquiv.mul_apply, hone f hf, ih _ (lev_sl X hf γ), pow_succ', map_mul, X.sl_mul]

theorem rootF_finite_galois_isPGroup : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (X : Tower Ω ε), ∀ (l M₀ k n : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∀ U : X.K, Lev X (M₀ * l ^ k) U →
    FiniteDimensional (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧
      IsGalois (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) ∧
      IsPGroup l (rootF X M₀ (M₀ * l ^ k) (l ^ n) U ≃ₐ[levF X M₀] rootF X M₀ (M₀ * l ^ k) (l ^ n) U) := by
  intro Ω _ _ _ ε X l M₀ k n hl hM₀ hd U hU
  have hM : 0 < M₀ * l ^ k := mul_pos hM₀ (pow_pos hl.pos k)
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨Q, hQ⟩ := exists_isSplittingField X M₀ _ _ hM (dvd_mul_right _ _) hm U hU
  haveI := charZero_levF X M₀
  haveI hfin : FiniteDimensional (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) :=
    Polynomial.IsSplittingField.finiteDimensional _ Q
  haveI : Normal (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U) := Normal.of_isSplittingField Q
  refine ⟨hfin, isGalois_iff.2 ⟨inferInstance, inferInstance⟩, fun τ => ⟨k + n, ?_⟩⟩
  obtain ⟨γ, hγ, hτ⟩ := exists_apply_eq_sl X M₀ _ _ hM (dvd_mul_right _ _) U τ
  have hfix : ∀ (f : X.K) (hf : Lev X (M₀ * l ^ k) f),
      (τ ^ l ^ k) ⟨_, algebraMap_mem_rootF X M₀ _ (l ^ n) U hf⟩ = ⟨_, algebraMap_mem_rootF X M₀ _ (l ^ n) U hf⟩ := by
    intro f hf
    apply Subtype.ext
    rw [hτ _ f hf, hf _ (CongruenceDescent.pow_pow_mem_Gamma_mul hd hγ k)]
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hμ : ∀ z : rootF X M₀ (M₀ * l ^ k) (l ^ n) U, z ^ l ^ n = 1 →
      z ∈ (algebraMap (levF X M₀) (rootF X M₀ (M₀ * l ^ k) (l ^ n) U)).range := by
    intro z hz
    have hz' : (z : AlgebraicClosure X.K) ^ l ^ n = 1 := congrArg Subtype.val hz
    have hint : IsIntegral Ω (z : AlgebraicClosure X.K) :=
      IsIntegral.of_pow hm (by rw [hz']; exact isIntegral_one)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one Ω _
      (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint))
    exact ⟨⟨_, (levF X M₀).algebraMap_mem c⟩, Subtype.ext hc⟩
  rw [pow_add, pow_mul]
  refine aut_eq_one_of_fix _ _ ?_
  rintro ⟨x, hx⟩ (⟨f, hf, rfl⟩ | ⟨δ, -, hδ⟩)
  · refine pow_apply_eq_of_fix_pow _ hμ (τ ^ l ^ k) _ ?_
    exact (map_pow _ _ _).trans (congrArg (· ^ l ^ n) (hfix f hf))
  · refine pow_apply_eq_of_fix_pow _ hμ (τ ^ l ^ k) _ ?_
    have h := hfix _ (lev_sl X hU δ)
    have e : (⟨x, hx⟩ ^ l ^ n : rootF X M₀ (M₀ * l ^ k) (l ^ n) U) =
        ⟨_, algebraMap_mem_rootF X M₀ _ (l ^ n) U (lev_sl X hU δ)⟩ := Subtype.ext hδ
    exact (congrArg _ e).trans (h.trans e.symm)

end GlobalTheory.KZ.ES.RootGal
