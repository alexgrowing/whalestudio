import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral.Local

theorem inOpen_of_section {O : Type} [CommRing O] [IsLocalRing O] {B : Type} [CommRing B] [Algebra O B]
    [IsLocalRing B] (ψ : B →ₐ[O] O) {X : Over (Sp O)} {U : X.left.Opens} {w : specO O B ⟶ X}
    (h : InOpen U (ptMap ψ ≫ w)) : InOpen U w := by
  have hs : Function.Surjective ψ.toRingHom := fun a => ⟨algebraMap O B a, ψ.commutes a⟩
  haveI : IsLocalHom ψ.toRingHom := IsLocalHom.of_surjective _ hs
  unfold InOpen at h ⊢
  rw [Over.comp_left, Scheme.Hom.comp_preimage] at h
  refine (IsLocalRing.closedPoint_mem_iff (R := B) _).1 ?_
  have h1 : IsLocalRing.closedPoint O ∈ (ptMap ψ).left ⁻¹ᵁ (w.left ⁻¹ᵁ U) := by
    rw [h]; trivial
  have h2 : (ptMap ψ).left (IsLocalRing.closedPoint O) = IsLocalRing.closedPoint B :=
    IsLocalRing.comap_closedPoint ψ.toRingHom
  rw [← h2]
  exact h1

theorem section_comp {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B] (ψ : B →ₐ[O] O) :
    ptMap ψ ≫ ptMap (Algebra.ofId O B) = 𝟙 _ := by
  ext1
  simp only [ptMap, Over.comp_left, Over.homMk_left, Over.id_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : ψ.toRingHom.comp (Algebra.ofId O B).toRingHom = RingHom.id O := RingHom.ext fun a => ψ.commutes a
  rw [this]
  exact Spec.map_id _

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem inOpen_generic {U : P.G.left.Opens} {z : specO O O ⟶ P.G} {z' : Pts P.A.A} (hz : IsGeneric P z z')
    (h : InOpen U z) : InOpen (P.gen ⁻¹ᵁ U) z' := by
  unfold InOpen at h ⊢
  unfold IsGeneric at hz
  rw [← Scheme.Hom.comp_preimage]
  erw [hz]
  rw [Scheme.Hom.comp_preimage]
  erw [h]
  rfl

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem exists_lift {B : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [Module.Finite O B] [Module.Flat O B]
    (ψ₀ : B →ₐ[O] O) {N : ℕ} {x : specO O B ⟶ P.Gt} (hx : x ^ N = 1) :
    ∃ x' : specO O B ⟶ P.G, x' ^ N = 1 ∧ ∀ ψ : B →ₐ[O] O, ptMap ψ ≫ x' = P.toG (ptMap ψ ≫ x) := by
  haveI := P.isLocalRing
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : B) := fun h => hp₀ (by simpa using h.map ψ₀)
  have hc : IsAdicComplete (Ideal.span {(p : B)}) B := by
    have := GlobalTheory.FlatComplete.isAdicComplete_of_finite_flat O (Ideal.span {(p : O)}) inferInstance B
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  obtain ⟨x', hx', -⟩ := existsUnique_right (P := P) hp hc x
  have hpow : ∀ n : ℕ, Corr P (x ^ n) (x' ^ n) := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact Corr.one
    | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx'
  refine ⟨x', (existsUnique_right (P := P) hp hc 1).unique (hx ▸ hpow N) Corr.one, fun ψ => ?_⟩
  exact (existsUnique_right (P := P) hp₀ inferInstance _).unique (hx'.comp ψ) fun m => P.red_toG _ m

variable [IsAlgClosed C] [CharZero C]

theorem exists_const_mul_unit (hΘ : HasCubeFn P.A) (hU : HasTrivialisingOpen P) (hT : TranslatesInto P)
    (hV : CubeValuesIntegral P) {B : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [Module.Finite O B]
    [Module.Flat O B] (ψ₀ : B →ₐ[O] O) {N : ℕ} (hN : 1 ≤ N) {x y : specO O B ⟶ P.Gt} (hx : x ^ N = 1)
    (hy : y ^ N = 1) : ∃ (d : Cˣ) (u : Bˣ), ∀ ψ : B →ₐ[O] O,
      (weil P.A N (P.toA (ptMap ψ ≫ x)) (P.toA (ptMap ψ ≫ y)) : C) = d * algebraMap O C (ψ u) := by
  haveI := P.isLocalRing
  obtain ⟨x', hx', hxψ⟩ := exists_lift P ψ₀ hx
  obtain ⟨y', hy', hyψ⟩ := exists_lift P ψ₀ hy
  obtain ⟨U, hUs, hg⟩ := hU
  obtain ⟨Θ, hnat, hweil⟩ := hΘ (P.gen ⁻¹ᵁ U) hg
  obtain ⟨z₀, hz₀⟩ := hT U hUs (Fin N × Fin N) fun ij => ptMap ψ₀ ≫ (x' ^ (ij.1 : ℕ) * y' ^ (ij.2 : ℕ))
  obtain ⟨z, hz⟩ : ∃ z : specO O B ⟶ P.G, ptMap ψ₀ ≫ z = z₀ :=
    ⟨ptMap (Algebra.ofId O B) ≫ z₀, by rw [← Category.assoc, section_comp, Category.id_comp]⟩
  have hin : ∀ i j : ℕ, InOpen U (z * x' ^ i * y' ^ j) := fun i j => by
    refine inOpen_of_section ψ₀ ?_
    rw [_root_.mul_assoc, MonObj.comp_mul, hz, pow_eq_pow_mod i hx', pow_eq_pow_mod j hy']
    exact hz₀ (⟨_, Nat.mod_lt _ hN⟩, ⟨_, Nat.mod_lt _ hN⟩)
  have c₁ : ∀ i : ℕ, CubeIn U z (y' ^ i) y' x' := fun i a b c _ _ _ => by
    have := hin c (i * a + b)
    rwa [mul_right_comm, pow_add, pow_mul, ← _root_.mul_assoc] at this
  have c₂ : ∀ i : ℕ, CubeIn U z (x' ^ i) x' y' := fun i a b c _ _ _ => by
    have := hin (i * a + b) c
    rwa [pow_add, pow_mul, ← _root_.mul_assoc] at this
  choose d₁ u₁ h₁ using fun i => hV U Θ hnat B ⟨ψ₀⟩ _ _ _ _ (c₁ i)
  choose d₂ u₂ h₂ using fun i => hV U Θ hnat B ⟨ψ₀⟩ _ _ _ _ (c₂ i)
  refine ⟨(∏ i ∈ Finset.range N, d₁ i) / ∏ i ∈ Finset.range N, d₂ i,
    (∏ i ∈ Finset.range N, u₁ i) / ∏ i ∈ Finset.range N, u₂ i, fun ψ => ?_⟩
  let j : (specO O O ⟶ P.G) →* Pts P.A.A := P.exists_generic.choose
  let F : (specO O B ⟶ P.G) →* Pts P.A.A :=
    j.comp (MonoidHom.mk' (fun w => ptMap ψ ≫ w) fun a b => MonObj.comp_mul _ _ _)
  have hF : ∀ w, IsGeneric P (ptMap ψ ≫ w) (F w) := fun w => (P.exists_generic.choose_spec.2 _ _).2 rfl
  have ex : P.toA (ptMap ψ ≫ x) = F x' := congrArg j (hxψ ψ).symm
  have ey : P.toA (ptMap ψ ≫ y) = F y' := congrArg j (hyψ ψ).symm
  let m : Bˣ →* Cˣ := Units.map ((algebraMap O C).comp ψ.toRingHom).toMonoidHom
  have e₁ : ∀ i, Θ C (𝟙 _) (F z) (F y' ^ i) (F y') (F x') = d₁ i * m (u₁ i) := fun i =>
    Units.ext (h₁ i ψ _ _ _ _ (hF _) (by rw [← map_pow]; exact hF _) (hF _) (hF _))
  have e₂ : ∀ i, Θ C (𝟙 _) (F z) (F x' ^ i) (F x') (F y') = d₂ i * m (u₂ i) := fun i =>
    Units.ext (h₂ i ψ _ _ _ _ (hF _) (by rw [← map_pow]; exact hF _) (hF _) (hF _))
  have hw := hweil N hN (F x') (F y') (F z) (by rw [← map_pow, hx', map_one]) (by rw [← map_pow, hy', map_one])
    fun a b => by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_mul]
      exact inOpen_generic P (hF _) ((hin a b).comp _)
  rw [Finset.prod_congr rfl fun i _ => e₁ i, Finset.prod_congr rfl fun i _ => e₂ i, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, ← map_prod, ← map_prod, mul_div_mul_comm, ← map_div] at hw
  rw [ex, ey, hw]
  rfl

theorem weilIntegralLocal (hΘ : HasCubeFn P.A) (hU : HasTrivialisingOpen P) (hT : TranslatesInto P)
    (hV : CubeValuesIntegral P) : WeilIntegralLocal P := by
  intro B _ _ _ _ _ N hN x y hx hy
  rcases isEmpty_or_nonempty (B →ₐ[O] O) with h0 | ⟨⟨ψ₀⟩⟩
  · exact ⟨0, fun ψ => h0.elim ψ⟩
  obtain ⟨d, u, h⟩ := exists_const_mul_unit P hΘ hU hT hV ψ₀ hN hx hy
  have tx : P.toA (ptMap ψ₀ ≫ x) ^ N = 1 := by
    rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one]
  have ty : P.toA (ptMap ψ₀ ≫ y) ^ N = 1 := by
    rw [← map_pow, ← MonObj.comp_pow, hy, MonObj.comp_one, map_one]
  have hw : weil P.A N (P.toA (ptMap ψ₀ ≫ x)) (P.toA (ptMap ψ₀ ≫ y)) ^ N = 1 := by
    rw [← weil_pow_left hN tx ty, tx]
    simpa using weil_pow_left hN tx ty 0
  have hv : v (weil P.A N (P.toA (ptMap ψ₀ ≫ x)) (P.toA (ptMap ψ₀ ≫ y)) : C) = 1 := by
    have := congrArg (fun w : Cˣ => v (w : C)) hw
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le (by omega)).1 this
  rw [h, map_mul, P.integers.one_of_isUnit (u.isUnit.map ψ₀), _root_.mul_one] at hv
  obtain ⟨d₀, hd₀⟩ := P.integers.exists_of_le_one hv.le
  refine ⟨algebraMap O B d₀ * u, fun ψ => ?_⟩
  rw [h, map_mul, map_mul, ψ.commutes, ← hd₀]
  rfl

theorem weilIntegralLocal_of_cubes : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HasCubeFn P.A → HasTrivialisingOpen P →
    TranslatesInto P → CubeValuesIntegral P → WeilIntegralLocal P :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P => weilIntegralLocal P

end GlobalTheory.WeilIntegral.Local
