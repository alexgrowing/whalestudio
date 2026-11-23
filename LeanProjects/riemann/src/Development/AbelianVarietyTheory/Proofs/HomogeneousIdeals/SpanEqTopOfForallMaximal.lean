import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')

namespace GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

section Away

variable {S S' S'' T : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S''] [CommRing T] [Algebra R T]

def IsAway (ρ : S →ₐ[R] S') (g : S) : Prop :=
  @IsLocalization.Away S _ g S' _ (ρ : S →+* S').toAlgebra

abbrev awayHom (R : Type) [CommRing R] {S : Type} [CommRing S] [Algebra R S] (g : S) :
    S →ₐ[R] Localization.Away g := IsScalarTower.toAlgHom R S _

theorem isAway_iff (ρ : S →ₐ[R] S') (g : S) : IsAway ρ g ↔
    IsUnit (ρ g) ∧ (∀ z, ∃ (N : ℕ) (a : S), z * ρ g ^ N = ρ a) ∧
      ∀ a, ρ a = 0 → ∃ N : ℕ, g ^ N * a = 0 := by
  letI := (ρ : S →+* S').toAlgebra
  constructor
  · intro h
    haveI : IsLocalization.Away g S' := h
    refine ⟨IsLocalization.Away.algebraMap_isUnit g, fun z => IsLocalization.Away.surj g z,
      fun a ha => ?_⟩
    obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (S := S') g (a := a) (b := 0)
      (by rw [map_zero]; exact ha)
    exact ⟨N, by simpa using hN⟩
  · rintro ⟨h1, h2, h3⟩
    refine IsLocalization.Away.mk g h1 h2 fun a b hab => ?_
    obtain ⟨N, hN⟩ := h3 (a - b) (by rw [map_sub, sub_eq_zero]; exact hab)
    exact ⟨N, by rwa [mul_sub, sub_eq_zero] at hN⟩

theorem isAway_awayHom (g : S) : IsAway (awayHom R g) g :=
  (isAway_iff _ _).2 ⟨IsLocalization.Away.algebraMap_isUnit g,
    fun z => IsLocalization.Away.surj g z, fun a ha => by
      obtain ⟨N, hN⟩ := IsLocalization.Away.exists_of_eq (S := Localization.Away g) g (a := a)
        (b := 0) (by rw [map_zero]; exact ha)
      exact ⟨N, by simpa using hN⟩⟩

namespace IsAway

variable {ρ : S →ₐ[R] S'} {g : S}

theorem unit (h : IsAway ρ g) : IsUnit (ρ g) := ((isAway_iff _ _).1 h).1

theorem surj (h : IsAway ρ g) (z : S') : ∃ (N : ℕ) (a : S), z * ρ g ^ N = ρ a :=
  ((isAway_iff _ _).1 h).2.1 z

theorem ker (h : IsAway ρ g) {a : S} (ha : ρ a = 0) : ∃ N : ℕ, g ^ N * a = 0 :=
  ((isAway_iff _ _).1 h).2.2 a ha

theorem surj_fin (h : IsAway ρ g) {κ : Type} [Finite κ] (z : κ → S') :
    ∃ (N : ℕ) (a : κ → S), ∀ i, z i * ρ g ^ N = ρ (a i) := by
  choose N a hNa using fun i => h.surj (z i)
  obtain ⟨M, hM⟩ := (Set.finite_range N).bddAbove
  refine ⟨M, fun i => a i * g ^ (M - N i), fun i => ?_⟩
  rw [map_mul, ← hNa, map_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' (hM ⟨i, rfl⟩)]

theorem ker_fin (h : IsAway ρ g) {κ : Type} [Finite κ] {a : κ → S} (ha : ∀ i, ρ (a i) = 0) :
    ∃ N : ℕ, ∀ i, g ^ N * a i = 0 := by
  choose N hN using fun i => h.ker (ha i)
  obtain ⟨M, hM⟩ := (Set.finite_range N).bddAbove
  refine ⟨M, fun i => ?_⟩
  rw [← Nat.sub_add_cancel (hM ⟨i, rfl⟩), pow_add, mul_assoc, hN, mul_zero]

theorem lift (h : IsAway ρ g) (φ : S →ₐ[R] T) (hφ : IsUnit (φ g)) :
    ∃ ψ : S' →ₐ[R] T, ψ.comp ρ = φ := by
  letI := (ρ : S →+* S').toAlgebra
  haveI : IsLocalization.Away g S' := h
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r => (ρ.commutes r).symm
  exact ⟨IsLocalization.Away.liftAlgHom g hφ,
    AlgHom.ext fun a => IsLocalization.Away.lift_eq g hφ a⟩

theorem ext (h : IsAway ρ g) {ψ ψ' : S' →ₐ[R] T} (e : ψ.comp ρ = ψ'.comp ρ) : ψ = ψ' := by
  ext z
  obtain ⟨N, a, hz⟩ := h.surj z
  have e' : ∀ a, ψ (ρ a) = ψ' (ρ a) := fun a => AlgHom.congr_fun e a
  have hu : IsUnit (ψ (ρ g) ^ N) := (h.unit.map ψ).pow N
  apply hu.mul_right_cancel
  rw [← map_pow, ← map_mul, hz, map_pow, e', e', ← map_pow, ← map_mul, hz]

theorem comp (h : IsAway ρ g) {ρ' : S' →ₐ[R] S''} {g' : S} (h' : IsAway ρ' (ρ g')) :
    IsAway (ρ'.comp ρ) (g * g') := by
  refine (isAway_iff _ _).2 ⟨?_, fun z => ?_, fun a ha => ?_⟩
  · rw [map_mul]; exact (h.unit.map ρ').mul h'.unit
  · obtain ⟨N, b, hb⟩ := h'.surj z
    obtain ⟨M, a, ha⟩ := h.surj b
    refine ⟨N + M, a * g ^ N * g' ^ M, ?_⟩
    simp only [AlgHom.comp_apply, map_mul, map_pow, ← ha, ← hb]
    ring
  · obtain ⟨N, hN⟩ := h'.ker (a := ρ a) ha
    rw [← map_pow, ← map_mul] at hN
    obtain ⟨M, hM⟩ := h.ker hN
    refine ⟨N + M, ?_⟩
    linear_combination g ^ N * g' ^ M * hM

theorem cancel (h : IsAway ρ g) {ρ' : S' →ₐ[R] S''} {g' : S}
    (h' : IsAway (ρ'.comp ρ) (g * g')) : IsAway ρ' (ρ g') := by
  have hu := h'.unit
  rw [map_mul] at hu
  obtain ⟨w, hw⟩ := h.unit.exists_right_inv
  refine (isAway_iff _ _).2 ⟨isUnit_of_mul_isUnit_right hu, fun z => ?_, fun b hb => ?_⟩
  · obtain ⟨N, a, ha⟩ := h'.surj z
    refine ⟨N, ρ a * w ^ N, ?_⟩
    simp only [AlgHom.comp_apply, map_mul, map_pow] at ha ⊢
    have hw' : (ρ' (ρ g) * ρ' w) ^ N = 1 := by rw [← map_mul, hw, map_one, one_pow]
    rw [← ha]
    linear_combination (-(z * ρ' (ρ g') ^ N)) * hw'
  · obtain ⟨N, a, ha⟩ := h.surj b
    obtain ⟨M, hM⟩ := h'.ker (a := a) (by rw [AlgHom.comp_apply, ← ha, map_mul, hb, zero_mul])
    refine ⟨M, ?_⟩
    have := congrArg ρ hM
    simp only [map_mul, map_pow, map_zero, ← ha] at this
    have hw' : (ρ g * w) ^ (M + N) = 1 := by rw [hw, one_pow]
    linear_combination w ^ (M + N) * this - (ρ g' ^ M * b) * hw'

theorem swap (h : IsAway ρ g) {ρ₂ : S →ₐ[R] S''} {g' : S} (h₂ : IsAway ρ₂ g')
    {ν : S' →ₐ[R] T} {ξ : S'' →ₐ[R] T} (e : ν.comp ρ = ξ.comp ρ₂) (hξ : IsAway ξ (ρ₂ g)) :
    IsAway ν (ρ g') := by
  refine h.cancel ?_
  rw [e, mul_comm]
  exact h₂.comp hξ

theorem mem_map (h : IsAway ρ g) {J : Ideal S} {z : S'} (hz : z ∈ J.map ρ) :
    ∃ (N : ℕ) (a : S), a ∈ J ∧ z * ρ g ^ N = ρ a := by
  letI := (ρ : S →+* S').toAlgebra
  haveI : IsLocalization.Away g S' := h
  obtain ⟨⟨a, ⟨_, N, rfl⟩⟩, e⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) S').1 hz
  exact ⟨N, a, a.2, by rw [← map_pow]; exact e⟩

theorem pow_mul_mem (h : IsAway ρ g) {J : Ideal S} {c : S} (hc : ρ c ∈ J.map ρ) :
    ∃ N : ℕ, g ^ N * c ∈ J := by
  obtain ⟨N, a, ha, e⟩ := h.mem_map hc
  obtain ⟨M, hM⟩ := h.ker (a := c * g ^ N - a) (by rw [map_sub, map_mul, map_pow, e, sub_self])
  refine ⟨M + N, ?_⟩
  have : g ^ (M + N) * c = g ^ M * a := by linear_combination hM
  rw [this]
  exact J.mul_mem_left _ ha

theorem isOpenImmersion (h : IsAway ρ g) : IsOpenImmersion (spMap ρ).left := by
  letI := (ρ : S →+* S').toAlgebra
  haveI : IsLocalization.Away g S' := h
  exact IsOpenImmersion.of_isLocalization (S := S') g

theorem mem_range (h : IsAway ρ g) (p : PrimeSpectrum S) (hp : g ∉ p.asIdeal) :
    p ∈ Set.range (spMap ρ).left := by
  letI := (ρ : S →+* S').toAlgebra
  haveI : IsLocalization.Away g S' := h
  have := PrimeSpectrum.localization_away_comap_range S' g
  have hp' : p ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := hp
  rw [← this] at hp'
  exact hp'

end IsAway

theorem span_eq_top_of_forall_maximal {s : Set S}
    (h : ∀ m : Ideal S, m.IsMaximal → ∃ f ∈ s, f ∉ m) : Ideal.span s = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, hfm⟩ := h m hm
  exact hfm (hle (Ideal.subset_span hf))

theorem span_range_map {κ : Type} {s : κ → S} (hs : Ideal.span (Set.range s) = ⊤)
    (φ : S →ₐ[R] T) : Ideal.span (Set.range fun i => φ (s i)) = ⊤ := by
  have := congrArg (Ideal.map φ) hs
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

end Away

section Glue

variable {X : Over (Spec (CommRingCat.of R))} {A : Type} [CommRing A] [Algebra R A]
  {κ : Type} {s : κ → A} {B : κ → Type} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]

def awayCover (hs : Ideal.span (Set.range s) = ⊤) (q : ∀ i, A →ₐ[R] B i)
    (hq : ∀ i, IsAway (q i) (s i)) : (Spec (CommRingCat.of A)).OpenCover :=
  Scheme.Cover.mkOfCovers κ (fun i => Spec (CommRingCat.of (B i))) (fun i => (spMap (q i)).left)
    (fun p => by
      have : ∃ i, s i ∉ (p : PrimeSpectrum A).asIdeal := by
        by_contra! hc
        exact (p : PrimeSpectrum A).isPrime.ne_top
          (top_le_iff.1 (hs ▸ Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hc i)))
      obtain ⟨i, hi⟩ := this
      obtain ⟨y, hy⟩ := (hq i).mem_range p hi
      exact ⟨i, y, hy⟩)
    (fun i => (hq i).isOpenImmersion)

theorem away_ext (hs : Ideal.span (Set.range s) = ⊤) (q : ∀ i, A →ₐ[R] B i)
    (hq : ∀ i, IsAway (q i) (s i)) {y y' : sp A ⟶ X}
    (h : ∀ i, spMap (q i) ≫ y = spMap (q i) ≫ y') : y = y' :=
  Over.OverMorphism.ext <| (awayCover hs q hq).hom_ext _ _ fun i =>
    congrArg CommaMorphism.left (h i)

theorem away_glue (hs : Ideal.span (Set.range s) = ⊤) (q : ∀ i, A →ₐ[R] B i)
    (hq : ∀ i, IsAway (q i) (s i)) (y : ∀ i, sp (B i) ⟶ X)
    (h : ∀ i j (T : Type) [CommRing T] [Algebra R T] (a : B i →ₐ[R] T) (b : B j →ₐ[R] T),
      a.comp (q i) = b.comp (q j) → spMap a ≫ y i = spMap b ≫ y j) :
    ∃ z : sp A ⟶ X, ∀ i, spMap (q i) ≫ z = y i := by
  have hc : ∀ i j : κ, pullback.fst ((awayCover hs q hq).f i) ((awayCover hs q hq).f j) ≫ (y i).left =
      pullback.snd _ _ ≫ (y j).left := by
    intro i j
    letI := (q i : A →+* B i).toAlgebra
    letI := (q j : A →+* B j).toAlgebra
    haveI : IsScalarTower R A (B i) := IsScalarTower.of_algebraMap_eq fun r => ((q i).commutes r).symm
    haveI : IsScalarTower R A (B j) := IsScalarTower.of_algebraMap_eq fun r => ((q j).commutes r).symm
    have := congrArg CommaMorphism.left (h i j (TensorProduct A (B i) (B j))
      Algebra.TensorProduct.includeLeft
      (Algebra.TensorProduct.includeRight.restrictScalars R)
      (AlgHom.ext fun a => by
        change (algebraMap A (B i) a) ⊗ₜ[A] (1 : B j) = (1 : B i) ⊗ₜ[A] algebraMap A (B j) a
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]))
    change pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (B i))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (B j)))) ≫ _ = pullback.snd _ _ ≫ _
    rw [← pullbackSpecIso_hom_fst, ← pullbackSpecIso_hom_snd, Category.assoc, Category.assoc]
    exact congrArg _ this
  have hk : ∀ i : κ, (spMap (q i)).left ≫ (awayCover hs q hq).glueMorphisms (fun i => (y i).left) hc =
      (y i).left := fun i => (awayCover hs q hq).ι_glueMorphisms _ hc i
  refine ⟨Over.homMk ((awayCover hs q hq).glueMorphisms (fun i => (y i).left) hc) ?_,
    fun i => Over.OverMorphism.ext (hk i)⟩
  refine (awayCover hs q hq).hom_ext _ _ fun (i : κ) => ?_
  change (spMap (q i)).left ≫ _ = (spMap (q i)).left ≫ (sp A).hom
  rw [← Category.assoc, hk, Over.w, Over.w]

theorem agree_of_isAway {B₁ B₂ B₁₂ : Type} [CommRing B₁] [Algebra R B₁] [CommRing B₂] [Algebra R B₂]
    [CommRing B₁₂] [Algebra R B₁₂] {f g : A} {q₁ : A →ₐ[R] B₁} {q₂ : A →ₐ[R] B₂}
    (h₁ : IsAway q₁ f) (h₂ : IsAway q₂ g) {a₀ : B₁ →ₐ[R] B₁₂} {b₀ : B₂ →ₐ[R] B₁₂}
    (e₀ : a₀.comp q₁ = b₀.comp q₂) (h₁₂ : IsAway (a₀.comp q₁) (f * g))
    {y₁ : sp B₁ ⟶ X} {y₂ : sp B₂ ⟶ X} (hy : spMap a₀ ≫ y₁ = spMap b₀ ≫ y₂)
    (T : Type) [CommRing T] [Algebra R T] (a : B₁ →ₐ[R] T) (b : B₂ →ₐ[R] T)
    (e : a.comp q₁ = b.comp q₂) : spMap a ≫ y₁ = spMap b ≫ y₂ := by
  obtain ⟨ψ, hψ⟩ := h₁₂.lift (a.comp q₁) (by
    rw [map_mul]
    refine (h₁.unit.map a).mul ?_
    rw [e]
    exact h₂.unit.map b)
  have ha : ψ.comp a₀ = a := h₁.ext hψ
  have hb : ψ.comp b₀ = b := h₂.ext (by rw [AlgHom.comp_assoc, ← e₀, hψ, e])
  rw [← ha, ← hb, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, hy]

end Glue

section Chart

variable {X : Over (Spec (CommRingCat.of R))} {A A₀ B : Type} [CommRing A] [Algebra R A]
  [CommRing A₀] [Algebra R A₀] [CommRing B] [Algebra R B]

theorem exists_spMap (f : sp (R₀ := R) A ⟶ sp B) : ∃ φ : B →ₐ[R] A, f = spMap φ := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap R B) ≫ Spec.preimage f.left) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [Spec.map_comp, Spec.map_preimage]
    exact Over.w f
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  refine ⟨⟨(Spec.preimage f.left).hom, fun r => RingHom.congr_fun e' r⟩, Over.OverMorphism.ext ?_⟩
  exact (Spec.map_preimage f.left).symm

theorem chart_inj (j : sp B ⟶ X) [IsOpenImmersion j.left] {φ φ' : B →ₐ[R] A}
    (h : spMap φ ≫ j = spMap φ' ≫ j) : φ = φ' := by
  have h1 := congrArg CommaMorphism.left h
  simp only [Over.comp_left, cancel_mono, spMap_left] at h1
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h1))

theorem exists_chart_pt (j : sp B ⟶ X) [IsOpenImmersion j.left] (y : sp A ⟶ X)
    (h : Set.range y.left ⊆ Set.range j.left) : ∃ φ : B →ₐ[R] A, y = spMap φ ≫ j := by
  obtain ⟨φ, hφ⟩ := exists_spMap (R := R) (A := A) (B := B)
    (Over.homMk (IsOpenImmersion.lift j.left y.left h) (by
      rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]))
  refine ⟨φ, ?_⟩
  rw [← hφ]
  exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left y.left h).symm

theorem spMap_surjective (q : A →ₐ[R] A₀) (hq : Function.Surjective q)
    (hn : ∀ a, q a = 0 → IsNilpotent a) : Function.Surjective (spMap q).left := by
  intro p
  have := range_comap_of_surjective A₀ (q : A →+* A₀) hq
  have hp : (p : PrimeSpectrum A) ∈ PrimeSpectrum.zeroLocus (RingHom.ker (q : A →+* A₀) : Set A) :=
    fun a ha => by
      obtain ⟨n, hn⟩ := hn a ha
      exact (p : PrimeSpectrum A).isPrime.mem_of_pow_mem n (by rw [hn]; exact zero_mem _)
  rw [← this] at hp
  exact hp

theorem exists_chart_pt_of_nil (j : sp B ⟶ X) [IsOpenImmersion j.left] (q : A →ₐ[R] A₀)
    (hq : Function.Surjective q) (hn : ∀ a, q a = 0 → IsNilpotent a) (y : sp A ⟶ X)
    (φ₀ : B →ₐ[R] A₀) (h : spMap q ≫ y = spMap φ₀ ≫ j) :
    ∃ φ : B →ₐ[R] A, y = spMap φ ≫ j ∧ q.comp φ = φ₀ := by
  obtain ⟨φ, rfl⟩ := exists_chart_pt j y (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨p₀, rfl⟩ := spMap_surjective q hq hn p
    refine ⟨(spMap φ₀).left p₀, ?_⟩
    have := congrArg (fun z : sp A₀ ⟶ X => z.left p₀) h
    simpa using this.symm)
  rw [← Category.assoc, spMap_comp] at h
  exact ⟨φ, rfl, chart_inj j h⟩

theorem smooth_of_chart [Smooth X.hom] (j : sp B ⟶ X) [IsOpenImmersion j.left] :
    Algebra.Smooth R B := by
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    have e : j.left ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := Over.w j
    rw [← e]
    infer_instance
  exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 this)

theorem exists_local_chart (y : sp A ⟶ X) (m : Ideal A) (hm : m.IsPrime) :
    ∃ f ∉ m, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (j : sp B ⟶ X),
      IsOpenImmersion j.left ∧ ∀ (T : Type) [CommRing T] [Algebra R T] (φ : A →ₐ[R] T),
        IsUnit (φ f) → ∃ ψ : B →ₐ[R] T, spMap φ ≫ y = spMap ψ ≫ j := by
  let p : (sp (R₀ := R) A).left := (⟨m, hm⟩ : PrimeSpectrum A)
  obtain ⟨B, j₀, hj₀, hmem, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X.left) (x := y.left p) (U := ⊤) trivial
  letI : Algebra R B := (Spec.preimage (j₀ ≫ X.hom)).hom.toAlgebra
  let j : sp (R₀ := R) B ⟶ X := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ X.hom)).symm
  obtain ⟨_, ⟨f, rfl⟩, hf, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := (⟨m, hm⟩ : PrimeSpectrum A)) (u := (y.left ⁻¹ᵁ j₀.opensRange).1) hmem
    (y.left ⁻¹ᵁ j₀.opensRange).2
  refine ⟨f, hf, B, inferInstance, inferInstance, j, hj₀, fun T _ _ φ hφ => ?_⟩
  haveI : IsOpenImmersion j.left := hj₀
  refine exists_chart_pt j _ ?_
  rintro _ ⟨t, rfl⟩
  have : (spMap φ).left t ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
    intro (h : φ f ∈ (t : PrimeSpectrum T).asIdeal)
    exact (t : PrimeSpectrum T).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hφ)
  exact hsub this

end Chart

end GlobalTheory.SqZero
