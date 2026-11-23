import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.SqZero

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {A A' : Type} [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
  {v : Fin n → (epsR R ⟶ G)}

def expHom (hv : ∀ i, IsTangent (v i)) {J : Ideal A} (hJ : J ^ 2 = ⊥) :
    (Fin n → J) →+ Additive (redKer (R := R) G J) :=
  AddMonoidHom.mk' (fun c => Additive.ofMul
      ⟨lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2),
        lieExp_mem_redKer hv _ (fun i => (c i).2) _⟩)
    (fun c c' => congrArg Additive.ofMul <| Subtype.ext <|
      lieExp_add hv _ _ _ _ (fun i => mul_eq_zero_of_sq hJ (c i).2 (c' i).2) _)

theorem expHom_apply (hv : ∀ i, IsTangent (v i)) {J : Ideal A} (hJ : J ^ 2 = ⊥) (c : Fin n → J) :
    ((expHom hv hJ c).toMul : sp A ⟶ G) =
      lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2) := rfl

section Hom

variable {H : Over (Spec (CommRingCat.of R))} [GrpObj H] {m : ℕ}
  {w : Fin m → (epsR R ⟶ H)} (f : G ⟶ H) [IsMonHom f]

omit [IsCommMonObj G] in
theorem isTangent_comp {x : epsR R ⟶ G} (hx : IsTangent x) : IsTangent (x ≫ f) := by
  unfold IsTangent at hx ⊢
  rw [Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, IsMonHom.one_hom]

omit [IsCommMonObj G] in

theorem existsUnique_lieMatrix (hv : ∀ i, IsTangent (v i)) (hw : IsLieBasis w) :
    ∃! M : Matrix (Fin n) (Fin m) R, ∀ i, IsLieComb (M i) w (v i ≫ f) := by
  have hx : ∀ i, ∃! c, IsLieComb c w (v i ≫ f) := fun i => hw.2 _ (isTangent_comp f (hv i))
  exact ⟨fun i => (hx i).exists.choose, fun i => (hx i).exists.choose_spec,
    fun M' hM' => funext fun i => (hx i).unique (hM' i) (hx i).exists.choose_spec⟩

variable [IsCommMonObj H]

end Hom

variable [Smooth G.hom]

theorem expHom_bijective (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) :
    Function.Bijective (expHom hv.1 hJ) := by
  obtain ⟨hinj, hsurj⟩ := expBij A hv J hJ
  refine ⟨fun c c' h => ?_, fun y => ?_⟩
  · have h' : ((Additive.toMul (expHom hv.1 hJ c) : redKer (R := R) G J) : sp A ⟶ G) =
        ((Additive.toMul (expHom hv.1 hJ c') : redKer (R := R) G J) : sp A ⟶ G) := by rw [h]
    rw [expHom_apply, expHom_apply] at h'
    have := hinj (fun i => (c i : A)) (fun i => (c' i : A)) (fun i => (c i).2) (fun i => (c' i).2) _ _ h'
    funext i
    exact Subtype.ext (congrFun this i)
  · obtain ⟨c, hc, hcJ, hy⟩ := hsurj ((Additive.toMul y : redKer (R := R) G J) : sp A ⟶ G)
      (Additive.toMul y : redKer (R := R) G J).2
    refine ⟨fun i => ⟨c i, hcJ i⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [expHom_apply, hy]

def kerEquiv (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) :
    Additive (redKer (R := R) G J) ≃+ (Fin n → J) :=
  (AddEquiv.ofBijective (expHom hv.1 hJ) (expHom_bijective hv hJ)).symm

theorem kerEquiv_symm_apply (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) (c : Fin n → J) :
    (((kerEquiv hv hJ).symm c).toMul : sp A ⟶ G) =
      ∏ i, spMap (epsTo R (c i : A) (mul_eq_zero_of_sq hJ (c i).2 (c i).2)) ≫ v i := rfl

theorem kerEquiv_eq_iff (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥)
    (y : redKer (R := R) G J) (c : Fin n → J) : kerEquiv hv hJ (Additive.ofMul y) = c ↔
      (y : sp A ⟶ G) =
        lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2) := by
  constructor
  · rintro rfl
    have := kerEquiv_symm_apply hv hJ (kerEquiv hv hJ (Additive.ofMul y))
    rw [AddEquiv.symm_apply_apply] at this
    exact this
  · intro h
    rw [← AddEquiv.eq_symm_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [kerEquiv_symm_apply]
    exact h

theorem eq_lieExp_kerEquiv (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥)
    (y : redKer (R := R) G J) : (y : sp A ⟶ G) =
      lieExp v (fun i => (kerEquiv hv hJ (Additive.ofMul y) i : A))
        (fun _ => mul_eq_zero_of_sq hJ (Subtype.prop _) (Subtype.prop _)) := by
  have := kerEquiv_symm_apply hv hJ (kerEquiv hv hJ (Additive.ofMul y))
  rw [AddEquiv.symm_apply_apply] at this
  exact this

theorem kerEquiv_map (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) {J' : Ideal A'}
    (hJ' : J' ^ 2 = ⊥) (φ : A →ₐ[R] A') (hφ : ∀ a ∈ J, φ a ∈ J') (y : redKer (R := R) G J)
    (i : Fin n) :
    (kerEquiv hv hJ' (Additive.ofMul ⟨spMap φ ≫ y.1, comp_mem_redKer y.2 φ hφ⟩) i : A') =
      φ (kerEquiv hv hJ (Additive.ofMul y) i) := by
  have hy := eq_lieExp_kerEquiv hv hJ y
  have key : kerEquiv hv hJ' (Additive.ofMul ⟨spMap φ ≫ y.1, comp_mem_redKer y.2 φ hφ⟩) =
      fun i => ⟨φ (kerEquiv hv hJ (Additive.ofMul y) i), hφ _ (kerEquiv hv hJ (Additive.ofMul y) i).2⟩ := by
    rw [kerEquiv_eq_iff]
    show spMap φ ≫ (y : sp A ⟶ G) = _
    rw [hy]
    refine (comp_lieExp v φ _ _).trans ?_
    exact lieExp_congr v (fun _ => rfl) _ _
  rw [key]

theorem zpow_eq_one_of_mem_redKer (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) {k : ℤ}
    (hk : ∀ a ∈ J, k • a = 0) {y : sp A ⟶ G} (hy : y ∈ redKer G J) : y ^ k = 1 := by
  have hc : k • kerEquiv hv hJ (Additive.ofMul (⟨y, hy⟩ : redKer (R := R) G J)) = 0 := by
    funext i
    apply Subtype.ext
    simp [hk _ (kerEquiv hv hJ (Additive.ofMul (⟨y, hy⟩ : redKer (R := R) G J)) i).2]
  have h1 : k • Additive.ofMul (⟨y, hy⟩ : redKer (R := R) G J) = 0 := by
    apply (kerEquiv hv hJ).injective
    rw [map_zsmul, map_zero]
    exact hc
  have h2 := congrArg (fun z => ((Additive.toMul z : redKer (R := R) G J) : sp A ⟶ G)) h1
  simpa using h2

theorem pow_eq_one_of_mem_redKer (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥) {k : ℕ}
    (hk : ∀ a ∈ J, k • a = 0) {y : sp A ⟶ G} (hy : y ∈ redKer G J) : y ^ k = 1 := by
  have := zpow_eq_one_of_mem_redKer hv hJ (k := (k : ℤ)) (fun a ha => by rw [natCast_zsmul]; exact hk a ha) hy
  rwa [zpow_natCast] at this

theorem existsUnique_eq_lieExp_mul (hv : IsLieBasis v) {J : Ideal A} (hJ : J ^ 2 = ⊥)
    {y y' : sp A ⟶ G}
    (h : spMap (Ideal.Quotient.mkₐ R J) ≫ y = spMap (Ideal.Quotient.mkₐ R J) ≫ y') :
    ∃! c : Fin n → J,
      y' = lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2) * y := by
  have hmem : y' * y⁻¹ ∈ redKer G J := by
    show y' * y⁻¹ ∈ (pointsMap G (Ideal.Quotient.mkₐ R J)).ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ptsMap_apply, ptsMap_apply, h, mul_inv_cancel]
  refine ⟨kerEquiv hv hJ (Additive.ofMul ⟨_, hmem⟩), ?_, ?_⟩
  · have := eq_lieExp_kerEquiv hv hJ ⟨_, hmem⟩
    dsimp only
    rw [← this]
    exact (inv_mul_cancel_right y' y).symm
  · intro c hc
    have : (y' * y⁻¹ : sp A ⟶ G) =
        lieExp v (fun i => (c i : A)) (fun i => mul_eq_zero_of_sq hJ (c i).2 (c i).2) := by
      rw [hc, mul_inv_cancel_right]
    exact ((kerEquiv_eq_iff hv hJ ⟨_, hmem⟩ c).2 this).symm

section Surjective

variable {J : Ideal A} {T T' : Type} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']

def IsLiftAlong {X : Over (Spec (CommRingCat.of R))} (y₀ : sp (R₀ := R) (A ⧸ J) ⟶ X)
    (φ : A →ₐ[R] T) (y : sp T ⟶ X) : Prop :=
  ∀ (T₀ : Type) [CommRing T₀] [Algebra R T₀] (q : T →ₐ[R] T₀) (q₀ : (A ⧸ J) →ₐ[R] T₀),
    q.comp φ = q₀.comp (Ideal.Quotient.mkₐ R J) → spMap q ≫ y = spMap q₀ ≫ y₀

theorem IsLiftAlong.map {X : Over (Spec (CommRingCat.of R))} {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ X}
    {φ : A →ₐ[R] T} {y : sp T ⟶ X} (h : IsLiftAlong y₀ φ y) (ψ : T →ₐ[R] T') :
    IsLiftAlong y₀ (ψ.comp φ) (spMap ψ ≫ y) := by
  intro T₀ _ _ q q₀ hq
  rw [← Category.assoc, spMap_comp]
  exact h T₀ (q.comp ψ) q₀ (by rw [AlgHom.comp_assoc]; exact hq)

theorem isLiftAlong_of_quotient {X : Over (Spec (CommRingCat.of R))}
    {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ X} {φ : A →ₐ[R] T} {y : sp T ⟶ X}
    (h : spMap (Ideal.Quotient.mkₐ R (J.map φ)) ≫ y =
      spMap (Ideal.quotientMapₐ (J.map φ) φ Ideal.le_comap_map) ≫ y₀) : IsLiftAlong y₀ φ y := by
  intro T₀ _ _ q q₀ hq
  have hker : ∀ a ∈ J.map φ, q a = 0 := (fun a ha => RingHom.mem_ker.1 (Ideal.map_le_iff_le_comap.2 (fun b hb => Ideal.mem_comap.2 (RingHom.mem_ker.2 (by
        have := AlgHom.congr_fun hq b
        simpa [Ideal.Quotient.eq_zero_iff_mem.2 hb] using this))) ha))
  obtain ⟨q', rfl⟩ : ∃ q' : (T ⧸ J.map φ) →ₐ[R] T₀, q = q'.comp (Ideal.Quotient.mkₐ R _) :=
    ⟨Ideal.Quotient.liftₐ _ q hker, by ext a; rfl⟩
  have e2 : q₀ = q'.comp (Ideal.quotientMapₐ (J.map φ) φ Ideal.le_comap_map) := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (AlgHom.congr_fun hq a).symm
  subst e2
  rw [← spMap_comp, ← spMap_comp, Category.assoc, h, Category.assoc]

omit [IsCommMonObj G] [Smooth G.hom] in
theorem IsLiftAlong.mul {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G} {φ : A →ₐ[R] T} {y z : sp T ⟶ G}
    (h : IsLiftAlong y₀ φ y) (hz : z ∈ redKer G (J.map φ)) : IsLiftAlong y₀ φ (z * y) := by
  intro T₀ _ _ q q₀ hq
  have hz' : spMap q ≫ z = 1 := comp_eq_one_of_mem_redKer hz q (fun a ha => RingHom.mem_ker.1 (Ideal.map_le_iff_le_comap.2 (fun b hb => Ideal.mem_comap.2 (RingHom.mem_ker.2 (by
        have := AlgHom.congr_fun hq b
        simpa [Ideal.Quotient.eq_zero_iff_mem.2 hb] using this))) ha))
  rw [← ptsMap_apply, map_mul, ptsMap_apply, ptsMap_apply, hz', one_mul]
  exact h T₀ q q₀ hq

omit [Smooth G.hom] in
theorem IsLiftAlong.mul_inv_mem {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G} {φ : A →ₐ[R] T} {y y' : sp T ⟶ G}
    (h : IsLiftAlong y₀ φ y) (h' : IsLiftAlong y₀ φ y') : y * y'⁻¹ ∈ redKer G (J.map φ) := by
  have e : ∀ w, IsLiftAlong y₀ φ w → spMap (Ideal.Quotient.mkₐ R (J.map φ)) ≫ w =
      spMap (Ideal.quotientMapₐ (J.map φ) φ Ideal.le_comap_map) ≫ y₀ := fun w hw =>
    hw _ _ _ (by ext a; rfl)
  show y * y'⁻¹ ∈ (pointsMap G (Ideal.Quotient.mkₐ R (J.map φ))).ker
  rw [MonoidHom.mem_ker, map_mul, map_inv, ptsMap_apply, ptsMap_apply, e y h, e y' h', mul_inv_cancel]

theorem isLiftAlong_of_away {X : Over (Spec (CommRingCat.of R))} {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ X}
    {φ : A →ₐ[R] T} {y : sp T ⟶ X} {κ : Type} {s : κ → T} (hs : Ideal.span (Set.range s) = ⊤)
    (h : ∀ i, IsLiftAlong y₀ ((awayHom R (s i)).comp φ) (spMap (awayHom R (s i)) ≫ y)) :
    IsLiftAlong y₀ φ y := by
  intro T₀ _ _ q q₀ hq
  have hs' : Ideal.span (Set.range fun i => q (s i)) = ⊤ := span_range_map hs q
  apply away_ext hs' (fun i => awayHom R (q (s i))) (fun i => isAway_awayHom _)
  intro i
  obtain ⟨ψ, hψ⟩ := (isAway_awayHom (R := R) (s i)).lift ((awayHom R (q (s i))).comp q)
    (isAway_awayHom (R := R) (q (s i))).unit
  rw [← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, ← hψ, ← spMap_comp (awayHom R (s i)) ψ,
    Category.assoc]
  exact h i _ ψ _ (by rw [← AlgHom.comp_assoc, hψ, AlgHom.comp_assoc, hq, AlgHom.comp_assoc])

theorem exists_add_eq_of_isCoprime {T₁ T₂ T₁₂ : Type} [CommRing T₁] [Algebra R T₁] [CommRing T₂]
    [Algebra R T₂] [CommRing T₁₂] [Algebra R T₁₂] {f g : T} (hfg : IsCoprime f g)
    {ρ₁ : T →ₐ[R] T₁} {ρ₂ : T →ₐ[R] T₂} {ρ : T →ₐ[R] T₁₂} (h₁ : IsAway ρ₁ f) (h₂ : IsAway ρ₂ g)
    (h : IsAway ρ (f * g)) {a : T₁ →ₐ[R] T₁₂} {b : T₂ →ₐ[R] T₁₂} (ha : a.comp ρ₁ = ρ)
    (hb : b.comp ρ₂ = ρ) {I : Ideal T} {z : T₁₂} (hz : z ∈ I.map ρ) :
    ∃ z₁ ∈ I.map ρ₁, ∃ z₂ ∈ I.map ρ₂, z = a z₁ + b z₂ := by
  obtain ⟨N, x, hx, hzx⟩ := h.mem_map hz
  obtain ⟨u, w, huw⟩ := hfg.pow (m := N) (n := N)
  obtain ⟨e₁, he₁⟩ := h₁.unit.exists_left_inv
  obtain ⟨e₂, he₂⟩ := h₂.unit.exists_left_inv
  refine ⟨ρ₁ (w * x) * e₁ ^ N, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hx)),
    ρ₂ (u * x) * e₂ ^ N, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hx)), ?_⟩
  have ha' : ∀ t, a (ρ₁ t) = ρ t := fun t => by rw [← ha]; rfl
  have hb' : ∀ t, b (ρ₂ t) = ρ t := fun t => by rw [← hb]; rfl
  have P1 : a e₁ ^ N * ρ f ^ N = 1 := by rw [← mul_pow, ← ha', ← map_mul, he₁, map_one, one_pow]
  have P2 : b e₂ ^ N * ρ g ^ N = 1 := by rw [← mul_pow, ← hb', ← map_mul, he₂, map_one, one_pow]
  have key := congrArg ρ huw
  simp only [map_add, map_mul, map_pow, map_one] at key
  rw [map_mul] at hzx
  simp only [map_mul, map_pow, ha', hb']
  rw [← hzx]
  linear_combination (-z) * key - (ρ w * z * ρ g ^ N) * P1 - (ρ u * z * ρ f ^ N) * P2

private theorem ideal_map_map_le_map_comp {P Q S : Type} [CommRing P] [CommRing Q] [CommRing S] [Algebra R P]
    [Algebra R Q] [Algebra R S] (I : Ideal P) (p : P →ₐ[R] Q) (q : Q →ₐ[R] S) :
    (I.map p).map q ≤ I.map (q.comp p) :=
  Ideal.map_le_iff_le_comap.2 (Ideal.map_le_iff_le_comap.2 fun _ hx =>
    Ideal.mem_comap.2 (Ideal.mem_comap.2 (Ideal.mem_map_of_mem (q.comp p) hx)))

theorem exists_isLiftAlong_of_isCoprime (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥)
    {y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G} {φ : A →ₐ[R] T} {f g : T} (hfg : IsCoprime f g)
    {y₁ : sp (R₀ := R) (Localization.Away f) ⟶ G} {y₂ : sp (R₀ := R) (Localization.Away g) ⟶ G}
    (hy₁ : IsLiftAlong y₀ ((awayHom R f).comp φ) y₁)
    (hy₂ : IsLiftAlong y₀ ((awayHom R g).comp φ) y₂) : ∃ y, IsLiftAlong y₀ φ y := by
  have hfu : IsUnit (awayHom R (f * g) f * awayHom R (f * g) g) := by
    rw [← map_mul]; exact (isAway_awayHom (R := R) (f * g)).unit
  obtain ⟨a, ha⟩ := (isAway_awayHom (R := R) f).lift (awayHom R (f * g)) (isUnit_of_mul_isUnit_left hfu)
  obtain ⟨b, hb⟩ := (isAway_awayHom (R := R) g).lift (awayHom R (f * g)) (isUnit_of_mul_isUnit_right hfu)
  have hK : (J.map ((awayHom R (f * g)).comp φ)) ^ 2 = ⊥ := map_sq hJ _
  have hy₁' : IsLiftAlong y₀ ((awayHom R (f * g)).comp φ) (spMap a ≫ y₁) := by
    have := hy₁.map a; rwa [← AlgHom.comp_assoc, ha] at this
  have hy₂' : IsLiftAlong y₀ ((awayHom R (f * g)).comp φ) (spMap b ≫ y₂) := by
    have := hy₂.map b; rwa [← AlgHom.comp_assoc, hb] at this
  have hmem := hy₁'.mul_inv_mem hy₂'
  obtain ⟨-, hsurj⟩ := expBij (Localization.Away (f * g)) hv (J.map ((awayHom R (f * g)).comp φ)) hK
  obtain ⟨c, hc, hcJ, hcy⟩ := hsurj _ hmem
  have hcJ' : ∀ i, c i ∈ (J.map φ).map (awayHom R (f * g)) := fun i => by
      have h0 : J.map ((awayHom R (f * g)).comp φ) ≤ (J.map φ).map (awayHom R (f * g)) :=
        Ideal.map_le_iff_le_comap.2 fun _ hx => Ideal.mem_comap.2 (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem φ hx))
      exact h0 (hcJ i)
  choose z₁ hz₁ z₂ hz₂ hz using fun i => exists_add_eq_of_isCoprime (R := R) hfg (isAway_awayHom (R := R) f)
    (isAway_awayHom (R := R) g) (isAway_awayHom (R := R) (f * g)) ha hb (hcJ' i)
  have E1 : ∀ i, z₁ i ∈ J.map ((awayHom R f).comp φ) := fun i => ideal_map_map_le_map_comp J φ _ (hz₁ i)
  have E2 : ∀ i, z₂ i ∈ J.map ((awayHom R g).comp φ) := fun i => ideal_map_map_le_map_comp J φ _ (hz₂ i)
  have H1 : ((J.map φ).map (awayHom R f)).map a ≤ J.map ((awayHom R (f * g)).comp φ) := by
    refine (ideal_map_map_le_map_comp _ _ _).trans ?_
    rw [ha]; exact ideal_map_map_le_map_comp _ _ _
  have H2 : ((J.map φ).map (awayHom R g)).map b ≤ J.map ((awayHom R (f * g)).comp φ) := by
    refine (ideal_map_map_le_map_comp _ _ _).trans ?_
    rw [hb]; exact ideal_map_map_le_map_comp _ _ _
  have ma : ∀ i, a (z₁ i) ∈ J.map ((awayHom R (f * g)).comp φ) := fun i => H1 (Ideal.mem_map_of_mem a (hz₁ i))
  have mb : ∀ i, b (z₂ i) ∈ J.map ((awayHom R (f * g)).comp φ) := fun i => H2 (Ideal.mem_map_of_mem b (hz₂ i))
  have hL₁ : lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i)) ∈
      redKer G (J.map ((awayHom R f).comp φ)) := lieExp_mem_redKer hv.1 _ E1 _
  have hL₂ : lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i)) ∈
      redKer G (J.map ((awayHom R g).comp φ)) := lieExp_mem_redKer hv.1 _ E2 _
  have hl₁ := hy₁.mul (inv_mem hL₁)
  have hl₂ := hy₂.mul hL₂
  have e1 : lieExp v c hc = (spMap a ≫ lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i))) *
      (spMap b ≫ lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i))) := by
    rw [comp_lieExp, comp_lieExp, ← lieExp_add hv.1 _ _ _ _ (fun i => mul_eq_zero_of_sq hK (ma i) (mb i))
      (fun i => mul_eq_zero_of_sq hK (add_mem (ma i) (mb i)) (add_mem (ma i) (mb i)))]
    exact lieExp_congr v (fun i => hz i) _ _
  have key : spMap a ≫ ((lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i)))⁻¹ * y₁) =
      spMap b ≫ (lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i)) * y₂) := by
    rw [← ptsMap_apply G a, ← ptsMap_apply G b, map_mul, map_mul, map_inv, ptsMap_apply, ptsMap_apply,
      ptsMap_apply, ptsMap_apply]
    have : spMap a ≫ y₁ = (spMap a ≫ lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i))) *
        (spMap b ≫ lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i))) * (spMap b ≫ y₂) := by
      rw [← e1, ← hcy, inv_mul_cancel_right]
    rw [this, mul_assoc, inv_mul_cancel_left]
  have hs : Ideal.span (Set.range fun i : Bool => cond i f g) = ⊤ := by
    obtain ⟨u, w, huw⟩ := hfg
    refine (Ideal.eq_top_iff_one _).2 ?_
    rw [← huw]
    exact add_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨true, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨false, rfl⟩))
  obtain ⟨z, hzz⟩ := away_glue (X := G) hs (fun i => awayHom R (cond i f g)) (fun i => isAway_awayHom _)
    (fun i => Bool.rec (motive := fun i => sp (R₀ := R) (Localization.Away (cond i f g)) ⟶ G)
      (lieExp v z₂ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E2 i) (E2 i)) * y₂)
      ((lieExp v z₁ (fun i => mul_eq_zero_of_sq (map_sq hJ _) (E1 i) (E1 i)))⁻¹ * y₁) i)
    (by
      intro i j T₀ _ _ a' b' e
      cases i <;> cases j
      · have := (isAway_awayHom (R := R) g).ext e; subst this; rfl
      · exact (agree_of_isAway (isAway_awayHom (R := R) g) (isAway_awayHom (R := R) f) (hb.trans ha.symm)
          (by rw [hb, mul_comm]; exact isAway_awayHom _) key.symm T₀ a' b' e)
      · exact (agree_of_isAway (isAway_awayHom (R := R) f) (isAway_awayHom (R := R) g) (ha.trans hb.symm)
          (by rw [ha]; exact isAway_awayHom _) key T₀ a' b' e)
      · have := (isAway_awayHom (R := R) f).ext e; subst this; rfl)
  refine ⟨z, isLiftAlong_of_away hs fun i => ?_⟩
  rw [hzz i]
  cases i
  · exact hl₂
  · exact hl₁

theorem reduction_surjective (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥) :
    Function.Surjective (pointsMap G (Ideal.Quotient.mkₐ R J)) := by
  intro y₀
  have hzero : ∃ y : sp (Localization.Away (0 : A)) ⟶ G, IsLiftAlong y₀ (awayHom R 0) y := by
    refine ⟨1, fun T₀ _ _ q q₀ _ => ?_⟩
    have h01 : (0 : Localization.Away (0 : A)) = 1 := by
      have := (isAway_awayHom (R := R) (0 : A)).unit
      rw [map_zero] at this
      exact isUnit_zero_iff.1 this
    have : Subsingleton T₀ := subsingleton_of_zero_eq_one (by rw [← map_zero q, h01, map_one])
    have hs : Ideal.span (Set.range fun i : Empty => i.elim) = (⊤ : Ideal T₀) :=
      (Ideal.eq_top_iff_one _).2 (by rw [Subsingleton.elim (1 : T₀) 0]; exact zero_mem _)
    exact away_ext (X := G) (B := fun _ => T₀) hs (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
  have hmul : ∀ c f : A, (∃ y : sp (Localization.Away f) ⟶ G, IsLiftAlong y₀ (awayHom R f) y) →
      ∃ y : sp (Localization.Away (c * f)) ⟶ G, IsLiftAlong y₀ (awayHom R (c * f)) y := by
    rintro c f ⟨y, hy⟩
    have hu : IsUnit (awayHom R (c * f) c * awayHom R (c * f) f) := by
      rw [← map_mul]; exact (isAway_awayHom (R := R) (c * f)).unit
    obtain ⟨ψ, hψ⟩ := (isAway_awayHom (R := R) f).lift (awayHom R (c * f)) (isUnit_of_mul_isUnit_right hu)
    exact ⟨spMap ψ ≫ y, by have := hy.map ψ; rwa [hψ] at this⟩
  have hadd : ∀ f g : A, (∃ y : sp (Localization.Away f) ⟶ G, IsLiftAlong y₀ (awayHom R f) y) →
      (∃ y : sp (Localization.Away g) ⟶ G, IsLiftAlong y₀ (awayHom R g) y) →
      ∃ y : sp (Localization.Away (f + g)) ⟶ G, IsLiftAlong y₀ (awayHom R (f + g)) y := by
    rintro f g ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
    have hu : IsUnit (awayHom R (f + g) (f + g)) := (isAway_awayHom (R := R) (f + g)).unit
    have hcop : IsCoprime (awayHom R (f + g) f) (awayHom R (f + g) g) :=
      ⟨↑hu.unit⁻¹, ↑hu.unit⁻¹, by rw [← mul_add, ← map_add]; exact hu.val_inv_mul⟩
    obtain ⟨ψ₁, hψ₁⟩ := (isAway_awayHom (R := R) f).lift
      ((awayHom R (awayHom R (f + g) f)).comp (awayHom R (f + g))) (isAway_awayHom (R := R) (awayHom R (f + g) f)).unit
    obtain ⟨ψ₂, hψ₂⟩ := (isAway_awayHom (R := R) g).lift
      ((awayHom R (awayHom R (f + g) g)).comp (awayHom R (f + g))) (isAway_awayHom (R := R) (awayHom R (f + g) g)).unit
    have h1 : IsLiftAlong y₀ ((awayHom R (awayHom R (f + g) f)).comp (awayHom R (f + g))) (spMap ψ₁ ≫ y₁) := by
      have := hy₁.map ψ₁; rwa [hψ₁] at this
    have h2 : IsLiftAlong y₀ ((awayHom R (awayHom R (f + g) g)).comp (awayHom R (f + g))) (spMap ψ₂ ≫ y₂) := by
      have := hy₂.map ψ₂; rwa [hψ₂] at this
    exact exists_isLiftAlong_of_isCoprime hv hJ hcop h1 h2
  have hmax : ∀ m : Ideal A, m.IsMaximal →
      ∃ f ∈ {f : A | ∃ y : sp (Localization.Away f) ⟶ G, IsLiftAlong y₀ (awayHom R f) y}, f ∉ m := by
    intro m hm
    have := hm.isPrime
    have hJm : RingHom.ker (Ideal.Quotient.mkₐ R J) ≤ m := by
      intro x hx
      have hxJ : x ∈ J := by simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hx
      have h2 : x ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hxJ 2
      rw [hJ, Ideal.mem_bot] at h2
      exact hm.isPrime.mem_of_pow_mem 2 (h2 ▸ m.zero_mem)
    have hm' : (m.map (Ideal.Quotient.mkₐ R J)).IsPrime :=
      Ideal.map_isPrime_of_surjective (Ideal.Quotient.mkₐ_surjective R J) hJm
    obtain ⟨fb, hfb, B, _, _, j, hj, hchart⟩ := exists_local_chart y₀ _ hm'
    have := hj
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective R J fb
    refine ⟨f, ?_, fun hf => hfb (Ideal.mem_map_of_mem _ hf)⟩
    have hI : (J.map (awayHom R f)) ^ 2 = ⊥ := map_sq hJ _
    obtain ⟨ψ₀, hψ₀⟩ := hchart (Localization.Away f ⧸ J.map (awayHom R f))
      (Ideal.quotientMapₐ (J.map (awayHom R f)) (awayHom R f) Ideal.le_comap_map)
      ((isAway_awayHom (R := R) f).unit.map (Ideal.Quotient.mkₐ R (J.map (awayHom R f))))
    have := smooth_of_chart j
    refine ⟨spMap (Algebra.FormallySmooth.lift (J.map (awayHom R f)) ⟨2, hI.trans Ideal.zero_eq_bot.symm⟩ ψ₀) ≫ j,
      isLiftAlong_of_quotient ?_⟩
    rw [hψ₀, ← Category.assoc, spMap_comp]
    congr 2
    ext x
    exact Algebra.FormallySmooth.mk_lift _ _ _ x
  have hspan := span_eq_top_of_forall_maximal hmax
  have h1 : (1 : A) ∈ Ideal.span {f : A | ∃ y : sp (Localization.Away f) ⟶ G, IsLiftAlong y₀ (awayHom R f) y} :=
    hspan ▸ Submodule.mem_top
  have hL1 : ∃ y : sp (Localization.Away (1 : A)) ⟶ G, IsLiftAlong y₀ (awayHom R 1) y :=
    Submodule.span_induction (p := fun x _ => ∃ y : sp (Localization.Away x) ⟶ G, IsLiftAlong y₀ (awayHom R x) y)
      (fun x hx => hx) hzero (fun x y _ _ hx hy => hadd x y hx hy) (fun c x _ hx => hmul c x hx) h1
  obtain ⟨y1, hy1⟩ := hL1
  have hy1' : IsLiftAlong y₀ ((awayHom R (1 : A)).comp (AlgHom.id R A)) y1 := by rw [AlgHom.comp_id]; exact hy1
  obtain ⟨y, hy⟩ := exists_isLiftAlong_of_isCoprime hv hJ isCoprime_one_left hy1' hy1'
  refine ⟨y, ?_⟩
  have := hy (A ⧸ J) (Ideal.Quotient.mkₐ R J) (AlgHom.id R _) (by rw [AlgHom.comp_id, AlgHom.id_comp])
  rw [ptsMap_apply, this, spMap_id, Category.id_comp]

theorem reduction_surjective_of_isNilpotent (hv : IsLieBasis v) (hJ : IsNilpotent J) :
    Function.Surjective (pointsMap G (Ideal.Quotient.mkₐ R J)) := by
  have main : ∀ k : ℕ, ∀ (B : Type) [CommRing B] [Algebra R B] (I : Ideal B), I ^ (k + 1) = ⊥ →
      Function.Surjective (pointsMap G (Ideal.Quotient.mkₐ R I)) := by
    intro k
    induction k with
    | zero =>
      intro B _ _ I hI
      refine reduction_surjective hv (le_bot_iff.1 ?_)
      rw [← hI]; exact Ideal.pow_le_pow_right (by norm_num)
    | succ k ih =>
      intro B _ _ I hI
      have hle : I ^ (k + 1) ≤ I := Ideal.pow_le_self (by omega)
      have hsq : (I ^ (k + 1)) ^ 2 = ⊥ := by
        rw [← pow_mul]; exact le_bot_iff.1 (hI ▸ Ideal.pow_le_pow_right (by omega))
      have hmap : (I.map (Ideal.Quotient.mkₐ R (I ^ (k + 1)))) ^ (k + 1) = ⊥ := by
        rw [← Ideal.map_pow]
        exact (Ideal.map_eq_bot_iff_le_ker _).2 (by
          intro x hx
          simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hx)
      intro y₀
      let e := DoubleQuot.quotQuotEquivQuotOfLEₐ R hle
      obtain ⟨y₂, hy₂⟩ := ih _ _ hmap (spMap (e.symm : (B ⧸ I) →ₐ[R] _) ≫ y₀)
      obtain ⟨y, hy⟩ := reduction_surjective hv hsq y₂
      refine ⟨y, ?_⟩
      rw [ptsMap_apply] at hy₂ hy ⊢
      have he : Ideal.Quotient.mkₐ R I = (e : _ →ₐ[R] B ⧸ I).comp
          ((Ideal.Quotient.mkₐ R (I.map (Ideal.Quotient.mkₐ R (I ^ (k + 1))))).comp (Ideal.Quotient.mkₐ R (I ^ (k + 1)))) := by
        ext x; rfl
      rw [he, ← spMap_comp, ← spMap_comp]
      simp only [Category.assoc]
      rw [hy, hy₂, ← Category.assoc, spMap_comp, AlgEquiv.comp_symm, spMap_id, Category.id_comp]
  obtain ⟨k, hk⟩ := hJ
  refine main k A J (le_bot_iff.1 ?_)
  rw [← Ideal.zero_eq_bot, ← hk]
  exact Ideal.pow_le_pow_right (by omega)

theorem ptsMap_surjective_of_isNilpotent (hv : IsLieBasis v) (q : A →ₐ[R] A')
    (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q)) :
    Function.Surjective (pointsMap G q) := by
  intro y₀
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  obtain ⟨y, hy⟩ := reduction_surjective_of_isNilpotent hv hn (spMap (e.symm : A' →ₐ[R] _) ≫ y₀)
  refine ⟨y, ?_⟩
  rw [ptsMap_apply] at hy ⊢
  have he : q = (e : _ →ₐ[R] A').comp (Ideal.Quotient.mkₐ R (RingHom.ker q)) := by ext x; rfl
  rw [he, ← spMap_comp]
  simp only [Category.assoc]
  rw [hy, ← Category.assoc, spMap_comp, AlgEquiv.comp_symm, spMap_id, Category.id_comp]

end Surjective

end GlobalTheory.SqZero

namespace GlobalTheory

open SqZero

attribute [local instance] Over.cartesianMonoidalCategory

theorem sqZero_reduction_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Sp R))
    [GrpObj G] [IsCommMonObj G] [Smooth G.hom] :
    ∃ n : ℕ, ∀ (A : Type) [CommRing A] [Algebra R A] (J : Ideal A), J ^ 2 = ⊥ →
      Nonempty (Additive (redKer (R := R) G J) ≃+ (Fin n → J)) ∧
      (∀ y₀ : sp (R₀ := R) (A ⧸ J) ⟶ G, ∃ y : sp A ⟶ G, spMap (Ideal.Quotient.mkₐ R J) ≫ y = y₀) ∧
      ∀ k : ℕ, (∀ a ∈ J, k • a = 0) → ∀ y ∈ redKer (R := R) G J, y ^ k = 1 := by
  obtain ⟨n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G inferInstance
  refine ⟨n, fun A _ _ J hJ => ⟨⟨kerEquiv hv hJ⟩, fun y₀ => ?_, fun k hk y hy => pow_eq_one_of_mem_redKer hv hJ hk hy⟩⟩
  obtain ⟨y, hy⟩ := reduction_surjective hv hJ y₀
  exact ⟨y, by rw [← hy, ptsMap_apply]⟩

end GlobalTheory
