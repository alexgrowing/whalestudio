import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.T2SpacePtsOverOfIsSeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {g : ℕ}

def ReadsPeriods (t : SAB H S) {T : Over S} (c₀ : ℂˣ → Γ(T.left, ⊤)ˣ) (D : Datum H) (ty : Fin g → (E →+* ℂ))
    (P : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (T ⟶ t.G)) : Prop :=
  (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧
    ∀ (k : ℕ) (a a₂ : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a a₂ : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (c₀ c)

theorem int_eq_of_exp_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  have hk : 0 < (n - m).natAbs + 1 := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  have h0 : (((n - m).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = ((((n - m).natAbs + 1 : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((n - m).natAbs + 1 : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem discrete_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    DiscreteTopology P.range.toIntSubmodule := hP.2.2.1

theorem countable_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    (P.range : Set (Fin g → ℂ)).Countable :=
  have := hP.2.2.1
  countable_of_isDiscrete_finiteDimensional DiscreteTopology.isDiscrete

theorem exists_linearEquiv_of_period {t : SAB H S} {y : Sp ℂ ⟶ S} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {g₀ : ℕ} {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ t.G)}
    (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t.semi.separated
  have := discrete_periods hP
  have : IsZLattice ℝ P.range.toIntSubmodule := ⟨hP.2.2.2.1⟩
  exact he.exists_linearEquiv P.range.toIntSubmodule hk ha hs hh hc

theorem exists_isometry {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 he.1 he.2.1 he.2.2.1
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add, hr₀, hr₀, hr₀, map_add, map_add])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

theorem div_eq_iff {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)} (hP : Function.Injective P)
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n)
    (a b : L) : e ((n : ℂ)⁻¹ • P a) = e ((n : ℂ)⁻¹ • P b) ↔ ∃ x, a = b + n • x := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [eq_iff_sub_of_add he, hk, ← smul_sub, ← map_sub]
  refine exists_congr fun x => ?_
  rw [eq_inv_smul_iff₀ h0, Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.eq_iff, eq_sub_iff_add_eq', eq_comm]

theorem exists_div_of_pow {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)}
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n) {x : Q} (hx : x ^ n = 1) :
    ∃ a, x = e ((n : ℂ)⁻¹ • P a) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨z, rfl⟩ := hs x
  have hp : ∀ m : ℕ, e (m • z) = e z ^ m := fun m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, map_zero_of_add he]
    | succ m ih => rw [succ_nsmul, he, ih, pow_succ]
  obtain ⟨a, ha⟩ := (hk _).1 ((hp n).trans hx)
  exact ⟨a, by rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]⟩

theorem exists_pointEquiv {S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {y : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G y φ) :
    ∃ β : (𝟙_ (Over S') ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (β x).left = x.left ≫ φ := by
  have w : ∀ x : 𝟙_ (Over S') ⟶ G', x.left ≫ G'.hom = 𝟙 S' := fun x => Over.w x
  let f : (𝟙_ (Over S') ⟶ G') → (Over.mk y ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = y
    rw [Category.assoc, h.1.w, ← Category.assoc, w]
    exact Category.id_comp y)
  have hb : Function.Bijective f := by
    refine ⟨fun a b hab => Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((w a).trans (w b).symm)),
      fun x => ?_⟩
    have hx : x.left ≫ G.hom = 𝟙 S' ≫ y := (Over.w x).trans (Category.id_comp y).symm
    exact ⟨Over.homMk (h.1.lift x.left (𝟙 S') hx) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ hx)⟩
  refine ⟨⟨Equiv.ofBijective f hb, fun a b => Over.OverMorphism.ext ?_⟩, fun _ => rfl⟩
  exact (h.2 _ a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm.trans
    (mul_left_congr (Category.id_comp y) _ _ _ _ rfl rfl)

theorem weilIs_congr {X : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {a b : X ⟶ S} (h : a = b) {k : ℤ}
    {x y : Over.mk a ⟶ G} {x' y' : Over.mk b ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left)
    {c : Γ(X, ⊤)ˣ} (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst h
  rwa [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]

def WeilPull : Prop :=
  ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) →
    ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ),
      x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c)

theorem exists_fibre (hW : WeilPull) {t : SAB H S} {y : Sp ℂ ⟶ S} {t₁ : SAB H (Sp ℂ)} (m : SABMap t₁ t y)
    {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (hr : ReadsPeriods t unitOn D ty P e) :
    ∃ e₁ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t₁.G), (∀ z, (e₁ z).left ≫ m.φ = (e z).left) ∧
      (∀ z w, e₁ (z + w) = e₁ z * e₁ w) ∧ Function.Surjective e₁ ∧ ReadsPeriods t₁ unitOn D ty P e₁ ∧
      ∀ (g₀ : ℕ) (u : HolUnif t₁.G t₁.PP.L g₀), ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e₁ (h z) = u.ex z := by
  obtain ⟨β, hβ⟩ := exists_pointEquiv m.cart
  have h₁ : ∀ z, (β.symm (e z)).left ≫ m.φ = (e z).left := fun z => by rw [← hβ, β.apply_symm_apply]
  refine ⟨fun z => β.symm (e z), h₁, fun z w => by simp only [he.1, map_mul], β.symm.surjective.comp he.2.1,
    ⟨fun z => by rw [← hr.1, β.symm.map_eq_one_iff], fun a z => ?_, fun k a b c hk hc => ?_⟩, fun g₀ u => ?_⟩
  · apply β.injective
    rw [β.apply_symm_apply, hr.2.1]
    apply Over.OverMorphism.ext
    rw [hβ, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, h₁]
  · obtain ⟨w, hw, -⟩ := m.lin
    refine (hW _ _ t.G t₁.G y m.φ _ _ t.PP.isLB t₁.PP.isLB m.cart ⟨w, hw⟩ _ k _ _ (pushPt m.cart.1.w _)
      (pushPt m.cart.1.w _) _ rfl rfl).2 ?_
    exact weilIs_congr (Category.id_comp y).symm (h₁ _).symm (h₁ _).symm (hr.2.2 k a b c hk hc)
  · have := u.discrete
    obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP he hr.1 (e₀ := fun z => β (u.ex z))
      (fun z w => by rw [u.ex_add, map_mul]) (β.surjective.comp u.ex_onto) (fun U f => by
        have k := u.hol (m.φ ⁻¹ᵁ U) ((m.φ.app U).hom f)
        simp only [hβ, Set.mem_univ, true_and, Points.valAt'_eq_valR] at k ⊢
        have k₂ : ∀ z, valR ((u.ex z).left ≫ m.φ) U f = valR (u.ex z).left (m.φ ⁻¹ᵁ U) ((m.φ.app U).hom f) :=
          fun z => Points.valR_comp (C := ℂ) (u.ex z).left m.φ U f
        exact ⟨k.1, k.2.congr fun z _ => k₂ z⟩)
      ((countable_of_isDiscrete_finiteDimensional (s := (u.Λ : Set (Fin g₀ → ℂ)))
        DiscreteTopology.isDiscrete).mono fun z hz => (u.ker z).1 (β.map_eq_one_iff.1 hz))
    exact ⟨h, fun z => by simp only [hh, β.symm_apply_apply]⟩

end GlobalTheory.UnifPoint
