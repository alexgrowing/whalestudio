import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibresStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace ExpUniqFamily

theorem linear_eq_zero_of_discrete {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ)) [DiscreteTopology Λ]
    (f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, f z ∈ Λ) (z : Fin g → ℂ) : f z = 0 := by
  have hc : Continuous (fun z => (⟨f z, hf z⟩ : Λ)) :=
    f.continuous_of_finiteDimensional.subtype_mk _
  have := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hc (x := z) (y := 0))
  simpa using this

theorem eq_iff_sub {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    (z w : V) : e z = e w ↔ e (z - w) = 1 := by
  have h := he (z - w) w
  rw [sub_add_cancel] at h
  rw [h]
  exact mul_eq_right

theorem int_eq_of_exp (n n' : ℤ)
    (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n' : ℂ) / k)) : n = n' := by
  have hk : 0 < (n' - n).natAbs + 1 := Nat.succ_pos _
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  generalize hkk : (n' - n).natAbs + 1 = k at hk hm
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : ((n' - n : ℤ) : ℂ) = ((k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hm ⊢
    linear_combination hm
  have h4 : n' - n = k * m := Int.cast_injective h3
  have h5 : n' - n = 0 := Int.eq_zero_of_abs_lt_dvd (m := k) ⟨m, h4⟩ (by
    rw [← hkk, Int.abs_eq_natAbs]; push_cast; omega)
  omega

theorem algebraic {O Q L L' : Type} [CommRing O] [Group Q] [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] {g : ℕ} (χ : Fin g → O → ℂ) (P : L →+ (Fin g → ℂ)) (P' : L' →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x i, P (a • x) i = χ i a * P x i) (hP' : ∀ (a : O) x i, P' (a • x) i = χ i a * P' x i)
    (iP : Function.Injective P) (iP' : Function.Injective P')
    (dP : DiscreteTopology P.range) (dP' : DiscreteTopology P'.range)
    (e e' : (Fin g → ℂ) → Q) (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (act : O → Q → Q) (hl : ∀ a z, e (fun k => χ k a * z k) = act a (e z))
    (hl' : ∀ a z, e' (fun k => χ k a * z k) = act a (e' z))
    (f f' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hf : ∀ z, e' (f z) = e z) (hf' : ∀ z, e (f' z) = e' z) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : L ≃ₗ[O] L'), (∀ z, e' (h z) = e z) ∧
      (∀ a, P' (gam a) = h (P a)) ∧
      ∀ (k : ℕ) a b, 0 < k → e ((k : ℂ)⁻¹ • P a) = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  have h1 : ∀ z, f' (f z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P.range (f' ∘ₗ f - LinearMap.id) (fun z => (hk _).1 <|
      (eq_iff_sub e ha _ _).1 (by simp [hf, hf'])) z
  have h2 : ∀ z, f (f' z) = z := fun z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ f' - LinearMap.id) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp [hf, hf'])) z
  let d : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => LinearMap.pi fun k => χ k a • LinearMap.proj k
  have hd : ∀ a z, d a z = fun k => χ k a * z k := fun a z => rfl
  have h3 : ∀ a z, f (d a z) = d a (f z) := fun a z => sub_eq_zero.1 <|
    linear_eq_zero_of_discrete P'.range (f ∘ₗ d a - d a ∘ₗ f) (fun z => (hk' _).1 <|
      (eq_iff_sub e' ha' _ _).1 (by simp only [LinearMap.comp_apply, hf, hd, hl, hl'])) z
  have m1 : ∀ a, ∃ b, P' b = f (P a) := fun a => (hk' _).1 (by rw [hf]; exact (hk _).2 ⟨a, rfl⟩)
  have m2 : ∀ b, ∃ a, P a = f' (P' b) := fun b => (hk _).1 (by rw [hf']; exact (hk' _).2 ⟨b, rfl⟩)
  choose ga hga using m1
  choose de hde using m2
  let gam : L ≃ₗ[O] L' :=
    { toFun := ga
      invFun := de
      map_add' := fun a b => iP' (by simp [hga])
      map_smul' := fun c a => iP' (by
        have e1 : P (c • a) = d c (P a) := funext fun i => hP c a i
        have e2 : P' (c • ga a) = d c (P' (ga a)) := funext fun i => hP' c _ i
        rw [RingHom.id_apply, hga, e1, e2, hga, h3])
      left_inv := fun a => iP (by rw [hde, hga, h1])
      right_inv := fun b => iP' (by rw [hga, hde, h2]) }
  refine ⟨LinearEquiv.ofLinear f f' (LinearMap.ext h2) (LinearMap.ext h1), gam, hf, hga, ?_⟩
  intro k a b hk0 hab
  have hk1 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
  rw [← hf, map_smul, ← hga, eq_iff_sub e' ha', hk'] at hab
  obtain ⟨c, hc⟩ := hab
  refine ⟨c, iP' ?_⟩
  show P' (ga a) = _
  rw [map_add, map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hk1, one_smul]
  abel

theorem isHolTo_fibre {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {X : Scheme.{0}} (y : V × W → (Sp ℂ ⟶ X)) (h : IsHolTo (Set.univ ×ˢ Set.univ) y) (b : V) :
    IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hd : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, ?_⟩
  · have := h1.preimage hd.continuous
    convert this using 1
    ext z
    simp
  · exact h2.comp hd.differentiableOn (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_ex {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (U.Di i) ty P) : IsHolTo Set.univ (fun z => (U.ex i P z).left) :=
  isHolTo_fibre _ (U.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2 0

theorem fibrewise {X : Scheme.{0}} (t : SAB H X) (D₁ D₂ : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (y y' : Sp ℂ ⟶ X) (hy : y = y') (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ t.G))
    (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (hl : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (hl' : ∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t.act.act a)
    (hw : ∀ (k : ℕ) (a b : D₁.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₁.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hw' : ∀ (k : ℕ) (a b : D₂.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₂.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c))
    (hh : IsHolTo Set.univ (fun z => (e z).left)) (hh' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd : (∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
      ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
        ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (hd' : (∀ w, ∃! v : epsPt y' ⟶ t.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧
      ∀ v : epsPt y' ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La ≃ₗ[𝓞 E] D₂.La), (∀ z, (e' (h z)).left = (e z).left) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', D₂.EF (gam a) (gam a') = D₁.EF a a') ∧
      ∀ (k : ℕ) (s : 𝟙_ (Over X) ⟶ t.G) a b, 0 < k → toUnit _ ≫ s = e ((k : ℂ)⁻¹ • P a) →
        toUnit _ ≫ s = e' ((k : ℂ)⁻¹ • P' b) → ∃ c, gam a = b + k • c := by
  subst hy
  have dk : DiscreteTopology {z // e z = 1} := by
    have h0 : (fun z => e z = 1) = fun z => z ∈ P.range := funext fun z => propext (hk z)
    show DiscreteTopology (Subtype fun z => e z = 1)
    rw [h0]
    exact hP.2.2.1
  have dk' : DiscreteTopology {z // e' z = 1} := by
    have h0 : (fun z => e' z = 1) = fun z => z ∈ P'.range := funext fun z => propext (hk' z)
    show DiscreteTopology (Subtype fun z => e' z = 1)
    rw [h0]
    exact hP'.2.2.1
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres X X t.G t.G y y g g e e' (𝟙 _) (MonoidHom.id _) t.semi.smooth ha ha' hh hh' hd' dk'
    (Category.id_comp _) (fun _ => Category.comp_id _)
  obtain ⟨f', hf', -⟩ := GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres X X t.G t.G y y g g e' e (𝟙 _) (MonoidHom.id _) t.semi.smooth ha' ha hh' hh hd dk
    (Category.id_comp _) (fun _ => Category.comp_id _)
  obtain ⟨h, gam, h1, h2, h3⟩ := algebraic (fun k (a : 𝓞 E) => ty k (a : E)) P P' hP.1 hP'.1 hP.2.1 hP'.2.1
    hP.2.2.1 hP'.2.2.1 e e' ha ha' hk hk' (fun a x => x ≫ t.act.act a) hl hl' f f' hf hf'
  refine ⟨h, gam, fun z => by rw [h1], h2, fun a a' => ?_, fun k s a b hk0 e1 e2 => h3 k a b hk0 (e1.symm.trans e2)⟩
  refine int_eq_of_exp _ _ fun k hk0 => ?_
  have w1 := hw k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  have w2 := hw' k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  rw [h2, h2, ← map_smul h, ← map_smul h, h1, h1] at w2
  exact congrArg Units.val (weilIs_unique_fieldPoint X t.G t.PP.L t.PP.isLB ℂ y k _ _ _ _ w2 w1)

end ExpUniqFamily

theorem familyUnif_exp_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i j : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (P' : (U.Di j).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → IsPeriod (U.Di j) ty P' → U.u i P = U.u j P' → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ z, (U.ex j P' (h z)).left = (U.ex i P z).left) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', (U.Di j).EF (gam a) (gam a') = (U.Di i).EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t j a + l.M • e) ∧ ∀ a, ∃ e, gam (U.t i a) = U.t j a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i j P P' hP hP' hu
  obtain ⟨h, gam, h1, h2, h3, h4⟩ := ExpUniqFamily.fibrewise Xo.univ.t (U.Di i) (U.Di j) ty P P' hP hP' _ _ hu
    (U.ex i P) (U.ex j P') (U.ex_add i P hP) (U.ex_add j P' hP') (U.ex_ker i P hP) (U.ex_ker j P' hP')
    (U.ex_lin i P hP) (U.ex_lin j P' hP') (U.ex_weil i P hP) (U.ex_weil j P' hP')
    (ExpUniqFamily.isHolTo_ex U i P hP) (ExpUniqFamily.isHolTo_ex U j P' hP') (U.ex_diff i P hP) (U.ex_diff j P' hP')
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  exact ⟨h, gam, h1, h2, h3,
    fun a ha => h4 l.M _ _ _ hM (U.ex_eta i P hP a ha) (U.ex_eta j P' hP' a ha),
    fun a => h4 l.A _ _ _ l.A_pos (U.ex_etaA i P hP a) (U.ex_etaA j P' hP' a)⟩

end GlobalTheory
