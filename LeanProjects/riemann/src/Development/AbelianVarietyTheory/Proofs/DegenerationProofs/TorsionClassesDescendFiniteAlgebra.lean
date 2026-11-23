import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescentSubring
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.TorsDesc

theorem s_mem_of_basis {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ) (g : N.Gt) {ι : Type}
    (e : Module.Basis ι ℤ N.X) (hθ : ∀ χ χ', N.θ (N.c χ) (N.c χ') g.b ∈ U) (he : ∀ l, g.s (e l) ∈ U) (χ : N.X) :
    g.s χ ∈ U := by
  have hχ : χ ∈ Submodule.span ℤ (Set.range e) := by rw [e.span_eq]; trivial
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hχ
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact he l
  | zero => rw [NumD.Gt.s_zero]; exact U.one_mem
  | add x y _ _ hx hy =>
    rw [eq_div_iff_mul_eq'.2 (g.mult x y)]
    exact U.div_mem (U.mul_mem hx hy) (hθ _ _)
  | neg x _ hx =>
    have := g.mult x (-x)
    rw [add_neg_cancel, NumD.Gt.s_zero, one_mul] at this
    exact (U.mul_mem_cancel_left hx).1 (this ▸ hθ _ _)

theorem s_mem_of_root {F : Type} [CommRing F] (N : NumD F) (U : Subgroup Fˣ)
    (hθ : ∀ x y u, N.θ x y u ∈ U) (hψ : ∀ χ, N.ψ χ ∈ U) {k : ℕ} (hU : ∀ u : Fˣ, u ^ k ∈ U → u ∈ U) (p : N.QT k)
    (χ : N.X) : p.1.2.s χ ∈ U := by
  refine hU _ ?_
  rw [← NumD.Gt.pow_s, N.mem_QT.1 p.2, NumD.io_s]
  exact U.mul_mem (U.div_mem (U.div_mem (hψ _) (hψ _)) (hψ _)) (U.prod_mem fun _ _ => hθ _ _ _)

theorem exists_finite_subalgebra (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F]
    (K : IntermediateField (FractionRing O) F) [FiniteDimensional (FractionRing O) K] :
    ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∀ x ∈ K, IsIntegral O x → x ∈ O₁ := by
  have : CharZero (FractionRing O) := IsFractionRing.charZero_of_isFractionRing O
  have : Module.Finite O (integralClosure O K) := IsIntegralClosure.finite O (FractionRing O) K _
  let v : K →ₐ[O] F := { K.val.toRingHom with commutes' := fun _ => rfl }
  have hv : Function.Injective v := Subtype.val_injective
  refine ⟨(integralClosure O K).map v, Module.Finite.equiv ((integralClosure O K).equivMapOfInjective v hv).toLinearEquiv,
    fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (isIntegral_algHom_iff v hv).1 hi

theorem descend : ∀ (O F : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CharZero O] [Field F] [Algebra (FractionRing O) F] [Algebra O F] [IsScalarTower O (FractionRing O) F] [Algebra.IsAlgebraic (FractionRing O) F] (S : ValuationSubring F), (∀ x, x ∈ S ↔ IsIntegral O x) → ∀ (N : NumD F) (K₁ : IntermediateField (FractionRing O) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing O) K₁ → (∀ χ, N.c χ ∈ A₀) → (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) → (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) → (∀ x ∈ A₀, N.th x ∈ K₁) → (∀ χ, (N.ψ χ : F) ∈ K₁) → (∀ x y u, S.valuation (N.θ x y u : F) = 1) → (∀ x, S.valuation (N.σ x : F) = 1) → (∀ x, N.th x ∈ S) → (∀ χ, S.valuation (N.ψ χ : F) = 1) → ∀ (Ix : Type) [Finite Ix] (k : Ix → ℕ) (p : ∀ i, N.QT (k i)), (∀ i, 0 < k i) → (∀ i, (p i).1.2.b ∈ A₀) → ∃ O₁ : Subalgebra O F, Module.Finite O O₁ ∧ ∃ (N₀ : NumD O₁) (I : NumD.Hom O₁.val.toRingHom N₀ N), I.lam = 1 ∧ ∀ i (p' : N.QT (k i)), N.QEq (p i) p' → ∃ p₀ : N₀.QT (k i), p'.1.1.toAdd = I.e p₀.1.1.toAdd ∧ I.Rel p₀.1.2 p'.1.2 := by
  intro O F _ _ _ _ _ _ _ _ _ _ S hS N K₁ A₀ hK hc hθ hσ hth hψ vθ vσ vth vψ Ix _ k p hk hp
  let e := Module.Free.chooseBasis ℤ N.X
  let T : Set F := Set.range fun il : Ix × Module.Free.ChooseBasisIndex ℤ N.X => ((p il.1).1.2.s (e il.2) : F)
  have : Finite T := (Set.finite_range _).to_subtype
  have : FiniteDimensional (FractionRing O) (IntermediateField.adjoin (FractionRing O) T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let K₂ := K₁ ⊔ IntermediateField.adjoin (FractionRing O) T
  have : FiniteDimensional (FractionRing O) K₂ := IntermediateField.finiteDimensional_sup _ _
  have h12 : K₁ ≤ K₂ := le_sup_left
  obtain ⟨O₁, hfin, hO⟩ := exists_finite_subalgebra O F K₂
  have hunit : ∀ u : Fˣ, (u : F) ∈ K₂ → S.valuation (u : F) = 1 → ∃ a : O₁ˣ, O₁.val.toRingHom a = u := by
    intro u hu hv
    have h1 : (u : F) ∈ O₁ := hO _ hu ((hS _).1 ((S.valuation_le_one_iff _).1 hv.le))
    have h2 : ((u⁻¹ : Fˣ) : F) ∈ O₁ := by
      rw [Units.val_inv_eq_inv_val]
      exact hO _ (K₂.inv_mem hu) ((hS _).1 ((S.valuation_le_one_iff _).1 (by rw [map_inv₀, hv, inv_one])))
    exact ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, rfl⟩
  let U : Subgroup Fˣ :=
    { carrier := {u | (u : F) ∈ K₂}
      mul_mem' := fun ha hb => K₂.mul_mem ha hb
      one_mem' := K₂.one_mem
      inv_mem' := fun {u} hu => by
        change ((u⁻¹ : Fˣ) : F) ∈ K₂
        rw [Units.val_inv_eq_inv_val]
        exact K₂.inv_mem hu }
  let V : Subgroup Fˣ := (S.valuation.toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom F)).ker
  obtain ⟨N₀, I, hI, h⟩ := GlobalTheory.Ex.NumD.exists_descent_subring O₁ F O₁.val.toRingHom Subtype.val_injective N A₀ hc
    (fun x hx y hy u hu => hunit _ (h12 (hθ x hx y hy u hu)) (vθ _ _ _))
    (fun x hx => hunit _ (h12 (hσ x hx)) (vσ _))
    (fun x hx => ⟨⟨_, hO _ (h12 (hth x hx)) ((hS _).1 (vth x))⟩, rfl⟩)
    (fun χ => hunit _ (h12 (hψ χ)) (vψ _))
  refine ⟨O₁, hfin, N₀, I, hI, fun i p' ⟨z, _, hz⟩ => h _ p' ?_ fun χ => hunit _ ?_ ?_⟩
  · rw [hz]
    exact A₀.mul_mem (hp i) (hc z)
  · have h1 : (p i).1.2.s χ ∈ U := s_mem_of_basis N U _ e (fun χ χ' => h12 (hθ _ (hc _) _ (hc _) _ (hp i)))
      (fun l => (le_sup_right : _ ≤ K₂) (IntermediateField.subset_adjoin _ _ ⟨(i, l), rfl⟩)) χ
    have hψU : ∀ χ, N.ψ χ ∈ U := fun χ => h12 (hψ χ)
    change p'.1.2.s χ ∈ U
    rw [hz, NumD.Gt.mul_s]
    exact U.div_mem (U.mul_mem h1 (U.div_mem (U.div_mem (hψU _) (hψU _)) (hψU _)))
      (h12 (hθ _ (hc _) _ (hp i) _ (hc z)))
  · refine s_mem_of_root N V vθ vψ (fun u hu => ?_) p' χ
    have : S.valuation (u : F) ^ k i = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val]; exact hu
    exact (pow_eq_one_iff_of_nonneg zero_le (hk i).ne').1 this

end GlobalTheory.Ex.TorsDesc
