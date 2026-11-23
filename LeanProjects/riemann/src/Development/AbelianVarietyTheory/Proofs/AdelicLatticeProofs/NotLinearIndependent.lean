import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableExpMulOfAnnihilatedStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatBilinForm

open Matrix

namespace GlobalTheory.VacuumLine

theorem exists_coord {U : Type} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    (J : U →ₗ[ℝ] U) (hJ : ∀ x, J (J x) = -x) :
    ∃ (g : ℕ) (e : U ≃ₗ[ℝ] (Fin g → ℂ)), ∀ v, e (J v) = Complex.I • e v := by
  let φ : ℂ →ₐ[ℝ] Module.End ℝ U := Complex.liftAux (J : Module.End ℝ U) (by ext x; simp [hJ])
  letI : Module ℂ U := Module.compHom U (φ : ℂ →+* Module.End ℝ U)
  have hsm : ∀ (z : ℂ) (v : U), z • v = z.re • v + z.im • J v := fun z v => by
    change φ z v = _
    simp [φ, Complex.liftAux_apply]
  haveI : IsScalarTower ℝ ℂ U := ⟨fun r z v => by
    simp [hsm, smul_add, smul_smul]⟩
  haveI : FiniteDimensional ℂ U := Module.Finite.of_restrictScalars_finite ℝ ℂ U
  have hI : ∀ v : U, Complex.I • v = J v := fun v => by simp [hsm]
  let e := (Module.finBasis ℂ U).equivFun
  exact ⟨_, e.restrictScalars ℝ, fun v => by rw [← hI]; exact e.map_smul _ _⟩

theorem exists_ratForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hN : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v, (B u v : ℝ) = -om (p u) (p v) := by
  first
  | exact @_root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm
  | exact _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm
  | (apply _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> assumption)
  | (intros; apply _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RationalValueRealScalar.exists_rat_bilinForm ..)

theorem span_image {U : Type} [AddCommGroup U] [Module ℝ U]
    {V : Type} [AddCommGroup V] (p : V →+ U) (hsp : Submodule.span ℝ (Set.range p) = ⊤)
    (L : AddSubgroup V) (hN : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L) :
    Submodule.span ℝ (p '' (L : Set V)) = ⊤ := by
  rw [eq_top_iff, ← hsp, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨N, hN0, hx⟩ := hN x
  have h0 : (N : ℝ) ≠ 0 := by positivity
  have : p x = (N : ℝ)⁻¹ • p (N • x) := by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ h0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)

theorem fg_of_integral {U : Type} [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U]
    (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (hom : ∀ x, om x = 0 → x = 0)
    {V : Type} [AddCommGroup V] (p : V →+ U) (hp : Function.Injective p) (L : AddSubgroup V)
    (hsp : Submodule.span ℝ (p '' (L : Set V)) = ⊤)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) :
    (AddSubgroup.toIntSubmodule L).FG := by
  have hfg : (Submodule.span ℝ (p '' (L : Set V))).FG := hsp ▸ Module.Finite.fg_top
  obtain ⟨s, hs, hss⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  rw [hsp] at hss
  have h : ∀ (x : AddSubgroup.toIntSubmodule L) (y : s), ∃ k : ℤ, (k : ℝ) = om (p x) y := by
    rintro x ⟨y, hy⟩
    obtain ⟨y, hy', rfl⟩ := hs hy
    obtain ⟨k, hk⟩ := hint x x.2 y hy'
    exact ⟨k, hk.symm⟩
  choose k hk using h
  let φ : AddSubgroup.toIntSubmodule L →+ (s → ℤ) := AddMonoidHom.mk' k fun a b => by
    funext y
    apply Int.cast_injective (α := ℝ)
    simp [hk]
  have hφ : Function.Injective φ.toIntLinearMap := by
    refine (injective_iff_map_eq_zero _).2 fun x hx => Subtype.ext (hp ?_)
    rw [ZeroMemClass.coe_zero, map_zero]
    refine hom _ (LinearMap.ext_on hss.symm fun y hy => ?_)
    have : k x ⟨y, hy⟩ = 0 := congrFun hx ⟨y, hy⟩
    have h2 := hk x ⟨y, hy⟩
    rw [this] at h2
    simpa using h2.symm
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective _ hφ)

theorem not_linearIndependent : ∀ (U : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] (J : U →ₗ[ℝ] U) (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ), (∀ x, J (J x) = -x) → (∀ x y, om x y = -om y x) → (∀ x y, om (J x) (J y) = om x y) → (∀ x, x ≠ 0 → om (J x) x < 0) → ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (p : V →+ U), Function.Injective p → Submodule.span ℝ (Set.range p) = ⊤ → ∀ L : AddSubgroup V, (∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L) → (∀ x : V, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ f : Fin 2 → U → ℂ, (∀ k, Differentiable ℝ (f k)) → (∀ k w z, (fderiv ℝ (f k) w z - Real.pi * Complex.I * (om w z : ℂ) * f k w) + Complex.I * (fderiv ℝ (f k) w (J z) - Real.pi * Complex.I * (om w (J z) : ℂ) * f k w) = 0) → (∀ k, ∀ v ∈ L, ∀ z, f k (z + p v) = c v * Complex.exp (-(Real.pi * Complex.I) * (om z (p v) : ℂ)) * f k z) → ¬ LinearIndependent ℂ f := by
  intro U _ _ _ J om hJ halt hinv hpos V _ _ _ p hp hsp L hN hL c hc f hd hann hf hli
  obtain ⟨g, e, he⟩ := exists_coord J hJ
  have hs : ∀ z, e.symm (Complex.I • z) = J (e.symm z) := fun z => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  obtain ⟨Hm, hH, hHpos, hHim⟩ := GlobalTheory.PeriodNonempty.exists_herm
    (-(om.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap))
    (fun x y => by simp [halt (e.symm x)]) (fun x y => by simp [hs, hinv])
    (fun x hx => by simpa [hs] using hpos (e.symm x) (by simpa using hx))
  have him : ∀ x y, (x ⬝ᵥ Hm.mulVec (star y)).im = -om (e.symm x) (e.symm y) := hHim
  have hpos' : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := hHpos
  have hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k := fun x hx => (hL x).1 hx
  obtain ⟨B, hB⟩ := exists_ratForm om p L hN hint
  have hspL := span_image p hsp L hN
  have hom : ∀ x, om x = 0 → x = 0 := fun x hx => by
    by_contra h
    have := hpos x h
    rw [halt, hx] at this
    simp at this
  have hfg := fg_of_integral om hom p hp L hspL hint
  let P : V →ₗ[ℤ] (Fin g → ℂ) := (e.toLinearMap.toAddMonoidHom.comp p).toIntLinearMap
  have hP : ∀ v, P v = e (p v) := fun _ => rfl
  let E : (Fin g → ℂ) →L[ℝ] U := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  have hE : ∀ z, E z = e.symm z := fun _ => rfl
  have hconj : ∀ x y : Fin g → ℂ,
      x ⬝ᵥ Hm.mulVec (star y) = starRingEnd ℂ (y ⬝ᵥ Hm.mulVec (star x)) := fun x y => by
    change _ = star _
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  refine GlobalTheory.Dict.ThetaOne.proportional_of_selfDual B P (e.injective.comp hp)
    (AddSubgroup.toIntSubmodule L) hfg ?_ ?_ hH hpos' ?_ c hc
    (fun k w => Complex.exp (Real.pi / 2 * (w ⬝ᵥ Hm.mulVec (star w))) * f k (e.symm w)) ?_ ?_ ?_
  · intro x
    refine (hL x).trans (forall₂_congr fun y _ => ⟨?_, ?_⟩)
    · rintro ⟨k, hk⟩
      refine ⟨-k, Rat.cast_injective (α := ℝ) ?_⟩
      rw [hB, hk]; simp
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      have := hB x y
      rw [hk] at this
      push_cast at this ⊢
      linarith
  · have : P '' (AddSubgroup.toIntSubmodule L : Set V) = e.toLinearMap '' (p '' (L : Set V)) := by
      rw [Set.image_image]; rfl
    rw [this, ← Submodule.map_span, hspL, Submodule.map_top, LinearEquiv.range]
  · intro u v
    rw [him, hB, hP, hP, e.symm_apply_apply, e.symm_apply_apply]
  · intro k
    refine GlobalTheory.T.differentiable_exp_mul_of_annihilated' g Hm hH (fun w => f k (E w)) ((hd k).comp E.differentiable) fun w z => ?_
    have h1 : fderiv ℝ (fun w => f k (E w)) w = (fderiv ℝ (f k) (E w)).comp E :=
      ((hd k (E w)).hasFDerivAt.comp w E.hasFDerivAt).fderiv
    have h2 := hann k (e.symm w) (e.symm z)
    rw [h1]
    simp only [ContinuousLinearMap.comp_apply, hE, him, hs]
    push_cast
    linear_combination h2
  · intro k v hv z
    have h1 : (om (e.symm z) (p v) : ℂ) = -((z ⬝ᵥ Hm.mulVec (star (P v))).im : ℂ) := by
      rw [him, hP, e.symm_apply_apply]; simp
    have h2 : e.symm (z + P v) = e.symm z + p v := by rw [map_add, hP, e.symm_apply_apply]
    have h3 : (Real.pi / 2 * ((z + P v) ⬝ᵥ Hm.mulVec (star (z + P v))) : ℂ) +
        -(Real.pi * Complex.I) * (om (e.symm z) (p v) : ℂ) =
        (Real.pi * (z ⬝ᵥ Hm.mulVec (star (P v))) +
          Real.pi / 2 * (P v ⬝ᵥ Hm.mulVec (star (P v)))) +
          Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)) := by
      rw [h1, star_add, mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hconj (P v) z]
      have h4 := Complex.sub_conj (z ⬝ᵥ Hm.mulVec (star (P v)))
      push_cast at h4
      linear_combination (-(Real.pi : ℂ) / 2) * h4
    have h5 := congrArg Complex.exp h3
    rw [Complex.exp_add, Complex.exp_add _ (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)))] at h5
    simp only [h2, hf k v hv]
    linear_combination c v * f k (e.symm z) * h5
  · rw [Fintype.linearIndependent_iff] at hli ⊢
    intro a ha
    refine hli a (funext fun u => ?_)
    have h1 := congrFun ha (e u)
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      e.symm_apply_apply] at h1 ⊢
    refine mul_left_cancel₀
      (Complex.exp_ne_zero (Real.pi / 2 * (e u ⬝ᵥ Hm.mulVec (star (e u))))) ?_
    linear_combination h1

end GlobalTheory.VacuumLine
