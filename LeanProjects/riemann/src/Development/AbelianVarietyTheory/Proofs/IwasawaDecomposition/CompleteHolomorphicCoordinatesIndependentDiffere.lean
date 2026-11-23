import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.CompleteCoords

theorem exists_linearIndependent_extend {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {a : ℕ} (ℓ : Fin a → M) (hℓ : LinearIndependent ℂ ℓ) :
    ∀ m : ℕ, a + m ≤ Module.finrank ℂ M → ∃ f : Fin (a + m) → M, LinearIndependent ℂ f ∧
      ∀ i : Fin a, f (Fin.castAdd m i) = ℓ i := by
  intro m
  induction m with
  | zero => intro _; exact ⟨ℓ, hℓ, fun i => rfl⟩
  | succ m ih =>
    intro h
    obtain ⟨f, hf, hfℓ⟩ := ih (by omega)
    obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hf (by omega)
    refine ⟨Fin.snoc f x, hx, fun i => ?_⟩
    have e : (Fin.castAdd (m + 1) i : Fin (a + (m + 1))) = Fin.castSucc (Fin.castAdd m i) := rfl
    rw [e, Fin.snoc_castSucc, hfℓ]

theorem complete_coords : ∀ (n a : ℕ) (v₀ : ReciprocityTheory.L2DbarEstimates.V n) (O : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G : Fin a → ReciprocityTheory.L2DbarEstimates.V n → ℂ), IsOpen O → v₀ ∈ O → (∀ i, DifferentiableOn ℂ (G i) O) → (∀ i, G i v₀ = 0) → LinearIndependent ℂ (fun i => fderiv ℂ (G i) v₀) → ∃ ψ : OpenPartialHomeomorph (ReciprocityTheory.L2DbarEstimates.V n) (Fin n → ℂ), v₀ ∈ ψ.source ∧ ψ.source ⊆ O ∧ ψ v₀ = 0 ∧ DifferentiableOn ℂ ψ ψ.source ∧ DifferentiableOn ℂ ψ.symm ψ.target ∧ ∀ v ∈ ψ.source, ∀ (j : Fin n) (hj : (j : ℕ) < a), ψ v j = G ⟨j, hj⟩ v := by
  intro n a v₀ O G hO hv₀ hG hG0 hli
  classical
  set ℓ : Fin a → (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) := fun i => fderiv ℂ (G i) v₀ with hℓdef
  have hfr : Module.finrank ℂ (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) = n := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap), Module.finrank_linearMap,
      finrank_euclideanSpace_fin, Module.finrank_self, Nat.mul_one]
  have han : a ≤ n := by
    have := hli.fintype_card_le_finrank
    simpa [hfr] using this
  obtain ⟨f', hf', hf'ℓ⟩ := exists_linearIndependent_extend ℓ hli (n - a) (by rw [hfr]; omega)
  have hn : a + (n - a) = n := by omega
  set f : Fin n → (ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ) := fun j => f' (Fin.cast hn.symm j) with hfdef
  have hf : LinearIndependent ℂ f := hf'.comp _ (Fin.cast_injective _)
  have hfa : ∀ (j : Fin n) (h : (j : ℕ) < a), f j = ℓ ⟨j, h⟩ := by
    intro j h
    have e : Fin.cast hn.symm j = Fin.castAdd (n - a) ⟨j, h⟩ := Fin.ext rfl
    simp only [hfdef, e, hf'ℓ]

  set Φ : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → ℂ) :=
    fun v j => if h : (j : ℕ) < a then G ⟨j, h⟩ v else f j (v - v₀) with hΦ
  have hGan : ∀ i, ∀ x ∈ O, AnalyticAt ℂ (G i) x := fun i x hx =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hO (hG i) hx
  have hΦan : ∀ x ∈ O, AnalyticAt ℂ Φ x := by
    intro x hx
    refine (analyticAt_pi_iff (f := fun j v => Φ v j)).2 fun j => ?_
    by_cases h : (j : ℕ) < a
    · simpa [hΦ, h] using hGan ⟨j, h⟩ x hx
    · simp only [hΦ, h, dite_false]
      exact ((f j).analyticAt _).comp (analyticAt_id.sub analyticAt_const)

  set D : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi f with hD
  have hΦD : HasFDerivAt Φ D v₀ := by
    refine (hasFDerivAt_pi (φ := fun j v => Φ v j)).2 fun j => ?_
    by_cases h : (j : ℕ) < a
    · simp only [hΦ, h, dite_true]
      rw [hfa j h]
      exact ((hGan ⟨j, h⟩ v₀ hv₀).differentiableAt).hasFDerivAt
    · simp only [hΦ, h, dite_false]
      have e : (fun x => f j (x - v₀)) = fun x => f j x - f j v₀ := by
        funext x; simp [map_sub]
      rw [e]
      exact (f j).hasFDerivAt.sub_const _
  have hinj : Function.Injective D := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : ∀ j, f j v = 0 := fun j => by
      have := congrFun hv j
      simpa [hD] using this
    have hspan : Submodule.span ℂ (Set.range f) = ⊤ := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        exact Subsingleton.elim _ _
      · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
        exact hf.span_eq_top_of_card_eq_finrank (by simp [hfr])
    have hall : ∀ φ : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ, φ v = 0 := by
      intro φ
      have hmem : φ ∈ Submodule.span ℂ (Set.range f) := hspan ▸ Submodule.mem_top
      refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨j, rfl⟩; exact hv' j
      · simp
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro c x _ hx; simp [hx]
    by_contra hne
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hne
    exact hφ (hall φ)
  have hsurj : Function.Surjective D := by
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (D : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] (Fin n → ℂ)))
      (by simp [finrank_euclideanSpace_fin])).1 hinj
    exact this
  set e : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj) with he
  have heD : (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) = D := by
    rw [he, ContinuousLinearEquiv.coe_ofBijective]
  have hs : HasStrictFDerivAt Φ (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) v₀ := by
    have h1 := ((hΦan v₀ hv₀).contDiffAt (n := 1)).hasStrictFDerivAt one_ne_zero
    rwa [hΦD.fderiv, ← heD] at h1

  have hΦC : ContDiffOn ℂ 1 Φ O := AnalyticOnNhd.contDiffOn (fun x hx => hΦan x hx) hO.uniqueDiffOn
  set W : Set (ReciprocityTheory.L2DbarEstimates.V n) :=
    O ∩ fderiv ℂ Φ ⁻¹' Set.range ContinuousLinearEquiv.toContinuousLinearMap with hW
  have hWo : IsOpen W :=
    (hΦC.continuousOn_fderiv_of_isOpen hO le_rfl).isOpen_inter_preimage hO
      ContinuousLinearEquiv.isOpen
  have hv₀W : v₀ ∈ W := ⟨hv₀, ⟨e, by rw [hΦD.fderiv, heD]⟩⟩
  refine ⟨(hs.toOpenPartialHomeomorph Φ).restrOpen W hWo, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hs.mem_toOpenPartialHomeomorph_source, hv₀W⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun x hx => hx.2.1
  · show Φ v₀ = 0
    funext j
    by_cases h : (j : ℕ) < a
    · simp [hΦ, h, hG0]
    · simp [hΦ, h]
  · intro x hx
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact (hΦan x hx.2.1).differentiableAt.differentiableWithinAt
  · intro y hy
    set ψ := (hs.toOpenPartialHomeomorph Φ).restrOpen W hWo with hψ
    have hx : ψ.symm y ∈ ψ.source := ψ.map_target hy
    rw [hψ, OpenPartialHomeomorph.restrOpen_source] at hx
    obtain ⟨e', he'⟩ := hx.2.2
    have hd : HasFDerivAt (ψ : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → ℂ))
        (e' : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)) (ψ.symm y) := by
      have := (hΦan _ hx.2.1).differentiableAt.hasFDerivAt
      rw [← he'] at this
      exact this
    exact (ψ.hasFDerivAt_symm hy hd).differentiableAt.differentiableWithinAt
  · intro v _ j hj
    show Φ v j = _
    simp [hΦ, hj]

end GlobalTheory.CompleteCoords
