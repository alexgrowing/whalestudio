import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Gordan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem weight_zero_power_series_surjective (O : Type) [CommRing O] {σ τ X : Type} [Finite τ] [AddCommGroup X] (wt : σ → X)
    (g : τ → (σ →₀ ℕ)) (hg0 : ∀ s, g s ≠ 0) (hgw : ∀ s, Finsupp.weight wt (g s) = 0)
    (hgen : ∀ n, Finsupp.weight wt n = 0 → ∃ d : τ →₀ ℕ, Finsupp.linearCombination ℕ g d = n) :
    ∃ φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O,
      (∀ F, φ F ∈ wtPart O wt 0) ∧ ∀ f ∈ wtPart O wt 0, ∃ F, φ F = f := by
  classical
  let a : τ → MvPowerSeries σ O := fun s => monomial (g s) 1
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero fun s => by
    show constantCoeff (monomial (g s) (1 : O)) = 0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg (hg0 s).symm]
  have hprod : ∀ d : τ →₀ ℕ, (d.prod fun s e => a s ^ e) = monomial (Finsupp.linearCombination ℕ g d) (1 : O) := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' h h' =>
      rw [Finsupp.prod_add_index' (by simp) (fun s m n => pow_add _ _ _), h, h', map_add, monomial_mul_monomial,
        one_mul]
    | single s k =>
      rw [Finsupp.prod_single_index (by simp), Finsupp.linearCombination_single]
      show (monomial (g s) (1 : O)) ^ k = _
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ih, monomial_mul_monomial, one_mul, succ_nsmul]
  have hw : ∀ d : τ →₀ ℕ, Finsupp.weight wt (Finsupp.linearCombination ℕ g d) = 0 := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' h h' => rw [map_add, map_add, h, h', add_zero]
    | single s k => rw [Finsupp.linearCombination_single, map_nsmul, hgw, nsmul_zero]
  have hco : ∀ (F : MvPowerSeries τ O) n, coeff n (substAlgHom ha F) =
      ∑ᶠ d, coeff d F * (if n = Finsupp.linearCombination ℕ g d then 1 else 0) := by
    intro F n
    rw [coe_substAlgHom, coeff_subst ha]
    refine finsum_congr fun d => ?_
    rw [hprod, coeff_monomial, smul_eq_mul]
  refine ⟨substAlgHom ha, fun F n hn => ?_, fun f hf => ?_⟩
  · rw [hco]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    exact hn (hw d)
  · choose! e he using hgen
    let F : MvPowerSeries τ O := fun d =>
      if d = e (Finsupp.linearCombination ℕ g d) then coeff (Finsupp.linearCombination ℕ g d) f else 0
    have hF : ∀ d, coeff d F =
      if d = e (Finsupp.linearCombination ℕ g d) then coeff (Finsupp.linearCombination ℕ g d) f else 0 :=
      fun _ => rfl
    refine ⟨F, ?_⟩
    ext n
    rw [hco]
    by_cases hn : Finsupp.weight wt n = 0
    · rw [finsum_eq_single _ (e n)]
      · rw [hF, he n hn, if_pos rfl, if_pos rfl, mul_one]
      · intro d hd
        by_cases h : n = Finsupp.linearCombination ℕ g d
        · rw [hF, ← h, if_neg hd, zero_mul]
        · rw [if_neg h, mul_zero]
    · rw [hf n hn]
      refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
      rw [if_neg, mul_zero]
      rintro rfl
      exact hn (hw d)

theorem UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsCO O (W.gr 0) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W _
  obtain ⟨g, hg, hgen, -⟩ := UpperTheory.V.Alg.gordan W.σ X W.wt
  obtain ⟨φ, hφ, hs⟩ := weight_zero_power_series_surjective O W.wt (fun s : g => (s : W.σ →₀ ℕ)) (fun s => (hg s s.2).1)
    (fun s => (hg s s.2).2) (fun n hn => by
      have h := hgen n hn
      induction h using AddSubmonoid.closure_induction with
      | mem x hx => exact ⟨Finsupp.single ⟨x, hx⟩ 1, by simp⟩
      | zero => exact ⟨0, map_zero _⟩
      | add x y hx hy ihx ihy =>
        have hw : ∀ z ∈ AddSubmonoid.closure (g : Set (W.σ →₀ ℕ)), Finsupp.weight W.wt z = 0 := by
          intro z hz
          induction hz using AddSubmonoid.closure_induction with
          | mem x hx => exact (hg x hx).2
          | zero => exact map_zero _
          | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
        obtain ⟨d, hd⟩ := ihx (hw x hx)
        obtain ⟨d', hd'⟩ := ihy (hw y hy)
        exact ⟨d + d', by rw [map_add, hd, hd']⟩)
  have hp : ∀ F, W.π (φ F) ∈ W.part 0 := fun F => ⟨φ F, hφ F, rfl⟩
  let p : MvPowerSeries g O →ₐ[O] W.gr 0 :=
    { toFun := fun F => ⟨⟨W.π (φ F), W.part_le_A (hp F)⟩, hp F⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun F G => Subtype.ext (Subtype.ext (by simp))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun F G => Subtype.ext (Subtype.ext (by simp))
      commutes' := fun c => Subtype.ext (Subtype.ext (by
        show W.π (φ (algebraMap O _ c)) = algebraMap O R c
        rw [AlgHom.commutes, AlgHom.commutes])) }
  haveI : IsCO O (MvPowerSeries g O) := UpperTheory.V.Alg.co_mvps O O g
  haveI : Nontrivial (W.gr 0) := ⟨⟨0, 1, fun h =>
    zero_ne_one (α := R) (congrArg (fun x : W.gr 0 => ((x : W.A) : R)) h)⟩⟩
  refine UpperTheory.V.Alg.co_quot O (MvPowerSeries g O) (W.gr 0) p ?_
  rintro ⟨⟨x, hxA⟩, f, hf, hx⟩
  obtain ⟨F, rfl⟩ := hs f hf
  exact ⟨F, Subtype.ext (Subtype.ext hx)⟩
