import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedFlagCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedDeletionCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaActsTriviallyOnRootsOfUnity
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SeedDefs
open UpperTheory.GalN.V

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem near {K : Type} [NormedField K] [IsUltrametricDist K] (d x y z : K) (hd : ‖d - 1‖ < 1) (hx : ‖x - y‖ < 1)
    (hy : ‖y‖ = 1) (hz : ‖z - y‖ < 1) : ‖d * x - z‖ < 1 := by
  have h1 : ‖x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (x - y) y
    rw [sub_add_cancel] at this
    exact this.trans (max_le hx.le hy.le)
  have h2 : ‖(d - 1) * x‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h1) hd
  have h3 : d * x - z = (d - 1) * x + ((x - y) + (y - z)) := by ring
  rw [h3]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2 ?_)
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx ?_)
  rwa [norm_sub_rev]

theorem UpperTheory.GalN.V.indLoc0 :
    AllInd fun {Ω} _ _ _ {l} _ _ _ T _ R δ => ∃ n, LocOk T ⟨twF T R δ, n⟩ ∧ ∃ (m : Fin 4 → ℤ) (b : ℤ) (N : ℕ),
  (∀ i : Fin 3, m i.succ + 2 ≤ m i.castSucc) ∧ Wts0 T (fun i => 2 * m i + b) ⟨twF T R δ, n⟩ ∧ 0 < N ∧
  ∀ g, (δ g ^ 2 * cycBar T.F Ω l g ^ (-b)) ^ N = 1 := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H
  obtain ⟨m, hm, hF⟩ := UpperTheory.induced_flag_condition Ω l c D T k₀ φ ι k t r α β R δ H
  obtain ⟨b, N, U, hN, hδ, hU, hI⟩ := UpperTheory.induced_deletion_condition Ω l c D T k₀ φ ι k t r α β R δ H
  choose n hn using fun v : T.ι => hF (T.pl v) (T.ovl v)
  have key : ∀ v s, adj (n v) * twF T R δ s * n v = (δ s : Qbar l) • (adj (n v) * (R (resQ T.F s) : M4 (Qbar l)) * n v) := by
    intro v s
    have : twF T R δ s = (δ s : Qbar l) • (R (resQ T.F s) : M4 (Qbar l)) := tw_val (R.comp (resQ T.F)) δ s
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
  have key' : ∀ v s i, PD.ψ (⟨twF T R δ, n⟩ : PD T.ι (G T.F Ω) (Qbar l)) v i s =
      (δ s : Qbar l) * (adj (n v) * (R (resQ T.F s) : M4 (Qbar l)) * n v) i i := by
    intro v s i
    show (adj (n v) * twF T R δ s * n v) i i = _
    rw [key, Matrix.smul_apply, smul_eq_mul]
  have ined : ∀ (A : ValuationSubring Ω) (s : G T.F Ω), s ∈ Ine (F := T.F) A → s ∈ Dec (F := T.F) A := fun A s hs => hs.1
  refine ⟨n, ⟨fun v => (hn v).1, ?_, ?_, ?_⟩, m, b, N, hm, ⟨U, hU, ?_⟩, hN, hδ⟩
  · intro v s hs i j hij
    show (adj (n v) * twF T R δ s * n v) i j = 0
    rw [key, Matrix.smul_apply, ((hn v).2 s hs).1 i j hij, smul_zero]
  · intro v s hs i
    obtain ⟨h1, h2⟩ := UpperTheory.inertia_acts_trivially_on_roots_of_unity T.F Ω l H.hyp.good.l_odd (T.pl v) (T.ovl v) s hs
    have h3 : cycBar T.F Ω l s = 1 := by
      simp [cycBar, h2]
    rw [key', (((hn v).2 s (ined _ _ h1)).2 i).2 h1, (hI _ (T.ovl v) s h1).2 h2, h3]
    simp
  · intro v s hs i
    rw [key']
    have hk : resQ T.F s ∈ k₀.fixingSubgroup := H.hyp.spl _ (T.ovl v) hs
    refine near _ _ _ _ (H.δ_one s) (((hn v).2 s hs).2 i).1 ?_ (H.chars.inn s hk i)
    fin_cases i
    · exact H.chars.unit D.ξ _
    · simp
    · exact H.chars.unit D.ξ _
    · simp
  · intro v i s hs
    rw [key', (((hn v).2 s (ined _ _ hs.2)).2 i).2 hs.2, ← Units.val_mul, ← Units.val_pow_eq_pow_val, mul_pow,
      (hI _ (T.ovl v) s hs.2).1 hs.1, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    congr 2
    push_cast
    ring
