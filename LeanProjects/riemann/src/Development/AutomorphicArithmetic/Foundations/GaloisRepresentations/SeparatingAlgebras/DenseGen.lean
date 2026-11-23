import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  have h2 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact inv_lt_one_of_one_lt₀ h2

theorem UpperTheory.Gal.Gen.denseGen_pf :
    UpperTheory.Gal.Gen.Step → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.DenseGen := by
  intro hStep hPF E _ _ _ l _ ι a ha w₀ hl hs K hK W S Φ hS f hf ε hε
  have hl1 := norm_l_lt_one l
  have hr0 : 0 ≤ Real.sqrt ‖((l : ℕ) : Qbar l)‖ := Real.sqrt_nonneg _
  have hr1 : Real.sqrt ‖((l : ℕ) : Qbar l)‖ < 1 := by
    rw [Real.sqrt_lt' one_pos]
    simpa using hl1
  have key : ∀ m : ℕ, ∀ f ∈ fixedBy W K,
      ∃ G ∈ part W K (fun U => ∀ w ∈ S, GenAt w (Φ w) U), ∃ e : UA E a → ℂ,
        (∀ g, ‖ι.symm (e g)‖ ≤ Real.sqrt ‖((l : ℕ) : Qbar l)‖ ^ m) ∧
        ∀ v g, f.1 v g - G.1 v g = e g * f.1 v g := by
    intro m
    induction m with
    | zero =>
      intro f _
      refine ⟨0, Submodule.zero_mem _, fun _ => 1, fun g => ?_, fun v g => ?_⟩
      · simp
      · simp
    | succ m ih =>
      intro f hf
      obtain ⟨G, hG, e, he, hfe⟩ := ih f hf
      have hGf : G ∈ fixedBy W K := (hPF E a W K _).2.1 hG
      obtain ⟨G', hG', e', he', hfe'⟩ :=
        hStep E l ι a ha w₀ hl hs K hK W S Φ hS (f - G) (Submodule.sub_mem _ hf hGf)
      refine ⟨G + G', Submodule.add_mem _ hG hG', fun g => e' g * e g, fun g => ?_, fun v g => ?_⟩
      · rw [map_mul, norm_mul, pow_succ, mul_comm]
        exact mul_le_mul (he g) (Real.le_sqrt_of_sq_le (he' g)) (norm_nonneg _) (pow_nonneg hr0 _)
      · have h1 := hfe' v g
        have h2 := hfe v g
        have h3 : (f - G).1 v g = f.1 v g - G.1 v g := by simp
        have h4 : (G + G').1 v g = G.1 v g + G'.1 v g := by simp
        rw [h3] at h1
        rw [h4, mul_assoc, ← h2, ← h1]
        ring
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hr1
  obtain ⟨G, hG, e, he, hfe⟩ := key m f hf
  exact ⟨G, hG, e, fun g => (he g).trans hm.le, hfe⟩
