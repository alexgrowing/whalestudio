import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.OneCharU

open private isPush_push from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OneChar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Z.J

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

def UpperTheory.V.SmallClassNumbers.OnePoint : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N),
    eO l c.O = 1 → GD Ω K l e ψ → ∀ ι : Qbar l ≃+* ℂ, Vlen Ω c e ψ ≠ 0 →
    ∃ (D : Dat Ω K c e ψ) (U : D.ULoc) (g₁ : G ℚ Ω) (r : G ℚ Ω →* GG 3 (PadicAlgCl l)) (h : D.IsPt U g₁ r),
      D.Marked g₁ ∧ ¬ Upper D.η r ∧ ¬ Lower D.η r ∧
      (Adm3U ι e N (D.rhoK r h.mult) ∨ Af.Adm2 ι e (N * (discr K).natAbs) (D.rhoK r h.mult))

theorem UpperTheory.V.SmallClassNumbers.onePoint (hC : U3.CohInp) (hLM : LemmaM) (hLM' : LemmaM') (hLP : LemmaP) (hK : Z.Kato.KatoTwo)
    (hRI : Th.RigI) (hRII : Th.RigII) (hAd : AdmI) (hA : Aut.AutomorphyUnramifiedCoefficients) : UpperTheory.V.SmallClassNumbers.OnePoint := by
  intro Ω _ _ _ K _ _ _ _ _ l _ c N _ e ψ he hG ι h0
  classical
  obtain ⟨D⟩ := exists_dat hG
  obtain ⟨g₁, hM, hFin, hB, hW⟩ := hA Ω K l c N e ψ D he ι
  obtain ⟨U⟩ := exists_uLoc hC D
  obtain ⟨S⟩ := exists_ring hC D U g₁ hM
  obtain ⟨M⟩ := exists_model hC hLP D hM S
  have hex : ∃ f : S.R →ₐ[c.O] PadicAlgCl l, TwoPt D.η S.r.hom f := by
    by_contra hn
    obtain ⟨hlen, T, hT, -, hle⟩ := model_upper S M hG.l_odd hM hLM (hFin U S)
      (Z.J.ptHyp_ofU hC hK hRI hRII D hM S ι hB hW M.x₀ M.base) 1 (map_one _) fun f hf => absurd ⟨f, hf⟩ hn
    have hT0 : T = ∅ := Finset.eq_empty_of_forall_notMem fun f hf => hn ⟨f, hT.1 f hf⟩
    rw [hT0, Finset.sum_empty, mul_zero, Chr.nrm, he, ENat.toNat_one, Nat.cast_one, div_one] at hle
    have h1 : M.len.toNat = 0 := by exact_mod_cast le_antisymm hle (Nat.cast_nonneg _)
    have h2 : M.len = 0 := (ENat.toNat_eq_zero.1 h1).resolve_right hlen
    exact h0 (le_antisymm (h2 ▸ vlen_le hC hLM' D hM S M) zero_le')
  obtain ⟨f, hf⟩ := hex
  have hp := isPt_push D hM S f hf.1
  refine ⟨D, U, g₁, _, hp, hM, hf.2.1, hf.2.2, ?_⟩
  rcases (twoPt_shape S hG.l_odd hM f hf).1 with h | h
  · exact Or.inl (hAd D hM S f hf.1 hp.mult ι h (hB U S _ _ _ (isPush_push f _) h))
  · exact Or.inr (admissible_of_typeII hC D hM hp ι h (hW U S _ _ (isPush_push f _) h (typeII_facts hC D hM hp h).1))
