import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.EqOfRes

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

open private card_bad irr_inf from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.EqOfRes

namespace UpperTheory.V.Z.Win

private theorem fix_root {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l p c : ℕ} (hc : p + 1 = 4 * l * c)
    (hl : A.valuation (l : Ω) < 1) {g : G ℚ Ω} (hg : g ∈ Dec (F := ℚ) A) {δ : Ω} (hδ : δ ^ 2 = -(p : Ω)) : g δ = δ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hcast : (p : Ω) + 1 = 4 * (l : Ω) * (c : Ω) := by
    have := congrArg (Nat.cast : ℕ → Ω) hc
    push_cast at this
    exact this
  have hsq : (g δ) ^ 2 = δ ^ 2 := by
    rw [← map_pow, hδ, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  exfalso
  set u : Ω := (1 + δ) / 2 with hu
  have hgu : g u = 1 - u := by
    rw [hu, map_div₀, map_add, map_one, h, map_ofNat]
    ring
  have hg1u : g (1 - u) = u := by
    rw [map_sub, map_one, hgu]
    ring
  have hprod : u * (1 - u) = (l : Ω) * (c : Ω) := by
    rw [hu]
    linear_combination (-1 / 4 : Ω) * hδ + (1 / 4 : Ω) * hcast
  have hc1 : A.valuation (c : Ω) ≤ 1 := by
    have := A.valuation_le_one (c : A)
    simpa using this
  have hlc : A.valuation ((l : Ω) * (c : Ω)) < 1 := by
    rw [Valuation.map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hc1) hl
  have key : A.valuation u < 1 ∨ A.valuation (1 - u) < 1 := by
    by_contra hne
    push_neg at hne
    have h1 : 1 ≤ A.valuation (u * (1 - u)) := by
      rw [Valuation.map_mul]
      exact one_le_mul hne.1 hne.2
    rw [hprod] at h1
    exact absurd hlc (not_lt.mpr h1)
  have both : A.valuation u < 1 ∧ A.valuation (1 - u) < 1 := by
    rcases key with k | k
    · refine ⟨k, ?_⟩
      rw [← hgu]
      exact (valuation_apply_lt_one_iff hg u).mpr k
    · refine ⟨?_, k⟩
      rw [← hg1u]
      exact (valuation_apply_lt_one_iff hg (1 - u)).mpr k
  have h1 : A.valuation (u + (1 - u)) < 1 :=
    lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt both.1 both.2)
  simp at h1

private theorem fix_field {Ω K : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    (h2 : Module.finrank ℚ K = 2) {δ : K} {p : ℕ} (hp : 0 < p) (hδ : δ ^ 2 = -(p : K)) (g : G ℚ Ω)
    (hg : g (algebraMap K Ω δ) = algebraMap K Ω δ) (x : K) : g (algebraMap K Ω x) = algebraMap K Ω x := by
  have hli : LinearIndependent ℚ ![(1 : K), δ] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp at hab
      exact ⟨hab, rfl⟩
    · exfalso
      have hbK : algebraMap ℚ K b ≠ 0 := (map_ne_zero _).mpr hb
      have hδ' : δ = algebraMap ℚ K (-a / b) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hab
        rw [map_div₀, map_neg, eq_div_iff hbK]
        linear_combination hab
      have hq : (-a / b) ^ 2 = -(p : ℚ) := by
        apply (algebraMap ℚ K).injective
        rw [map_pow, ← hδ', hδ, map_neg, map_natCast]
      have h0 : (0 : ℚ) ≤ (-a / b) ^ 2 := sq_nonneg _
      have hp' : (0 : ℚ) < p := by exact_mod_cast hp
      linarith
  have hspan : Submodule.span ℚ (Set.range ![(1 : K), δ]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [h2])
  have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), δ]) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  rw [← hf]
  simp [Fin.sum_univ_two, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, hg]

private theorem fam_one (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(p : ℤ) ∧ ∃ δ : K, δ ^ 2 = -(p : K) := by
  obtain ⟨K, _, _, h2, hd⟩ := KStar.Consta.exists_quadField hp h4
  obtain ⟨⟨δ, hδ⟩, htc⟩ := KStar.Choice.exists_sq_eq_neg_of_discr h2 hp.ne_zero hd
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  exact ⟨K, _, _, IsCMField.ofCMExtension ℚ K, h2, hd, δ, hδ⟩

theorem quadFamSplit (l : ℕ) [hl : Fact l.Prime] (N : ℕ) :
    ∃ (K : Fin N → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, IsCMField (K i)),
      (∀ i, Module.finrank ℚ (K i) = 2) ∧ (∀ i j, i ≠ j → IsCoprime (discr (K i)) (discr (K j))) ∧
      ∀ i, ∃ (p c : ℕ) (δ : K i), 0 < p ∧ p + 1 = 4 * l * c ∧ δ ^ 2 = -(p : K i) := by
  haveI : NeZero (4 * l) := ⟨by have := hl.out.pos; omega⟩
  have hS := Nat.infinite_setOfPred_prime_and_eq_mod (q := 4 * l) (a := -1) isUnit_one.neg
  let e := hS.natEmbedding
  let P : Fin N → ℕ := fun i => (e (i : ℕ)).1
  have hPp : ∀ i, (P i).Prime := fun i => (e (i : ℕ)).2.1
  have hPm : ∀ i, ((P i : ℕ) : ZMod (4 * l)) = -1 := fun i => (e (i : ℕ)).2.2
  have hPinj : Function.Injective P := by
    intro i j h
    exact Fin.ext (e.injective (Subtype.ext h))
  have hdvd : ∀ i, ∃ c, P i + 1 = 4 * l * c := by
    intro i
    have h0 : ((P i + 1 : ℕ) : ZMod (4 * l)) = 0 := by
      push_cast
      rw [hPm i]
      ring
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  have hF : ∀ i : Fin N, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(P i : ℤ) ∧ ∃ δ : K, δ ^ 2 = -(P i : K) := by
    intro i
    obtain ⟨c, hc⟩ := hdvd i
    have h4 : 4 ∣ P i + 1 := ⟨l * c, by rw [hc, mul_assoc]⟩
    exact fam_one (P i) (hPp i) (by omega)
  choose K hF1 hF2 hF3 hF4 using hF
  refine ⟨K, hF1, hF2, hF3, fun i => (hF4 i).1, ?_, ?_⟩
  · intro i j hij
    rw [(hF4 i).2.1, (hF4 j).2.1, IsCoprime.neg_neg_iff, Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes (hPp i) (hPp j)).mpr (fun h => hij (hPinj h))
  · intro i
    obtain ⟨c, hc⟩ := hdvd i
    obtain ⟨δ, hδ⟩ := (hF4 i).2.2
    exact ⟨P i, c, δ, (hPp i).pos, hc, hδ⟩

def SplitIn (l : ℕ) (K Ω : Type) [Field K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] : Prop :=
  ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x

theorem thirdSplit (K K' Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field K'] [NumberField K'] [IsCMField K'] [Field Ω]
    [Algebra ℚ Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] [IsAlgClosure ℚ Ω]
    (hK : Module.finrank ℚ K = 2) (hK' : Module.finrank ℚ K' = 2) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G ℚ Ω →* GL (Fin n) (Qbar l))
    (hr : IsIrr (r.comp (resG ℚ K Ω))) (hr' : IsIrr (r.comp (resG ℚ K' Ω))) :
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : IsCMField K'') (_ : Algebra K'' Ω) (_ : IsScalarTower ℚ K'' Ω),
      Module.finrank ℚ K'' = 2 ∧ SplitIn l K'' Ω ∧ IsIrr (r.comp ((resG ℚ K Ω).range ⊓ (resG ℚ K'' Ω).range).subtype) ∧
        IsIrr (r.comp ((resG ℚ K' Ω).range ⊓ (resG ℚ K'' Ω).range).subtype) := by
  classical
  haveI hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI hAlg : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hclos : ∀ (E : Type) [Field E] [Algebra ℚ E] [Algebra E Ω] [IsScalarTower ℚ E Ω], IsAlgClosure E Ω :=
    fun E _ _ _ _ => ⟨hAC, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  obtain ⟨Kf, hF, hN, hC, h2f, hcop, hsplit⟩ := quadFamSplit l (4 * n ^ 2 + 1)
  have hemb : ∀ i, ∃ (_ : Algebra (Kf i) Ω), IsScalarTower ℚ (Kf i) Ω := by
    intro i
    let f : Kf i →ₐ[ℚ] Ω := IsAlgClosed.lift
    letI : Algebra (Kf i) Ω := f.toRingHom.toAlgebra
    exact ⟨inferInstance, IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)⟩
  choose algI towI using hemb
  have hsign : ∀ i, ∃ δ : G ℚ Ω →* (Qbar l)ˣ, δ ≠ 1 ∧ IsSign (Kf i) δ := by
    intro i
    haveI := hclos (Kf i)
    obtain ⟨δ, -, h1, h2, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ (Kf i) Ω l (h2f i)
    exact ⟨δ, h1, h2⟩
  choose δf hδne hδs using hsign
  haveI := hclos K
  haveI := hclos K'
  obtain ⟨ε, -, hεne, hεs, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  obtain ⟨ε', -, hεne', hεs', -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K' Ω l hK'
  have hinj : Function.Injective δf := by
    intro i j hij
    by_contra hne
    apply UpperTheory.V.Br.signNe (Kf i) (Kf j) Ω (h2f i) (hcop i j hne)
    ext s
    rw [← (hδs i).1 s, ← (hδs j).1 s, hij]
  have hbadK := card_bad (resG ℚ K Ω) ε hεs.1 hεs.2 hεne δf hinj (fun i => (hδs i).2) (r.comp (resG ℚ K Ω)) hr
  have hbadK' := card_bad (resG ℚ K' Ω) ε' hεs'.1 hεs'.2 hεne' δf hinj (fun i => (hδs i).2) (r.comp (resG ℚ K' Ω)) hr'
  obtain ⟨i, hi⟩ : ∃ i, i ∉ (Finset.univ.filter fun i => RepIso (r.comp (resG ℚ K Ω))
      (tw (r.comp (resG ℚ K Ω)) ((δf i).comp (resG ℚ K Ω)))) ∪
      (Finset.univ.filter fun i => RepIso (r.comp (resG ℚ K' Ω))
      (tw (r.comp (resG ℚ K' Ω)) ((δf i).comp (resG ℚ K' Ω)))) := by
    by_contra hall
    push_neg at hall
    have h1 : (Finset.univ : Finset (Fin (4 * n ^ 2 + 1))) ⊆ _ := fun i _ => hall i
    have h2 := (Finset.card_le_card h1).trans ((Finset.card_union_le _ _).trans (add_le_add hbadK hbadK'))
    simp at h2
    linarith
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hi
  refine ⟨Kf i, hF i, hN i, hC i, algI i, towI i, h2f i, ?_, ?_, ?_⟩
  · intro A hA g hg x
    obtain ⟨p, c, δ, hp, hpc, hδ⟩ := hsplit i
    have hδΩ : (algebraMap (Kf i) Ω δ) ^ 2 = -(p : Ω) := by
      rw [← map_pow, hδ, map_neg, map_natCast]
    exact fix_field (h2f i) hp hδ g (fix_root A hpc hA hg hδΩ) x
  · exact irr_inf (resG ℚ K Ω) (resG ℚ (Kf i) Ω).range (δf i) (hδs i).1 (hδs i).2 r hr hi.1
  · exact irr_inf (resG ℚ K' Ω) (resG ℚ (Kf i) Ω).range (δf i) (hδs i).1 (hδs i).2 r hr' hi.2

end UpperTheory.V.Z.Win
