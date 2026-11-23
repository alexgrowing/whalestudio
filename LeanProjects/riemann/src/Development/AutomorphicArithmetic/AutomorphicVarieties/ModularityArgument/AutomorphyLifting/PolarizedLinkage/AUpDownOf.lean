import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.ThruTr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

section Places

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

private def overUnder (w : HeightOneSpectrum (𝓞 K)) : PlacesOver K (w.under (𝓞 F)) := ⟨w, ⟨rfl⟩⟩

private theorem under_of_over {v : HeightOneSpectrum (𝓞 F)} (w : PlacesOver K v) : w.1.under (𝓞 F) = v := by
  refine HeightOneSpectrum.ext ?_
  rw [HeightOneSpectrum.under_asIdeal]
  exact w.2.over.symm

private theorem nonempty_over (v : HeightOneSpectrum (𝓞 F)) : Nonempty (PlacesOver K v) :=
  (Ideal.nonempty_primesOver (S := 𝓞 K) v.asIdeal).map (placesOverEquiv K v).symm

private theorem exists_above (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 F) = v :=
  let ⟨w⟩ := nonempty_over (K := K) v
  ⟨w.1, under_of_over w⟩

private theorem l_mem_under (l : ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]

private theorem under_self (v : HeightOneSpectrum (𝓞 F)) : v.under (𝓞 F) = v := by
  refine HeightOneSpectrum.ext ?_
  rw [HeightOneSpectrum.under_asIdeal]
  ext x
  rw [Ideal.mem_comap]
  rfl

private theorem under_under {E : Type} [Field E] [NumberField E] [Algebra F E] [Algebra E K] [IsScalarTower F E K]
    (w : HeightOneSpectrum (𝓞 K)) : (w.under (𝓞 E)).under (𝓞 F) = w.under (𝓞 F) := by
  refine HeightOneSpectrum.ext ?_
  simp only [HeightOneSpectrum.under_asIdeal]
  ext x
  simp only [Ideal.mem_comap]
  rw [← IsScalarTower.algebraMap_apply]

end Places

section One

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]

private theorem win_one (hO : ImaginaryQuadraticEtaCharacter.WinOf) (π : CuspSub K 1) : ∃ t : ℝ, ∀ v, WinAt π t v := by
  obtain ⟨t, ht⟩ := hO K 1 le_rfl π
  refine ⟨t, fun v => ?_⟩
  obtain ⟨⟨s₀, hs₀⟩, huniq, hf, -, -⟩ := suppFacts K 1 le_rfl π v
  have hle : ∀ s, SuppAt π v s → ∀ y ∈ s, y.1 = 1 := fun s hs y hy => by
    obtain ⟨-, hsum, hpos⟩ := hf s hs
    have h1 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ (Multiset.mem_map_of_mem _ hy)
    have h2 := hpos y hy
    omega
  have hcard : ∀ s, SuppAt π v s → s.card ≤ 1 := fun s hs => by
    obtain ⟨-, hsum, -⟩ := hf s hs
    have e : s.map Sigma.fst = s.map fun _ => 1 := Multiset.map_congr rfl (hle s hs)
    rw [e, Multiset.map_const', Multiset.sum_replicate] at hsum
    simpa using hsum.le
  refine ht v ((hf s₀ hs₀).1.2 (hle s₀ hs₀)) fun s hs ξ hξ ξ' hξ' _ => ?_
  obtain ⟨a, ha⟩ := hξ
  obtain ⟨b, hb⟩ := hξ'
  have h1 : s.card = 1 := le_antisymm (hcard s hs) (Multiset.card_pos_iff_exists_mem.2 ⟨_, ha⟩)
  obtain ⟨y, rfl⟩ := Multiset.card_eq_one.1 h1
  have e := (polFacts (v.adicCompletion K)).2.2.1 ξ ξ' a b ((Multiset.mem_singleton.1 ha).trans (Multiset.mem_singleton.1 hb).symm)
  subst e
  rw [mul_inv_cancel]
  simp only [MonoidHom.one_apply, Units.val_one]
  intro h
  have h2 : Ideal.absNorm v.asIdeal = 1 := by exact_mod_cast h.symm
  exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h2)

end One

section Pol

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

private theorem polarized_of_att (H : HypothesesH) {ι : Qbar l ≃+* ℂ} (hn : 1 ≤ n) {r : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}
    (hp : Sol.Pol ι r) (ha : AttC ι r π) : ∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ := by
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := UpperTheory.cyclotomicCharacter_plusPart (algOfCyc H) UpperTheory.cyclotomic_char_conj_invariant K Ω l ι n r hp
  have hd := selfDualC H K Ω l ι n hn r π ha χ μ hμ c P hc hP
  have hsign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel _ Ω l ι χ μ hμ hs
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
    rcases sq_eq_one_iff.1 h3 with e | e
    · exact ⟨0, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
    · exact ⟨1, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
  have hN : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  refine ⟨χ * quadChar K ^ (m + n), fun v => ?_, hN ▸ hd⟩
  rw [HChar.locInf_mul, locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
  simp

end Pol

private structure Hyp : Prop where
  pr : HypothesesH
  row : RowT
  weak : WeakOfAtt
  flag : FlagLaws
  thru0 : Thru false
  thru1 : Thru true
  ud : WinUpDown
  wo : ImaginaryQuadraticEtaCharacter.WinOf

section Two

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

private def W1 (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → Unl1 r v → PotUnl r v

private def W2 [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ π : CuspSub F n, (CG.mk π).IsRegAlg → AttC ι r π → ∃ t : ℝ, ∀ v : HeightOneSpectrum (𝓞 F),
    (((l : ℕ) : 𝓞 F) ∉ v.asIdeal ∨ PotUnl r v) → WinAt π t v

private theorem second_condition_trivial_extension [IsCMField F] (h : Hyp) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin 1) (Qbar l)) : W2 ι r := fun π _ _ =>
  let ⟨t, ht⟩ := win_one h.wo π
  ⟨t, fun v _ => ht v⟩

end Two

section Step

variable {F K Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field K] [NumberField K] [IsCMField K] [Field Ω]
  [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}

private theorem cond_down (h : Hyp) (hf : Flagged r) {w : HeightOneSpectrum (𝓞 K)}
    (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal ∨ PotUnl (r.comp (resG F K Ω)) w) :
    ((l : ℕ) : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal ∨ PotUnl r (w.under (𝓞 F)) := by
  by_cases e : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
  · exact Or.inr ((((h.flag F Ω l n r).2.2.2 K).2.2 w e).2 hf |>.1 (hw.resolve_left fun k => k e))
  · exact Or.inl fun k => e ((l_mem_under l w).1 k)

private theorem cond_up (h : Hyp) {w : HeightOneSpectrum (𝓞 K)}
    (hv : ((l : ℕ) : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal ∨ PotUnl r (w.under (𝓞 F))) :
    ((l : ℕ) : 𝓞 K) ∉ w.asIdeal ∨ PotUnl (r.comp (resG F K Ω)) w := by
  by_cases e : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
  · exact Or.inr ((((h.flag F Ω l n r).2.2.2 K).2.2 w e).1 (hv.resolve_left fun k => k ((l_mem_under l w).2 e)))
  · exact Or.inl e

private theorem first_condition_up (h : Hyp) (hf : Flagged r) (hW : W1 r) : W1 (r.comp (resG F K Ω)) := fun w e hu =>
  (((h.flag F Ω l n r).2.2.2 K).2.2 w e).1
    (hW _ ((l_mem_under l w).2 e) (((((h.flag F Ω l n r).2.2.2 K).2.2 w e).2 hf).2 hu))

private theorem first_condition_down (h : Hyp) (hf : Flagged r) (hK : Keeps r K) (hW : W1 (r.comp (resG F K Ω))) : W1 r := by
  intro v e hu
  obtain ⟨w, rfl⟩ := exists_above (K := K) v
  have e' := (l_mem_under l w).1 e
  exact ((((h.flag F Ω l n r).2.2.2 K).2.2 w e').2 hf).1 (hW w e' (hK w e' hu))

private theorem second_condition_up (h : Hyp) [IsGalois F K] (hp : (Module.finrank F K).Prime) (hn : 2 ≤ n) (hf : Flagged r)
    (ha : IsRegAlgAutomorphicAttached ι r) (hW : W2 ι r) : W2 ι (r.comp (resG F K Ω)) := by
  intro P _ hP
  obtain ⟨π, hreg, hπ⟩ := ha
  obtain ⟨t, ht⟩ := hW π hreg hπ
  refine ⟨t, fun w hw => ?_⟩
  exact ((h.ud F K hp n hn π P (h.weak F K Ω l ι n r π P hπ hP) t (w.under (𝓞 F))).1 (ht _ (cond_down h hf hw)) (overUnder w)).1

private theorem win_down (h : Hyp) [IsGalois F K] (hp : (Module.finrank F K).Prime) (hn : 2 ≤ n) (hr : Continuous r) (hI : IneAb r)
    {π : CuspSub F n} (hπ : AttC ι r π) {Q : CuspSub K n} (hreg : (CG.mk Q).IsRegAlg) (hpol : ∃ χ, GlobalTheory.ContraPair.PolarizedPair Q χ)
    (hQ : AttC ι (r.comp (resG F K Ω)) Q) {t : ℝ} {v : HeightOneSpectrum (𝓞 F)}
    (hc : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal ∨ PotUnl r v) (hwin : ∀ w : PlacesOver K v, WinAt Q t w.1) : WinAt π t v := by
  refine (h.ud F K hp n hn π Q (h.weak F K Ω l ι n r π Q hπ hQ) t v).2 fun w => ⟨hwin w, ?_⟩
  by_cases e : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  · exact h.thru1 h.row F K Ω l ι n hn r hr hI Q hreg hpol hQ v (by simp [e]) (fun _ => hc.resolve_left fun k => k e) w t (hwin w)
  · exact h.thru0 h.row F K Ω l ι n hn r hr hI Q hreg hpol hQ v (by simp [e]) (by simp) w t (hwin w)

private theorem second_condition_down (h : Hyp) [IsGalois F K] (hp : (Module.finrank F K).Prime) (hn : 2 ≤ n) (hr : Continuous r) (hI : IneAb r)
    (hpol : Sol.Pol ι (r.comp (resG F K Ω))) (ha : IsRegAlgAutomorphicAttached ι (r.comp (resG F K Ω))) (hW : W2 ι (r.comp (resG F K Ω))) : W2 ι r := by
  intro π _ hπ
  obtain ⟨Q, hreg, hQ⟩ := ha
  obtain ⟨t, ht⟩ := hW Q hreg hQ
  refine ⟨t, fun v hv => win_down h hp hn hr hI hπ hreg (polarized_of_att h.pr (by omega) hpol hQ) hQ hv fun w => ht w.1 ?_⟩
  refine cond_up h ?_
  rwa [under_of_over w]

private theorem aut_up (hE : Sol.Equi F Ω K) (H : HypothesesH) (hn : 1 ≤ n) (hr : Continuous r) (hirr : IsIrr (r.comp (resG F K Ω)))
    (hpol : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) : IsRegAlgAutomorphicAttached ι (r.comp (resG F K Ω)) :=
  ((autBridge H K Ω l ι n _).2.1).1 ((hE l ι n hn r hr hirr hpol).1 (((autBridge H F Ω l ι n r).2.1).2 ha))

end Step

section SlopeTestRemainingChoices

private theorem exists_cm_field_tower (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra F K] [Algebra F Ω]
    [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (h1 : Module.finrank F K = 1) (N : ℕ) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra K M) (_ : Algebra F M) (_ : Algebra M Ω)
      (_ : IsScalarTower F K M) (_ : IsScalarTower F M Ω) (_ : IsScalarTower K M Ω) (_ : IsAlgClosure M Ω) (_ : IsGalois K M) (_ : IsGalois F M),
      (Module.finrank K M).Prime ∧ (Module.finrank F M).Prime ∧ N < Module.finrank K M ∧ N < Module.finrank F M := by
  obtain ⟨L, _, _, _, hL, hp, hlt⟩ := UpperTheory.solvable_cyclic_subextension_over_rat (max N (Module.finrank ℚ K))
  obtain ⟨M, _, _, _, _, _, f, _, hd, hadj⟩ := UpperTheory.solvable_auxiliary_galois_extension K Ω L hp (lt_of_le_of_lt (le_max_right _ _) hlt)
  have hM : IsCMField M := (UpperTheory.solvable_cm_compositum_maximalRealSubfield L K M f hL hadj (Or.inr inferInstance)).resolve_left fun hR => by
    obtain ⟨v⟩ : Nonempty (InfinitePlace M) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.2 ((isTotallyComplex_of_algebra K M).isComplex v)) (hR.isReal v)
  letI : Algebra F M := ((algebraMap K M).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F M Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω, IsScalarTower.algebraMap_apply K M Ω]; rfl
  haveI : IsAlgClosure M Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed K
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := K) M }
  have hbij : Function.Bijective (algebraMap F K) := by
    refine ⟨(algebraMap F K).injective, fun x => ?_⟩
    have e : (⊥ : Subalgebra F K) = ⊤ := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1
    exact Algebra.mem_bot.1 (e ▸ Algebra.mem_top : x ∈ (⊥ : Subalgebra F K))
  haveI : IsGalois F M :=
    IsGalois.of_equiv_equiv (F := K) (E := M) (f := (RingEquiv.ofBijective (algebraMap F K) hbij).symm) (g := RingEquiv.refl M) (by
      ext x
      obtain ⟨y, rfl⟩ := hbij.2 x
      have : (RingEquiv.ofBijective (algebraMap F K) hbij).symm (algebraMap F K y) = y :=
        (RingEquiv.ofBijective (algebraMap F K) hbij).symm_apply_apply y
      simp [this, IsScalarTower.algebraMap_apply F K M])
  have hd' : Module.finrank F M = Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank F K M, h1, one_mul, hd]
  exact ⟨M, ‹Field M›, ‹NumberField M›, hM, ‹Algebra K M›, ‹Algebra F M›, ‹Algebra M Ω›, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hd ▸ hp, hd' ▸ hp, hd ▸ lt_of_le_of_lt (le_max_left _ _) hlt, hd' ▸ lt_of_le_of_lt (le_max_left _ _) hlt⟩

end SlopeTestRemainingChoices

section One2

variable {F K Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field K] [NumberField K] [IsCMField K] [Field Ω]
  [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)}

private theorem compl_self (v : HeightOneSpectrum (𝓞 F)) :
    ∃ i : (v.under (𝓞 F)).adicCompletion F ≃+* v.adicCompletion F, IsCompl i := by
  have : ∀ v' : HeightOneSpectrum (𝓞 F), v' = v → ∃ i : v'.adicCompletion F ≃+* v.adicCompletion F, IsCompl i := by
    rintro _ rfl
    exact ⟨RingEquiv.refl _, continuous_id, fun _ => rfl⟩
  exact this _ (under_self v)

private theorem second_condition_up_trivial (h : Hyp) (h1 : Module.finrank F K = 1) (hn : 2 ≤ n) (hr : Continuous r)
    (hirr : IsIrr (r.comp (resG F K Ω))) (hpol : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) (hf : Flagged r) (hW : W2 ι r) :
    W2 ι (r.comp (resG F K Ω)) := by
  obtain ⟨M, _, _, _, _, _, _, _, _, _, _, _, _, pK, pF, lK, lF⟩ := exists_cm_field_tower F K Ω h1 n
  obtain ⟨hN, hidx⟩ := UpperTheory.galois_representation_image_spec K M Ω
  have hirr' : IsIrr ((r.comp (resG F K Ω)).comp (resG K M Ω)) :=
    UpperTheory.galois_representation_irreducible_prime_dimension _ _ _ n _ _ hN (by rw [hidx]; exact pK) (by rw [hidx]; exact lK) hirr
  have e : (r.comp (resG F K Ω)).comp (resG K M Ω) = r.comp (resG F M Ω) := rfl
  rw [e] at hirr'
  obtain ⟨Q, -, hQ⟩ := aut_up (UpperTheory.V.Z.Bc.stepC h.pr h.pr.cyc F M Ω pF inferInstance inferInstance) h.pr (by omega) hr hirr' hpol ha
  have hQ' : AttC ι ((r.comp (resG F K Ω)).comp (resG K M Ω)) Q := by rw [e]; exact hQ
  intro P _ hP
  obtain ⟨π, hreg, hπ⟩ := ha
  obtain ⟨t, ht⟩ := hW π hreg hπ
  refine ⟨t, fun w hw => ?_⟩
  have bF := h.weak F M Ω l ι n r π Q hπ hQ
  have bK := h.weak K M Ω l ι n _ P Q hP hQ'
  refine (h.ud K M pK n hn P Q bK t w).2 fun u => ?_
  haveI hv : u.1.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    Ideal.LiesOver.trans u.1.asIdeal w.asIdeal (w.under (𝓞 F)).asIdeal
  obtain ⟨a, b⟩ := (h.ud F M pF n hn π Q bF t (w.under (𝓞 F))).1 (ht _ (cond_down h hf hw)) ⟨u.1, hv⟩
  obtain ⟨i, hi⟩ := compl_self (w.under (𝓞 F))
  exact ⟨a, thruTr F K F M n Q w (w.under (𝓞 F)) u ⟨u.1, hv⟩ rfl i hi b⟩

private theorem second_condition_down_trivial (h : Hyp) (h1 : Module.finrank F K = 1) (hn : 2 ≤ n) (hr : Continuous r)
    (hirr : IsIrr (r.comp (resG F K Ω))) (hpol : Sol.Pol ι r) (ha : IsRegAlgAutomorphicAttached ι r) (hf : Flagged (r.comp (resG F K Ω)))
    (haK : IsRegAlgAutomorphicAttached ι (r.comp (resG F K Ω))) (hI : IneAb r) (hW : W2 ι (r.comp (resG F K Ω))) : W2 ι r := by
  obtain ⟨M, _, _, _, _, _, _, _, _, _, _, _, _, pK, pF, lK, lF⟩ := exists_cm_field_tower F K Ω h1 n
  obtain ⟨hN, hidx⟩ := UpperTheory.galois_representation_image_spec K M Ω
  have hirr' : IsIrr ((r.comp (resG F K Ω)).comp (resG K M Ω)) :=
    UpperTheory.galois_representation_irreducible_prime_dimension _ _ _ n _ _ hN (by rw [hidx]; exact pK) (by rw [hidx]; exact lK) hirr
  have e : (r.comp (resG F K Ω)).comp (resG K M Ω) = r.comp (resG F M Ω) := rfl
  rw [e] at hirr'
  have aM := aut_up (UpperTheory.V.Z.Bc.stepC h.pr h.pr.cyc F M Ω pF inferInstance inferInstance) h.pr (by omega) hr hirr' hpol ha
  have hW' := second_condition_up (F := K) (K := M) h pK hn hf haK hW
  rw [e] at hW'
  exact second_condition_down (K := M) h pF hn hr hI (UpperTheory.solvable_polarized_restriction F M Ω l ι n r hpol) aM hW'

end One2

section Tower

private def Good (F K Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field K] [NumberField K] [IsCMField K] [Field Ω]
    [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r →
    IsIrr (r.comp (resG F K Ω)) → Sol.Pol ι r → IsRegAlgAutomorphicAttached ι r → Flagged r →
      (WitA ι r → WitA ι (r.comp (resG F K Ω))) ∧ (IneAb r → Keeps r K → WitA ι (r.comp (resG F K Ω)) → WitA ι r)

variable {F K Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field K] [NumberField K] [IsCMField K] [Field Ω]
  [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]

private theorem good_prime (h : Hyp) [IsGalois F K] (hp : (Module.finrank F K).Prime) (hE : Sol.Equi F Ω K) : Good F K Ω := by
  intro l _ ι n hn r hr hirr hpol ha hf
  have haK := aut_up hE h.pr hn hr hirr hpol ha
  have hpK := UpperTheory.solvable_polarized_restriction F K Ω l ι n r hpol
  refine ⟨fun hW => ⟨first_condition_up h hf hW.1, ?_⟩, fun hI hK hW => ⟨first_condition_down h hf hK hW.1, ?_⟩⟩
  · obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
    · exact second_condition_trivial_extension h ι _
    · exact second_condition_up h hp h2 hf ha hW.2
  · obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
    · exact second_condition_trivial_extension h ι _
    · exact second_condition_down h hp h2 hr hI hpK haK hW.2

private theorem good_one (h : Hyp) (h1 : Module.finrank F K = 1) (hE : Sol.Equi F Ω K) : Good F K Ω := by
  intro l _ ι n hn r hr hirr hpol ha hf
  have haK := aut_up hE h.pr hn hr hirr hpol ha
  have hfK := ((h.flag F Ω l n r).2.2.2 K).2.1 hf
  refine ⟨fun hW => ⟨first_condition_up h hf hW.1, ?_⟩, fun hI hK hW => ⟨first_condition_down h hf hK hW.1, ?_⟩⟩
  · obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
    · exact second_condition_trivial_extension h ι _
    · exact second_condition_up_trivial h h1 h2 hr hirr hpol ha hf hW.2
  · obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
    · exact second_condition_trivial_extension h ι _
    · exact second_condition_down_trivial h h1 h2 hr hirr hpol ha hfK haK hI hW.2

end Tower

private theorem good_trans (h : Hyp) (F E K Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field E] [NumberField E] [IsCMField E]
    [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω]
    (H : ∀ [Algebra E Ω] [IsScalarTower F E Ω] [IsScalarTower E K Ω] [IsAlgClosure E Ω],
      Good F E Ω ∧ Good E K Ω ∧ Sol.Equi F Ω E) : Good F K Ω := by
  letI : Algebra E Ω := ((algebraMap K Ω).comp (algebraMap E K)).toAlgebra
  haveI : IsScalarTower E K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω, IsScalarTower.algebraMap_apply F E K]; rfl
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  obtain ⟨g1, g2, hE⟩ := H
  intro l _ ι n hn r hr hirr hpol ha hf
  have hc : (r.comp (resG F E Ω)).comp (resG E K Ω) = r.comp (resG F K Ω) := rfl
  have i2 : IsIrr ((r.comp (resG F E Ω)).comp (resG E K Ω)) := hc ▸ hirr
  have i1 : IsIrr (r.comp (resG F E Ω)) := (UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ i2
  have fl := (h.flag F Ω l n r).2.2.2 E
  have hfE := fl.2.1 hf
  have d1 := g1 l ι n hn r hr i1 hpol ha hf
  have d2 : (WitA ι (r.comp (resG F E Ω)) → WitA ι (r.comp (resG F K Ω))) ∧
      (IneAb (r.comp (resG F E Ω)) → Keeps (r.comp (resG F E Ω)) K → WitA ι (r.comp (resG F K Ω)) → WitA ι (r.comp (resG F E Ω))) :=
    g2 l ι n hn _ (hr.comp (continuous_restrictScalarsHom F E Ω)) i2 (UpperTheory.solvable_polarized_restriction F E Ω l ι n r hpol)
      (aut_up hE h.pr hn hr i1 hpol ha) hfE
  refine ⟨fun hW => d2.1 (d1.1 hW), fun hI hK hW => d1.2 hI ?_ (d2.2 (fl.1 hI) ?_ hW)⟩
  · intro w e hu
    obtain ⟨u, rfl⟩ := exists_above (K := K) w
    have e' := (l_mem_under l u).1 e
    rw [under_under] at hu
    exact ((((h.flag E Ω l n (r.comp (resG F E Ω))).2.2.2 K).2.2 u e').2 hfE).2 (hK u e' hu)
  · intro u e hu
    have e' := (l_mem_under (F := E) l u).2 e
    have k := ((fl.2.2 (u.under (𝓞 E)) e').2 hf).2 hu
    rw [under_under] at k
    exact hK u e k

private theorem good_all (h : Hyp) (d : ℕ) :
    ∀ (F K Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra F K] [Algebra F Ω]
      [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] [IsGalois F K],
      Module.finrank F K = d → IsSolvable (K ≃ₐ[F] K) → Good F K Ω := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd hsol
  by_cases h1 : Module.finrank F K = 1
  · exact good_one h h1 (UpperTheory.V.Z.Bc.solC h.pr h.pr.cyc F K Ω hsol inferInstance inferInstance)
  by_cases hp : (Module.finrank F K).Prime
  · exact good_prime h hp (UpperTheory.V.Z.Bc.solC h.pr h.pr.cyc F K Ω hsol inferInstance inferInstance)
  obtain ⟨E, hb, ht, hg, hE0⟩ := UpperTheory.solvable_cm_extension_tower F K hsol (Or.inr inferInstance) (Or.inr inferInstance) h1 hp
  haveI hE : IsCMField E := hE0.resolve_left fun hR => by
    obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact (InfinitePlace.not_isReal_iff_isComplex.2 ((isTotallyComplex_of_algebra F E).isComplex v)) (hR.isReal v)
  have hmul : Module.finrank F E * Module.finrank E K = d := by rw [Module.finrank_mul_finrank, hd]
  have p1 : 0 < Module.finrank F E := Module.finrank_pos
  have p2 : 0 < Module.finrank E K := Module.finrank_pos
  have n1 : Module.finrank F E ≠ 1 := fun e => hb (IntermediateField.finrank_eq_one_iff.1 e)
  have n2 : Module.finrank E K ≠ 1 := fun e => ht (IntermediateField.finrank_eq_one_iff_eq_top.1 e)
  have l1 : Module.finrank F E < d := by
    rw [← hmul]; exact lt_mul_of_one_lt_right p1 (by omega)
  have l2 : Module.finrank E K < d := by
    rw [← hmul]; exact lt_mul_of_one_lt_left p2 (by omega)
  haveI : Group.IsSolvable (K ≃ₐ[F] K) := hsol
  have s1 : IsSolvable (E ≃ₐ[F] E) :=
    Group.isSolvable_of_surjective (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) K)
  have s2 : IsSolvable (K ≃ₐ[E] K) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom F : (K ≃ₐ[E] K) →* (K ≃ₐ[F] K)))
      (AlgEquiv.restrictScalars_injective F)
  refine good_trans h F E K Ω ?_
  intro iA i1 i2 i3
  exact ⟨ih _ l1 F E Ω rfl s1, ih _ l2 E K Ω rfl s2, UpperTheory.V.Z.Bc.solC h.pr h.pr.cyc F E Ω s1 inferInstance hE⟩

end UpperTheory.V.Z.Win

open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.aUpDownOf :
    UpperTheory.V.Z.Win.AUpDownOf := by
  intro hW hF hT0 hT1 hU hO H R F K Ω _ _ _ _ _ _ _ _ _ _ _ _ _ hsol l _ ι n hn r hr hirr hpol ha hf
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) K⟩
  exact good_all ⟨H, R, hW, hF, hT0, hT1, hU, hO⟩ _ F K Ω rfl hsol l ι n hn r hr hirr hpol ha hf
