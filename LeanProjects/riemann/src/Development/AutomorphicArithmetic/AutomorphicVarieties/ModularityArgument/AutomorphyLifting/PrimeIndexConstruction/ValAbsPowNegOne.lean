import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ThruBadAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IndGlue
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppSmo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Win.Birth

section Count

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem degs_le (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 F) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

private def pt (w w' : HeightOneSpectrum (𝓞 E)) (h : w'.under (𝓞 F) = w.under (𝓞 F)) :
    (w.under (𝓞 F)).asIdeal.primesOver (𝓞 E) :=
  ⟨w'.asIdeal, w'.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal h).symm⟩⟩

private theorem pt_ne {w a b : HeightOneSpectrum (𝓞 E)} {ha : a.under (𝓞 F) = w.under (𝓞 F)} {hb : b.under (𝓞 F) = w.under (𝓞 F)}
    (h : a ≠ b) : pt w a ha ≠ pt w b hb := fun e => h (HeightOneSpectrum.ext (congrArg Subtype.val e))

private theorem over_two (h2 : Module.finrank F E = 2) {w w' w'' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 F) = w.under (𝓞 F)) (hu' : w''.under (𝓞 F) = w.under (𝓞 F)) :
    normV w = normV (w.under (𝓞 F)) ∧ (w'' = w ∨ w'' = w') := by
  classical
  have := w.isPrime
  have := w'.isPrime
  have := w''.isPrime
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have h4 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  have h5 := w''.asIdeal.inertiaDeg_pos (𝓞 F)
  have hs := degs_le h2 (w.under (𝓞 F)) {pt w w rfl, pt w w' hu}
  rw [Finset.sum_pair (pt_ne hne.symm)] at hs
  simp only [pt] at hs
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.AboveL.SatBC.normV_under_pow F E w, show w.asIdeal.inertiaDeg (𝓞 F) = 1 by omega, pow_one]
  · by_contra hc
    push Not at hc
    have hs' := degs_le h2 (w.under (𝓞 F)) {pt w w rfl, pt w w' hu, pt w w'' hu'}
    rw [Finset.sum_insert (by simpa using ⟨pt_ne hne.symm, pt_ne hc.1.symm⟩), Finset.sum_pair (pt_ne hc.2.symm)] at hs'
    simp only [pt] at hs'
    omega

variable (sat : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop)

variable (F) in

private def HasPair (u : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = u ∧ w'.under (𝓞 F) = u

private def IsPair (u : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ) : Prop :=
  ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = u ∧ w'.under (𝓞 F) = u ∧
    ∃ B₁ B₂, sat w B₁ ∧ sat w' B₂ ∧ B = B₁ + B₂

private def IsRoots (u : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ) : Prop :=
  ∃ (w : HeightOneSpectrum (𝓞 E)) (B' : Multiset ℂˣ), w.under (𝓞 F) = u ∧ sat w (B'.map (· ^ 2)) ∧
    B = B' + B'.map (fun b => -b)

private def indSat (u : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ) : Prop :=
  IsPair sat u B ∨ (¬ HasPair (E := E) F u ∧ B = Classical.epsilon (IsRoots sat u))

variable {sat}

private theorem indSat_unique (h2 : Module.finrank F E = 2) (hu : ∀ w B B', sat w B → sat w B' → B = B')
    (u : HeightOneSpectrum (𝓞 F)) (B B' : Multiset ℂˣ) (h : indSat sat u B) (h' : indSat sat u B') : B = B' := by
  rcases h with ⟨w₁, w₂, hne, rfl, e₂, B₁, B₂, s₁, s₂, rfl⟩ | ⟨hn, rfl⟩
  · rcases h' with ⟨w₃, w₄, hne', e₃, e₄, B₃, B₄, s₃, s₄, rfl⟩ | ⟨hn, -⟩
    · rcases (over_two h2 hne.symm e₂ e₃).2 with rfl | rfl <;> rcases (over_two h2 hne.symm e₂ e₄).2 with rfl | rfl
      · exact absurd rfl hne'
      · rw [hu _ _ _ s₁ s₃, hu _ _ _ s₂ s₄]
      · rw [hu _ _ _ s₁ s₄, hu _ _ _ s₂ s₃, add_comm]
      · exact absurd rfl hne'
    · exact absurd ⟨w₁, w₂, hne, rfl, e₂⟩ hn
  · rcases h' with ⟨w₁, w₂, hne, e₁, e₂, -⟩ | ⟨-, rfl⟩
    · exact absurd ⟨w₁, w₂, hne, e₁, e₂⟩ hn
    · rfl

private theorem sq_surj : Function.Surjective (Multiset.map (· ^ 2) : Multiset ℂˣ → Multiset ℂˣ) := by
  refine Multiset.map_surjective_of_surjective fun z => ?_
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (n := 2) two_pos
  have h0 : x ≠ 0 := fun h => z.ne_zero (by rw [← hx, h]; simp)
  exact ⟨Units.mk0 x h0, Units.ext (by simpa using hx)⟩

private theorem indSys_indSat (h2 : Module.finrank F E = 2) (hex : ∀ᶠ w in Filter.cofinite, ∃ B, sat w B) :
    IndSys (F := F) sat (indSat sat) := by
  have hev : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∃ B, sat w B := by
    rw [Filter.eventually_cofinite] at hex ⊢
    refine (hex.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
    by_contra h0
    exact hv fun w hw => not_not.1 fun hP => h0 ⟨w, hP, hw⟩
  refine ((GlobalTheory.AboveL.SatBC.tendsto_under F E).eventually hev).mono fun w hw => ⟨fun w' hne hu => ?_, fun hq => ?_⟩
  · obtain ⟨B, hB⟩ := hw w rfl
    obtain ⟨B', hB'⟩ := hw w' hu
    exact ⟨B, B', hB, hB', Or.inl ⟨w, w', hne.symm, rfl, hu, B, B', hB, hB', rfl⟩⟩
  have hq1 : 1 < normV (w.under (𝓞 F)) := NumberField.HeightOneSpectrum.one_lt_absNorm _
  have hnp : ¬ HasPair (E := E) F (w.under (𝓞 F)) := by
    rintro ⟨a, b, hab, ha, hb⟩
    have e : normV w = normV (w.under (𝓞 F)) := by
      rcases (over_two h2 hab.symm (hb.trans ha.symm) (ha ▸ rfl : w.under (𝓞 F) = a.under (𝓞 F))).2 with rfl | rfl
      · exact (over_two h2 hab.symm (hb.trans ha.symm) rfl).1
      · exact (over_two h2 hab (ha.trans hb.symm) rfl).1
    rw [e] at hq
    nlinarith
  obtain ⟨B₀, h₀⟩ := hw w rfl
  obtain ⟨Bs, rfl⟩ := sq_surj B₀
  obtain ⟨w', B', hu, hs, he⟩ := Classical.epsilon_spec (p := IsRoots sat (w.under (𝓞 F))) ⟨_, w, Bs, rfl, h₀, rfl⟩
  obtain rfl : w' = w := by
    by_contra hc
    exact hnp ⟨w', w, hc, hu, rfl⟩
  exact ⟨_, B', hs, he, Or.inr ⟨hnp, rfl⟩⟩

end Count

private theorem algSat_val (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem eig_unique {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂ}
    (h : FrobEig ι r w B) (h' : FrobEig ι r w B') : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  have e := congrArg Polynomial.roots (((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ))
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e

section Tw

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {a : ℕ}

private theorem val_absPow_neg_one (u : HeightOneSpectrum (𝓞 K)) :
    (((GlobalTheory.HeckeGal.Model.absPow K (-1)).val u : ℂˣ) : ℂ) = (normV u : ℂ) := by
  rw [(GlobalTheory.HeckeGal.Model.absPow_isAbsPow K (-1)).2.1 u]
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem val_absPow_one (u : HeightOneSpectrum (𝓞 K)) :
    (((GlobalTheory.HeckeGal.Model.absPow K 1).val u : ℂˣ) : ℂ) = (normV u : ℂ)⁻¹ := by
  rw [(GlobalTheory.HeckeGal.Model.absPow_isAbsPow K 1).2.1 u]
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply, Complex.cpow_neg]

private theorem sat_tw {π : CuspSub K a} {w : HeightOneSpectrum (𝓞 K)} {B : Multiset ℂˣ} (h : (CG.mk π).HasSat w B) (s : ℝ) :
    (CG.mk (π.twist (GlobalTheory.HeckeGal.Model.absPow K s))).HasSat w (B.map (· * (GlobalTheory.HeckeGal.Model.absPow K s).val w)) :=
  GlobalTheory.SphGal.hasSatGL_twist K a π _ w B ((GlobalTheory.HeckeGal.Model.absPow_isAbsPow K s).1 w) h

end Tw

private theorem indSys_of_att {K M Ω : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field Ω]
    [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure M Ω] (h2 : Module.finrank K M = 2)
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {π : CuspSub M 2} {r : G M Ω →* GL (Fin 2) (Qbar l)} (hatt : AttC ι r π)
    {R : G K Ω →* GL (Fin 4) (Qbar l)} (H : IndCh (galEmb K M Ω) r R) {P : CuspSub K 4} (hP : AttC ι R P) :
    IndSys (F := K) (E := M) (CG.mk π).HasSat (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow K (-1)))).HasSat := by
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  have hu : ∀ w B B', (CG.mk π).HasSat w B → (CG.mk π).HasSat w B' → B = B' := fun _ _ _ h h' => h.unique h'
  have hsys := indSys_indSat (F := K) h2 (hatt.2.mono fun w ⟨B, h, _⟩ => ⟨B, h⟩)
  have hA := attInd K M Ω h2 l ι r R _ _ hu (indSat_unique h2 hu) hatt hsys hP.1 H
  have hl : ∀ᶠ u : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ u.asIdeal := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have key : ∀ᶠ u : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ B, indSat (F := K) (CG.mk π).HasSat u B →
      (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow K (-1)))).HasSat u B := by
    filter_upwards [hA.2, hP.2, hl] with u ⟨B, hB, hF⟩ ⟨Bp, hBp, hFp⟩ hlu B₂ hB₂
    obtain rfl := indSat_unique h2 hu _ _ _ hB₂ hB
    have hc : CharEig ι (cycBar K Ω l)⁻¹ u (normV u : ℂ) := by
      have := UpperTheory.V.Af.Es.charEig_cyc (Ω := Ω) ι hlu 1
      simpa using this
    have e := eig_unique (UpperTheory.frobenius_eigenvalues_twist K Ω l ι 4 R _ u _ _ hFp hc) hF
    have hq : (((normV u : ℝ) ^ ((((4 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2
        (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm u))) _).ne'
    have e2 : B₂ = Bp.map (· * (GlobalTheory.HeckeGal.Model.absPow K (-1)).val u) := by
      rw [algSat_val, algSat_val, Multiset.map_map] at e
      refine Multiset.map_injective (fun a b h => Units.ext (mul_left_cancel₀ hq h)) (e.symm.trans ?_)
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun b _ => ?_
      simp only [Function.comp_apply, Units.val_mul, val_absPow_neg_one]
      ring
    rw [e2]
    exact sat_tw hBp (-1)
  filter_upwards [hsys, (GlobalTheory.AboveL.SatBC.tendsto_under K M).eventually key] with w hw hk
  refine ⟨fun w' hne hw' => ?_, fun hq => ?_⟩
  · obtain ⟨B, B', h1, h2', h3⟩ := hw.1 w' hne hw'
    exact ⟨B, B', h1, h2', hk _ h3⟩
  · obtain ⟨B, B', h1, h2', h3⟩ := hw.2 hq
    exact ⟨B, B', h1, h2', hk _ h3⟩

theorem awInd : AwInd := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ h2 l _ ι π r hatt ⟨t, ht⟩ hb R H P _ hP
  have hs := indSys_of_att h2 hatt H hP
  have hQ : ∀ v, ImaginaryQuadraticEtaCharacter.WinAt (P.twist (GlobalTheory.HeckeGal.Model.absPow K (-1))) t v := fun v =>
    ImaginaryQuadraticEtaCharacter.winInd K M h2 _ π hs t v fun w => ⟨ht w.1, thruBad K M h2 π hb v w⟩
  obtain ⟨a, ha⟩ := ImaginaryQuadraticEtaCharacter.winTw K (GlobalTheory.HeckeGal.Model.absPow K 1)
  refine ⟨t + a, fun v => ImaginaryQuadraticEtaCharacter.suppSmo K 4 (by norm_num) _ _ ?_ (t + a) v (ha 4 (by norm_num) _ t v (hQ v))⟩
  refine hP.2.mono fun u ⟨B, hB, _⟩ => ⟨B, ?_, hB⟩
  have h1 := sat_tw (sat_tw hB (-1)) 1
  have hq : (normV u : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm u)).ne'
  have e : (B.map (· * (GlobalTheory.HeckeGal.Model.absPow K (-1)).val u)).map (· * (GlobalTheory.HeckeGal.Model.absPow K 1).val u) = B := by
    rw [Multiset.map_map]
    refine (Multiset.map_congr rfl fun b _ => ?_).trans (Multiset.map_id B)
    refine Units.ext ?_
    simp only [Function.comp_apply, Units.val_mul, val_absPow_neg_one, val_absPow_one, id]
    field_simp
  rwa [e] at h1

end UpperTheory.V.Z.Win.Birth
