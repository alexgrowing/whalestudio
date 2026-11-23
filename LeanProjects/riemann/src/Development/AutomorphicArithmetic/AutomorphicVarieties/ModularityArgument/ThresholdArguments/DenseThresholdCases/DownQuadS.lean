import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsoOfFrobOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCentChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PolGL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol UpperTheory.V.Z.Bc
private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)
private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem isoOfFrobOne (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)) (hr : Continuous r)
    (hr' : Continuous r') (hs : IsSSRep r) (hs' : IsSSRep r')
    (hw : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 →
      ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) : RepIso r r' := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, hd, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv hd
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
private theorem normV_one {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) (h : w.asIdeal.inertiaDeg ℤ = 1) : normV w = normV (w.under (𝓞 K)) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [Ideal.inertiaDeg_tower (R := ℤ) (w.under (𝓞 K)).asIdeal w.asIdeal] at h
  rw [normV_under (K := K) w, Nat.eq_one_of_mul_eq_one_left h, pow_one]
theorem UpperTheory.V.Z.Bc.automorphic_rank_two_of_automorphic_restrict_of_finite_det :
    ∀ (H : _root_.UpperTheory.V.Af.HypothesesH') (cyc : DescS) (hG : GapTwo) (hR : ExRTwo) (M Ω : Type) [Field M] [NumberField M] [Field Ω] [Algebra ℚ Ω]
      [Algebra M Ω] [IsScalarTower ℚ M Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure M Ω] (hp : Module.finrank ℚ M = 2) (hM : IsCMField M)
      (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hr : Continuous r)
      (hirr : IsIrr (r.comp (resG ℚ M Ω))) (hfin : ∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (r s) ^ N = 1), IsAut ι (r.comp (resG ℚ M Ω)) → IsAut ι r := by
  intro H cyc hG hR M Ω _ _ _ _ _ _ _ _ hp hM l _ ι r hr hirr hfin
  haveI : Algebra.IsQuadraticExtension ℚ M := ⟨hp⟩
  have hK : IsTotallyReal ℚ := inferInstance
  have hdown := cyc M hp inferInstance
  have hss : IsSSRep (r.comp (resG ℚ M Ω)) := (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr
  have hirr' : IsIrr r := (Bc.irrBasic.1 _ _ _ 2 r).1 _ hirr
  have hcont := continuous_restrictScalarsHom ℚ M Ω
  rintro ⟨sat', inf', hc', hreg', hatt'⟩
  have hgap : Gap2 inf' := by
    rcases hc' with ⟨_, P, rfl, rfl⟩ | ⟨hR', -⟩
    · refine hG M Ω l ι _ P ((GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_) hatt' (hfin.imp fun N h => ⟨h.1, fun s => h.2 _⟩)
      obtain ⟨m, hm, h⟩ := hreg' τ
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) hm]
      exact h
    · exact (not_both M hR' inferInstance).elim
  obtain ⟨sat, inf, hc, hbc, hinf⟩ := hdown sat' inf' hc' hreg' hgap (UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties ℚ M Ω l ι 2 r sat' hatt')
  have hreg : RegInf 2 inf := fun τ => by
    obtain ⟨m, hm, h⟩ := hreg' (ComplexEmbedding.lift M τ)
    have := hinf _ m hm
    rw [ComplexEmbedding.lift_comp_algebraMap] at this
    exact ⟨m, this, h⟩
  obtain ⟨r₁, hr₁, hatt₁⟩ := (show ∃ r₁ : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous r₁ ∧ AttachedSys ι r₁ sat by
    rcases hc with ⟨hC, -⟩ | ⟨hR', π, rfl, rfl⟩
    · exact (not_both ℚ hK hC).elim
    · obtain ⟨ω, hω, -⟩ := _root_.UpperTheory.V.Sd.Wc.centChar_alt H.toClassicalTheorems ℚ π
      refine hR ℚ Ω l ι π ω (fun v => ?_) ⟨fun v v' => by rw [Subsingleton.elim v v'], _root_.UpperTheory.V.Sd.Wc.polGL2_alt H.toClassicalTheorems ℚ π ω hω⟩
      have := hreg v.embedding
      simpa only [InfinitePlace.mk_embedding] using this)
  have hN := (UpperTheory.galois_representation_image_spec ℚ M Ω).1
  have hss₁ := UpperTheory.semisimpleModule_restriction_to_normal_subgroup _ _ _ 2 r₁ (resG ℚ M Ω) hN hatt₁.1
  have hiso : RepIso (r₁.comp (resG ℚ M Ω)) (r.comp (resG ℚ M Ω)) := by
    refine isoOfFrobOne M Ω l ι 2 _ _ (hr₁.comp hcont) (hr.comp hcont) hss₁ hss ?_
    filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under ℚ M).eventually hatt₁.2, hatt'.2]
      with w h1 ⟨B₁, hB₁, h₁⟩ ⟨B', hB', h'⟩ hd
    have hn := normV_one (K := ℚ) w hd
    obtain ⟨B, hB, hP⟩ := h1 hn
    obtain rfl := cusp_unique hc _ _ _ hB hB₁
    obtain rfl := cusp_unique hc' _ _ _ hP hB'
    have h3 := (UpperTheory.frobenius_power_compatibility ℚ M Ω l ι w 1 (by rw [pow_one]; exact hn)).1 2 r₁ _ h₁
    simp only [pow_one, Multiset.map_id'] at h3
    rw [← hn] at h3
    exact ⟨_, h3, h'⟩
  obtain ⟨δ, hδ, hiso'⟩ := UpperTheory.schur_extension _ _ _ 2 r r₁ (resG ℚ M Ω) hN hirr hiso
  have hF := UpperTheory.finiteCharacter_of_algebraic_cyclotomic (_root_.UpperTheory.V.Af.algOfCyc_s H)
  obtain ⟨sat₂, inf₂, hc₂, hreg₂, hatt₂⟩ := _root_.UpperTheory.V.Af.twist_invariance_automorphic H ℚ Ω l ι 2 r₁ δ ⟨sat, inf, hc, hreg, hatt₁⟩
    (hF.1 ℚ Ω l ι δ (hF.2 ℚ M Ω l δ hδ))
  exact ⟨sat₂, inf₂, hc₂, hreg₂, (Bc.irrBasic.1 _ Unit _ 2 _).2.1 hirr',
    hatt₂.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso hiso'⟩⟩
end
