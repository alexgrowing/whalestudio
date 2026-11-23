import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEntryLeMRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIntIndMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalSplitOfPointwise
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsQuadCharUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdChEOfOrdUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorHalfNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticUniformizerOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralSubst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrInertOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AddCharConductorInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerSphericalSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCpowLtOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorSplitPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LfVInert
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RamifiedQuadraticExtensionUniformizer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticExtensionUniformizerValuationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerMemSphericalSpanStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitStandardVector

theorem isUnit1_localChar {K : Type} [Field K] [NumberField K] (c : HeckeCharacter K) (w : PlK K) :
    IsUnit1 (localChar c w) := by
  refine ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => ?_⟩
  rw [GroundTheory.Automorphic.GodementSection.coe_localChar]
  exact Circle.norm_coe _

theorem exists_sqrt_unit (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) : ∃ b : ℂˣ, b ^ 2 = a ∧ ‖(b : ℂ)‖ = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) (n := 2) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact a.ne_zero (by simpa using hz.symm)
  refine ⟨Units.mk0 z hz0, Units.ext (by simpa using hz), ?_⟩
  have h2 : ‖z‖ ^ 2 = 1 := by rw [← norm_pow, hz, ha]
  have h0 : 0 ≤ ‖z‖ := norm_nonneg z
  simpa using (pow_eq_one_iff_of_nonneg h0 (by norm_num)).1 h2

section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem indicator_eq_phiS :
    Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} (1 : F × F → ℂ) = phiS := by
  funext x
  by_cases h1 : x.1 ∈ 𝒪[F]
  · by_cases h2 : x.2 ∈ 𝒪[F]
    · rw [Set.indicator_of_mem (show x ∈ {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} from ⟨h1, h2⟩)]
      simp [phiS, intInd_of_mem h1, intInd_of_mem h2]
    · rw [Set.indicator_of_notMem (fun h => h2 h.2)]
      simp [phiS, intInd_of_notMem h2]
  · rw [Set.indicator_of_notMem (fun h => h1 h.1)]
    simp [phiS, intInd_of_notMem h1]

theorem sphN_WcS_phiS (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (hχ : Ad3.IsStd χ)
    (hc₁ : IsUnramifiedChar c₁) (hc₂ : IsUnramifiedChar c₂) : SphN (GL2LocalData.WcS χ c₁ c₂ phiS) := by
  have H1 := GlobalTheory.CompanionTheory.SphTheta.SplitRW.rW_phiS F χ hχ
  have H2 := RowIwasawa.iwasawa_lower_row F
  have key : ∀ g : GL (Fin 2) F, GL2LocalData.WcS χ c₁ c₂ phiS g =
      ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det g) (1 / 2) *
        ((((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (xRow g) : ℂ) *
          ∫ u, sphJ c₁ c₂ (g.val).det (mRow g) u ∂multHaar F) := by
    intro g
    unfold GL2LocalData.WcS
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [H1 g u, sphJ]
    ring
  refine ⟨?_, ?_⟩
  · intro k hk g
    obtain ⟨hm, hD, hM, hx⟩ := H2 g k hk
    have hk1 : modulus (k.val).det = 1 := by
      have := (H2 1 k hk).2.1
      simpa using this
    have hdet : Matrix.GeneralLinearGroup.det (g * k) =
        Matrix.GeneralLinearGroup.det g * Matrix.GeneralLinearGroup.det k := map_mul _ _ _
    have hc : ((c₁ (Matrix.GeneralLinearGroup.det (g * k)) : ℂˣ) : ℂ) =
        ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
      rw [hdet, map_mul, Units.val_mul, char_eq_one hc₁ (u := Matrix.GeneralLinearGroup.det k) hk1, mul_one]
    have hmp : mp (Matrix.GeneralLinearGroup.det (g * k)) (1 / 2) =
        mp (Matrix.GeneralLinearGroup.det g) (1 / 2) := by
      unfold mp
      have : modulus ((Matrix.GeneralLinearGroup.det (g * k) : Fˣ) : F) =
          modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) := hD
      rw [this]
    rw [key, key, hc, hmp, hM, sphJ_congr c₁ c₂ hD hM]
    by_cases hle : modulus (g.val).det ≤ modulus (mRow g) ^ 2
    · have ht := hx hle
      have h1 : χ (xRow (g * k) - xRow g) = 1 := by
        have h := isTrivialOn_addCharConductor hχ.1 hχ.2.1
        rw [hχ.2.2] at h
        exact h _ (mem_valBall_zero_iff.2 ht)
      have h2 : χ (xRow (g * k)) = χ (xRow g) := by
        have e : xRow (g * k) = (xRow (g * k) - xRow g) + xRow g := by ring
        rw [e, AddChar.map_add_eq_mul, h1, one_mul]
      rw [h2]
    · have h0 : (fun u => sphJ c₁ c₂ (g.val).det (mRow g) u) = fun _ => 0 :=
        funext (sphJ_eq_zero c₁ c₂ hm hle)
      simp only [h0, integral_zero, mul_zero]
  · rw [key]
    have hm1 : mRow (1 : GL (Fin 2) F) = 1 := by
      simp [mRow]
    have hx1 : xRow (1 : GL (Fin 2) F) = 0 := by
      simp [xRow]
    have hJ : (fun u => sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u) =
        (unitFiltrationUnits F 0 : Set Fˣ).indicator (fun _ => (1 : ℂ)) := by
      funext u
      by_cases hu : u ∈ (unitFiltrationUnits F 0 : Set Fˣ)
      · have hu1 : modulus (u : F) = 1 := mem_units_iff_modulus.1 hu
        rw [Set.indicator_of_mem hu]
        have e1 : ((c₂ u)⁻¹ : ℂˣ) = 1 := by
          have : c₂ u = 1 := hc₂ (mem_units_iff_modulus.2 hu1)
          rw [this, inv_one]
        unfold sphJ
        rw [e1, char_eq_one hc₁ hu1, intInd_of_mem, intInd_of_mem]
        · simp
        · rw [← modulus_le_one_iff]; simp [modulus_mul, hu1]
        · rw [← modulus_le_one_iff]; simp [modulus_mul, modulus_inv, hu1]
      · rw [Set.indicator_of_notMem hu]
        have hu1 : modulus (u : F) ≠ 1 := fun h => hu (mem_units_iff_modulus.2 h)
        unfold sphJ
        rcases lt_or_gt_of_ne hu1 with h | h
        · rw [intInd_of_notMem (x := (1 * (u : F))⁻¹)]
          · simp
          · rw [← modulus_le_one_iff, one_mul, modulus_inv, not_le]
            exact (one_lt_inv₀ (modulus_pos u.ne_zero)).2 h
        · rw [intInd_of_notMem (x := ((1 : GL (Fin 2) F).val).det * u / 1)]
          · simp
          · rw [← modulus_le_one_iff, not_le]
            simpa using h
    have hmeas : MeasurableSet (unitFiltrationUnits F 0 : Set Fˣ) := by
      exact (isOpen_unitFiltrationUnits 0).measurableSet
    have hint : ∫ u, sphJ c₁ c₂ ((1 : GL (Fin 2) F).val).det 1 u ∂multHaar F = 1 := by
      rw [hJ, integral_indicator_const _ hmeas]
      simp [Measure.real, multHaar_unitFiltrationUnits_zero]
    rw [hm1, hx1, hint]
    simp [mp]

theorem WcS_std_eq (χ : AddChar F Circle) (hχ : Ad3.IsStd χ) (c₁ c₂ : Fˣ →* ℂˣ) (u₁ : IsUnit1 c₁)
    (u₂ : IsUnit1 c₂) (r₁ : IsUnramifiedChar c₁) (r₂ : IsUnramifiedChar c₂) (g : GL (Fin 2) F) :
    GL2LocalData.WcS χ c₁ c₂ (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1) g =
      Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ)
        ![c₁ (unifUnit F), c₂ (unifUnit F)] g := by
  rw [indicator_eq_phiS]
  obtain ⟨-, h1, h2⟩ := GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial F χ hχ
  have hs := sphN_WcS_phiS χ c₁ c₂ hχ r₁ r₂
  have hm := GlobalTheory.T.compact_whittaker_mem_spherical_span F χ hχ c₁ c₂ u₁ u₂ r₁ r₂ phiS isLocallyConstant_phiS
    hasCompactSupport_phiS
  have := GlobalTheory.CompanionTheory.SphericalSpan.eq_mul_sphericalWhittaker F 2 _ h1 h2 _ _ hm
    (fun g k hk => hs.1 k hk g) g
  rwa [hs.2, one_mul] at this

end Split

section Inert

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [CharZero F]
  (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem indicator_eq_intInd : Set.indicator {x : E | x ∈ 𝒪[E]} (1 : E → ℂ) = intInd := by
  funext x
  by_cases h : x ∈ 𝒪[E]
  · rw [Set.indicator_of_mem (show x ∈ {x : E | x ∈ 𝒪[E]} from h)]
    simp [intInd, h]
  · rw [Set.indicator_of_notMem (show x ∉ {x : E | x ∈ 𝒪[E]} from h)]
    simp [intInd, h]

theorem Wc_intInd_right (h2 : Module.finrank F E = 2) (χ : AddChar F Circle) (η : Fˣ →* ℂˣ)
    (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ) (hχ : Ad3.IsStd χ) (hc : IsUnramifiedChar c)
    (hη1 : ∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) (hηu : IsUnramifiedChar η)
    (hform : ∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det →
      GL2LocalData.rW χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 =
      (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) *
        intInd ((t : E) * algebraMap F E (mRow g)⁻¹))
    (g k : GL (Fin 2) F) (hk : k ∈ GLnLocal.integralGL F 2) :
    GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd (g * k) =
      GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd g := by
  classical
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  have hrow := RowIwasawa.iwasawa_lower_row F
  have hdk : modulus (k.val).det = 1 := by
    have h1 := (hrow 1 k hk).2.1
    simpa using h1
  obtain ⟨s, hs⟩ : ∃ s : Eˣ, Algebra.norm F (s : E) = (k.val).det := by
    have hk0 : (k.val).det ≠ 0 := (Matrix.GeneralLinearGroup.det k).ne_zero
    have h1 := hη1 (Units.mk0 _ hk0)
    rw [InertAsm.char_congr η hηu (u := Units.mk0 _ hk0) (v := 1) (by simpa using hdk), map_one,
      Units.val_one, Units.val_mk0, GL2LocalData.nsg] at h1
    by_contra hn
    rw [if_neg hn] at h1
    norm_num at h1
  by_cases hg : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · obtain ⟨t, ht⟩ := hg
    have ht' : Algebra.norm F ((t * s : Eˣ) : E) = ((g * k).val).det := by
      rw [Units.val_mul, map_mul, ht, hs, Units.val_mul, Matrix.det_mul]
    rw [InertAsm.Wc_eq hc hform _ _ ht', InertAsm.Wc_eq hc hform _ _ ht]
    obtain ⟨hm0, hdet, hmm, hx⟩ := hrow g k hk
    exact InertAsm.val_eq hχ hη1 hηu hc ht ht' hm0 (hrow (g * k) 1 (one_mem _)).1 hdet hmm hx
  · have hg' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((g * k).val).det := by
      rintro ⟨t', ht'⟩
      refine hg ⟨t' * s⁻¹, ?_⟩
      have hs0 : Algebra.norm F (s : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 s.ne_zero
      have hmul : Algebra.norm F ((t' * s⁻¹ : Eˣ) : E) * Algebra.norm F (s : E) =
          Algebra.norm F (t' : E) := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel_right]
      have hd : ((g * k).val).det = (g.val).det * (k.val).det := by
        rw [Units.val_mul, Matrix.det_mul]
      rw [ht', hs, hd] at hmul
      exact mul_right_cancel₀ (hs ▸ hs0) hmul
    rw [GL2LocalData.Wc, GL2LocalData.Wc, dif_neg hg, dif_neg hg']

theorem Wc_std_eq (h2 : Module.finrank F E = 2) (hcont : Continuous (algebraMap F E))
    (hord : GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1)
    (χ : AddChar F Circle) (hχ : Ad3.IsStd χ) (σ : E ≃ₐ[F] E) (hσ : σ ≠ AlgEquiv.refl)
    (η : Fˣ →* ℂˣ) (hη : ∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) (c : Eˣ →* ℂˣ)
    (hc : IsUnramifiedChar c) (b : ℂˣ)
    (hb : b ^ 2 = c (Units.map (algebraMap F E).toMonoidHom (unifUnit F))) (g : GL (Fin 2) F) :
    GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) (GL2LocalData.lamE E χ η) c
                 (Set.indicator {x : E | x ∈ 𝒪[E]} 1) g =
      Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![b, -b] g := by
  obtain ⟨η', hη'⟩ := GlobalTheory.CompanionTheory.SphTheta.UnramQuad.exists_quadChar_unramified F E h2 hcont hord
  have hηe : η = η' := by
    ext a
    rw [hη, hη'.1]
  subst hηe
  have hstd := GlobalTheory.CompanionTheory.SphTheta.isStd_chE_of_ord_unif F E h2 hcont hord χ hχ
  have hlam := GlobalTheory.CompanionTheory.LamUnr.lamE_eq_one F E χ η hχ hstd hη'.2.1 hη'.2.2.1
  have hform := GlobalTheory.CompanionTheory.SphTheta.inert_rw F E h2 hcont hord χ η σ hσ hχ hstd hη'
    (GlobalTheory.CompanionTheory.NormGauss.gauss_main F E h2 hcont hord χ η hχ hstd hη')
  rw [hlam, indicator_eq_intInd]
  have hψ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar χ) x = 1 := by
    intro x hx
    have h1 := isTrivialOn_addCharConductor hχ.1 hχ.2.1 x
      (by rw [hχ.2.2]; exact mem_valBall_zero_iff.2 hx)
    simp [h1]
  have hg := Spherical.eq_iwasawa g
  have hu := Spherical.iwasawaUnip_mem g
  have hk := Spherical.iwasawaInt_mem g
  set u := Spherical.iwasawaUnip g
  set k := Spherical.iwasawaInt g
  set l := Iwasawa.iwasawaExponent F 2 g
  rw [hg, Spherical.sphericalWhittaker_apply hψ _ hu hk,
    Wc_intInd_right F E h2 χ η σ c hχ hc hη'.1 hη'.2.1 hform _ k hk, mul_assoc,
    GlobalTheory.CompanionTheory.SphTheta.WcLeft.Wc_unipotent_mul F E h2 hcont hord χ η σ c hχ hc hη' hform u _ hu,
    GlobalTheory.T.quadratic_extension_uniformizer_valuation F E h2 hcont hord χ η σ c hχ hc hη' hform b hb l]
  have hpsi : Whittaker.psiN (Circle.coeHom.compAddChar χ) u = (χ (u.val 0 1) : ℂ) := by
    simp [Whittaker.psiN, Whittaker.superdiagSum, Fin.sum_univ_two]
    rfl
  rw [hpsi]
  split_ifs with hl
  · ring
  · simp

end Inert

variable {K : Type} [Field K] [NumberField K]

theorem key (hd : Module.finrank ℚ K = 2) (D : Dat) (DK : DatK K) (hbc : IsBC D DK)
    (c : HeckeCharacter K) (v : Pl) (hv : v ∉ D.bad) (hw : Th.Unr c v)
    (Wt : GL (Fin 2) (Qv v) → ℂ) (hth : Th.StdTh c v Wt) :
    ∃ y : Fin 2 → ℂˣ, (∀ j, ‖((y j : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ g, Wt g = Spherical.sphericalWhittaker (Circle.coeHom.compAddChar (GP.psiF v)⁻¹) y g) ∧
      ∀ s : ℂ, lfV DK c v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * ((y j : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ ∧
        lfV DK c⁻¹ v s = ∏ i : Fin 3, ∏ j : Fin 2, (1 - ((![D.ν v (unifUnit (Qv v)), 1, (D.ν v (unifUnit (Qv v)))⁻¹] : Fin 3 → ℂˣ) i : ℂ) * (((y j)⁻¹ : ℂˣ) : ℂ) * (residueCard (Qv v) : ℂ) ^ (-s))⁻¹ := by
  have hχ : IsStd (GP.psiF v)⁻¹ := GlobalTheory.CompanionTheory.SphStd.isStd_psiF_inv v
  rcases hth with ⟨w₁, w₂, i₁, i₂, hne, rfl⟩ | ⟨w, i, hu, σ, η, hσ, hη, rfl⟩
  · obtain ⟨u₁, u₂, r₁, r₂, hl⟩ := GlobalTheory.CompanionTheory.SplitPrime.split_lfV K hd D DK hbc c v hv hw w₁ w₂ hne
    refine ⟨_, fun j => ?_, fun g => WcS_std_eq _ hχ _ _ u₁ u₂ r₁ r₂ g, hl⟩
    fin_cases j
    · exact u₁.2 _
    · exact u₂.2 _
  · obtain ⟨hfin, -, hb⟩ := GlobalTheory.CompanionTheory.InertFactor.lfV_inert K hd D DK hbc c v hv hw w hu
    have hord : GroundTheory.LocalField.ord (algebraMap (Qv v) (Kv K w) (unifUnit (Qv v) : Qv v)) = 1 := by
      rcases GlobalTheory.CompanionTheory.QuadPlace.split_or_inert_of_unramified K hd v (fun w' _ => (hw w').2) with
        ⟨w₁, w₂, h₁, h₂, hne⟩ | ⟨w', hw', -, -, ho⟩
      · exact absurd ((hu w₁ h₁).trans (hu w₂ h₂).symm) hne
      · obtain rfl := hu w' hw'
        exact ho
    have hU := isUnit1_localChar c w
    obtain ⟨b, hb2, hbn⟩ := exists_sqrt_unit
      (localChar c w (Units.map (algebraMap (Qv v) (Kv K w)).toMonoidHom (unifUnit (Qv v)))) (hU.2 _)
    refine ⟨![b, -b], fun j => ?_, fun g => Wc_std_eq (Qv v) (Kv K w) hfin
      (continuous_adicCompletionMap v w) hord _ hχ σ hσ η hη _ (hw w).1 b hb2 g, hb b hb2⟩
    fin_cases j
    · exact hbn
    · simpa using hbn

theorem main : ∀ (K : Type) [Field K] [NumberField K], Ad3.K.QuadraticBaseChangeGL3.CasselmanShalikaStandardVector K := by
  intro K _ _ hd D DK hbc c v hv hw Wt hth s hs
  obtain ⟨y, hy, hW, hl⟩ := key hd D DK hbc c v hv hw Wt hth
  have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  obtain ⟨-, h1, -⟩ := GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ
  have hone : GP.sph D v 1 = 1 := Spherical.sphericalWhittaker_one h1 _
  obtain ⟨a, b⟩ := GlobalTheory.CompanionTheory.UnramifiedZeta.unramified_sum (Qv v) (GP.psiF v) hψ (D.ν v) (D.unit v) (D.unr v hv) y hy Wt hW s hs
  rw [hone, one_mul, one_mul]
  exact ⟨a.trans (hl s).1.symm, b.trans (hl s).2.symm⟩

end GlobalTheory.CompanionTheory.SplitStandardVector
