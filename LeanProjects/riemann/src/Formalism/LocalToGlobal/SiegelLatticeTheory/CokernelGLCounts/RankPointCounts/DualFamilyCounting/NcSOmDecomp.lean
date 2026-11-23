import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitSk
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RpAbsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RPGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FiniteOnCompacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DetAdm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.OmDecompPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.SG.Pf.NcS.SplitSk
open PI.VolStabS.PositiveNearLattice PI.VolStabS.TopoNuFin
open scoped TensorProduct ENNReal

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem projV_ext {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ} {x y : Fin a → Fin M → Af F ⊗[F] E}
    (h : ∀ v, projV v x = projV v y) : x = y := by
  funext i j
  rw [eq_sum_crd b (Af F) (x i j), eq_sum_crd b (Af F) (y i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine FiniteAdeleRing.ext (K := F) fun v => ?_
  have e1 := PI.VolStabS.AdmissibleCompactSupport.crd_projV b x v i j k
  have e2 := PI.VolStabS.AdmissibleCompactSupport.crd_projV b y v i j k
  rw [← e1, ← e2, h v]

theorem finCpt_of_int (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ν : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (key : ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
      (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
      Integrable Φ ν)
    (K : Set (Fin a → Fin M → AF F ⊗[F] E)) (hK : IsCompact K) : ν K < ⊤ := by
  classical
  let b := Module.finBasis F E
  have hKi : IsCompact (projInf '' K) := hK.image (continuous_projInf b)
  obtain ⟨f, hf1, -, hfc, -⟩ :=
    exists_continuous_one_zero_of_isCompact hKi isClosed_empty (Set.disjoint_empty _)
  let Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ := fun Y => ((f Y : ℝ) : ℂ)
  have hΦic : Continuous Φinf := Complex.continuous_ofReal.comp f.continuous
  have hΦis : HasCompactSupport Φinf := hfc.comp_left Complex.ofReal_zero
  have hKf : IsCompact (projFin '' K) := hK.image (continuous_projFin b)
  let Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun v => projV v '' (projFin '' K)
  have hKv : ∀ v, IsCompact (Kv v) := fun v => hKf.image (PI.VolStabS.TopoMeas.continuous_projV b v)
  have hev : ∀ᶠ v in cofinite, Kv v ⊆ latV b v := by
    have h := fun (x : Fin a) (i : Fin M) (k : Fin (Module.finrank F E)) =>
      eventually_int_of_compact (hKf.image
        (f := fun Y : Fin a → Fin M → Af F ⊗[F] E => crd b (Af F) (Y x i) k)
        ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply x))))
    filter_upwards [eventually_all.2 fun x => eventually_all.2 fun i => eventually_all.2 fun k =>
      h x i k] with v hv
    rintro _ ⟨Y, hY, rfl⟩ x i k
    have e := crd_map b (evalV F v) (Y x i) k
    change crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Y x i)) k ∈ _
    rw [e]
    exact hv x i k _ ⟨Y, hY, rfl⟩
  choose C hCo hCc hKC using fun v => exists_clopen_compact b v (hKv v)
  let Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun v => if Kv v ⊆ latV b v then latV b v else C v
  have hCvo : ∀ v, IsClopen (Cv v) := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact isClopen_latV b v a M
    · rw [show Cv v = C v from if_neg h]; exact hCo v
  have hCvc : ∀ v, IsCompact (Cv v) := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact isCompact_latV b v a M
    · rw [show Cv v = C v from if_neg h]; exact hCc v
  have hKCv : ∀ v, Kv v ⊆ Cv v := fun v => by
    by_cases h : Kv v ⊆ latV b v
    · rw [show Cv v = latV b v from if_pos h]; exact h
    · rw [show Cv v = C v from if_neg h]; exact hKC v
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (Cv v).indicator 1
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun Y => ∏ᶠ v, Φv v (projV v Y)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hSB : ∀ v, IsSB (Φv v) := fun v =>
    ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) (hCvo v)).isLocallyConstant,
      HasCompactSupport.intro' (hCvc v) (hCvo v).isClosed fun Y hY => Set.indicator_of_notMem hY _⟩
  have hpure : IsPureFin b Φf Φv := by
    refine ⟨hSB, ?_, fun _ => rfl⟩
    filter_upwards [hev] with v hv
    simp only [Φv, Cv, hv, if_true]
  have hint := key _ b Φ Φinf Φf Φv hΦic hΦis hpure (fun _ => rfl)
  have hone : ∀ X ∈ K, Φ X = 1 := by
    intro X hX
    have h1 : Φinf (projInf X) = 1 := by
      simp only [Φinf, hf1 ⟨X, hX, rfl⟩, Pi.one_apply, Complex.ofReal_one]
    have h2 : Φf (projFin X) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      exact Set.indicator_of_mem (hKCv v ⟨projFin X, ⟨X, hX, rfl⟩, rfl⟩) _
    simp only [Φ, h1, h2, mul_one]
  calc ν K ≤ ν {X | 1 ≤ ‖Φ X‖ₑ} := measure_mono fun X hX => by
        simp [hone X hX]
    _ ≤ ∫⁻ X, ‖Φ X‖ₑ ∂ν := by
        have := mul_meas_ge_le_lintegral₀ hint.aestronglyMeasurable.enorm 1
        simpa using this
    _ < ⊤ := hint.2

end SlopeTestRemainingChoices

theorem omega_decomposition_holds : OmDecomp := by
  intro F E _ _ _ _ _ σ n J ψ a X0 hT νX hStd hdet ha hn hSWa hSWc hOm μinf νinf fibInf hμ hν hfib
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set TI := hermOf (Ainf F) σ (gramE σ J X0) hT with hTI

  have hA1 := hOm.2.2 μinf hμ
  have hA2 := hA1.2 νinf hν
  obtain ⟨μv, hμv⟩ := hA2.1
  have hA3 := hA2.2 μv hμv
  obtain ⟨νv, hνv⟩ := hA3.1
  have hA4 := hA3.2 νv hνv
  have hA5 := hA4.2 fibInf hfib
  obtain ⟨fibV, hfv⟩ := hA5.1
  have hQ := hA5.2 fibV hfv
  have cF := PI.VolStabS.rpFib_holds F E σ hStd.1 n J hStd.2.1 hSWa hSWc a ha hn X0 hT hdet
  obtain ⟨hsfI, hintI⟩ := cF.1 μinf νinf fibInf hfib
  have hFv := fun v => cF.2 v (μv v) (νv v) (fibV v) (hfv v)
  have hSB : ∀ v (Φ : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ), IsSB Φ →
      Integrable Φ (fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) :=
    fun v Φ h => (hFv v).2 Φ h.1.continuous h.2
  let b := Module.finBasis F E
  have hmult : ∀ (Φf : (Fin a → Fin n → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) :=
    fun Φf Φv hp => (hQ _ b 0 0 Φf Φv continuous_const HasCompactSupport.zero hp
      (fun X => by simp)).2.1
  have hνXfin : ∀ K, IsCompact K → νX K < ⊤ :=
    fun K hK => finCpt_of_int σ J νX (fun d b Φ Φinf Φf Φv h1 h2 h3 h4 => (hQ d b Φ Φinf Φf Φv h1 h2 h3 h4).1) K hK
  rcases PI.VolStabS.RestrProdA.rpTail_holds F E σ hStd.1 n J hStd.2.1 hSWa hSWc a ha hn X0 hT hdet
      fibV _ b hSB hmult with ⟨v0, hv0⟩ | hconv
  ·
    have hν0 : νX = 0 := by
      refine PI.VolStabS.DeterminantAdmissible.detAdm_gen νX 0 hνXfin (fun K _ => by simp) ?_
      rintro Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩
      obtain ⟨-, -, hEq⟩ := hQ d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr
      have h0 : HasProd (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))) 0 :=
        hasProd_zero_of_exists_eq_zero ⟨v0, hv0 _ (hp.1 v0)⟩
      rw [hEq, h0.tprod_eq, mul_zero, integral_zero_measure]
    refine ⟨0, fun A S _ => ?_⟩
    rw [hν0]
    simp
  · let W : HeightOneSpectrum (𝓞 F) → Type := fun v => Fin a → Fin n → Fv F v ⊗[F] E
    let m : ∀ v, Measure (W v) := fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)
    have : ∀ v, SigmaFinite (m v) := fun v => (hFv v).1
    have := hsfI
    have hLm : ∀ v, MeasurableSet (latV (M := n) (n := a) b v) := fun v =>
      (isClopen_latV b v a n).isOpen.measurableSet
    have hLf : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
      have h := hSB v _ (isSB_latV b v a n)
      rw [integrable_indicator_iff (hLm v)] at h
      exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
    obtain ⟨ρ, hρsf, hρgood, hρmarg, hρint⟩ :=
      PI.VolStabS.rpAbs_holds (HeightOneSpectrum (𝓞 F)) W m (fun v => latV b v) hLm hLf hconv
    have := hρsf
    obtain ⟨Γ, hΓm, hΓ⟩ := PI.VolStabS.rpGlue_holds F E n a _ b
    let P : Measure ((Fin a → Fin n → Ainf F ⊗[F] E) × ∀ v, W v) := (fibInf TI).prod ρ
    have hgood : P (Set.univ ×ˢ {x : ∀ v, W v | ¬ ∀ᶠ v in Filter.cofinite, x v ∈ latV b v}) = 0 := by
      rw [Measure.prod_prod, hρgood, mul_zero]
    have hae' : ∀ᵐ p ∂P, ∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v := by
      rw [ae_iff]
      exact measure_mono_null (fun p hp => Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩) hgood

    have hν0 : ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E) (Φ : (Fin a → Fin n → AF F ⊗[F] E) → ℂ)
        (Φinf : (Fin a → Fin n → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin n → Af F ⊗[F] E) → ℂ)
        (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ),
        Continuous Φinf → HasCompactSupport Φinf → IsPureFin b' Φf Φv → IsProdInfFin Φ Φinf Φf →
        Integrable Φ (P.map Γ) ∧
        ∫ X, Φ X ∂(P.map Γ) = (∫ X, Φinf X ∂(fibInf TI)) *
          ∏' v, ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) := by
      intro d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr
      have hΦm : Measurable Φ :=
        PI.VolStabS.TopoMeas.measurable_adm Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩
      have hf : ∀ v, Integrable (Φv v) (m v) := fun v => hSB v _ (hp.1 v)
      have hfc : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1 :=
        (hp.2.1.and (PI.VolStabS.RestrProdA.latCofin_holds F E a n d' _ b' b)).mono
          fun v h => h.1.trans (by rw [h.2])
      obtain ⟨hIρ, hHP⟩ := hρint Φv hf hfc
      have hae : (fun p => Φ (Γ p)) =ᵐ[P] fun p => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v) := by
        filter_upwards [hae'] with p hp'
        obtain ⟨e1, e2⟩ := hΓ p hp'
        rw [hpr (Γ p), hp.2.2 (projFin (Γ p)), e1]
        congr 1
        exact finprod_congr fun v => by rw [e2 v]
      have hPI : Integrable (fun p : _ × (∀ v, W v) => Φinf p.1 * ∏ᶠ v, Φv v (p.2 v)) P :=
        (hintI Φinf hc1 hc2).mul_prod hIρ
      refine ⟨(integrable_map_measure hΦm.aestronglyMeasurable hΓm.aemeasurable).2
        (hPI.congr hae.symm), ?_⟩
      rw [integral_map hΓm.aemeasurable hΦm.aestronglyMeasurable, integral_congr_ae hae,
        integral_prod_mul (fun y => Φinf y) (fun x : ∀ v, W v => ∏ᶠ v, Φv v (x v)),
        ← hHP.tprod_eq]
    have hνeq : νX = P.map Γ := by
      refine PI.VolStabS.DeterminantAdmissible.detAdm_gen νX (P.map Γ) hνXfin
        (finCpt_of_int σ J (P.map Γ) fun d b Φ Φinf Φf Φv h1 h2 h3 h4 =>
          (hν0 d b Φ Φinf Φf Φv h1 h2 h3 h4).1) ?_
      rintro Φ ⟨d', b', Φinf, Φf, Φv, hc1, hc2, hp, hpr⟩
      rw [(hQ d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr).2.2, (hν0 d' b' Φ Φinf Φf Φv hc1 hc2 hp hpr).2]

    let G : (∀ v, W v) → (Fin a → Fin n → Af F ⊗[F] E) := fun x => projFin (Γ (0, x))
    have hGm : Measurable G :=
      (continuous_projFin b).measurable.comp (hΓm.comp measurable_prodMk_left)
    have hΓG : ∀ p : (Fin a → Fin n → Ainf F ⊗[F] E) × (∀ v, W v),
        (∀ᶠ v in Filter.cofinite, p.2 v ∈ latV b v) → projInf (Γ p) = p.1 ∧ projFin (Γ p) = G p.2 := by
      intro p hp
      refine ⟨(hΓ p hp).1, projV_ext b fun v => ?_⟩
      rw [(hΓ p hp).2 v]
      exact ((hΓ (0, p.2) hp).2 v).symm
    have hρae : ∀ᵐ y ∂ρ, ∀ᶠ v in Filter.cofinite, y v ∈ latV b v := by
      rw [ae_iff]; exact hρgood
    refine ⟨ρ.map G, fun A S hS => ?_⟩
    rw [Measure.map_apply hGm hS, hνeq]
    set c := ∫⁻ z, A z ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) with hcdef
    set I : (Fin a → Fin n → AF F ⊗[F] E) → ℝ≥0∞ := fun y => A (projInf y) * S.indicator 1 (projFin y)
      with hIdef
    apply le_antisymm
    · obtain ⟨h, hhm, hhle, hheq⟩ := exists_measurable_le_lintegral_eq (P.map Γ) I
      rw [hheq, lintegral_map hhm hΓm, lintegral_prod_symm (fun z => h (Γ z)) (hhm.comp hΓm).aemeasurable]
      calc ∫⁻ y, ∫⁻ x, h (Γ (x, y)) ∂(fibInf TI) ∂ρ ≤ ∫⁻ y, (G ⁻¹' S).indicator (fun _ => c) y ∂ρ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hρae] with y hy
            have hxy := fun x => hΓG (x, y) hy
            by_cases hyS : G y ∈ S
            · rw [Set.indicator_of_mem (show y ∈ G ⁻¹' S from hyS)]
              refine lintegral_mono fun x => ?_
              calc h (Γ (x, y)) ≤ I (Γ (x, y)) := hhle _
                _ = A x := by
                  simp only [hIdef, (hxy x).1, (hxy x).2, Set.indicator_of_mem hyS, Pi.one_apply, mul_one]
            · rw [Set.indicator_of_notMem (show y ∉ G ⁻¹' S from hyS)]
              refine le_of_eq (lintegral_eq_zero_iff' ?_ |>.2 ?_) |>.trans (le_refl _)
              · exact (hhm.comp (hΓm.comp measurable_prodMk_right)).aemeasurable
              · refine Filter.Eventually.of_forall fun x => ?_
                have := hhle (Γ (x, y))
                simp only [hIdef, (hxy x).1, (hxy x).2, Set.indicator_of_notMem hyS, mul_zero] at this
                exact le_antisymm this (zero_le')
        _ = c * ρ (G ⁻¹' S) := lintegral_indicator_const (hGm hS) c
        _ = ρ (G ⁻¹' S) * c := mul_comm _ _
    · by_cases hc0 : c = 0
      · rw [hc0, mul_zero]; exact zero_le'
      obtain ⟨A', hA'm, hA'le, hA'eq⟩ := exists_measurable_le_lintegral_eq (fibInf TI) A
      have hIm : Measurable (fun y : Fin a → Fin n → AF F ⊗[F] E =>
          A' (projInf y) * S.indicator 1 (projFin y)) :=
        (hA'm.comp (continuous_projInf b).measurable).mul
          ((measurable_one.indicator hS).comp (continuous_projFin b).measurable)
      calc ρ (G ⁻¹' S) * c = (∫⁻ x, A' x ∂(fibInf TI)) * ∫⁻ y, (G ⁻¹' S).indicator 1 y ∂ρ := by
            rw [lintegral_indicator_one (hGm hS), ← hA'eq, mul_comm]
        _ = ∫⁻ p, A' p.1 * (G ⁻¹' S).indicator 1 p.2 ∂P :=
            (lintegral_prod_mul hA'm.aemeasurable (measurable_one.indicator (hGm hS)).aemeasurable).symm
        _ = ∫⁻ p, (fun y => A' (projInf y) * S.indicator 1 (projFin y)) (Γ p) ∂P := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae'] with p hp
            obtain ⟨e1, e2⟩ := hΓG p hp
            simp only [e1, e2]
            rfl
        _ = ∫⁻ y, A' (projInf y) * S.indicator 1 (projFin y) ∂(P.map Γ) := (lintegral_map hIm hΓm).symm
        _ ≤ ∫⁻ y, I y ∂(P.map Γ) := lintegral_mono fun y => by
            simp only [hIdef]
            gcongr
            exact hA'le _

end Formalism.L2.SG.Pf.NcS.OmDecompPf
