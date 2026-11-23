import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualHaarMeasureInfiniteAdeles
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SdPi

section Abstract

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : Type} [Fintype P]

theorem exists_form (e : A ≃+* (P → ℝ)) (he' : Continuous e.symm)
    (χ : A → ℂ) (hχc : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) (hχa : ∀ x y, χ (x + y) = χ x * χ y)
    (hnd : ∀ x, (∀ y, χ (x * y) = 1) → x = 0) :
    ∃ a : P → ℝ, (∀ w, a w ≠ 0) ∧
      ∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * e x w : ℝ) : ℂ)) := by
  classical
  obtain ⟨L, hLc, hLa, hL⟩ := GlobalTheory.GaugeEx.SdInf.exists_log_char (fun u => χ (e.symm u))
    (hχc.comp he') (fun u => hχ1 _) (fun u v => by rw [map_add, hχa])
  let Lh : (P → ℝ) →+ ℝ := AddMonoidHom.mk' L hLa
  let Ll : (P → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := L, map_add' := hLa, map_smul' := fun c u => map_real_smul Lh hLc c u }
  let a : P → ℝ := fun w => L (fun j => if w = j then 1 else 0)
  have hform : ∀ u, L u = ∑ w, a w * u w := fun u => by
    have h := Ll.pi_apply_eq_sum_univ u
    change L u = ∑ i, u i • L (fun j => if i = j then 1 else 0) at h
    rw [h]
    exact Finset.sum_congr rfl fun w _ => by simp [a, mul_comm]
  have hchi : ∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * e x w : ℝ) : ℂ)) :=
    fun x => by
      have := hL (e x)
      simp only [RingEquiv.symm_apply_apply] at this
      rw [this, hform]
  refine ⟨a, fun w hw => ?_, hchi⟩
  have h0 : e.symm (fun j => if w = j then 1 else 0) = 0 := hnd _ fun y => by
    have : ∑ j, a j * e (e.symm (fun j => if w = j then (1 : ℝ) else 0) * y) j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        by_cases h : w = j
        · subst h; simp [hw]
        · simp [map_mul, h]
    rw [hchi, this]
    simp
  have h1 := congrFun (congrArg e h0) w
  simp at h1

def eqv (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm) : A ≃ₜ+ (P → ℝ) :=
  { e.toAddEquiv with
    continuous_toFun := he
    continuous_invFun := he' }

theorem eqv_apply (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm) (x : A) :
    eqv e he he' x = e x := rfl

def eqvPi (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm) (ι : Type) :
    (ι → A) ≃ₜ+ (ι × P → ℝ) :=
  { toFun := fun x q => e (x q.1) q.2
    invFun := fun u i => e.symm fun w => u (i, w)
    left_inv := fun x => by funext i; simp
    right_inv := fun u => by funext q; simp
    map_add' := fun x y => by funext q; simp
    continuous_toFun := continuous_pi fun q =>
      (continuous_apply q.2).comp (he.comp (continuous_apply q.1))
    continuous_invFun := continuous_pi fun i =>
      he'.comp (continuous_pi fun w => continuous_apply (i, w)) }

theorem eqvPi_apply (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm) (ι : Type)
    (x : ι → A) (q : ι × P) : eqvPi e he he' ι x q = e (x q.1) q.2 := rfl

end Abstract

section Meas

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] {P : Type} [Fintype P]

theorem map_pi_eq (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm)
    (k : Measure A) [SigmaFinite k] (c₀ : ℝ≥0∞) (h0 : c₀ ≠ 0) (ht : c₀ ≠ ⊤)
    (hm : k.map (eqv e he he') = c₀ • (volume : Measure (P → ℝ))) (ι : Type) [Fintype ι] :
    (Measure.pi fun _ : ι => k).map (eqvPi e he he' ι) =
      (∏ _i : ι, c₀) • (volume : Measure (ι × P → ℝ)) := by
  set c : ℝ≥0∞ := ∏ _i : ι, c₀ with hcdef
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => h0
  have hct : c ≠ ⊤ := ENNReal.prod_ne_top fun _ _ => ht
  have hEm : Measurable (eqvPi e he he' ι) := (eqvPi e he he' ι).continuous.measurable
  have hem : Measurable (eqv e he he') := (eqv e he he').continuous.measurable
  have hrect : ∀ s : ι × P → Set ℝ, (∀ q, MeasurableSet (s q)) →
      ((Measure.pi fun _ : ι => k).map (eqvPi e he he' ι)) (Set.pi Set.univ s) =
        c * ∏ q, volume (s q) := by
    intro s hs
    rw [Measure.map_apply hEm (MeasurableSet.univ_pi hs)]
    have hpre : eqvPi e he he' ι ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ fun i => eqv e he he' ⁻¹' Set.pi Set.univ fun w => s (i, w) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, eqvPi_apply,
        eqv_apply, Prod.forall]
    rw [hpre, Measure.pi_pi]
    have hi : ∀ i, k (eqv e he he' ⁻¹' Set.pi Set.univ fun w => s (i, w)) =
        c₀ * ∏ w, volume (s (i, w)) := fun i => by
      rw [← Measure.map_apply hem (MeasurableSet.univ_pi fun w => hs _), hm, Measure.smul_apply,
        smul_eq_mul, volume_pi_pi]
    simp only [hi]
    rw [Finset.prod_mul_distrib, Fintype.prod_prod_type]
  have hv : (volume : Measure (ι × P → ℝ)) =
      c⁻¹ • (Measure.pi fun _ : ι => k).map (eqvPi e he he' ι) := by
    rw [volume_pi]
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, hrect s hs, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct,
      one_mul]
  rw [hv, smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]

theorem selfDual_pi_of_form [LocallyCompactSpace A] (e : A ≃+* (P → ℝ)) (he : Continuous e)
    (he' : Continuous e.symm) (a : P → ℝ) (ha : ∀ w, a w ≠ 0) (χ : A → ℂ)
    (hχ : ∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * e x w : ℝ) : ℂ)))
    (k : Measure A) (hk : SelfDual k fun s t => χ (s * t)) (ι : Type) [Fintype ι] :
    SelfDual (Measure.pi fun _ : ι => k) (fun x y => χ (x ⬝ᵥ y)) := by
  haveI := hk.1
  have h1 : SelfDual (k.map (eqv e he he')) (fun u v : P → ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (u w * v w) : ℝ) : ℂ))) := by
    refine (selfDual_transport A (P → ℝ) (eqv e he he') k _).1 ?_
    have hf : (fun x y : A => Complex.exp (2 * Real.pi * Complex.I *
        ((∑ w, a w * (eqv e he he' x w * eqv e he he' y w) : ℝ) : ℂ))) =
        fun s t => χ (s * t) := by
      funext s t
      simp only [hχ, map_mul, Pi.mul_apply, eqv_apply]
    rw [hf]
    exact hk
  have h2 := GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag P a ha (k.map (eqv e he he')) h1
  have hc0 : 0 < ∏ w, √|a w| := Finset.prod_pos fun w _ => Real.sqrt_pos.2 (abs_pos.2 (ha w))
  have h3 := map_pi_eq e he he' k _ (by simpa using hc0) ENNReal.ofReal_ne_top h2 ι
  have hcc : ∏ _i : ι, ENNReal.ofReal (∏ w, √|a w|) =
      ENNReal.ofReal (∏ q : ι × P, √|a q.2|) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => hc0.le), Fintype.prod_prod_type]
  have h4 := GlobalTheory.SelfDualDiagReal.selfDual_diag (ι × P) (fun q => a q.2) (fun q => ha q.2)
  rw [← hcc, ← h3] at h4
  have h5 := (selfDual_transport (ι → A) (ι × P → ℝ) (eqvPi e he he' ι)
    (Measure.pi fun _ => k) _).2 h4
  have hf : (fun x y : ι → A => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ q : ι × P, a q.2 * (eqvPi e he he' ι x q * eqvPi e he he' ι y q) : ℝ) : ℂ))) =
      fun x y => χ (x ⬝ᵥ y) := by
    funext x y
    have hdot : ∀ w, e (x ⬝ᵥ y) w = ∑ i, e (x i) w * e (y i) w := fun w => by
      simp [dotProduct, map_sum, Finset.sum_apply]
    have hs : ∑ q : ι × P, a q.2 * (eqvPi e he he' ι x q * eqvPi e he he' ι y q) =
        ∑ w, a w * e (x ⬝ᵥ y) w := by
      simp only [eqvPi_apply, hdot, Finset.mul_sum]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [hχ, hs]
  rw [hf] at h5
  exact h5

end Meas

end GlobalTheory.CompanionTheory.SW.SdPi

open GlobalTheory.CompanionTheory.SW.SdPi GlobalTheory.CompanionTheory.SW.RealCoord in

theorem GlobalTheory.CompanionTheory.SW.selfDual_pi_inf : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ k : Measure (Ainf F), SelfDual k (fun s t => psiInf F ψ (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiInf F ψ (x ⬝ᵥ y)) := by
  intro F _ _ hF ψ hψ k hk ι _
  haveI := hF
  obtain ⟨h1, h2, h3, h4, -⟩ := isLocR_Ainf F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have he : Continuous (coord F) := (isHomeomorph_coord F).continuous
  have he' : Continuous (coord F).symm := (coordHomeo F).symm.continuous
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨a, ha, hχ⟩ := exists_form (coord F) he' (psiInf F ψ) hpc (fun _ => hψ.2.1 _)
    (fun u v => by
      simp only [psiInf, map_add, ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
    (GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).2.2
  exact selfDual_pi_of_form (coord F) he he' a ha _ hχ k hk ι
