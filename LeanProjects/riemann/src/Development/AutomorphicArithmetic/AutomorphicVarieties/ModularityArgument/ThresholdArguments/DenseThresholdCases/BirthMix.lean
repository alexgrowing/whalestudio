import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PrOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PlainAtRTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutNewform2A
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVROrdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Sd
open private attR_tw_cyc norm_of_cong U1 cong_iff cyc_mem ordAt_tw irrOpen_of cont_units from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.MixSeed
theorem UpperTheory.V.Z.Win.Birth.mix_birth_of_prints :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.Esk.PropMV → UpperTheory.V.Z.Win.Birth.MixSeedP := by
  classical
  rintro hP hM F Ω _ _ _ _ _ _ l _ hl hev hsp ι ξ hξ hodd hunr ⟨u, Au, hu2, hAu, hur⟩ hsq hdec P ⟨w₁, hw₁, hl₁⟩ ⟨w₂, hw₂, hl₂⟩
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hv : ∀ {w : Pl F} {A : ValuationSubring Ω}, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → IsPlaceOver A w →
      A.valuation (l : Ω) < 1 := fun h hA => by simpa using (hA _).2 h
  have hn : ∀ g, ‖(ξ g : Qbar l)‖ = 1 := fun g => by
    have : Finite (G F Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hξ
    have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : ξ g ^ ξ.ker.index = 1 := by rw [← map_pow]; exact ξ.ker.pow_index_mem g
    have h2 : ‖(ξ g : Qbar l)‖ ^ ξ.ker.index = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 h2
  obtain ⟨A₁, hA₁⟩ := exists_isPlaceOver Ω w₁
  obtain ⟨A₂, hA₂⟩ := exists_isPlaceOver Ω w₂
  have hF2 : 2 ≤ Module.finrank ℚ F := by
    have h0 : 0 < Module.finrank ℚ F := Module.finrank_pos
    obtain ⟨j, hj⟩ := hev
    omega
  obtain ⟨k, t, hk2, ht2, hkl, htl, c, a, π₁, r₁, h₁, hres₁, ha⟩ := hM F Ω l hl hF2 hsp ι ξ hξ hodd hunr ⟨u, Au, hu2, hAu, hur⟩ P
    ⟨w₁, hw₁, hl₁, A₁, hA₁, hdec A₁ (hv hl₁ hA₁)⟩ ⟨w₂, hw₂, hl₂, A₂, hA₂, hdec A₂ (hv hl₂ hA₂)⟩
  have hkz : (l : ℤ) - 1 ∣ k := by
    rw [← Nat.cast_pred (Fact.out : l.Prime).pos]
    exact Int.natCast_dvd_natCast.2 hkl
  have htz : (l : ℤ) - 1 ∣ t := by
    rw [← Nat.cast_pred (Fact.out : l.Prime).pos]
    exact Int.natCast_dvd_natCast.2 htl
  let m : Pl F → Fin 2 → ℤ := fun w => if w ∈ P then ![(t : ℤ), -(k : ℤ) - t] else ![0, -(k : ℤ)]
  have hm₁ : ∀ w ∈ P, m w = ![(t : ℤ), -(k : ℤ) - t] := fun w h => if_pos h
  have hm₂ : ∀ w ∉ P, m w = ![0, -(k : ℤ)] := fun w h => if_neg h
  replace h₁ : OrdForm ι ξ (-(k : ℤ)) c m a π₁ r₁ := h₁
  obtain ⟨π, hatt, hinf⟩ := attR_tw_cyc h₁.att k
  have SF := shapeFacts l (G F Ω) 2 r₁ (cycBar F Ω l ^ k)
  have hU : ∀ g : G F Ω, cycBar F Ω l g ^ k ∈ U1 l := fun g => by simpa using cyc_mem g hkz
  have hn' : ∀ i g, ‖(((![1, ξ] : Fin 2 → G F Ω →* (Qbar l)ˣ) i g : (Qbar l)ˣ) : Qbar l)‖ = 1 :=
    Fin.forall_fin_two.2 ⟨fun g => by simp, hn⟩
  have hres : ResSum (tw r₁ (cycBar F Ω l ^ k)) ![1, ξ] := by
    refine (shapeFacts l (G F Ω) 2 _ 1).2.2.2.2.1 _ _ 1 (fun i g => ?_)
      (SF.2.2.2.1 _ (fun g => norm_of_cong (hU g)) hres₁) fun i g => ?_
    · rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hn', one_mul]
      exact norm_of_cong (hU g)
    · rw [Cong, norm_sub_rev]
      refine (cong_iff (hn' i g)).2 ?_
      rw [MonoidHom.mul_apply, Equiv.Perm.one_apply, mul_inv_cancel_comm]
      exact hU g
  have hO := _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_printsH hP F Ω l hl hsp ι ξ _ c m a π₁ r₁ h₁
  have hO₁ : ∀ w ∈ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      OrdAt (tw r₁ (cycBar F Ω l ^ k)) ![(k : ℤ) + t, -(t : ℤ)] ![ξ, 1] A := fun w h hw A hA => by
    obtain ⟨κ, h1, h2, h3⟩ := hO w hw A hA
    have := ordAt_tw (ψ₀ := ξ) (ψ₁ := 1) h₁.cont hkz.neg_right (by rw [mul_one]; exact h₁.det)
      (continuous_of_isOpen_ker' ξ hξ) hn (fun g => by simp) hA (hunr A (hv hw hA)) (by rw [hm₁ w h]; exact htz) h1 h2
      (fun σ hσ => by rw [Cong, ← (ha w hw A hA σ hσ).1 h]; exact h3 σ hσ) hkz
    convert this using 1
    rw [hm₁ w h]
    ext i
    fin_cases i <;> simp <;> ring
  have hO₂ : ∀ w ∉ P, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ A, IsPlaceOver A w →
      OrdAt (tw r₁ (cycBar F Ω l ^ k)) ![(k : ℤ), 0] ![1, ξ] A := fun w h hw A hA => by
    obtain ⟨κ, h1, h2, h3⟩ := hO w hw A hA
    have := ordAt_tw (ψ₀ := 1) (ψ₁ := ξ) h₁.cont hkz.neg_right (by rw [one_mul]; exact h₁.det)
      continuous_const (fun g => by simp) hn hA (fun _ _ => rfl) (by rw [hm₂ w h]; exact dvd_zero _) h1 h2
      (fun σ hσ => by
        have h4 := h3 σ hσ
        rw [(ha w hw A hA σ hσ).2 h] at h4
        exact h4) hkz
    convert this using 1
    rw [hm₂ w h]
    ext i
    fin_cases i <;> simp
  refine ⟨k, t, π, tw r₁ (cycBar F Ω l ^ k), hk2, ht2, hkl, htl, ?_, ?_, hatt, ?_, hres,
    ⟨fun A hA => ?_, UpperTheory.V.Z.Win.Birth.prTw F Ω l ι r₁ _ (by
      simpa using (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP.toClassicalTheorems F Ω l ι).1 (k : ℤ) 1 (by simp)) (UpperTheory.V.Z.Win.Birth.prOrd F Ω l ι ξ _ c m a π₁ r₁ h₁)⟩,
    fun w hw => ⟨fun h => ⟨hO₁ w h hw, fun τ hτ => ?_⟩, fun h => ⟨hO₂ w h hw, fun τ hτ => ?_⟩⟩⟩
  · have hz : Continuous fun s : G F Ω => ((cycZ F Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (continuous_cycZ F Ω l)
    have hcyc : Continuous fun s : G F Ω => (cycBar F Ω l s : Qbar l) :=
      (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
    refine cont_units _ ?_
    simp only [tw_val, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    exact (hcyc.pow k).smul (Units.continuous_val.comp h₁.cont)
  · have hk0 : (k : ℤ) ≠ 0 := by omega
    exact irrOpen_of hl hn (SF.2.2.2.2.2 (_root_.UpperTheory.V.Sd.ordinary_irreducible_of_printed_hida hP F Ω l hl hsp ι ξ _ c m a π₁ r₁ h₁)) hres hsq (hv hl₂ hA₂)
      hk0 (hO₂ w₂ hw₂ hl₂ A₂ hA₂)
  · refine MonoidHom.ext fun g => Units.ext ?_
    have h2 : Matrix.GeneralLinearGroup.det (r₁ g) = cycBar F Ω l g ^ (-(k : ℤ)) * ξ g := DFunLike.congr_fun h₁.det g
    have h3 := congrArg Units.val h2
    rw [Matrix.GeneralLinearGroup.val_det_apply] at h3
    rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, tw_val, Matrix.det_smul, h3]
    simp only [zpow_neg, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      Fintype.card_fin]
    field_simp
  · refine (shapeFacts l (G F Ω) 2 _ 1).2.1 _ _ _ 1 (SF.1 _ _ (_root_.UpperTheory.V.Z.Win.RR.ordAway_a_alt hP F Ω l ι ξ _ c m a π₁ r₁ h₁ A hA))
      fun i s hs => ?_
    have h1 : cycZ F Ω l s = 1 := (UpperTheory.V.Base.places F Ω l A).2.2.2 hA hs
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, cycBar, MonoidHom.comp_apply, h1, map_one, one_pow, mul_one]
    rfl
  · convert hinf _ _ ((h₁.above w hw).2.2.2.2.2 τ hτ) using 2
    rw [hm₁ w h]
    ext i
    fin_cases i <;> simp <;> ring
  · convert hinf _ _ ((h₁.above w hw).2.2.2.2.2 τ hτ) using 2
    rw [hm₂ w h]
    ext i
    fin_cases i <;> simp
end
