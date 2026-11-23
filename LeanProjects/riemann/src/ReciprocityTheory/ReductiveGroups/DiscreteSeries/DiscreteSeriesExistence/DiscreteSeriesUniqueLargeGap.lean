import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AllSmoothOfKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalExists

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

theorem final_lowKMultOneG :
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → (N : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
      ∀ S S' : Submodule ℂ H, Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S →
        Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S' → S = S' := by
  intro N ε lam H _ _ σ hHC hDS h hgap hlt S S' hS hS'
  haveI : CompleteSpace H := hDS.1
  exact lowKMultOneG_of_cas N ε lam H σ hHC hDS h hgap hlt
    (casOnSmooth_of_isDS hDS ⟨hHC.1, h, hgap, hlt⟩) S S' hS hS'

theorem final_deg_DSUniqG :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
        ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x, U (σ g x) = σ' g (U x) := by
  intro n ε lam H H' _ _ _ _ _ _ σ σ' hHC hDS hDS' h hgap hlt
  exact (isDS_props_of_gap n ε lam hHC h hgap hlt H σ hDS).2.2.2.2 H' σ' hDS'

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem final_cayley_facts {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) :
    Pᴴ * P = 1 ∧ P * Pᴴ = 1 ∧ P⁻¹ = Pᴴ ∧ P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ = Formalism.REAL.Jm ε := by
  obtain ⟨⟨-, hJ⟩, hU⟩ := hP
  have h1 : Pᴴ * P = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : P * Pᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  refine ⟨h1, h2, Matrix.inv_eq_left_inv h1, ?_⟩
  rw [← hJ]
  calc P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.one_mul, Matrix.mul_one]

theorem final_conj_mem {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * Pᴴ ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨-, -, -, h4⟩ := final_cayley_facts hP
  obtain ⟨⟨-, hJ⟩, -⟩ := hP
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc P * (gᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * g * Pᴴ)
      = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by simp only [Matrix.mul_assoc]
    _ = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by rw [hJ, hg']
    _ = Formalism.REAL.Jm ε := h4

theorem final_c_mem {P P' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (hP' : Formalism.MainNotions.S.IsCayleyU k r ε P') :
    P' * Pᴴ ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨-, -, -, h4⟩ := final_cayley_facts hP
  obtain ⟨⟨-, hJ'⟩, -⟩ := hP'
  show (P' * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P' * Pᴴ) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc P * P'ᴴ * Formalism.REAL.Jm ε * (P' * Pᴴ) = P * (P'ᴴ * Formalism.REAL.Jm ε * P') * Pᴴ := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hJ']; exact h4

end Cayley

theorem discrete_series_unique_large_gap :
    ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        ((2 * r + k + 1 : ℕ) : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDSHpk k r ε lam σ →
      ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
        (σ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDSHpk k r ε lam σ' →
      ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, U (σ g x) = σ' g (U x) := by
  intro k r ε lam hHC h hgap hbd H _ _ _ σ hσ H' _ _ _ σ' hσ'
  obtain ⟨P, hP, hds⟩ := hσ
  obtain ⟨P', hP', hds'⟩ := hσ'
  obtain ⟨U, hU⟩ := final_deg_DSUniqG (2 * r + k + 1) ε lam H H' (fun g => σ (P⁻¹ * g * P))
    (fun g => σ' (P'⁻¹ * g * P')) hHC hds hds' h hgap hbd
  obtain ⟨h1, h2, h3, -⟩ := final_cayley_facts hP
  obtain ⟨h1', h2', h3', -⟩ := final_cayley_facts hP'
  have kP : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pᴴ * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have kP' : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P'ᴴ * (P' * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hU' : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ (P⁻¹ * g * P) x) = σ' (P'⁻¹ * g * P') (U x) := hU
  have hrep : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (fun g => σ' (P'⁻¹ * g * P')) := hds'.2.2.1
  have hmul : ∀ a ∈ Formalism.MainNotions.S.UJset ε, ∀ b ∈ Formalism.MainNotions.S.UJset ε, ∀ y : H',
      σ' (P'⁻¹ * (a * b) * P') y = σ' (P'⁻¹ * a * P') (σ' (P'⁻¹ * b * P') y) := by
    intro a ha b hb y
    exact congrArg (fun T : H' →L[ℂ] H' => T y) (hrep.1.2 a ha b hb)
  have hnorm : ∀ a ∈ Formalism.MainNotions.S.UJset ε, ∀ y : H', ‖σ' (P'⁻¹ * a * P') y‖ = ‖y‖ := hrep.2.1
  have hone : σ' 1 = 1 := by
    have h0 : σ' (P'⁻¹ * 1 * P') = 1 := hrep.1.1
    rwa [Matrix.mul_one, h3', h1'] at h0
  have hc : P' * Pᴴ ∈ Formalism.MainNotions.S.UJset ε := final_c_mem hP hP'
  have hci : P * P'ᴴ ∈ Formalism.MainNotions.S.UJset ε := final_c_mem hP' hP
  let f : H' →ₗᵢ[ℂ] H' :=
    { toLinearMap := (σ' (P'⁻¹ * (P' * Pᴴ) * P')).toLinearMap
      norm_map' := hnorm _ hc }
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨σ' (P'⁻¹ * (P * P'ᴴ) * P') y, ?_⟩
    show σ' (P'⁻¹ * (P' * Pᴴ) * P') (σ' (P'⁻¹ * (P * P'ᴴ) * P') y) = y
    rw [← hmul _ hc _ hci]
    have e : P'⁻¹ * (P' * Pᴴ * (P * P'ᴴ)) * P' = 1 := by
      rw [h3']
      simp only [Matrix.mul_assoc, kP, kP', h1, h1', Matrix.mul_one]
    rw [e, hone]
    rfl
  refine ⟨U.trans (LinearIsometryEquiv.ofSurjective f hsurj), ?_⟩
  intro g hg x
  show σ' (P'⁻¹ * (P' * Pᴴ) * P') (U (σ g x)) = σ' g (σ' (P'⁻¹ * (P' * Pᴴ) * P') (U x))
  have hgP : P * g * Pᴴ ∈ Formalism.MainNotions.S.UJset ε := final_conj_mem hP hg
  have hgP' : P' * g * P'ᴴ ∈ Formalism.MainNotions.S.UJset ε := final_conj_mem hP' hg
  have eσ : σ g = σ (P⁻¹ * (P * g * Pᴴ) * P) := by
    congr 1
    rw [h3]
    simp only [Matrix.mul_assoc, kP, h1, Matrix.mul_one]
  have eσ' : σ' g = σ' (P'⁻¹ * (P' * g * P'ᴴ) * P') := by
    congr 1
    rw [h3']
    simp only [Matrix.mul_assoc, kP', h1', Matrix.mul_one]
  have e2 : (P' * Pᴴ) * (P * g * Pᴴ) = (P' * g * P'ᴴ) * (P' * Pᴴ) := by
    simp only [Matrix.mul_assoc, kP, kP']
  rw [eσ, hU' _ hgP, eσ', ← hmul _ hc _ hgP, ← hmul _ hgP' _ hc, e2]

theorem final_HCMultDSG :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam →
      Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h →
      ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε σ S →
        FiniteDimensional ℂ
          (sSup {S' : Submodule ℂ H | ∃ Θ : S →ₗ[ℂ] H,
            (∀ (a : Formalism.REAL.KG ε) (v w : S), (w : H) = σ (Formalism.REAL.toMK a) v → Θ w = σ (Formalism.REAL.toMK a) (Θ v)) ∧
              S' = LinearMap.range Θ} : Submodule ℂ H) := by
  intro n ε lam H _ _ _ σ hlam hDS h hh hbig S hSf hSK
  classical
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, hbig⟩
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hirr : Formalism.MainNotions.S.IsIrredOn (UJset ε) σ := hDS.2.2.2.1
  obtain ⟨S0, hS0⟩ := hDS.2.2.2.2.2.1
  obtain ⟨V, hV, hV0, hVK, -⟩ := exists_datum_of_isKTypeOf hσ hS0
  have hD : IsDerivedOn ε σ (smD ε σ) (smE ε σ) := isDerivedOn_smE hσ
  have hV' : IsKIrrHW ε (smE ε σ) (lowK ε lam) V := hV
  have hc := casOnDatum_of_isDS hDS hgap hD hV' hVK
  have hclos : closGen (smE ε σ) V = ⊤ := data_closGen_eq_top hgap hσ hD hV' hc hVK hirr hV0
  have hE : IsGlRep (smE ε σ) := hD.glRep
  have hU : IsInfUnitary ε (smE ε σ) := isInfUnitary_of_isDerivedOn hσ hD
  have hKU : IsKUnitary ε (smE ε σ) := isKUnitary_of_isInfUnitary hU
  choose T hTf hTG hTk hTmem using fun μ => admissible hE hU hV' hc hgap μ
  haveI : ∀ μ, FiniteDimensional ℂ (T μ) := hTf
  have hKG : ∀ g ∈ Kset ε, ∃ a : Formalism.REAL.KG ε, Formalism.REAL.toMK a = g := by
    intro g hg
    have hg' : g ∈ Set.range (fun a : Formalism.REAL.KG ε => Formalism.REAL.toMK a) := by
      rw [Formalism.REAL.range_toMK]
      exact hg
    obtain ⟨a, ha⟩ := hg'
    exact ⟨a, ha⟩
  have hkfin : ∀ R : Submodule ℂ H, FiniteDimensional ℂ R → (∀ k ∈ Kset ε, ∀ x ∈ R, σ k x ∈ R) →
      R ≤ (genSub (smE ε σ) V).map (smD ε σ).subtype := fun R hRf hRK =>
    data_kfin_le hgap hσ hD hV' hc hVK R (by rw [hclos]; exact le_top) hRf hRK
  have hcomapK : ∀ R : Submodule ℂ H, (∀ k ∈ Kset ε, ∀ x ∈ R, σ k x ∈ R) →
      ∀ k ∈ Kset ε, ∀ v ∈ R.comap (smD ε σ).subtype, ∃ w ∈ R.comap (smD ε σ).subtype, (w : H) = σ k v :=
    fun R hRK k hk v hv => ⟨⟨σ k v, hD.kStable k hk (v : H) v.2⟩, hRK k hk (v : H) hv, rfl⟩
  have hcomapF : ∀ R : Submodule ℂ H, FiniteDimensional ℂ R → R ≤ smD ε σ →
      FiniteDimensional ℂ (R.comap (smD ε σ).subtype) := fun R hRf hRD => by
    haveI := hRf
    exact LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe hRD).symm
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S := hSK
  have hSD : S ≤ smD ε σ := (hkfin S hSf hSK').trans (Submodule.map_subtype_le _ _)
  haveI hSDf : FiniteDimensional ℂ (S.comap (smD ε σ).subtype) := hcomapF S hSf hSD
  have hSDk : IsKStableSub ε (smE ε σ) (S.comap (smD ε σ).subtype) :=
    isKStableSub_of_kStable hσ hD _ hSDf (hcomapK S hSK')
  have hSDc : ∀ c, ∀ v ∈ S.comap (smD ε σ).subtype, smE ε σ c c v ∈ S.comap (smD ε σ).subtype :=
    fun c => hSDk c c rfl
  let P : Set (Fin n → ℝ) :=
    {μ | ∃ w ∈ S.comap (smD ε σ).subtype, w ≠ 0 ∧ ∀ c, smE ε σ c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((smE ε σ c c).restrict (hSDc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((smE ε σ c c).restrict (hSDc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h0
      exact hw0 (congrArg Subtype.val h0)
  refine Submodule.finiteDimensional_of_le (S₂ := ((hPfin.toFinset).sup T).map (smD ε σ).subtype) ?_
  refine sSup_le ?_
  rintro _ ⟨Θ, hΘ, rfl⟩
  haveI := hSf
  have hRK : ∀ k ∈ Kset ε, ∀ x ∈ LinearMap.range Θ, σ k x ∈ LinearMap.range Θ := by
    rintro k hk _ ⟨v, rfl⟩
    obtain ⟨a, rfl⟩ := hKG k hk
    exact ⟨⟨σ (Formalism.REAL.toMK a) v, hSK' _ hk v v.2⟩, hΘ a v _ rfl⟩
  have hRle := hkfin (LinearMap.range Θ) inferInstance hRK
  have hRD : LinearMap.range Θ ≤ smD ε σ := hRle.trans (Submodule.map_subtype_le _ _)
  haveI hRDf : FiniteDimensional ℂ ((LinearMap.range Θ).comap (smD ε σ).subtype) :=
    hcomapF _ inferInstance hRD
  have hRDk : IsKStableSub ε (smE ε σ) ((LinearMap.range Θ).comap (smD ε σ).subtype) :=
    isKStableSub_of_kStable hσ hD _ hRDf (hcomapK _ hRK)
  have hRDG : (LinearMap.range Θ).comap (smD ε σ).subtype ≤ genSub (smE ε σ) V := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 (hRle (show (y : H) ∈ LinearMap.range Θ from hy))
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hz
  let f : (S.comap (smD ε σ).subtype) →ₗ[ℂ] (smD ε σ) :=
    LinearMap.codRestrict (smD ε σ) (Θ.comp (Submodule.comapSubtypeEquivOfLe hSD).toLinearMap)
      (fun s => hRD (LinearMap.mem_range_self Θ _))
  have hfv : ∀ s : S.comap (smD ε σ).subtype, ((f s : smD ε σ) : H) = Θ ⟨((s : smD ε σ) : H), s.2⟩ :=
    fun s => rfl
  have hf : ∀ (ν : Fin n → ℝ) (s : S.comap (smD ε σ).subtype),
      (∀ c, smE ε σ c c (s : smD ε σ) = (ν c : ℂ) • (s : smD ε σ)) →
      ∀ c, smE ε σ c c (f s) = (ν c : ℂ) • f s := by
    intro ν s hs
    have hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ ν ((s : smD ε σ) : H) := (isWtOn_iff hσ hD _ ν).2 hs
    refine (isWtOn_iff hσ hD (f s) ν).1 ?_
    intro θ hθ
    obtain ⟨a, ha⟩ := hKG _ hθ
    have hv := hw θ hθ
    rw [hfv]
    rw [← ha] at hv ⊢
    have h3 := hΘ a ⟨((s : smD ε σ) : H), s.2⟩
      (Complex.exp (((∑ b, ν b * θ b : ℝ) : ℂ) * Complex.I) • ⟨((s : smD ε σ) : H), s.2⟩) hv.symm
    rw [map_smul] at h3
    exact h3.symm
  have hwt : ∀ w ∈ (LinearMap.range Θ).comap (smD ε σ).subtype, w ≠ 0 → ∀ μ,
      IsKHWVec ε (smE ε σ) μ w → μ ∈ hPfin.toFinset := by
    intro y hy hy0 μ hμ
    rw [Set.Finite.mem_toFinset]
    have hyf : y ∈ LinearMap.range f := by
      obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (show (y : H) ∈ LinearMap.range Θ from hy)
      refine ⟨⟨⟨(v : H), hSD v.2⟩, v.2⟩, Subtype.ext ?_⟩
      rw [hfv]
      exact hv
    exact finalA_wt_mem hE hKU _ hSDc f hf hyf hy0 hμ.1
  have hRle' : (LinearMap.range Θ).comap (smD ε σ).subtype ≤ (hPfin.toFinset).sup T :=
    finalA_le_sup hE hU (genSub (smE ε σ) V) T hTk hTmem hPfin.toFinset _ _ rfl hRDf hRDG hRDk hwt
  intro x hx
  exact Submodule.mem_map.2 ⟨⟨x, hRD hx⟩,
    hRle' (show (⟨x, hRD hx⟩ : smD ε σ) ∈ (LinearMap.range Θ).comap (smD ε σ).subtype from hx), rfl⟩

end ReciprocityTheory.ChartRestriction.DS
