import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSphericalCuspFormWhittakerNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScaledLocalCharacterUnitConductorConductorExponeStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.JSW.NzSphRam

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne GlobalTheory.JSW.NzSph

variable {E : Type} [Field E] [NumberField E]

theorem diagPow_eq_tD {K : Type} [Field K] {n : ℕ} (ϖ : Kˣ) (l : Fin n → ℕ) :
    GlobalTheory.JSW.diagPow ϖ l = GlobalTheory.IwaCell.tD ϖ (fun i => ((l i : ℕ) : ℤ)) := by
  apply Units.ext
  unfold GlobalTheory.IwaCell.tD
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  simp [GlobalTheory.JSW.diagPow, Matrix.diagonal_apply]

variable [IsTotallyComplex E]

theorem exists_whittaker_ne_zero_induction_bad_places (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ)
    (hα : ∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (hϖ : ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E))
    (R : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ g : GA E (m + 1),
      (∀ w ∉ T, w ∉ R → GlobalTheory.CellDec.compV E (m + 1) w
        ((GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1)⁻¹ * g) ∈ KGL w (m + 1)) → whit φ.1 g ≠ 0 →
      ∃ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧
        ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) T,
          whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) ≠ 0 := by
  classical
  set t0 := GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1 with ht0
  induction R using Finset.induction_on with
  | empty =>
    intro φ hφV hφ g hg hW
    obtain ⟨k, hk1, hk2⟩ := exists_outside E (m + 1) T (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g))
    have hinv : act (.fin k) φ = φ := act_fin_eq_of_outside E (m + 1) φ (π.cusp φ hφV).1 T hφ k
      (fun w hw => by rw [hk1 w hw, map_pLoc_pFin]; exact hg w hw (Finset.notMem_empty w)) hk2
    refine ⟨φ, hφV, hφ, g * (finGL E (m + 1) k)⁻¹ * t0⁻¹, fun w hw => ?_, ?_⟩
    · simp only [map_mul, map_inv]
      rw [comp_finGL, hk1 w hw, map_pLoc_pFin]
      simp only [map_mul, map_inv]
      group
    · have e : g * (finGL E (m + 1) k)⁻¹ * t0⁻¹ * t0 = g * (finGL E (m + 1) k)⁻¹ := by group
      rw [e]
      have e2 : g = g * (finGL E (m + 1) k)⁻¹ * finGL E (m + 1) k := by group
      rw [e2, ← whit_act_fin, hinv] at hW
      exact hW
  | insert w R hwR ih =>
    intro φ hφV hφ g hg hW
    by_cases hwT : w ∈ T
    · refine ih φ hφV hφ g (fun v hv hvR => hg v hv ?_) hW
      rw [Finset.mem_insert, not_or]
      exact ⟨fun h => hv (h ▸ hwT), hvR⟩
    let gw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g
    obtain ⟨u, hu, N, l, k, hk, hdec⟩ := local_decomp E (m + 1) w (ϖ w) (hϖ w) gw
    let z := GlobalTheory.JSW.diagPow (ϖ w)⁻¹ (fun _ : Fin (m + 1) => N)
    let d := GlobalTheory.JSW.diagPow (ϖ w) l
    let F : GL (Fin (m + 1)) (w.adicCompletion E) →* GA E (m + 1) := (finGL E (m + 1)).comp (locGL E (m + 1) w)
    have hF : ∀ h, F h = finGL E (m + 1) (locGL E (m + 1) w h) := fun h => rfl
    let y := g * (F gw)⁻¹
    have hyw : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y = 1 := by
      show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (g * (finGL E (m + 1) (locGL E (m + 1) w gw))⁻¹) = 1
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL]; exact mul_inv_cancel _
    have hyv : ∀ v, v ≠ w → GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) y =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g := by
      intro v hv
      show GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (g * (finGL E (m + 1) (locGL E (m + 1) w gw))⁻¹) = _
      rw [map_mul, map_inv, comp_finGL, pLoc_locGL_of_ne hv, inv_one, mul_one]
    have hg' : g = y * F u * F z * F d * F k := by
      have : F gw = F u * F z * F d * F k := by
        rw [hdec, map_mul, map_mul, map_mul]
      calc g = y * F gw := by simp only [y]; group
        _ = _ := by rw [this]; simp only [mul_assoc]
    have hcont : Continuous φ.1 := (π.cusp _ hφV).1.continuous
    have hleft : AutomorphicForm.IsLeftInvariant φ.1 := fun γ x => by
      rw [show AdelicGLn.diagonal E (m + 1) γ = ratGL E (m + 1) γ from Units.ext (Matrix.ext fun _ _ => rfl)]
      exact (π.cusp _ hφV).1.left γ x

    have h1 : whit φ.1 (y * F u * F z * F d) ≠ 0 := by
      rw [hg', hF k, ← whit_act_fin, hφ w hwT k hk] at hW
      exact hW

    have h2 : whit φ.1 (y * F z * F d) ≠ 0 := by
      have e : y * F u * F z * F d = F u * (y * F z * F d) := by
        rw [hF u, commute_finGL_locGL w hyw u]; group
      rw [e, hF u, finGL_locGL_eq_uGL w hu, whit, whittaker_uGL_mul hcont hleft] at h1
      exact right_ne_zero_of_mul h1

    let φ₁ := act (.fin (locGL E (m + 1) w z)) φ
    have hφ₁V : φ₁ ∈ π.V := π.stable _ φ hφV
    have hφ₁ : ∀ v ∉ T, ∀ k' ∈ KGL v (m + 1), act (.fin (locGL E (m + 1) v k')) φ₁ = φ₁ := by
      intro v hv k' hk'
      have hc : locGL E (m + 1) v k' * locGL E (m + 1) w z = locGL E (m + 1) w z * locGL E (m + 1) v k' := by
        by_cases hvw : v = w
        · subst hvw; rw [← map_mul, ← map_mul, diagPow_const_comm]
        · exact (GlobalTheory.CuspRep.LocSph.comm_locGL v (locGL E (m + 1) w z) (pLoc_locGL_of_ne hvw z) k').symm
      simp only [φ₁]
      rw [← act_fin_mul, hc, act_fin_mul, hφ v hv k' hk']
    have h3 : whit φ₁.1 (y * F d) ≠ 0 := by
      have e : y * F z * F d = y * F d * F z := by
        rw [mul_assoc y (F z), mul_assoc y (F d), ← map_mul, ← map_mul, diagPow_const_comm]
      rw [e, hF z, ← whit_act_fin] at h2
      exact h2

    let e0 : ℤ := GlobalTheory.RamShift.condExp ϖ w
    let d0 := GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)))
    let ν : Fin (m + 1) → ℤ := fun i => ((l i : ℕ) : ℤ) - e0 * ((m : ℤ) - ((i : ℕ) : ℤ))
    have hν : 0 ≤ ν (Fin.last m) := by simp [ν]
    have hloc := GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter E m π w (α ⟨w, hwT⟩) (hα ⟨w, hwT⟩) φ₁ hφ₁V (hφ₁ w hwT) (ϖ w) (hϖ w) e0
      (GlobalTheory.T.scaledLocalCharacter_unitConductor_conductorExponent E ϖ w (hϖ w)) y hyw ν hν
    have htD : GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i) = d := by
      simp only [d, diagPow_eq_tD]
      congr 1
      funext i
      simp only [ν]
      ring
    have h4 : whit φ₁.1 (y * F d0) ≠ 0 := by
      have h3' : whit φ₁.1 (y * finGL E (m + 1) (locGL E (m + 1) w
          (GlobalTheory.IwaCell.tD (ϖ w) (fun i : Fin (m + 1) => e0 * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) ≠ 0 := by
        rw [htD]; exact h3
      rw [hloc] at h3'
      exact right_ne_zero_of_mul h3'
    refine ih φ₁ hφ₁V hφ₁ (y * F d0) (fun v hv hvR => ?_) h4
    by_cases hvw : v = w
    · subst hvw
      have hc : GlobalTheory.CellDec.compV E (m + 1) v t0 = d0 := by
        rw [ht0, GlobalTheory.CellDec.compV_tl, GlobalTheory.RamShift.shift_apply_of_notMem m ϖ hv]
      have hy1 : GlobalTheory.CellDec.compV E (m + 1) v y = 1 := hyw
      rw [map_mul, map_inv, map_mul, hc, hy1, hF, GlobalTheory.CellDec.compV_finGL_locGL_same, one_mul, inv_mul_cancel]
      exact one_mem _
    · have hyv' : GlobalTheory.CellDec.compV E (m + 1) v y = GlobalTheory.CellDec.compV E (m + 1) v g := hyv v hvw
      have hgv := hg v hv (by rw [Finset.mem_insert, not_or]; exact ⟨hvw, hvR⟩)
      rw [map_mul, map_mul, hyv', hF, GlobalTheory.CellDec.compV_finGL_locGL_ne hvw, mul_one, ← map_mul]
      exact hgv

end GlobalTheory.JSW.NzSphRam

namespace GlobalTheory.JSW.NzSphRam

open GlobalTheory.JSW.NzSph

theorem exists_sph_whit_tl_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (π : CuspSub E (m + 1)) (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂˣ),
    (∀ w, HasSatGL w.1 (π.locRep w.1) (Finset.univ.val.map (α w))) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∃ φ ∈ π.V, (∀ w ∉ T, ∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) ∧
      ∃ x ∈ GlobalTheory.JSW.supS E (m + 1) T,
        GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1) ≠ 0 := by
  intro E _ _ _ m T π α hα ϖ hϖ
  classical
  let B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ := fun w =>
    if h : w ∈ T then 0 else Finset.univ.val.map (α ⟨w, h⟩)
  obtain ⟨φ₀, hφ₀V, hφ₀0, hφ₀K⟩ := GlobalTheory.T.exists_global_spherical_vector_of_satake_family E (m + 1) π T B (fun w hw => by
    simp only [B, dif_neg hw]; exact hα ⟨w, hw⟩)
  obtain ⟨g, hg⟩ : ∃ g, whit φ₀.1 g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ₀0 (GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing E (m + 1) φ₀ (π.cusp φ₀ hφ₀V) h)
  set t0 := GlobalTheory.CellDec.tl (m + 1) ϖ (GlobalTheory.RamShift.shift m T ϖ).1
  have hfin := finite_bad E (m + 1) (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g))
  refine exists_whittaker_ne_zero_induction_bad_places m T π α hα ϖ hϖ hfin.toFinset φ₀ hφ₀V hφ₀K g (fun w _ hwR => ?_) hg
  by_contra h
  refine hwR (hfin.mem_toFinset.2 ?_)
  show GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (t0⁻¹ * g)) ∉ KGL w (m + 1)
  rw [map_pLoc_pFin]; exact h

end GlobalTheory.JSW.NzSphRam
