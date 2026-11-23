import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaCellsDisjointOffFinset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactIntegralGLFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell.CptMod

variable {E : Type} [Field E] [NumberField E]

theorem continuous_finGL_cpt {a : ℕ} : Continuous (finGL E a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

theorem exists_pLoc_ite {n : ℕ} (c : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ h : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) h = if w ∈ T then c w else 1 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun w => by simp⟩
  | insert v T hvT ih =>
    obtain ⟨h, hh⟩ := ih
    refine ⟨locGL E n v (c v) * h, fun w => ?_⟩
    rw [map_mul, hh w]
    by_cases hw : w = v
    · subst hw
      rw [pLoc_locGL, if_neg hvT, if_pos (Finset.mem_insert_self _ _), mul_one]
    · rw [pLoc_locGL_of_ne hw, one_mul]
      simp [Finset.mem_insert, hw]

theorem isCompact_intGL (n : ℕ) :
    IsCompact {κ : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ GlobalTheory.LFun.KGL w n} := by
  convert GlobalTheory.isCompact_KGL E n using 1
  ext κ
  simp only [Set.mem_setOf_eq, GlobalTheory.LFun.KGL, GlobalTheory.CellDec.mem_GLint_iff_entries_cell, ← map_inv]
  constructor
  · intro h
    exact ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩
  · intro h v
    exact ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩

theorem row_mul_inv {R : Type} [CommRing R] {n : ℕ} {A B : GL (Fin n) R} {i : Fin n}
    (h : (A : Matrix (Fin n) (Fin n) R) i = (B : Matrix (Fin n) (Fin n) R) i) :
    ((A * B⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i = (1 : Matrix (Fin n) (Fin n) R) i := by
  funext j
  rw [Units.val_mul, Matrix.mul_apply, h, ← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem row_last_unip_mul {R : Type} [CommRing R] {m : ℕ} {u : GL (Fin (m + 1)) R}
    (hu : u ∈ GlobalTheory.SmGL.unipB R (Fin (m + 1))) (k : GL (Fin (m + 1)) R) :
    ((u * k : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) =
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
  funext j
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · rw [h2, one_mul]
  · intro i _ hi
    rw [h1 _ _ (lt_of_le_of_ne (Fin.le_last i) hi), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem row_tl_mul {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {i : Fin n} (hl : ∀ w, l w i = 0) (g : GA E n) :
    ((GlobalTheory.CellDec.tl n ϖ l * g : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i = (g : Matrix (Fin n) (Fin n) (Ad E)) i := by
  have h0 : Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l = 0 := by
    ext w
    simp [hl w]
  funext j
  rw [GlobalTheory.CellDec.tl_eq_diagT, Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul]
  simp only [h0, GlobalTheory.CellDec.adl_zero, map_one, Units.val_one, one_mul]

theorem compV_tl_eq_one {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) {w : HeightOneSpectrum (𝓞 E)} (hw : l w = 0) :
    GlobalTheory.CellDec.compV E n w (GlobalTheory.CellDec.tl n ϖ l) = 1 := by
  rw [GlobalTheory.CellDec.compV_tl, hw]
  apply Units.ext
  rw [GlobalTheory.IwaCell.val_tD]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem tl_mul_comm [IsTotallyComplex E] {n : ℕ} (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (hl : ∀ v ∈ T, l v = 0) {p : GA E n}
    (hp : ∀ w ∉ T, GlobalTheory.CellDec.compV E n w p = 1) :
    GlobalTheory.CellDec.tl n ϖ l * p = p * GlobalTheory.CellDec.tl n ϖ l := by
  apply ga_ext
  · simp [GlobalTheory.CellDec.tl, map_mul]
  · apply GlobalTheory.CellDec.GL_ext_pLoc
    intro w
    change GlobalTheory.CellDec.compV E n w (GlobalTheory.CellDec.tl n ϖ l * p) = GlobalTheory.CellDec.compV E n w (p * GlobalTheory.CellDec.tl n ϖ l)
    rw [map_mul, map_mul]
    by_cases hw : w ∈ T
    · rw [compV_tl_eq_one ϖ l (hl w hw), one_mul, mul_one]
    · rw [hp w hw, one_mul, mul_one]

end GlobalTheory.RSCell.CptMod

namespace GlobalTheory.RSCell.CptMod

open scoped Pointwise

theorem exists_isCompact_mod_NA : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (F : GA E (m + 1) → ℂ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T) (U : Subgroup (GL (Fin (m + 1)) (Af E))) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (C : Set (GA E (m + 1))), IsCompact C →
    (∀ w, l₀.1 w (Fin.last m) = 0) → (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ p ∈ GlobalTheory.JSW.mirS E T m, GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * p ∈ C) →
    HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) → (∀ w ∉ T, FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) = 0) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ KGL w (m + 1)) ∧ (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ (x : ℝ) (g : GA E (m + 1)), g ∈ GlobalTheory.CellDec.C0 E (m + 1) T →
      GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) ≠ 0 → ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K := by
  intro E _ _ _ m T ϖ hϖ F l₀ U Φ J C hC hl0 hU hKT hN hsupp hΦ hΦs hJ horb
  set K₁ : Set (GA E (m + 1)) :=
    finGL E (m + 1) '' {κ | ∀ w, GeneralLinearGroup.map (pLoc E w) κ ∈ GlobalTheory.LFun.KGL w (m + 1)} with hK₁d
  set K₂ : Set (GA E (m + 1)) :=
    (fun u => infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) u)) '' tsupport Φ with hK₂d
  have hK₁ : IsCompact K₁ := (isCompact_intGL (m + 1)).image continuous_finGL_cpt
  have hK₂ : IsCompact K₂ := (show IsCompact (tsupport Φ) from hΦ).image_of_continuousOn
    (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn ((GlobalTheory.RSTheta.continuousOn_rowGL (Fin.last m)).mono hΦs))
  refine ⟨C * K₁ * K₂ * K₁, ((hC.mul hK₁).mul hK₂).mul hK₁, ?_⟩
  intro x g hg hB
  obtain ⟨u₁, hu₁, k, hk, rfl⟩ := hg
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 with ht
  have hrow : ((t * (u₁ * k) : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) =
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) := by
    rw [row_tl_mul ϖ l₀.1 hl0, row_last_unip_mul hu₁]
  set u : Fin (m + 1) → Cinf E := fun i => pInf E ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i) with hud
  set yf : Fin (m + 1) → Af E := fun i => pFin E ((k : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) i) with hyf
  set σ := infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) u) with hσ
  have hB1 := left_ne_zero_of_mul hB
  rw [enorm_ne_zero] at hB1
  unfold GlobalTheory.RSTheta.rsPsi GlobalTheory.ThetaPoisson.thetaFn at hB1
  rw [hrow] at hB1
  obtain ⟨hB2, hlat⟩ := mul_ne_zero_iff.1 hB1
  have hlat' : yf - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J := Set.mem_of_indicator_ne_zero hlat
  unfold GlobalTheory.RSTheta.rsInf at hB2
  obtain ⟨hB3, hΦu⟩ := mul_ne_zero_iff.1 hB2
  have hW : GlobalTheory.JSW.whit F (t * (u₁ * k) * σ⁻¹) ≠ 0 := left_ne_zero_of_mul hB3
  have hu_supp : u ∈ tsupport Φ := subset_tsupport _ (Function.mem_support.2 hΦu)
  have hunit : IsUnit (u (Fin.last m)) := GlobalTheory.RSTheta.isUnit_of_mem_rowSet (hΦs hu_supp)
  obtain ⟨κ, hκU, hκK, hκ1, hκrow⟩ := horb yf hlat'
  obtain ⟨hf, hhf⟩ := exists_pLoc_ite (fun w => GlobalTheory.CellDec.compV E (m + 1) w k) T
  set h := infGL E (m + 1) (GeneralLinearGroup.map (pInf E) k) * finGL E (m + 1) hf with hhd
  set kT := h⁻¹ * k with hkTd
  have hcV_inf : ∀ w (y : GL (Fin (m + 1)) (Cinf E)), GlobalTheory.CellDec.compV E (m + 1) w (infGL E (m + 1) y) = 1 := by
    intro w y
    change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (infGL E (m + 1) y)) = 1
    rw [pFin_infGL, map_one]
  have hcV_h : ∀ w, GlobalTheory.CellDec.compV E (m + 1) w h = if w ∈ T then GlobalTheory.CellDec.compV E (m + 1) w k else 1 := by
    intro w
    rw [hhd, map_mul, hcV_inf, GlobalTheory.CellDec.compV_finGL, hhf w, one_mul]
  have hinf_h : GeneralLinearGroup.map (pInf E) h = GeneralLinearGroup.map (pInf E) k := by
    rw [hhd, map_mul, pInf_infGL, pInf_finGL, mul_one]
  have hkT_inf : GeneralLinearGroup.map (pInf E) kT = 1 := by
    rw [hkTd, map_mul, map_inv, hinf_h, inv_mul_cancel]
  have hkT_T : ∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w kT = 1 := by
    intro w hw
    rw [hkTd, map_mul, map_inv, hcV_h, if_pos hw, inv_mul_cancel]
  have hkT_US : kT ∈ GlobalTheory.CellDec.US E (m + 1) T := GlobalTheory.CellDec.mem_US.2 fun w hw => by
    rw [hkTd, map_mul, map_inv, hcV_h, if_neg hw, inv_one, one_mul]
    exact GlobalTheory.CellDec.mem_US.1 hk w hw
  have hkT_fin : kT = finGL E (m + 1) (GeneralLinearGroup.map (pFin E) kT) := by
    conv_lhs => rw [← infGL_mul_finGL kT]
    rw [hkT_inf, map_one, one_mul]
  have hkT_K : ∀ w, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) kT) ∈ GlobalTheory.LFun.KGL w (m + 1) := by
    intro w
    change GlobalTheory.CellDec.compV E (m + 1) w kT ∈ _
    by_cases hw : w ∈ T
    · rw [hkT_T w hw]
      exact one_mem _
    · exact GlobalTheory.CellDec.mem_US.1 hkT_US w hw
  set B := finGL E (m + 1) κ * σ with hBd
  have hrowB : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) := by
    funext j
    apply ad_ext
    · change (GeneralLinearGroup.map (pInf E) h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j =
        (GeneralLinearGroup.map (pInf E) B : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j
      rw [hinf_h, hBd, map_mul, pInf_finGL, one_mul, hσ, pInf_infGL, GlobalTheory.RSTheta.val_rowGL hunit,
        GlobalTheory.RSTheta.rowMat, Matrix.updateRow_self]
      rfl
    · apply IsDedekindDomain.FiniteAdeleRing.ext
      intro w
      change (GlobalTheory.CellDec.compV E (m + 1) w h : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
        (GlobalTheory.CellDec.compV E (m + 1) w B : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j
      rw [hcV_h, hBd, map_mul, GlobalTheory.CellDec.compV_finGL, hσ, hcV_inf, mul_one]
      split_ifs with hw
      · rw [hκrow w hw j]
        rfl
      · rw [hκ1 w hw]
  set p := h * B⁻¹ with hpd
  have hp_sup : ∀ w ∉ T, GlobalTheory.CellDec.compV E (m + 1) w p = 1 := by
    intro w hw
    rw [hpd, map_mul, map_inv, hcV_h, if_neg hw, hBd, map_mul, GlobalTheory.CellDec.compV_finGL, hκ1 w hw, hσ, hcV_inf,
      mul_one, inv_one, one_mul]
  have hp_mir : p ∈ GlobalTheory.JSW.mirS E T m := by
    refine ⟨fun w hw => hp_sup w hw, fun j => ?_⟩
    have e := congrFun (row_mul_inv hrowB) j
    rw [← hpd] at e
    rw [e, Matrix.one_apply]
    by_cases hj : j = Fin.last m
    · rw [if_pos hj.symm, if_pos hj]
    · rw [if_neg (Ne.symm hj), if_neg hj]
  have hcomm : kT * σ⁻¹ = σ⁻¹ * kT := by
    rw [hkT_fin, hσ, ← map_inv]
    exact (infGL_comm _ _).symm
  have hnorm : ‖GlobalTheory.JSW.whit F (t * (u₁ * k) * σ⁻¹)‖ = ‖GlobalTheory.JSW.whit F (p * t)‖ := by
    have e1 : t * (u₁ * k) * σ⁻¹ = (t * u₁ * t⁻¹) * (t * k * σ⁻¹) := by group
    rw [e1, hN _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu₁)]
    have e2 : t * k * σ⁻¹ = t * h * σ⁻¹ * kT := by
      rw [mul_assoc (t * h), ← hcomm, hkTd]
      group
    rw [e2, hKT kT hkT_US hkT_inf hkT_T]
    have e3 : t * h * σ⁻¹ = t * p * finGL E (m + 1) κ := by
      rw [hpd, hBd]
      group
    rw [e3, hU κ hκU, tl_mul_comm ϖ l₀.1 l₀.2 hp_sup]
  have hWp : GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
    rw [← ht, ← norm_ne_zero_iff, ← hnorm, norm_ne_zero_iff]
    exact hW
  obtain ⟨u₂, hu₂, hu₂C⟩ := hsupp p hp_mir hWp
  refine ⟨u₂ * u₁⁻¹, mul_mem hu₂ (inv_mem hu₁), ?_⟩
  have e : u₂ * u₁⁻¹ * (u₁ * k) = u₂ * p * finGL E (m + 1) κ * σ * finGL E (m + 1) (GeneralLinearGroup.map (pFin E) kT) := by
    rw [← hkT_fin, hpd, hBd, hkTd]
    group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul hu₂C ⟨κ, hκK, rfl⟩) ⟨u, hu_supp, rfl⟩) ⟨_, hkT_K, rfl⟩

end GlobalTheory.RSCell.CptMod
