import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovArchimedeanTotallyComplexMirabolicStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.KirArchTransfer

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_here : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_map_pInf_here :
    Continuous (GeneralLinearGroup.map (pInf E) : GA E a → GL (Fin a) (Cinf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_here)

theorem ent {R : Type} [CommRing R] (p : Ad E →+* R) (g : GA E a) (i j : Fin a) :
    ((GeneralLinearGroup.map p g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j = p ((g : Matrix (Fin a) (Fin a) (Ad E)) i j) :=
  rfl

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem eq_finGL {q : GA E a} (hq : GeneralLinearGroup.map (pInf E) q = 1) :
    q = finGL E a (GeneralLinearGroup.map (pFin E) q) := by
  have h := infGL_mul_finGL q
  rw [hq, map_one, one_mul] at h
  exact h.symm

theorem comm_infGL {q : GA E a} (hq : GeneralLinearGroup.map (pInf E) q = 1) (y : GL (Fin a) (Cinf E)) :
    q * infGL E a y = infGL E a y * q := by
  rw [eq_finGL hq]
  exact (infGL_comm y _).symm

theorem infGL_apply_of_ne (y : GL (Fin a) (Cinf E)) {i j : Fin a} (h : i ≠ j) :
    (infGL E a y : Matrix (Fin a) (Fin a) (Ad E)) i j = sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) := by
  refine ad_ext ?_ ?_
  · rw [← ent, pInf_infGL, pInf_sInf]
  · rw [← ent, pFin_infGL, pFin_sInf]
    simp [Matrix.one_apply, h]

theorem infGL_mem_NA {u : GL (Fin a) (Cinf E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin a)) :
    infGL E a u ∈ GlobalTheory.JSW.NA E a := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · refine ad_ext ?_ ?_
    · rw [map_zero, ← ent, pInf_infGL]; exact h1 i j hji
    · rw [map_zero, ← ent, pFin_infGL]; simp [Matrix.one_apply, hji.ne']
  · refine ad_ext ?_ ?_
    · rw [map_one, ← ent, pInf_infGL]; exact h2 i
    · rw [map_one, ← ent, pFin_infGL]; simp

theorem psiN_infGL (u : GL (Fin a) (Cinf E)) :
    GlobalTheory.JSW.psiN (infGL E a u) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) := by
  have hs : GlobalTheory.Whittaker.superDiag (infGL E a u) = sInf E (GlobalTheory.Whittaker.superDiag u) := by
    simp only [GlobalTheory.Whittaker.superDiag, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := by
      intro e; subst e; simp at hj
    exact infGL_apply_of_ne u hij
  have h := GlobalTheory.ThetaPoisson.adelicChar_sInf_sum (E := E) (n := 1) (fun _ => GlobalTheory.Whittaker.superDiag u) (fun _ => 1)
  simp only [Fin.sum_univ_one, mul_one, Pi.one_apply] at h
  rw [GlobalTheory.JSW.psiN, hs, h]

theorem map_pInf_mem_unipB {u : GA E a} (hu : u ∈ GlobalTheory.JSW.NA E a) :
    GeneralLinearGroup.map (pInf E) u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin a) := by
  refine (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [ent, hu.1 i j hji, map_zero]
  · rw [ent, hu.2 i, map_one]

theorem ad_eq_ite_iff (x : Ad E) (c : Prop) [Decidable c] :
    x = (if c then 1 else 0) ↔ pInf E x = (if c then 1 else 0) ∧ pFin E x = (if c then 1 else 0) := by
  refine ⟨fun h => ?_, fun h => ad_ext ?_ ?_⟩
  · subst h; split_ifs <;> simp
  · rw [h.1]; split_ifs <;> simp
  · rw [h.2]; split_ifs <;> simp

theorem mem_mirS_iff {m : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) {q : GA E (m + 1)}
    (hq : GeneralLinearGroup.map (pInf E) q = 1) (y : GL (Fin (m + 1)) (Cinf E)) :
    q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m ↔
      (q ∈ GlobalTheory.JSW.supS E (m + 1) S ∧ ∀ j, ((GeneralLinearGroup.map (pFin E) q : GL (Fin (m + 1)) (Af E)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧
      y ∈ GlobalTheory.JSW.mirSet (Cinf E) m := by
  have hsup : ∀ w : HeightOneSpectrum (𝓞 E),
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (infGL E (m + 1) y) = 1 :=
    fun w => map_cornerGL_of_zero _ _ (fun _ => map_zero (pLoc E w)) y
  have hI : GeneralLinearGroup.map (pInf E) (q * infGL E (m + 1) y) = y := by
    rw [map_mul, hq, one_mul, pInf_infGL]
  have hF : GeneralLinearGroup.map (pFin E) (q * infGL E (m + 1) y) = GeneralLinearGroup.map (pFin E) q := by
    rw [map_mul, pFin_infGL, mul_one]
  have hrow : ∀ j, ((q * infGL E (m + 1) y : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (if j = Fin.last m then 1 else 0) ↔
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = (if j = Fin.last m then 1 else 0) ∧
      ((GeneralLinearGroup.map (pFin E) q : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E))
        (Fin.last m) j = (if j = Fin.last m then 1 else 0) := by
    intro j
    rw [ad_eq_ite_iff, ← ent, ← ent, hI, hF]
  have hS : q * infGL E (m + 1) y ∈ GlobalTheory.JSW.supS E (m + 1) S ↔ q ∈ GlobalTheory.JSW.supS E (m + 1) S := by
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    rw [map_mul, hsup, mul_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hS.1 h1, fun j => ((hrow j).1 (h2 j)).2⟩, fun j => ((hrow j).1 (h2 j)).1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨hS.2 h1, fun j => (hrow j).2 ⟨h3 j, h2 j⟩⟩

end GlobalTheory.JSW.KirArchTransfer

namespace GlobalTheory.JSW.KirArchTransfer

theorem kirillov_arch : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (q : GA E (m + 1)), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b q) (invSet E (m + 1)) → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (q * infGL E (m + 1) y)) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (q * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → GeneralLinearGroup.map (pInf E) q = 1 → W q ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m → GlobalTheory.JSW.kerInf ν k γ W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y) := by
  intro E _ _ _ m S b W q hbe hbC hbs hWe hWc hWg hq hWq
  classical
  by_cases hne : ∃ y₀ : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y₀ ∈ GlobalTheory.JSW.mirS E S m
  · obtain ⟨y₀, hy₀⟩ := hne
    have hP := ((mem_mirS_iff S hq y₀).1 hy₀).1
    have hiff : ∀ y, q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m ↔ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m :=
      fun y => (mem_mirS_iff S hq y).trans ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩
    have heq : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) →
        ∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y,
          F (q * infGL E (m + 1) (u * y)) =
            (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * F (q * infGL E (m + 1) y) := by
      intro F hF u hu y
      rw [map_mul, ← mul_assoc, comm_infGL hq u, mul_assoc, hF _ (infGL_mem_NA hu), psiN_infGL]
    obtain ⟨C, hC, hCp⟩ := hbC
    obtain ⟨X, _, ν, _, k, γ, hk, hK⟩ := GlobalTheory.T.kirillov_archimedean_totallyComplex_mirabolic E m (fun y => b (q * infGL E (m + 1) y))
      (fun y => W (q * infGL E (m + 1) y)) (heq b hbe) ⟨chart b q, hbs, fun y => chart_val b q y⟩
      ⟨GeneralLinearGroup.map (pInf E) '' C, hC.image continuous_map_pInf_here, fun y hy hb0 => by
        obtain ⟨u, hu, hu'⟩ := hCp _ ((hiff y).2 hy) hb0
        refine ⟨GeneralLinearGroup.map (pInf E) u, map_pInf_mem_unipB hu, _, hu', ?_⟩
        rw [map_mul, map_inv, map_mul, hq, one_mul, pInf_infGL]⟩
      (heq W hWe) hWc hWg (by simpa using hWq)
    refine ⟨X, inferInstance, ν, inferInstance, k, γ, hk, fun y hy => ?_⟩
    rw [← hK y ((hiff y).1 hy)]
    simp only [GlobalTheory.JSW.kerInf]
    congr 1
    funext x
    rw [map_mul, mul_assoc]
  · exact ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => 1, GlobalTheory.JSW.isRapidInf_dirac 1,
      fun y hy => (hne ⟨y, hy⟩).elim⟩

end GlobalTheory.JSW.KirArchTransfer
