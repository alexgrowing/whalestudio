import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalMirabolicWhittakerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMirabolicScalarUnitaryDecompositionArchimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnitMemOpenArchimedeanUnitsStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW.KirSemi

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem gl_af_ext {g h : GL (Fin a) (Af E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun x : GL (Fin a) (w.adicCompletion E) => x.1 i j) (H w)

theorem map_loc_fin (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) =
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g := by
  ext; rfl

theorem comm_of_supp (S : Finset (HeightOneSpectrum (𝓞 E))) {s t : GA E a} (hs : s ∈ supS E a S)
    (h1 : GeneralLinearGroup.map (pInf E) t = 1)
    (h2 : ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) : s * t = t * s := by
  apply ga_ext
  · simp [map_mul, h1]
  · apply gl_af_ext
    intro w
    simp only [map_mul, map_loc_fin]
    by_cases hw : w ∈ S
    · rw [h2 w hw]; simp
    · rw [hs w hw]; simp

theorem supS_mul (S : Finset (HeightOneSpectrum (𝓞 E))) {x y : GA E a} (hx : x ∈ supS E a S)
    (hy : y ∈ supS E a S) : x * y ∈ supS E a S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, one_mul]

theorem whit_rt (F : GA E a → ℂ) (h g : GA E a) : whit (fun y => F (y * h)) g = whit F (g * h) := by
  simp only [whit, GroundTheory.Automorphic.FourierWhittaker.whittaker, mul_assoc]

theorem ratGL_scalar_val (α : Eˣ) :
    ((ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) : GA E a) :
      Matrix (Fin a) (Fin a) (Ad E)) = Matrix.scalar (Fin a) (algebraMap E (Ad E) (α : E)) := by
  ext i j
  by_cases h : i = j <;> simp [ratGL, Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem aut_central {φ : Sm E a} (hφ : IsAutForm φ) (α : Eˣ) (g : GA E a) :
    φ.1 (g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α)) = φ.1 g := by
  have hc : g * ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) =
      ratGL E a (Units.map (Matrix.scalar (Fin a) : E →+* Matrix (Fin a) (Fin a) E).toMonoidHom α) * g := by
    apply Units.ext
    simp only [Units.val_mul, ratGL_scalar_val]
    exact ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _)).symm
  rw [hc, hφ.left]

theorem exists_mirabolic_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ ψ ∈ π.V, (∃ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit ψ.1 p ≠ 0) ∧ (∀ k : GA E (m + 1), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, φ.1 (g * k) = φ.1 g) → ∀ g, ψ.1 (g * k) = ψ.1 g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit ψ.1 (x * t) = c * GlobalTheory.JSW.whit ψ.1 x := by
  intro E _ _ _ m S π φ hφ ⟨x, hxS, hx⟩
  have haut : IsAutForm φ := (π.cusp φ hφ).1
  set xf := GeneralLinearGroup.map (pFin E) x with hxf
  obtain ⟨p0, ρ, k, hp0, hy⟩ := GlobalTheory.T.exists_mirabolic_scalar_unitary_decomposition_archimedean E m (GeneralLinearGroup.map (pInf E) x)
  let sc : (Cinf E)ˣ →* GL (Fin (m + 1)) (Cinf E) :=
    Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom
  have hsc : Continuous sc := by
    apply Continuous.units_map
    show Continuous (fun c : Cinf E => Matrix.scalar (Fin (m + 1)) c)
    simp only [Matrix.scalar_apply]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
  let ζ : (Cinf E)ˣ → ℂ := fun c =>
    whit φ.1 (infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf)
  have hζc : Continuous ζ :=
    (GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean E (m + 1) φ haut _ _).comp (hsc.mul continuous_const)
  have hζρ : ζ ρ ≠ 0 := by
    have hx' : infGL E (m + 1) p0 * infGL E (m + 1) (sc ρ * Unitary.toUnits k) * finGL E (m + 1) xf = x := by
      rw [← map_mul, ← mul_assoc]
      rw [show p0 * sc ρ * Unitary.toUnits k = GeneralLinearGroup.map (pInf E) x from hy.symm]
      exact infGL_mul_finGL x
    show whit φ.1 _ ≠ 0
    rw [hx']
    exact hx
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_field_unit_mem_open_archimedean_units E {c | ζ c ≠ 0} (isOpen_ne_fun hζc continuous_const) ⟨ρ, hζρ⟩
  set c := Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β with hc
  let zE : GL (Fin (m + 1)) E := Units.map (Matrix.scalar (Fin (m + 1)) : E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) E).toMonoidHom β⁻¹
  set s := infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf with hs
  have hcen : ∀ g : GL (Fin (m + 1)) (Cinf E), sc c * g = g * sc c := by
    intro g
    apply Units.ext
    exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _
  have hzinf : GeneralLinearGroup.map (pInf E) (ratGL E (m + 1) zE) = (sc c)⁻¹ := by
    have hci : (sc c)⁻¹ = sc (Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹) := by
      simp only [hc, map_inv]
    rw [hci]
    apply Units.ext
    show ((ratGL E (m + 1) zE : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)).map (pInf E) =
      Matrix.scalar (Fin (m + 1)) (((Units.map ((pInf E).comp (algebraMap E (Ad E))).toMonoidHom β⁻¹ : (Cinf E)ˣ)) : Cinf E)
    rw [ratGL_scalar_val]
    simp [Matrix.scalar_apply, Matrix.diagonal_map]
    funext v
    simp [pInf_algebraMap, map_inv₀]
  set z := GeneralLinearGroup.map (pFin E) (ratGL E (m + 1) zE) with hz
  have hsz : s * ratGL E (m + 1) zE = infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z) := by
    apply ga_ext
    · simp only [hs, map_mul, pInf_infGL, hzinf]
      simp
      rw [hcen]; group
    · simp [hs, hz, mul_assoc]
  let ψ : Sm E (m + 1) := act (Op.cpt k) (act (Op.fin (xf * z)) φ)
  have hψV : ψ ∈ π.V := π.stable _ _ (π.stable _ _ hφ)
  have hψ : ∀ g, ψ.1 g = φ.1 (g * s) := by
    intro g
    have h0 : ψ.1 g = φ.1 (g * infGL E (m + 1) (Unitary.toUnits k) * finGL E (m + 1) (xf * z)) := rfl
    rw [h0, mul_assoc, ← hsz, ← mul_assoc, aut_central haut β⁻¹]
  have hψf : ψ.1 = fun g => φ.1 (g * s) := funext hψ
  have hsS : s ∈ supS E (m + 1) S := by
    intro w hw
    rw [← map_loc_fin, hs, map_mul, pFin_infGL, pFin_finGL, one_mul, hxf, map_loc_fin]
    exact hxS w hw
  refine ⟨ψ, hψV, ⟨infGL E (m + 1) p0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro w hw
    rw [← map_loc_fin]
    simp
  · intro j
    have h1 : pInf E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        (p0 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Cinf E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
        (pInf_infGL (E := E) p0)
    have h2 : pFin E (((infGL E (m + 1) p0 : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) =
        ((1 : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j :=
      congrArg (fun y : GL (Fin (m + 1)) (Af E) => (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
        (pFin_infGL (E := E) p0)
    rw [hp0 j] at h1
    apply ad_ext
    · rw [h1]; split_ifs <;> simp
    · rw [h2]; split_ifs with h <;> simp [Matrix.one_apply, h, eq_comm]
  · rw [hψf, whit_rt]
    have : infGL E (m + 1) p0 * s = infGL E (m + 1) p0 * infGL E (m + 1) (sc c * Unitary.toUnits k) * finGL E (m + 1) xf := by
      rw [hs, mul_assoc]
    rw [this]
    exact hβ
  · intro k' h1 h2 hk g
    rw [hψ, hψ, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc, hk]
  · intro t c' h1 h2 hrel y hy
    rw [hψf, whit_rt, whit_rt, mul_assoc, ← comm_of_supp S hsS h1 h2, ← mul_assoc]
    exact hrel (y * s) (supS_mul S hy hsS)

theorem kirillov_semilocal_bump : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS E (m + 1) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  intro E _ _ _ m S b hb hC hU hsm π φ hφ hx
  obtain ⟨ψ, hψ, hp, hk, hrel⟩ := exists_mirabolic_nonzero E m S π φ hφ hx
  obtain ⟨F, hF, hFb, hFU, hFk, hFrel⟩ := GlobalTheory.T.kirillov_semilocal_mirabolic_whittaker E m S b hb hC hU hsm π ψ hψ hp
  exact ⟨F, hF, hFb, hFU, fun k h1 h2 h3 => hFk k h1 h2 (hk k h1 h2 h3),
    fun t c h1 h2 h3 => hFrel t c h1 h2 (hrel t c h1 h2 h3)⟩

end GlobalTheory.JSW.KirSemi
