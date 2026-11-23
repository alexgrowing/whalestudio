import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFourierSchwartzBruhatPlaneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerLowerLeftNonzeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerUpperTriangularCaseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableTwistedSectionLineStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSplitWhittakerDensityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatPlaneRightTranslateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIndicatorSchwartzBruhatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatPlaneCosetSpanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanSetEqLatticePreimageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeAnnulusCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIndicatorUnitScalingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLatticeIntegralGL2InvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWhittakerLeftUnipotentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerIntegralLatticeTorusFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterAnnulusIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurPolynomialGL2SumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfUniformizerPowerStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

theorem L_pF : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.pF χ Φ) := GlobalTheory.T.partial_fourier_schwartz_bruhat_plane

theorem L_modelNe : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 ≠ 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := GlobalTheory.T.weil_whittaker_lower_left_nonzero

theorem L_modelZero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 = 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := GlobalTheory.T.weil_whittaker_upper_triangular_case

theorem L_innInt : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ u : Fˣ, Integrable (fun y : F => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ)) (selfDualMeasure χ) := GlobalTheory.T.integrable_twisted_section_line

theorem L_denInt : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ → Integrable (GlobalTheory.CompanionTheory.WS.den χ c₁ c₂ Ψ) (multHaar F) := GlobalTheory.T.integrable_split_whittaker_density

theorem L_comp : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ), GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ g : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.IsSB (Ψ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) := GlobalTheory.T.schwartz_bruhat_plane_right_translate

theorem L_coset : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.cosetInd n x) := GlobalTheory.T.coset_indicator_schwartz_bruhat

theorem L_decomp : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Ψ : F × F → ℂ), GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∃ (n : ℤ) (s : Finset (F × F)) (a : F × F → ℂ), Ψ = ∑ x ∈ s, a x • GlobalTheory.CompanionTheory.WS.cosetInd n x := GlobalTheory.T.schwartz_bruhat_plane_coset_span

theorem L_lat : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), ∃ h : GL (Fin 2) F, GlobalTheory.CompanionTheory.WS.spanSet n x = GlobalTheory.CompanionTheory.WS.rowAct h ⁻¹' GlobalTheory.CompanionTheory.WS.Ln F 0 := GlobalTheory.T.span_set_eq_lattice_preimage

theorem L_orbit : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), x ∉ GlobalTheory.CompanionTheory.WS.Ln F n → ∃ s : Finset Fˣ, s.Nonempty ∧ (∀ t ∈ s, t ∈ unitFiltrationUnits F 0) ∧ (GlobalTheory.CompanionTheory.WS.spanSet n x).indicator (1 : F × F → ℂ) - (GlobalTheory.CompanionTheory.WS.spanSet n (((unifUnit F : Fˣ) : F) • x)).indicator (1 : F × F → ℂ) = ∑ t ∈ s, GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) := GlobalTheory.T.lattice_annulus_coset_decomposition

theorem L_cosetUnit : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F) (t : Fˣ), t ∈ unitFiltrationUnits F 0 → GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) = fun v => GlobalTheory.CompanionTheory.WS.cosetInd n x (((t⁻¹ : Fˣ) : F) • v) := GlobalTheory.T.coset_indicator_unit_scaling

theorem L_latK : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct k = GlobalTheory.CompanionTheory.WS.lat0 F := GlobalTheory.T.standard_lattice_integral_GL2_invariant

theorem L_left : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (v g : GL (Fin 2) F), v ∈ Iwasawa.unipotent F 2 → GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ (v * g) = Whittaker.psiN (Circle.coeHom.compAddChar χ) v * GlobalTheory.CompanionTheory.WS.WL χ c₁ c₂ Ψ g := GlobalTheory.T.split_whittaker_left_unipotent

theorem lattice_inner_integral_value : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ (l : Fin 2 → ℤ) (u : Fˣ), GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct (Iwasawa.torusPow F 2 l)) u = if -(l 0) ≤ ord (u : F) ∧ ord (u : F) ≤ -(l 1) then ((Spherical.qF F : ℕ) : ℂ) ^ (l 1) * (mp u 1)⁻¹ else 0 := GlobalTheory.T.inner_integral_lattice_torus_formula

theorem unramified_character_integral_sum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (μ : Fˣ →* ℂˣ), IsUnramifiedChar μ → ∀ A D : ℤ, ∫ u : Fˣ, (if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then ((μ u : ℂˣ) : ℂ) else 0) ∂multHaar F = ∑ j ∈ Finset.Icc D A, ((μ (unifUnit F) : ℂˣ) : ℂ) ^ (-j) := GlobalTheory.T.unramified_character_annulus_integral

theorem schur_polynomial_two_eval : ∀ (x y : ℂˣ) (A D : ℤ), D ≤ A → Spherical.evalAt ![x, y] (Spherical.schur ![A, D]) = ∑ j ∈ Finset.Icc D A, (x : ℂ) ^ (A + D - j) * (y : ℂ) ^ j := GlobalTheory.T.schur_polynomial_GL2_sum

theorem L_mpHalf : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (m : ℤ), mp (Iwasawa.uniformizerUnit F ^ m) (1 / 2) = Spherical.sqrtQ F ^ (-m) := GlobalTheory.T.modulus_half_uniformizer_power

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem rowAct_mul (g h : GL (Fin 2) F) (v : F × F) :
    rowAct (g * h) v = rowAct h (rowAct g v) := by
  simp only [rowAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

theorem mp_mul (x y : Fˣ) (s : ℂ) : mp (x * y) s = mp x s * mp y s := by
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s

theorem mp_ne_zero (x : Fˣ) (s : ℂ) : mp x s ≠ 0 := by
  have h0 : ((modulus (x : F) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero x.ne_zero
  simp only [mp]
  rw [Complex.cpow_def_of_ne_zero h0]
  exact Complex.exp_ne_zero _

theorem WL_mul (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (g h : GL (Fin 2) F) :
    WL χ c₁ c₂ Ψ (g * h) = ((c₁ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) *
      mp (Matrix.GeneralLinearGroup.det h) (1 / 2) * WL χ c₁ c₂ (Ψ ∘ rowAct h) g := by
  have hc : Ψ ∘ rowAct (g * h) = (Ψ ∘ rowAct h) ∘ rowAct g := by
    funext v; simp [rowAct_mul]
  simp only [WL, hc, map_mul, Units.val_mul, mp_mul]
  ring

theorem IsSB.add {Ψ₁ Ψ₂ : F × F → ℂ} (h₁ : IsSB Ψ₁) (h₂ : IsSB Ψ₂) : IsSB (Ψ₁ + Ψ₂) :=
  ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

theorem IsSB.smul {Ψ : F × F → ℂ} (a : ℂ) (h : IsSB Ψ) : IsSB (a • Ψ) :=
  ⟨h.1.comp (fun z : ℂ => a • z), h.2.comp_left (g := fun z : ℂ => a • z) (smul_zero a)⟩

theorem isSB_zero : IsSB (0 : F × F → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isSB_sum {ι : Type*} (s : Finset ι) (f : ι → F × F → ℂ) (h : ∀ i ∈ s, IsSB (f i)) :
    IsSB (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSB_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lin_add {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    {Ψ₁ Ψ₂ : F × F → ℂ} (hΨ₁ : IsSB Ψ₁) (hΨ₂ : IsSB Ψ₂) :
    lin χ c₁ c₂ (Ψ₁ + Ψ₂) = lin χ c₁ c₂ Ψ₁ + lin χ c₁ c₂ Ψ₂ := by
  have hinn : ∀ u, inn χ (Ψ₁ + Ψ₂) u = inn χ Ψ₁ u + inn χ Ψ₂ u := by
    intro u
    simp only [inn, Pi.add_apply, add_mul]
    exact integral_add (L_innInt F χ hχ Ψ₁ hΨ₁ u) (L_innInt F χ hχ Ψ₂ hΨ₂ u)
  have hden : den χ c₁ c₂ (Ψ₁ + Ψ₂) = fun u => den χ c₁ c₂ Ψ₁ u + den χ c₁ c₂ Ψ₂ u := by
    funext u
    simp only [den, hinn]
    ring
  simp only [lin, hden]
  exact integral_add (L_denInt F χ hχ c₁ c₂ h₁ h₂ Ψ₁ hΨ₁) (L_denInt F χ hχ c₁ c₂ h₁ h₂ Ψ₂ hΨ₂)

theorem lin_smul (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (a : ℂ) (Ψ : F × F → ℂ) :
    lin χ c₁ c₂ (a • Ψ) = a * lin χ c₁ c₂ Ψ := by
  have hinn : ∀ u, inn χ (a • Ψ) u = a * inn χ Ψ u := by
    intro u
    simp only [inn, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _
  have hden : den χ c₁ c₂ (a • Ψ) = fun u => a * den χ c₁ c₂ Ψ u := by
    funext u
    simp only [den, hinn]
    ring
  simp only [lin, hden]
  exact integral_const_mul a _

theorem mp_unit_one {t : Fˣ} (ht : t ∈ unitFiltrationUnits F 0) (s : ℂ) : mp t s = 1 := by
  have h := mem_unitFiltrationUnits_zero_iff_ord.1 ht
  simp only [mp, modulus_eq_one_iff.2 ⟨t.ne_zero, h⟩]
  simp

theorem lin_unit (χ : AddChar F Circle) {c₁ c₂ : Fˣ →* ℂˣ} (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂)
    (Ψ : F × F → ℂ) {t : Fˣ} (ht : t ∈ unitFiltrationUnits F 0) :
    lin χ c₁ c₂ (fun v => Ψ ((t : F) • v)) = lin χ c₁ c₂ Ψ := by
  have hinn : ∀ u, inn χ (fun v => Ψ ((t : F) • v)) u = inn χ Ψ (t * u) := by
    intro u
    simp only [inn, Prod.smul_mk, smul_eq_mul, Units.val_mul, mul_assoc]
  have e₁ : c₁ t = 1 := MonoidHom.mem_ker.1 (u₁ ht)
  have e₂ : c₂ t = 1 := MonoidHom.mem_ker.1 (u₂ ht)
  have hden : den χ c₁ c₂ (fun v => Ψ ((t : F) • v)) = fun u => den χ c₁ c₂ Ψ (t * u) := by
    funext u
    simp only [den, hinn, map_mul, Units.val_mul, mul_inv, mp_mul, e₁, e₂, mp_unit_one ht]
    simp
  simp only [lin, hden]
  exact integral_mul_left_eq_self (μ := multHaar F) (den χ c₁ c₂ Ψ) t

theorem WL_add {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    {Ψ₁ Ψ₂ : F × F → ℂ} (hΨ₁ : IsSB Ψ₁) (hΨ₂ : IsSB Ψ₂) :
    WL χ c₁ c₂ (Ψ₁ + Ψ₂) = WL χ c₁ c₂ Ψ₁ + WL χ c₁ c₂ Ψ₂ := by
  funext g
  have hc : (Ψ₁ + Ψ₂) ∘ rowAct g = Ψ₁ ∘ rowAct g + Ψ₂ ∘ rowAct g := rfl
  simp only [WL, Pi.add_apply, hc,
    lin_add hχ h₁ h₂ (L_comp F Ψ₁ hΨ₁ g) (L_comp F Ψ₂ hΨ₂ g)]
  ring

theorem WL_smul (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (a : ℂ) (Ψ : F × F → ℂ) :
    WL χ c₁ c₂ (a • Ψ) = a • WL χ c₁ c₂ Ψ := by
  funext g
  have hc : (a • Ψ) ∘ rowAct g = a • (Ψ ∘ rowAct g) := rfl
  simp only [WL, Pi.smul_apply, smul_eq_mul, hc, lin_smul]
  ring

theorem WL_sub {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    {Ψ₁ Ψ₂ : F × F → ℂ} (hΨ₁ : IsSB Ψ₁) (hΨ₂ : IsSB Ψ₂) :
    WL χ c₁ c₂ (Ψ₁ - Ψ₂) = WL χ c₁ c₂ Ψ₁ - WL χ c₁ c₂ Ψ₂ := by
  have h := WL_add hχ h₁ h₂ hΨ₁ (hΨ₂.smul (-1))
  rw [WL_smul] at h
  have e : Ψ₁ - Ψ₂ = Ψ₁ + (-1 : ℂ) • Ψ₂ := by simp [sub_eq_add_neg]
  rw [e, h]
  simp [sub_eq_add_neg]

theorem WL_sum {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    {ι : Type*} (s : Finset ι) (f : ι → F × F → ℂ) (h : ∀ i ∈ s, IsSB (f i)) :
    WL χ c₁ c₂ (∑ i ∈ s, f i) = ∑ i ∈ s, WL χ c₁ c₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := WL_smul χ c₁ c₂ 0 (0 : F × F → ℂ)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      WL_add hχ h₁ h₂ (h a (Finset.mem_insert_self a s))
        (isSB_sum s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem rowAct_smul (g : GL (Fin 2) F) (t : F) (v : F × F) : rowAct g (t • v) = t • rowAct g v := by
  simp only [rowAct, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.smul_mk]
  ext <;> simp <;> ring

theorem WL_unit (χ : AddChar F Circle) {c₁ c₂ : Fˣ →* ℂˣ} (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂)
    (Ψ : F × F → ℂ) {t : Fˣ} (ht : t ∈ unitFiltrationUnits F 0) :
    WL χ c₁ c₂ (fun v => Ψ ((t : F) • v)) = WL χ c₁ c₂ Ψ := by
  funext g
  have hc : (fun v => Ψ ((t : F) • v)) ∘ rowAct g = fun v => (Ψ ∘ rowAct g) ((t : F) • v) := by
    funext v
    simp [rowAct_smul]
  simp only [WL, hc, lin_unit χ u₁ u₂ _ ht]

abbrev Sp (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) : Submodule ℂ (GL (Fin 2) F → ℂ) :=
  Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g =>
    Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] (g * h)}

theorem L_detK (k : GL (Fin 2) F) (hk : k ∈ GLnLocal.integralGL F 2) :
    Matrix.GeneralLinearGroup.det k ∈ unitFiltrationUnits F 0 :=
  mem_unitFiltrationUnits_zero_iff_ord.2 (GroundTheory.Automorphic.GodementSectionLocal.ord_det_eq_zero hk)

theorem char_uniformizer {c : Fˣ →* ℂˣ} (u : IsUnramifiedChar c) :
    c (Iwasawa.uniformizerUnit F) = c (unifUnit F) := by
  have h : Iwasawa.uniformizerUnit F * (unifUnit F)⁻¹ ∈ unitFiltrationUnits F 0 := by
    rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_units_inv, ord_unifUnit,
      Iwasawa.coe_uniformizerUnit, ord_uniformizer (GLnLocal.irreducible_uniformizer F)]
    norm_num
  have := MonoidHom.mem_ker.1 (u h)
  rw [map_mul, map_inv] at this
  exact mul_inv_eq_one.1 this

theorem det_torusPow (l : Fin 2 → ℤ) :
    Matrix.GeneralLinearGroup.det (Iwasawa.torusPow F 2 l) = Iwasawa.uniformizerUnit F ^ (l 0 + l 1) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Iwasawa.coe_torusPow, Matrix.det_diagonal,
    Fin.prod_univ_two, Units.val_zpow_eq_zpow_val, Iwasawa.coe_uniformizerUnit,
    zpow_add₀ (by exact_mod_cast (GLnLocal.irreducible_uniformizer F).ne_zero)]

theorem L_val (χ : AddChar F Circle) (hχ : IsStd χ) (c₁ c₂ : Fˣ →* ℂˣ) (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (l : Fin 2 → ℤ) :
    WL χ c₁ c₂ (lat0 F) (Iwasawa.torusPow F 2 l) = if Antitone l then Spherical.halfModulus F l *
      Spherical.evalAt ![c₁ (unifUnit F), c₂ (unifUnit F)] (Spherical.schur l) else 0 := by
  obtain ⟨A, D, rfl⟩ : ∃ A D : ℤ, l = ![A, D] := ⟨l 0, l 1, by
    funext i; fin_cases i <;> rfl⟩
  have hanti : Antitone (![A, D] : Fin 2 → ℤ) ↔ D ≤ A := by
    constructor
    · intro h
      simpa using h (show (0 : Fin 2) ≤ 1 by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hrho : Spherical.rhoPair (![A, D] : Fin 2 → ℤ) = A - D := by
    simp [Spherical.rhoPair, Fin.sum_univ_two]
    ring
  set x := c₁ (unifUnit F) with hx
  set y := c₂ (unifUnit F) with hy
  have hden : ∀ u, den χ c₁ c₂ (lat0 F ∘ rowAct (Iwasawa.torusPow F 2 ![A, D])) u =
      ((Spherical.qF F : ℕ) : ℂ) ^ D *
        (if -A ≤ ord (u : F) ∧ ord (u : F) ≤ -D then (((c₁ * c₂⁻¹) u : ℂˣ) : ℂ) else 0) := by
    intro u
    have hm := mp_ne_zero u 1
    simp only [den, lattice_inner_integral_value F χ hχ ![A, D] u, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    split_ifs
    · simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      field_simp
    · simp
  have hlin : lin χ c₁ c₂ (lat0 F ∘ rowAct (Iwasawa.torusPow F 2 ![A, D])) =
      ((Spherical.qF F : ℕ) : ℂ) ^ D * ∑ j ∈ Finset.Icc D A, (((x * y⁻¹ : ℂˣ)) : ℂ) ^ (-j) := by
    have hμ : IsUnramifiedChar (c₁ * c₂⁻¹) := fun t ht => by
      have e₁ : c₁ t = 1 := MonoidHom.mem_ker.1 (u₁ ht)
      have e₂ : c₂ t = 1 := MonoidHom.mem_ker.1 (u₂ ht)
      simp [MonoidHom.mem_ker, e₁, e₂]
    have := unramified_character_integral_sum F (c₁ * c₂⁻¹) hμ A D
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this
    simp only [lin, hden]
    rw [integral_const_mul]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [this]
  simp only [WL, hlin, det_torusPow, L_mpHalf F, map_zpow, char_uniformizer u₁,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  by_cases hDA : D ≤ A
  · rw [if_pos (hanti.2 hDA), Spherical.halfModulus_eq, hrho, schur_polynomial_two_eval x y A D hDA, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hs : Spherical.sqrtQ F ≠ 0 := Spherical.sqrtQ_ne_zero
    have hq : ((Spherical.qF F : ℕ) : ℂ) = Spherical.sqrtQ F ^ (2 : ℤ) := by
      rw [zpow_ofNat, Spherical.sqrtQ_sq]
    have hx0 : (x : ℂ) ≠ 0 := x.ne_zero
    have hy0 : (y : ℂ) ≠ 0 := y.ne_zero
    rw [hq, ← _root_.zpow_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      mul_zpow, _root_.inv_zpow', neg_neg]
    have e₁ : (x : ℂ) ^ (A + D - j) = (x : ℂ) ^ (A + D) * (x : ℂ) ^ (-j) := by
      rw [← zpow_add₀ hx0]
      congr 1
    have e₂ : Spherical.sqrtQ F ^ (-(A - D)) = Spherical.sqrtQ F ^ (-(A + D)) * Spherical.sqrtQ F ^ (2 * D) := by
      rw [← zpow_add₀ hs]
      congr 1
      ring
    rw [e₁, e₂]
    ring
  · rw [if_neg (fun h => hDA (hanti.1 h)), Finset.Icc_eq_empty hDA]
    simp

theorem psi_std {χ : AddChar F Circle} (hχ : IsStd χ) :
    ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar χ) x = 1 := by
  intro x hx
  obtain ⟨hc, h1, h0⟩ := hχ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have := ht x (mem_valBall_zero_iff.2 hx)
  show ((χ x : Circle) : ℂ) = 1
  rw [this, Circle.coe_one]

theorem lattice_whittaker_eq_spherical {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (g : GL (Fin 2) F) :
    WL χ c₁ c₂ (lat0 F) g =
      Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] g := by
  have hu := Spherical.iwasawaUnip_mem g
  have hk := Spherical.iwasawaInt_mem g
  have hg := Spherical.eq_iwasawa g
  set u := Spherical.iwasawaUnip g
  set k := Spherical.iwasawaInt g
  set l := Iwasawa.iwasawaExponent F 2 g
  have hd := L_detK k hk
  rw [hg, WL_mul, L_latK F k hk, mul_assoc u, L_left F χ c₁ c₂ _ u _ hu, L_val χ hχ c₁ c₂ h₁ h₂ u₁ u₂ l,
    ← mul_assoc u, Spherical.sphericalWhittaker_apply (psi_std hχ) _ hu hk l,
    mp_unit_one hd, MonoidHom.mem_ker.1 (u₁ hd)]
  split_ifs <;> simp <;> ring

theorem WL_lat_mem {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (h : GL (Fin 2) F) :
    WL χ c₁ c₂ (lat0 F ∘ rowAct h) ∈ Sp χ c₁ c₂ := by
  set κ : ℂ := ((c₁ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det h) (1 / 2)
  have hκ : κ ≠ 0 := mul_ne_zero (Units.ne_zero _) (mp_ne_zero _ _)
  have e : WL χ c₁ c₂ (lat0 F ∘ rowAct h) = κ⁻¹ • fun g =>
      Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] (g * h) := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← lattice_whittaker_eq_spherical hχ h₁ h₂ u₁ u₂, WL_mul]
    show _ = κ⁻¹ * (κ * _)
    rw [inv_mul_cancel_left₀ hκ]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

theorem ind_spanSet (n : ℤ) (x : F × F) : ∃ h : GL (Fin 2) F,
    (spanSet n x).indicator (1 : F × F → ℂ) = lat0 F ∘ rowAct h := by
  obtain ⟨h, e⟩ := L_lat F n x
  refine ⟨h, ?_⟩
  funext v
  have hv : v ∈ spanSet n x ↔ rowAct h v ∈ Ln F 0 := by rw [e]; rfl
  by_cases hw : rowAct h v ∈ Ln F 0
  · rw [Function.comp, lat0, Set.indicator_of_mem (hv.2 hw), Set.indicator_of_mem hw]
    rfl
  · rw [Function.comp, lat0, Set.indicator_of_notMem (mt hv.1 hw), Set.indicator_of_notMem hw]

theorem isSB_span (n : ℤ) (x : F × F) : IsSB ((spanSet n x).indicator (1 : F × F → ℂ)) := by
  obtain ⟨h, e⟩ := ind_spanSet n x
  rw [e]
  have := L_coset F 0 (0 : F × F)
  have e0 : cosetInd 0 (0 : F × F) = lat0 F := by
    simp [cosetInd, lat0]
  exact L_comp F _ (e0 ▸ this) h

theorem WL_span_mem {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (n : ℤ) (x : F × F) :
    WL χ c₁ c₂ ((spanSet n x).indicator (1 : F × F → ℂ)) ∈ Sp χ c₁ c₂ := by
  obtain ⟨h, e⟩ := ind_spanSet n x
  rw [e]
  exact WL_lat_mem hχ h₁ h₂ u₁ u₂ h

theorem Ln_sub {n : ℤ} {a b : F × F} (ha : a ∈ Ln F n) (hb : b ∈ Ln F n) : a - b ∈ Ln F n :=
  ⟨sub_mem ha.1 hb.1, sub_mem ha.2 hb.2⟩

theorem WL_coset_mem {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) (n : ℤ) (x : F × F) :
    WL χ c₁ c₂ (cosetInd n x) ∈ Sp χ c₁ c₂ := by
  by_cases hx : x ∈ Ln F n
  · have e : cosetInd n x = (spanSet n 0).indicator (1 : F × F → ℂ) := by
      have : {v | v - x ∈ Ln F n} = spanSet n (0 : F × F) := by
        ext v
        constructor
        · intro hv
          refine ⟨0, zero_mem _, ?_⟩
          have := Ln_sub hv (Ln_sub (show (0 : F × F) ∈ Ln F n from ⟨zero_mem _, zero_mem _⟩) hx)
          simpa using this
        · rintro ⟨a, -, hv⟩
          simpa using Ln_sub (by simpa using hv) hx
      simp only [cosetInd, this]
    rw [e]
    exact WL_span_mem hχ h₁ h₂ u₁ u₂ n 0
  · obtain ⟨s, hs, ht, e⟩ := L_orbit F n x hx
    have hW : ∀ t ∈ s, WL χ c₁ c₂ (cosetInd n ((t : F) • x)) = WL χ c₁ c₂ (cosetInd n x) := by
      intro t hts
      rw [L_cosetUnit F n x t (ht t hts)]
      exact WL_unit χ u₁ u₂ _ (inv_mem (ht t hts))
    have hsum : ((s.card : ℂ)) • WL χ c₁ c₂ (cosetInd n x) =
        WL χ c₁ c₂ ((spanSet n x).indicator (1 : F × F → ℂ)) -
          WL χ c₁ c₂ ((spanSet n (((unifUnit F : Fˣ) : F) • x)).indicator (1 : F × F → ℂ)) := by
      rw [← WL_sub hχ h₁ h₂ (isSB_span _ _) (isSB_span _ _), e,
        WL_sum hχ h₁ h₂ s _ fun t _ => L_coset F n _, Finset.sum_congr rfl hW,
        Finset.sum_const, Nat.cast_smul_eq_nsmul]
    have hc : (s.card : ℂ) ≠ 0 := by
      exact_mod_cast hs.card_pos.ne'
    have : WL χ c₁ c₂ (cosetInd n x) = (s.card : ℂ)⁻¹ • ((s.card : ℂ) • WL χ c₁ c₂ (cosetInd n x)) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this, hsum]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (WL_span_mem hχ h₁ h₂ u₁ u₂ _ _)
      (WL_span_mem hχ h₁ h₂ u₁ u₂ _ _))

theorem WL_mem {χ : AddChar F Circle} (hχ : IsStd χ) {c₁ c₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 c₁) (h₂ : IsUnit1 c₂)
    (u₁ : IsUnramifiedChar c₁) (u₂ : IsUnramifiedChar c₂) {Ψ : F × F → ℂ} (hΨ : IsSB Ψ) :
    WL χ c₁ c₂ Ψ ∈ Sp χ c₁ c₂ := by
  obtain ⟨n, s, a, rfl⟩ := L_decomp F Ψ hΨ
  rw [WL_sum hχ h₁ h₂ s _ fun x _ => (L_coset F n x).smul (a x)]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [WL_smul]
  exact Submodule.smul_mem _ _ (WL_coset_mem hχ h₁ h₂ u₁ u₂ n x)

theorem WcS_eq_WL {χ : AddChar F Circle} (hχ : IsStd χ) (c₁ c₂ : Fˣ →* ℂˣ) {Φ : F × F → ℂ} (hΦ : IsSB Φ) :
    GL2LocalData.WcS χ c₁ c₂ Φ = WL χ c₁ c₂ (pF χ Φ) := by
  funext g
  have hdet : ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = (g.val).det := rfl
  have key : ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1)
      (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      mp u 1 * inn χ (pF χ Φ ∘ rowAct g) u := by
    intro u
    by_cases hc : g.val 1 0 = 0
    · exact L_modelZero F χ hχ Φ hΦ g hc u
    · exact L_modelNe F χ hχ Φ hΦ g hc u
  simp only [GL2LocalData.WcS, WL, lin, den, key]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring

theorem WcS_mem_span : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnit1 c₁ → IsUnit1 c₂ → IsUnramifiedChar c₁ → IsUnramifiedChar c₂ → ∀ Φ : F × F → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → GL2LocalData.WcS χ c₁ c₂ Φ ∈ Submodule.span ℂ {f : GL (Fin 2) F → ℂ | ∃ h : GL (Fin 2) F, f = fun g => Spherical.sphericalWhittaker (Circle.coeHom.compAddChar χ) ![c₁ (unifUnit F), c₂ (unifUnit F)] (g * h)} := by
  intro F _ _ _ _ _ _ χ hχ c₁ c₂ h₁ h₂ u₁ u₂ Φ hl hc
  have hΦ : IsSB Φ := ⟨hl, hc⟩
  rw [WcS_eq_WL hχ c₁ c₂ hΦ]
  exact WL_mem hχ h₁ h₂ u₁ u₂ (L_pF F χ hχ Φ hΦ)

end GlobalTheory.CompanionTheory.WS
