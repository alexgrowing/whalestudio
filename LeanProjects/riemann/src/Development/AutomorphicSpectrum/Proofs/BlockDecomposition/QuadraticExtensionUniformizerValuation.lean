import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import GroundTheory.AutomorphicForms.MacdonaldWhittaker
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEntryLeMRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdEqZeroOfModulusEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulIntInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.InertTorus

open GlobalTheory.CompanionTheory.NormGauss

section Schur

theorem evalAt_monomial_single (w : Fin 2 → ℂˣ) (a : Fin 2) (p : ℤ) :
    Spherical.evalAt w (Spherical.monomial (Pi.single a p)) = (w a : ℂ) ^ p := by
  rw [Spherical.monomial, Spherical.evalAt_single, one_mul, Spherical.monomialChar_apply,
    Finset.prod_eq_single a]
  · simp [Units.val_zpow_eq_zpow_val]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem evalAt_alternant_two (w : Fin 2 → ℂˣ) (p r : ℤ) :
    Spherical.evalAt w (Spherical.alternant ![p, r]) =
      (w 0 : ℂ) ^ p * (w 1 : ℂ) ^ r - (w 0 : ℂ) ^ r * (w 1 : ℂ) ^ p := by
  rw [Spherical.alternant_eq_det, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [map_sub, map_mul, map_mul]
  simp only [evalAt_monomial_single]

theorem staircase_two_eq : Spherical.staircase 2 = ![1, 0] := by
  funext i
  fin_cases i <;> simp [Spherical.staircase]

theorem evalAt_schur_pm (b : ℂˣ) (A D : ℤ) :
    Spherical.evalAt ![b, -b] (Spherical.schur ![A, D]) =
      if Even (A + D) then (-1 : ℂ) ^ D * (b : ℂ) ^ (A + D) else 0 := by
  have hb : (b : ℂ) ≠ 0 := b.ne_zero
  have h := congrArg (Spherical.evalAt ![b, -b]) (Spherical.alternant_mul_schur ![A, D])
  have e : (![A, D] + Spherical.staircase 2 : Fin 2 → ℤ) = ![A + 1, D] := by
    rw [staircase_two_eq]
    funext i
    fin_cases i <;> simp
  rw [e, map_mul, staircase_two_eq, evalAt_alternant_two, evalAt_alternant_two] at h
  have hneg : ∀ k : ℤ, (-(b : ℂ)) ^ k = (-1 : ℂ) ^ k * (b : ℂ) ^ k := fun k => by
    rw [← mul_zpow, neg_one_mul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_neg, hneg] at h
  simp only [zpow_one, zpow_zero, mul_one, one_mul] at h
  have hpar : (-1 : ℂ) ^ A = if Even (A + D) then (-1 : ℂ) ^ D else -(-1 : ℂ) ^ D := by
    rcases Int.even_or_odd A with a | a <;> rcases Int.even_or_odd D with d | d
    · rw [if_pos (a.add d), a.neg_one_zpow, d.neg_one_zpow]
    · rw [if_neg (by rw [Int.not_even_iff_odd]; exact a.add_odd d), a.neg_one_zpow,
        d.neg_one_zpow, neg_neg]
    · rw [if_neg (by rw [Int.not_even_iff_odd]; exact a.add_even d), a.neg_one_zpow,
        d.neg_one_zpow]
    · rw [if_pos (a.add_odd d), a.neg_one_zpow, d.neg_one_zpow]
  have h2 : (-1 : ℂ) ^ (A + 1) = -(-1 : ℂ) ^ A := by
    rw [zpow_add₀ (by norm_num), zpow_one]
    ring
  have hb1 : (b : ℂ) ^ (A + 1) * (b : ℂ) ^ D = (b : ℂ) ^ (A + D) * b := by
    rw [← zpow_add₀ hb, show A + 1 + D = A + D + 1 by ring, zpow_add₀ hb, zpow_one]
  rw [h2] at h
  have key : (2 * (b : ℂ)) * Spherical.evalAt ![b, -b] (Spherical.schur ![A, D]) =
      (b : ℂ) ^ (A + D) * b * ((-1 : ℂ) ^ D + (-1 : ℂ) ^ A) := by
    rw [← hb1]
    linear_combination h
  have h2b : (2 * (b : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hb
  refine mul_left_cancel₀ h2b ?_
  rw [key, hpar]
  split_ifs with he
  · ring
  · ring

end Schur

section Unif

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem unif_ne_zero : (GLnLocal.uniformizer K : K) ≠ 0 :=
  (Iwasawa.uniformizerUnit K).ne_zero

theorem ord_unif_zpow (k : ℤ) : ord ((GLnLocal.uniformizer K : K) ^ k) = k := by
  rw [ord_zpow unif_ne_zero, ord_uniformizer (GLnLocal.irreducible_uniformizer K), mul_one]

theorem modulus_unif_zpow (k : ℤ) :
    ((modulus ((GLnLocal.uniformizer K : K) ^ k) : NNReal) : ℝ) =
      (((NNReal.sqrt (residueCard K : NNReal) : NNReal) : ℝ) ^ (-k)) ^ 2 := by
  rw [modulus_of_ne_zero (zpow_ne_zero _ unif_ne_zero), ord_unif_zpow, ← NNReal.coe_zpow,
    ← NNReal.coe_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, NNReal.sq_sqrt]

end Unif

theorem cpow_half_sq {y : ℝ} (hy : 0 ≤ y) : (((y ^ 2 : ℝ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) = y := by
  have h := Complex.ofReal_cpow (sq_nonneg y) (1 / 2 : ℝ)
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy] at h
  rw [h]
  push_cast
  rfl

section Torus

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem torus_val (l : Fin 2 → ℤ) : (Iwasawa.torusPow F 2 l).val =
    Matrix.diagonal fun i => (GLnLocal.uniformizer F : F) ^ l i :=
  Iwasawa.coe_torusPow F 2 l

theorem torus_det (l : Fin 2 → ℤ) : ((Iwasawa.torusPow F 2 l).val).det =
    (GLnLocal.uniformizer F : F) ^ (l 0 + l 1) := by
  rw [torus_val, Matrix.det_fin_two, zpow_add₀ unif_ne_zero]
  simp

theorem mRow_torus (l : Fin 2 → ℤ) : mRow (Iwasawa.torusPow F 2 l) =
    (GLnLocal.uniformizer F : F) ^ l 1 := by
  have h : modulus (0 : F) < modulus ((GLnLocal.uniformizer F : F) ^ l 1) := by
    rw [modulus_zero]
    exact modulus_pos (zpow_ne_zero _ unif_ne_zero)
  have hz : (Iwasawa.torusPow F 2 l).val 1 0 = 0 := by simp [torus_val]
  have hd : (Iwasawa.torusPow F 2 l).val 1 1 = (GLnLocal.uniformizer F : F) ^ l 1 := by
    simp [torus_val]
  unfold mRow
  rw [hz, hd, if_pos h]

theorem xRow_torus (l : Fin 2 → ℤ) : xRow (Iwasawa.torusPow F 2 l) = 0 := by
  have h : modulus (0 : F) < modulus ((GLnLocal.uniformizer F : F) ^ l 1) := by
    rw [modulus_zero]
    exact modulus_pos (zpow_ne_zero _ unif_ne_zero)
  have hz : (Iwasawa.torusPow F 2 l).val 1 0 = 0 := by simp [torus_val]
  have hd : (Iwasawa.torusPow F 2 l).val 1 1 = (GLnLocal.uniformizer F : F) ^ l 1 := by
    simp [torus_val]
  have ho : (Iwasawa.torusPow F 2 l).val 0 1 = 0 := by simp [torus_val]
  unfold xRow
  rw [hz, hd, if_pos h, ho, zero_div]

theorem rhoPair_two (l : Fin 2 → ℤ) : Spherical.rhoPair l = l 0 - l 1 := by
  simp [Spherical.rhoPair, Fin.sum_univ_two]
  ring

theorem antitone_iff (l : Fin 2 → ℤ) : Antitone l ↔ l 1 ≤ l 0 := by
  constructor
  · intro h
    exact h (Fin.zero_le 1)
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

end Torus

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]

theorem not_norm_of_odd (hd : Module.finrank F E = 2)
    (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {k : ℤ} (hk : ¬ Even k) :
    ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = (GLnLocal.uniformizer F : F) ^ k := by
  rintro ⟨t, ht⟩
  have h := ord_normE hd h1 (t : E)
  rw [ht, ord_unif_zpow] at h
  exact hk ⟨ord (t : E), by omega⟩

theorem nsg_unif_zpow (hd : Module.finrank F E = 2)
    (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) {η : Fˣ →* ℂˣ}
    (hη : ∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) (D : ℤ) :
    GL2LocalData.nsg E ((GLnLocal.uniformizer F : F) ^ D) = (-1 : ℂ) ^ D := by
  have hu : ((η (Iwasawa.uniformizerUnit F) : ℂˣ) : ℂ) = -1 := by
    rw [hη, GL2LocalData.nsg, if_neg]
    have := not_norm_of_odd hd h1 (k := 1) (by decide)
    simpa using this
  have h := hη (Iwasawa.uniformizerUnit F ^ D)
  rw [map_zpow, Units.val_zpow_eq_zpow_val, hu, Units.val_zpow_eq_zpow_val,
    Iwasawa.coe_uniformizerUnit] at h
  exact h.symm

def unifE (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [Field E] [Algebra F E] (m : ℤ) : Eˣ :=
  Units.map (algebraMap F E).toMonoidHom (Iwasawa.uniformizerUnit F ^ m)

theorem coe_unifE (m : ℤ) :
    ((unifE F E m : Eˣ) : E) = algebraMap F E ((GLnLocal.uniformizer F : F) ^ m) := by
  simp [unifE, Units.val_zpow_eq_zpow_val]

theorem norm_unifE (hd : Module.finrank F E = 2) (m : ℤ) :
    Algebra.norm F ((unifE F E m : Eˣ) : E) = (GLnLocal.uniformizer F : F) ^ (m + m) := by
  rw [coe_unifE, Algebra.norm_algebraMap, hd, zpow_add₀ unif_ne_zero, pow_two]

theorem char_unifE [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)]
    {c : Eˣ →* ℂˣ} (hc : IsUnramifiedChar c) {b : ℂˣ}
    (hb : b ^ 2 = c (Units.map (algebraMap F E).toMonoidHom (unifUnit F))) (m : ℤ) :
    ((c (unifE F E m) : ℂˣ) : ℂ) = (b : ℂ) ^ (m + m) := by
  have h0 : c (Units.map (algebraMap F E).toMonoidHom (Iwasawa.uniformizerUnit F)) = b ^ 2 := by
    rw [hb]
    refine InertAsm.char_congr c hc ?_
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F), FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F)]
    congr 1
    rw [Iwasawa.coe_uniformizerUnit, modulus_of_ne_zero unif_ne_zero,
      modulus_of_ne_zero (Units.ne_zero _), ord_uniformizer (GLnLocal.irreducible_uniformizer F),
      ord_unif]
  rw [unifE, map_zpow, map_zpow, h0, zpow_add₀ (by exact b.ne_zero)]
  simp [Units.val_zpow_eq_zpow_val]
  have hb0 : (b : ℂ) ≠ 0 := b.ne_zero
  rw [← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ hb0]
  congr 1
  push_cast
  ring

theorem intInd_unifE (h1 : ord (algebraMap F E (unifUnit F : F)) = 1) (m D : ℤ) :
    (intInd (((unifE F E m : Eˣ) : E) * algebraMap F E ((GLnLocal.uniformizer F : F) ^ D)⁻¹) : ℂ) =
      if D ≤ m then 1 else 0 := by
  have he : ((unifE F E m : Eˣ) : E) * algebraMap F E ((GLnLocal.uniformizer F : F) ^ D)⁻¹ =
      algebraMap F E ((GLnLocal.uniformizer F : F) ^ (m - D)) := by
    rw [coe_unifE, ← map_mul, zpow_sub₀ unif_ne_zero, div_eq_mul_inv]
  have hne : algebraMap F E ((GLnLocal.uniformizer F : F) ^ (m - D)) ≠ 0 := by
    exact (map_ne_zero _).2 (zpow_ne_zero _ unif_ne_zero)
  rw [he]
  have hiff := mem_int_iff_ord hne
  rw [ord_map h1, ord_unif_zpow] at hiff
  split_ifs with h
  · exact intInd_of_mem (hiff.2 (by omega))
  · exact intInd_of_not_mem (fun hm => h (by have := hiff.1 hm; omega))

end Main

theorem sqrtQ_cpow (k : ℤ) {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    (((modulus ((GLnLocal.uniformizer F : F) ^ k) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      Spherical.sqrtQ F ^ (-k) := by
  rw [modulus_unif_zpow, cpow_half_sq (zpow_nonneg (NNReal.coe_nonneg _) _),
    Complex.ofReal_zpow]
  rfl

theorem sqrtQ_inv (k : ℤ) {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] :
    (((modulus ((GLnLocal.uniformizer F : F) ^ k) : ℝ)⁻¹ : ℝ) : ℂ) =
      Spherical.sqrtQ F ^ (2 * k) := by
  have h0 : Spherical.sqrtQ F ≠ 0 := Spherical.sqrtQ_ne_zero
  rw [modulus_unif_zpow, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_zpow]
  change ((Spherical.sqrtQ F ^ (-k)) ^ 2)⁻¹ = _
  rw [← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg]
  congr 1
  push_cast
  ring

theorem Wc_torusPow : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) (σ : E ≃ₐ[F] E) (c : Eˣ →* ℂˣ), Ad3.IsStd χ → IsUnramifiedChar c → ((∀ a, ((η a : ℂˣ) : ℂ) = GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ GL2LocalData.nsg E (-1 : F) = 1) → (∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det → GL2LocalData.rW χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) * intInd ((t : E) * algebraMap F E (mRow g)⁻¹)) → ∀ b : ℂˣ, b ^ 2 = c (Units.map (algebraMap F E).toMonoidHom (unifUnit F)) → ∀ l : Fin 2 → ℤ, GL2LocalData.Wc χ σ (selfDualMeasure (GL2LocalData.chE E χ)) 1 c intInd (Iwasawa.torusPow F 2 l) = if Antitone l then Spherical.halfModulus F l * Spherical.evalAt ![b, -b] (Spherical.schur l) else 0 := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ h2 _ h1 χ η σ c hχ hc hη hform b hb l
  obtain ⟨hη1, -, -, -⟩ := hη
  classical
  haveI : Fact (Module.finrank F E = 2) := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable F E := inferInstance
  have hl : l = ![l 0, l 1] := by
    funext i
    fin_cases i <;> rfl
  have hs : Spherical.evalAt ![b, -b] (Spherical.schur l) =
      if Even (l 0 + l 1) then (-1 : ℂ) ^ (l 1) * (b : ℂ) ^ (l 0 + l 1) else 0 := by
    have h := evalAt_schur_pm b (l 0) (l 1)
    rwa [← hl] at h
  have hs0 : Spherical.sqrtQ F ≠ 0 := Spherical.sqrtQ_ne_zero
  by_cases he : Even (l 0 + l 1)
  · obtain ⟨m, hm⟩ := id he
    have hN : Algebra.norm F ((unifE F E m : Eˣ) : E) = ((Iwasawa.torusPow F 2 l).val).det := by
      rw [norm_unifE h2, torus_det, hm]
    rw [InertAsm.Wc_eq hc hform _ _ hN, InertAsm.val, mRow_torus, xRow_torus, torus_det, hs,
      if_pos he, char_unifE hc hb, nsg_unif_zpow h2 h1 hη1, intInd_unifE h1, sqrtQ_cpow, sqrtQ_inv,
      AddChar.map_zero_eq_one, Circle.coe_one, Spherical.halfModulus_eq, rhoPair_two, ← hm]
    by_cases ha : l 1 ≤ l 0
    · rw [if_pos (by omega), if_pos ((antitone_iff l).2 ha),
        show -(l 0 - l 1) = -(l 0 + l 1) + 2 * l 1 by ring, zpow_add₀ hs0]
      ring
    · rw [if_neg (by omega), if_neg (fun h => ha ((antitone_iff l).1 h))]
      ring
  · have hn : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((Iwasawa.torusPow F 2 l).val).det := by
      rw [torus_det]
      exact not_norm_of_odd h2 h1 he
    rw [GL2LocalData.Wc, dif_neg hn, hs, if_neg he]
    simp

end GlobalTheory.CompanionTheory.SphTheta.InertTorus
