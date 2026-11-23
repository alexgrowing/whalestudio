import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralMulNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticExistsIntegersUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianTraceDualIntegersEqUniformizerPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureLUnitSmulAbsKSqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticGaussIntegralStableOfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGaussIntegralNormFormStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.WeilQuad.NonNorm

section Help
open scoped Pointwise
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem stable_unique (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K)
    {G G' : ℂ} (h : IsStableGauss A ψ x μ u G) (h' : IsStableGauss A ψ x μ u G') : G = G' := by
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  obtain ⟨Λ₀, ho, hc, hG⟩ := h
  obtain ⟨Λ₁, ho', hc', hG'⟩ := h'
  have hs : ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) = (Λ₀ : Set A.L) + (Λ₁ : Set A.L) :=
    AddSubgroup.add_normal Λ₀ Λ₁
  have hO : IsOpen ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := AddSubgroup.isOpen_mono le_sup_left ho
  have hC : IsCompact ((Λ₀ ⊔ Λ₁ : AddSubgroup A.L) : Set A.L) := by rw [hs]; exact hc.add hc'
  rw [← hG _ hO hC le_sup_left, ← hG' _ hO hC le_sup_right]

theorem NL_algebraMap [Unram F E] (A : Et F E) (c : A.K) : A.NL (algebraMap A.K A.L c) = c ^ 2 := by
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  apply hinj
  rw [hN, A.star_K, map_pow, sq]

theorem absK_zpow (A : Et F E) (u : A.Kˣ) (n : ℤ) :
    A.absK ((u ^ n : A.Kˣ) : A.K) = A.absK (u : A.K) ^ n := by
  simp [Et.absK, map_zpow]

theorem absK_pos (A : Et F E) (u : A.Kˣ) : 0 < A.absK (u : A.K) := by
  simp only [Et.absK, Units.isUnit, dite_true, IsUnit.unit_of_val_units]
  exact_mod_cast ((Group.isUnit u).map (distribHaarChar A.K)).ne_zero.bot_lt

theorem dual_mul (A : Et F E) (ψ : AddChar F ℂ) (O : Subring A.L) (t a : A.K) :
    {y : A.L | ∀ m ∈ O, A.kerL ψ (t * a) y m = 1} =
      {y : A.L | ∀ m ∈ O, A.kerL ψ a (algebraMap A.K A.L t * y) m = 1} := by
  ext y
  simp only [Set.mem_setOf_eq, Et.kerL]
  refine forall₂_congr fun m _ => ?_
  have : Algebra.trace A.K A.L (star (algebraMap A.K A.L t * y) * m) =
      t * Algebra.trace A.K A.L (star y * m) := by
    rw [star_mul', A.star_K, mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [this, mul_comm t a, mul_assoc]

theorem scaled_mul (A : Et F E) (O : Subring A.L) (t c : A.Kˣ) :
    {y : A.L | algebraMap A.K A.L (t : A.K) * y ∈ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (c : A.K) * z}} =
      {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((t⁻¹ * c : A.Kˣ) : A.K) * z} := by
  ext y
  simp only [Set.mem_setOf_eq, Units.val_mul, map_mul]
  refine exists_congr fun z => and_congr_right fun _ => ?_
  have h1 : algebraMap A.K A.L ((t⁻¹ : A.Kˣ) : A.K) * algebraMap A.K A.L (t : A.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  constructor
  · intro h; rw [← one_mul y, ← h1, mul_assoc, h, ← mul_assoc]
  · intro h; rw [h, ← mul_assoc, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

end Help

section Levels
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem kerL_mul_left (A : Et F E) (ψ : AddChar F ℂ) (a c : A.K) (y m : A.L) :
    A.kerL ψ a (algebraMap A.K A.L c * y) m = A.kerL ψ a y (algebraMap A.K A.L c * m) := by
  simp only [Et.kerL]
  rw [star_mul', A.star_K]
  ring_nf

theorem kerL_one (A : Et F E) (ψ : AddChar F ℂ) (a : A.K) (m : A.L) :
    A.kerL ψ a 1 m = A.psiK ψ (a * Algebra.trace A.K A.L m) := by
  simp [Et.kerL]

theorem trace_algebraMap_mul (A : Et F E) (c : A.K) (w : A.L) :
    Algebra.trace A.K A.L (algebraMap A.K A.L c * w) = c * Algebra.trace A.K A.L w := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem level0 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ O : Subring A.L, IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) → ∀ t : A.K, {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} = (O : Set A.L) → IsStableGauss A ψ x μ t (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ A ψ x μ hψ hμ O hOo hOc hOs htr t hD
  obtain ⟨-, -, hN, htrL, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have h1 : (1 : A.L) ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} := by rw [hD]; exact O.one_mem
  have hM : ∀ m ∈ O, A.psiK ψ (t * x * A.NL m) = 1 := fun m hm => by
    obtain ⟨z, hz, hzs⟩ := htr (A.NL m) (by rw [hN]; exact O.mul_mem hm (hOs m hm))
    have := h1 z hz
    rwa [kerL_one, hzs] at this
  have hDeq : ((O.toAddSubgroup : AddSubgroup A.L) : Set A.L) =
      {y : A.L | ∀ m ∈ O.toAddSubgroup, A.kerL ψ (t * x) y m = 1} := by
    simpa using hD.symm
  have hG := GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice F E A ψ x μ hψ hμ t O.toAddSubgroup O.toAddSubgroup hOo hOc hOo hOc
    (fun m hm => hM m hm) hDeq
  convert hG using 1
  simp only [gaussInt, Subring.coe_toAddSubgroup]
  rw [setIntegral_congr_fun hOo.measurableSet (g := fun _ => (1 : ℂ)) (fun y hy => hM y hy)]
  simp [Measure.real]

end Levels

section Level1
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def scaledSub (A : Et F E) (O : Subring A.L) (c : A.K) : AddSubgroup A.L where
  carrier := {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L c * z}
  add_mem' := by
    rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
    exact ⟨z + z', O.add_mem hz hz', by ring⟩
  zero_mem' := ⟨0, O.zero_mem, by simp⟩
  neg_mem' := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨-z, O.neg_mem hz, by ring⟩

def mulHomeo [Unram F E] (A : Et F E) (c : A.Kˣ) : A.L ≃ₜ A.L :=
  haveI := GlobalTheory.JR.EtMeas.finite_L A
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  { toFun := fun y => algebraMap A.K A.L (c : A.K) * y
    invFun := fun y => algebraMap A.K A.L ((c⁻¹ : A.Kˣ) : A.K) * y
    left_inv := fun y => by
      simp only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    right_inv := fun y => by
      simp only [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    continuous_toFun := continuous_const.mul continuous_id
    continuous_invFun := continuous_const.mul continuous_id }

theorem scaledSub_eq_image [Unram F E] (A : Et F E) (O : Subring A.L) (c : A.Kˣ) :
    ((scaledSub A O c : AddSubgroup A.L) : Set A.L) = mulHomeo A c '' (O : Set A.L) := by
  ext y
  simp only [scaledSub, AddSubgroup.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk,
    Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

theorem level1 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → IsField A.K → IsField A.L → ∀ (O : Subring A.L) (ϖ : A.Kˣ), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) → μ {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} = ENNReal.ofReal (A.absK (ϖ : A.K) ^ 2) * μ (O : Set A.L) → ∀ t : A.K, {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z} → IsStableGauss A ψ x μ t (-((A.absK (ϖ : A.K) : ℝ) : ℂ) * (((μ (O : Set A.L)).toReal : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ A ψ x μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖu hdich htr hnorm hsc t hD
  obtain ⟨-, hinj, hN, htrL, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  have hmemD : ∀ y : A.L, (∀ m ∈ O, A.kerL ψ (t * x) y m = 1) ↔ ∃ z ∈ O, y = algebraMap A.K A.L ϖ * z := fun y => by
    have := congrArg (y ∈ ·) hD
    simpa using this

  have hϖD : ∀ m ∈ O, A.kerL ψ (t * x) (algebraMap A.K A.L ϖ) m = 1 := (hmemD _).2 ⟨1, O.one_mem, by simp⟩
  have hψϖ : ∀ s : A.K, algebraMap A.K A.L s ∈ O → A.psiK ψ (t * x * ϖ * s) = 1 := fun s hs => by
    obtain ⟨w, hw, hws⟩ := htr s hs
    have := hϖD w hw
    simp only [Et.kerL, A.star_K, trace_algebraMap_mul, hws] at this
    rwa [← mul_assoc] at this

  have hnt : ∃ s : A.K, algebraMap A.K A.L s ∈ O ∧ A.psiK ψ (t * x * s) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∀ m ∈ O, A.kerL ψ (t * x) 1 m = 1 := fun m hm => by
      rw [kerL_one]
      exact hcon _ (by rw [htrL]; exact O.add_mem hm (hOs m hm))
    obtain ⟨z, hz, hz1⟩ := (hmemD 1).1 h1
    exact hϖu ⟨z, hz, hz1.symm⟩

  let M := scaledSub A O ϖ
  have hMo : IsOpen (M : Set A.L) := by
    rw [scaledSub_eq_image]; exact (mulHomeo A ϖ).isOpenMap _ hOo
  have hMc : IsCompact (M : Set A.L) := by
    rw [scaledSub_eq_image]; exact hOc.image (mulHomeo A ϖ).continuous
  have hM : ∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have hs : algebraMap A.K A.L ((ϖ : A.K) * A.NL z) ∈ O := by
      rw [map_mul, hN]; exact O.mul_mem hϖO (O.mul_mem hz (hOs z hz))
    have := hψϖ _ hs
    have hmul : A.NL (algebraMap A.K A.L ϖ * z) = A.NL (algebraMap A.K A.L ϖ) * A.NL z :=
      map_mul (Algebra.norm A.K) _ _
    rw [hmul, NL_algebraMap, show (ϖ : A.K) ^ 2 * A.NL z = (ϖ : A.K) * ((ϖ : A.K) * A.NL z) by ring]
    rwa [← mul_assoc]
  have hDeq : ((O.toAddSubgroup : AddSubgroup A.L) : Set A.L) =
      {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} := by
    ext y
    simp only [Subring.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_setOf_eq]
    have e1 : (∀ m ∈ M, A.kerL ψ (t * x) y m = 1) ↔ ∀ m ∈ O, A.kerL ψ (t * x) (algebraMap A.K A.L ϖ * y) m = 1 := by
      constructor
      · intro h m hm; rw [kerL_mul_left]; exact h _ ⟨m, hm, rfl⟩
      · rintro h _ ⟨m, hm, rfl⟩; rw [← kerL_mul_left]; exact h m hm
    rw [e1, hmemD]
    constructor
    · intro hy; exact ⟨y, hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      have hc : y = z := by
        have := congrArg (fun w => algebraMap A.K A.L ((ϖ⁻¹ : A.Kˣ) : A.K) * w) hzy
        simpa only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] using this
      rw [hc]; exact hz
  have hG := GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice F E A ψ x μ hψ hμ t M O.toAddSubgroup hMo hMc hOo hOc hM hDeq
  convert hG using 1
  simp only [gaussInt, Subring.coe_toAddSubgroup]
  rw [GlobalTheory.T.residue_gauss_integral_norm_form F E A ψ μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖu hdich hnorm hsc (t * x) hψϖ hnt]

end Level1

theorem gauss_at_uniformiser : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → ∃ ϖ : A.Kˣ, (¬ ∃ y, A.NL y = ϖ) ∧ IsStableGauss A ψ x μ ϖ (-(G₁ * ((A.absK ϖ : ℂ))⁻¹)) := by
  intro F E _ _ _ _ _ A ψ x μ ω hH G₁ hG₁
  obtain ⟨hK, hL, hψ, hSD, hω⟩ := hH
  have hμ : μ.IsAddHaarMeasure := hSD.1
  obtain ⟨ϖ, O, hOo, hOc, hOs, hϖn, hϖO, hϖu, hdich, htr, hnorm, hnb, hex⟩ := GlobalTheory.T.unramifiedQuadratic_exists_integers_uniformiser F E A hK hL
  obtain ⟨e, he⟩ := GlobalTheory.T.hermitianTraceDual_integers_eq_uniformizer_pow F E A ψ hψ hK hL ϖ O hOo hOc hOs hϖO hϖu hdich hnb hex x
  have hsc := GlobalTheory.T.haar_measure_L_unit_smul_absK_sq F E A μ hμ ϖ O

  have hD : ∀ t : A.Kˣ, {y : A.L | ∀ m ∈ O, A.kerL ψ ((t : A.K) * x) y m = 1} =
      {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((t⁻¹ * ϖ ^ e : A.Kˣ) : A.K) * z} := fun t => by
    rw [dual_mul A ψ O t x, ← scaled_mul A O t (ϖ ^ e), ← he]; rfl
  have hO1 : {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((1 : A.Kˣ) : A.K) * z} = (O : Set A.L) := by
    ext y; simp

  have hnp : ∀ j : ℤ, ∃ ℓ : A.L, A.NL ℓ = ((ϖ ^ (2 * j) : A.Kˣ) : A.K) := fun j =>
    ⟨algebraMap A.K A.L ((ϖ ^ j : A.Kˣ) : A.K), by
      rw [NL_algebraMap, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul, mul_comm]; norm_num⟩
  have hmove : ∀ (t : A.Kˣ) (j : ℤ) (G : ℂ), IsStableGauss A ψ x μ (t : A.K) G →
      IsStableGauss A ψ x μ ((t * ϖ ^ (2 * j) : A.Kˣ) : A.K) (G * ((A.absK (ϖ : A.K) : ℂ) ^ (2 * j))⁻¹) :=
    fun t j G h => by
      have := GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm F E A ψ x μ ω ⟨hK, hL, hψ, hSD, hω⟩ t (ϖ ^ (2 * j)) (hnp j) G h
      rwa [absK_zpow, Complex.ofReal_zpow] at this
  have hb : (A.absK (ϖ : A.K) : ℂ) ≠ 0 := by exact_mod_cast (absK_pos A ϖ).ne'
  obtain ⟨k, r, hr, hek⟩ : ∃ k r : ℤ, (r = 0 ∨ r = 1) ∧ e = 2 * k + r :=
    ⟨e / 2, e % 2, Int.emod_two_eq_zero_or_one e, by omega⟩
  refine ⟨ϖ, hϖn, ?_⟩
  rcases hr with rfl | rfl
  ·
    have h0 := level0 F E A ψ x μ hψ hμ O hOo hOc hOs htr ((ϖ ^ (2 * k) : A.Kˣ) : A.K) (by
      rw [hD, hek, show ((ϖ ^ (2 * k))⁻¹ * ϖ ^ (2 * k + 0) : A.Kˣ) = 1 by group]; exact hO1)
    have h1 := level1 F E A ψ x μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖu hdich htr hnorm hsc
      ((ϖ ^ (2 * k) * ϖ⁻¹ : A.Kˣ) : A.K) (by
      rw [hD, hek, show ((ϖ ^ (2 * k) * ϖ⁻¹)⁻¹ * ϖ ^ (2 * k + 0) : A.Kˣ) = ϖ by group])
    have g1 := hmove _ (-k) _ h0
    rw [show (ϖ ^ (2 * k) * ϖ ^ (2 * -k) : A.Kˣ) = 1 by group, Units.val_one] at g1
    have gϖ := hmove _ (1 - k) _ h1
    rw [show (ϖ ^ (2 * k) * ϖ⁻¹ * ϖ ^ (2 * (1 - k)) : A.Kˣ) = ϖ by group] at gϖ
    rw [stable_unique A ψ x μ 1 hG₁ g1]
    convert gϖ using 1
    rw [show (2 : ℤ) * (1 - k) = 2 + 2 * -k by ring, zpow_add₀ hb]
    have hP : (A.absK (ϖ : A.K) : ℂ) ^ (2 * -k) ≠ 0 := zpow_ne_zero _ hb
    field_simp
  ·
    have h1 := level1 F E A ψ x μ hψ hμ hK hL O ϖ hOo hOc hOs hϖO hϖu hdich htr hnorm hsc
      ((ϖ ^ (2 * k) : A.Kˣ) : A.K) (by
      rw [hD, hek, show ((ϖ ^ (2 * k))⁻¹ * ϖ ^ (2 * k + 1) : A.Kˣ) = ϖ by group])
    have h0 := level0 F E A ψ x μ hψ hμ O hOo hOc hOs htr ((ϖ ^ (2 * k) * ϖ : A.Kˣ) : A.K) (by
      rw [hD, hek, show ((ϖ ^ (2 * k) * ϖ)⁻¹ * ϖ ^ (2 * k + 1) : A.Kˣ) = 1 by group]; exact hO1)
    have g1 := hmove _ (-k) _ h1
    rw [show (ϖ ^ (2 * k) * ϖ ^ (2 * -k) : A.Kˣ) = 1 by group, Units.val_one] at g1
    have gϖ := hmove _ (-k) _ h0
    rw [show (ϖ ^ (2 * k) * ϖ * ϖ ^ (2 * -k) : A.Kˣ) = ϖ by group] at gϖ
    rw [stable_unique A ψ x μ 1 hG₁ g1]
    convert gϖ using 1
    have hP : (A.absK (ϖ : A.K) : ℂ) ^ (2 * -k) ≠ 0 := zpow_ne_zero _ hb
    field_simp

end GlobalTheory.JR.WeilQuad.NonNorm
