import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OddTheta

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = latticeArea L := by
  have hA := latticeArea_eq L
  have hpos := latticeArea_pos L
  have key : ∀ w₁ ∈ L.lattice, ∀ w₂ ∈ L.lattice, ∃ k : ℤ,
      ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hw₁
    obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.1 hw₂
    refine ⟨m * n' - n * m', ?_⟩
    simp [Complex.mul_im, Complex.mul_re]
    ring
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨hA ▸ hpos, L.ω₁, (h _).2 L.ω₁_mem_lattice, L.ω₂, (h _).2 L.ω₂_mem_lattice, hA⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := key w₁ ((h _).1 hw₁) w₂ ((h _).1 hw₂)
  rw [hk, abs_mul, ← hA] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left hpos.le hk1

theorem wpF_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) (z : ℂ) :
    wpF Λ z = L.weierstrassP z := by
  have hs : Summable (fun l : L.lattice => 1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) :=
    (L.hasSum_weierstrassP z).summable
  unfold wpF PeriodPair.weierstrassP
  rw [← hs.tsum_subtype_add_tsum_subtype_compl ({0} : Set L.lattice),
    tsum_singleton (0 : L.lattice) (fun l : L.lattice => 1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)]
  congr 1
  · simp
  · let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ (({0} : Set L.lattice)ᶜ : Set L.lattice) :=
      { toFun := fun w => ⟨⟨w.1, (h w.1).1 w.2.1⟩, fun hh =>
          w.2.2 (by simpa using congrArg Subtype.val (Set.mem_singleton_iff.1 hh))⟩
        invFun := fun l => ⟨l.1.1, (h _).2 l.1.2, fun hh =>
          l.2 (Set.mem_singleton_iff.2 (Subtype.ext (by simpa using hh)))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (e.tsum_eq (fun l => 1 / (z - ((l : L.lattice) : ℂ)) ^ 2 - 1 / ((l : L.lattice) : ℂ) ^ 2))

theorem law_iff (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (G : ℂ → ℂ) (ω z : ℂ) :
    U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z ↔
      G (z + ω) = sigmaSign L ω * Complex.exp (Real.pi * latticeForm L z ω +
        Real.pi * latticeForm L ω ω / 2) * G z := by
  have hs : (if ω / 2 ∈ Λ then (1 : ℂ) else -1) = sigmaSign L ω := by
    by_cases hw : ω / 2 ∈ Λ
    · rw [if_pos hw, sigmaSign_of_mem L ((h _).1 hw)]
    · rw [if_neg hw, sigmaSign_of_notMem L (fun hh => hw ((h _).2 hh))]
  have hU : U1 Λ ω G z = G (z + ω) *
      (Complex.exp (Real.pi * latticeForm L z ω + Real.pi * latticeForm L ω ω / 2))⁻¹ := by
    unfold U1
    rw [area_eq L Λ h, ← Complex.exp_neg]
    congr 2
    simp only [latticeForm]
    ring
  rw [hU, hs, mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _)]
  constructor <;> intro hh <;> rw [hh] <;> ring

theorem eq_deriv_mul (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hlaw : ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) (z : ℂ) :
    G z = deriv G 0 * canonicalSigma L z := by
  have hlaw' : ∀ w ∈ L.lattice, ∀ z, G (z + w) = sigmaSign L w *
      Complex.exp (Real.pi * latticeForm L z w + Real.pi * latticeForm L w w / 2) * G z :=
    fun w hw z => (law_iff L Λ h G w z).1 (hlaw w ((h w).2 hw) z)
  obtain ⟨c, hc⟩ := exists_eq_mul_canonicalSigma L hG hlaw'
  have hGf : G = fun z => c * canonicalSigma L z := funext hc
  have hd : deriv G 0 = c := by
    rw [hGf]
    exact ((hasDerivAt_canonicalSigma_zero L).const_mul c).deriv.trans (mul_one c)
  rw [hd]
  exact hc z

theorem canonicalSigma_spec (L : PeriodPair) (Λ : AddSubgroup ℂ)
    (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    Differentiable ℂ (canonicalSigma L) ∧ deriv (canonicalSigma L) 0 = 1 ∧
      (∀ z, canonicalSigma L (-z) = -canonicalSigma L z) ∧
      ∀ ω ∈ Λ, ∀ z, U1 Λ ω (canonicalSigma L) z =
        (if ω / 2 ∈ Λ then 1 else -1) * canonicalSigma L z := by
  refine ⟨differentiable_canonicalSigma L, (hasDerivAt_canonicalSigma_zero L).deriv,
    canonicalSigma_neg L, ?_⟩
  intro ω hω z
  exact (law_iff L Λ h _ ω z).2 (canonicalSigma_add L ((h ω).1 hω) z)

theorem sgStar_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    sgStar Λ = canonicalSigma L := by
  have hP : ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z :=
    ⟨_, canonicalSigma_spec L Λ h⟩
  unfold sgStar
  obtain ⟨hd, h1, -, hl⟩ := Classical.epsilon_spec hP
  funext z
  rw [eq_deriv_mul L Λ h _ hd hl z, h1, one_mul]

theorem exists_periodPair (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, hind, rfl⟩ := hΛ
  refine ⟨⟨w₁, w₂, hind⟩, fun z => ?_⟩
  show z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ Submodule.span ℤ {w₁, w₂}
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]

theorem sgStar_laws : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → (Differentiable ℂ (sgStar Λ) ∧ deriv (sgStar Λ) 0 = 1 ∧ (∀ z, sgStar Λ (-z) = -sgStar Λ z) ∧ ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z) ∧ (∀ z, sgStar Λ z = 0 ↔ z ∈ Λ) ∧ (∀ G : ℂ → ℂ, Differentiable ℂ G → (∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) → ∀ z, G z = deriv G 0 * sgStar Λ z) ∧ (∀ u v : ℂ, u ∉ Λ → v ∉ Λ → (wpF Λ u - wpF Λ v) * (sgStar Λ u ^ 2 * sgStar Λ v ^ 2) = -(sgStar Λ (u + v) * sgStar Λ (u - v))) ∧ ∀ c : ℂ, c ≠ 0 → ∀ z, sgStar (Λ.map (AddMonoidHom.mulLeft c)) (c * z) = c * sgStar Λ z := by
  intro Λ hΛ
  obtain ⟨L, h⟩ := exists_periodPair Λ hΛ
  have hσ := sgStar_eq L Λ h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ]
    exact canonicalSigma_spec L Λ h
  · intro z
    rw [hσ, canonicalSigma_eq_zero_iff L, h]
  · intro G hG hl z
    rw [hσ]
    exact eq_deriv_mul L Λ h G hG hl z
  · intro u v hu hv
    have hu' : u ∉ L.lattice := fun hh => hu ((h u).2 hh)
    have hv' : v ∉ L.lattice := fun hh => hv ((h v).2 hh)
    have hne : canonicalSigma L u ^ 2 * canonicalSigma L v ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hu'))
        (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hv'))
    rw [wpF_eq L Λ h, wpF_eq L Λ h, hσ, weierstrassP_sub_weierstrassP_canonicalSigma L hu' hv']
    exact div_mul_cancel₀ _ hne
  · intro c hc z
    have hhom := isHomothetic_scalePeriods L c hc
    have h' : ∀ x, x ∈ Λ.map (AddMonoidHom.mulLeft c) ↔ x ∈ (scalePeriods L c hc).lattice := by
      intro x
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hhom y).2 ((h y).1 hy)
      · intro hx
        refine ⟨c⁻¹ * x, (h _).2 ((hhom _).1 ?_), ?_⟩
        · rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
        · simp [hc]
    rw [sgStar_eq (scalePeriods L c hc) _ h', hσ, hhom.canonicalSigma_mul]

end GlobalTheory.OddTheta
