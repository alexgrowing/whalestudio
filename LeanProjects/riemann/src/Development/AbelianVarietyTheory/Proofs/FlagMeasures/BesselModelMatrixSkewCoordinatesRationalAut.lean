import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealFrameAutomorphismUnitriangularRowsCoords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovSkew

theorem herm_esI {k r : ℕ} (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  have ha := a.2
  have ht : WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
    have h1 : (esI k r a).val < r ∨ r + k < (esI k r a).val := Or.inr (by simp only [esI]; omega)
    apply Fin.ext; unfold WeylGroupFacts.tau; dsimp only; rw [if_pos h1]; simp only [esI, eI]; omega
  have hs : WeylGroupFacts.sgn k r (esI k r a) = 1 := if_neg (by simp only [esI]; omega)
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_one_dotProduct]
  simp only [mulVec, dotProduct, WeylGroupFacts.hpk_row, ht, hs]
  simp

theorem sum_eI_apply {k r : ℕ} (c : Fin r → ℂ) (a : Fin r) :
    (∑ b, c b • bvec (eI k r b)) (eI k r a) = c a := by
  simp [Finset.sum_apply, Rad.bvec_apply, Rad.eI_inj]

theorem coords_skew : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → q.1 = 0 → q.2.1 = 0 → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') ∧ (∀ p : {p : UT r // N.j ≤ p.1.1.val}, q.2.2.1 p = ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ) * σ (H.B (s (N.ist p.1.1.2)) (N.ist p.1.1.1))) ∧ ∀ a : {a : Fin r // N.j ≤ a.val}, q.2.2.2 a = ρ ^ (2 * (r - a.1.val)) * (σ (H.B (s (N.ist a.1)) (N.ist a.1))).im := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq hq1 hq2
  obtain ⟨hr, -, -, -, -, he, hi, -⟩ := hF
  have he1 : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) := fun a => (he a).1
  have ht : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (pow_pos hρ n).ne'
  set S : Matrix (Fin r) (Fin r) ℂ := skewM (Swap.extS r N.j q.2.2).1 (Swap.extS r N.j q.2.2).2 with hSdef
  have hM : crd k r N.j β q = pEl k r 0 S := by
    rw [RefCovTop.crd_of_zero β q hq1, Swap.pTop_eq, pOf, hq2, map_zero]
  have hS0 : ∀ a b : Fin r, ¬ N.j ≤ a.val → S a b = 0 := fun a b ha => Swap.skew_ext_zero q.2.2 a b ha
  have hcol : ∀ b : Fin r, pEl k r 0 S *ᵥ bvec (esI k r b) = bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a) := by
    intro b
    rw [((Rad.radical k r).1 0 S).2.2.1 b]
    simp [herm]
  have hsb : ∀ b : Fin r, N.j ≤ b.val → Φ (s (N.ist b)) =
      (((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) • (bvec (esI k r b) + ∑ a, S a b • bvec (eI k r a)) := by
    intro b hb; rw [← hq, hM, hi b hb, mulVec_smul, hcol]
  have hB : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → σ (H.B (s (N.ist b)) (N.ist a)) =
      (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) := by
    intro a b ha hb
    rw [← hr.2.2.1, hsb b hb, hi a ha, RealMat.herm_smul_right, herm_esI, Pi.smul_apply, Pi.add_apply, sum_eI_apply,
      Rad.bvec_apply, if_neg (Rad.eI_ne_esI a b), zero_add, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  refine ⟨fun b hb => ?_, fun p => ?_, fun a => ?_⟩
  · have hΦy : Φ (s (N.ist b) - N.ist b) = ∑ a, ((((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) * S a b) • bvec (eI k r a) := by
      rw [RealMat.phi_sub hr, hsb b hb, hi b hb, smul_add, add_sub_cancel_left, Finset.smul_sum]
      simp_rw [smul_smul]
    have hproj : NFGeom.proj N (s (N.ist b) - N.ist b) = s (N.ist b) - N.ist b := by
      apply RealMat.phi_inj hr
      rw [NFGeom.proj_apply, RealMat.phi_sum hr, hΦy, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with ha
      · rw [hr.2.1, he1, ← hr.2.2.1, hΦy, hi a ha, RealMat.herm_smul_right, herm_esI, sum_eI_apply, smul_smul]
        congr 1
        rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv, mul_comm, ← mul_assoc,
          mul_inv_cancel₀ (ht _), one_mul]
      · rw [hS0 a b ha, mul_zero, zero_smul]
    rw [← hproj]; exact NFGeom.proj_mem N _
  · obtain ⟨⟨⟨a, b⟩, hab⟩, ha⟩ := p
    have hab' : a < b := hab
    have ha' : N.j ≤ a.val := ha
    have hb : N.j ≤ b.val := le_trans ha' (le_of_lt hab')
    simp only
    rw [hB a b ha' hb]
    have hSab : S a b = q.2.2.1 ⟨⟨(a, b), hab⟩, ha⟩ := by
      simp [hSdef, skewM, hab', Swap.extS, Swap.extZ, ha']
    rw [hSab, pow_add, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv]
    have h1 := ht (r - a.val)
    have h2 := ht (r - b.val)
    field_simp
  · obtain ⟨a, ha⟩ := a
    simp only
    rw [hB a a ha ha]
    have hSaa : S a a = ((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I := by
      simp [hSdef, skewM, Swap.extS, Swap.extZ, ha]
    rw [hSaa]
    have e : ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * ((((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * (((q.2.2.2 ⟨a, ha⟩ : ℝ) : ℂ) * Complex.I))) =
        (((ρ ^ (r - a.val))⁻¹ * ((ρ ^ (r - a.val))⁻¹ * q.2.2.2 ⟨a, ha⟩) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e, Complex.mul_I_im, Complex.ofReal_re, two_mul, pow_add]
    have h1 : ρ ^ (r - a.val) ≠ 0 := (pow_pos hρ _).ne'
    field_simp

end GlobalTheory.DegVol.RefCovSkew
