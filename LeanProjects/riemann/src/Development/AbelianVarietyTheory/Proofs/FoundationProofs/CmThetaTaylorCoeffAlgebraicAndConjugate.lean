import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaConj

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}

noncomputable def topHom (σ : ℂ →+* ℂ) : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ :=
  σ.toRatAlgHom.comp (⊤ : IntermediateField ℚ ℂ).val

theorem cj_of_mem (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {x : ℂ} (hx : x ∈ M) :
    cj M ρ x = ρ ⟨x, hx⟩ := by
  simp [cj, TaylorLogMetric.liftM, hx]

theorem cj_top (σ : ℂ →+* ℂ) (x : ℂ) : cj ⊤ (topHom σ) x = σ x := by
  rw [cj_of_mem _ _ (IntermediateField.mem_top)]
  rfl

theorem cj_top_div (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (x y : ℂ) :
    cj ⊤ ρ (x / y) = cj ⊤ ρ x / cj ⊤ ρ y := by
  rw [cj_of_mem _ _ (IntermediateField.mem_top), cj_of_mem _ _ (IntermediateField.mem_top),
    cj_of_mem _ _ (IntermediateField.mem_top), ← map_div₀]
  rfl

theorem lamConj_congr {M M' : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {ρ' : M' →ₐ[ℚ] ℂ}
    {Λ : AddSubgroup ℂ} (h2 : cj M ρ (g2 Λ) = cj M' ρ' (g2 Λ)) (h3 : cj M ρ (g3 Λ) = cj M' ρ' (g3 Λ)) :
    lamConj M ρ Λ = lamConj M' ρ' Λ := by
  unfold cj at h2 h3
  unfold lamConj
  rw [h2, h3]

theorem IsLat.exists_periodPair {Λ : AddSubgroup ℂ} (h : IsLat Λ) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, hi, rfl⟩ := h
  refine ⟨⟨w₁, w₂, hi⟩, fun z => ?_⟩
  rw [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
  simp [zsmul_eq_mul]

theorem lamConj_eq_self {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {Λ : AddSubgroup ℂ} (h : IsLat Λ)
    (h2 : cj M ρ (g2 Λ) = g2 Λ) (h3 : cj M ρ (g3 Λ) = g3 Λ) : lamConj M ρ Λ = Λ := by
  obtain ⟨L, hL⟩ := h.exists_periodPair
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨Λ, h2.symm, h3.symm⟩
  exact (GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL).2.2.2.2.2.1 _ (hs.1.trans h2) (hs.2.trans h3)

theorem taylorCoeff_evenTheta_eq_normalised_translate (Λ : AddSubgroup ℂ) (t : ℂ) (n : ℕ) :
    coef1 (GL3Theta.th0 Λ t) n = coef1 (U1 Λ t (sgStar Λ)) n / coef1 (U1 Λ t (sgStar Λ)) 0 := by
  unfold coef1 GL3Theta.th0
  rw [iteratedDeriv_div_const]
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  ring

theorem latticeTranslationOperator_add_exists_const (Λ : AddSubgroup ℂ) (t ω : ℂ) (G : ℂ → ℂ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, U1 Λ (t + ω) G z = c * U1 Λ t (U1 Λ ω G) z := by
  refine ⟨Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * (area Λ : ℂ))),
    Complex.exp_ne_zero _, fun z => ?_⟩
  simp only [U1]
  rw [← add_assoc, mul_assoc (G _), ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [map_add]
  ring

theorem evenTheta_add_lattice_mem {Λ : AddSubgroup ℂ} (h : IsLat Λ) (t : ℂ) {ω : ℂ} (hω : ω ∈ Λ) :
    GL3Theta.th0 Λ (t + ω) = GL3Theta.th0 Λ t := by
  obtain ⟨c, hc, hU⟩ := latticeTranslationOperator_add_exists_const Λ t ω (sgStar Λ)
  have h1 := (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.2 ω hω
  set e : ℂ := (if ω / 2 ∈ Λ then 1 else -1) with he
  have he0 : e ≠ 0 := by rw [he]; split_ifs <;> simp
  have h2 : ∀ z, U1 Λ (t + ω) (sgStar Λ) z = (c * e) * U1 Λ t (sgStar Λ) z := by
    intro z
    rw [hU]
    simp only [U1] at h1 ⊢
    rw [h1]; ring
  funext z
  simp only [GL3Theta.th0]
  rw [h2, h2, mul_div_mul_left _ _ (mul_ne_zero hc he0)]

theorem two_torsion_unique {Λ : AddSubgroup ℂ} (h : IsLat Λ) (w : ℂ) (k : ℤ)
    (hw : w * (1 - w) = 2 * k) {t t' : ℂ}
    (h2 : 2 * t ∈ Λ) (ha : w * t ∉ Λ) (hb : (1 - w) * t ∉ Λ)
    (h2' : 2 * t' ∈ Λ) (ha' : w * t' ∉ Λ) (hb' : (1 - w) * t' ∉ Λ)
    (hs : ∀ z ∈ Λ, w * z ∈ Λ) : t - t' ∈ Λ := by
  have hk : ∀ u, 2 * u ∈ Λ → w * (1 - w) * u ∈ Λ := by
    intro u hu
    have := Λ.zsmul_mem hu k
    rw [hw]; convert this using 1; rw [zsmul_eq_mul]; ring
  have hs' : ∀ z ∈ Λ, (1 - w) * z ∈ Λ := fun z hz => by
    have := Λ.sub_mem hz (hs z hz); convert this using 1; ring

  have four : ∀ a b u : ℂ, 2 * a ∈ Λ → 2 * b ∈ Λ → 2 * u ∈ Λ → a ∉ Λ → b ∉ Λ → a - b ∉ Λ →
      u ∈ Λ ∨ u - a ∈ Λ ∨ u - b ∈ Λ ∨ u - a - b ∈ Λ := by
    obtain ⟨w₁, w₂, hi, rfl⟩ := h
    intro a b u h1 h2 h3 ha hb hab
    have red : ∀ (x : ℂ) (m n : ℤ), x = m * (w₁ / 2) + n * (w₂ / 2) → m % 2 = 0 → n % 2 = 0 →
        x ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
      intro x m n hx hm hn
      obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
      obtain ⟨n', rfl⟩ : ∃ n', n = 2 * n' := ⟨n / 2, by omega⟩
      rw [AddSubgroup.mem_closure_pair]
      refine ⟨m', n', ?_⟩
      rw [hx]; simp only [zsmul_eq_mul]; push_cast; ring
    rw [AddSubgroup.mem_closure_pair] at h1 h2 h3
    obtain ⟨a1, a2, ea⟩ := h1
    obtain ⟨b1, b2, eb⟩ := h2
    obtain ⟨u1, u2, eu⟩ := h3
    simp only [zsmul_eq_mul] at ea eb eu
    have ra := red a a1 a2 (by linear_combination (-1 / 2 : ℂ) * ea)
    have rb := red b b1 b2 (by linear_combination (-1 / 2 : ℂ) * eb)
    have rab := red (a - b) (a1 - b1) (a2 - b2)
      (by push_cast; linear_combination (-1 / 2 : ℂ) * ea + (1 / 2 : ℂ) * eb)
    have r0 := red u u1 u2 (by linear_combination (-1 / 2 : ℂ) * eu)
    have r1 := red (u - a) (u1 - a1) (u2 - a2)
      (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * ea)
    have r2 := red (u - b) (u1 - b1) (u2 - b2)
      (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * eb)
    have r3 := red (u - a - b) (u1 - a1 - b1) (u2 - a2 - b2)
      (by push_cast; linear_combination (-1 / 2 : ℂ) * eu + (1 / 2 : ℂ) * ea + (1 / 2 : ℂ) * eb)
    have na : ¬ (a1 % 2 = 0 ∧ a2 % 2 = 0) := fun h => ha (ra h.1 h.2)
    have nb : ¬ (b1 % 2 = 0 ∧ b2 % 2 = 0) := fun h => hb (rb h.1 h.2)
    have nab : ¬ ((a1 - b1) % 2 = 0 ∧ (a2 - b2) % 2 = 0) := fun h => hab (rab h.1 h.2)
    have : (u1 % 2 = 0 ∧ u2 % 2 = 0) ∨ ((u1 - a1) % 2 = 0 ∧ (u2 - a2) % 2 = 0) ∨
        ((u1 - b1) % 2 = 0 ∧ (u2 - b2) % 2 = 0) ∨
        ((u1 - a1 - b1) % 2 = 0 ∧ (u2 - a2 - b2) % 2 = 0) := by omega
    rcases this with h | h | h | h
    · exact Or.inl (r0 h.1 h.2)
    · exact Or.inr (Or.inl (r1 h.1 h.2))
    · exact Or.inr (Or.inr (Or.inl (r2 h.1 h.2)))
    · exact Or.inr (Or.inr (Or.inr (r3 h.1 h.2)))
  have hkt := hk t h2
  have hab : w * t - (1 - w) * t ∉ Λ := fun h => ha (by
    have := Λ.add_mem (Λ.add_mem (hs _ h) hkt) hkt
    convert this using 1; ring)
  rcases four (w * t) ((1 - w) * t) t' (by have := hs _ h2; convert this using 1; ring)
    (by have := hs' _ h2; convert this using 1; ring) h2' ha hb hab with h | h | h | h
  · exact absurd (hs _ h) ha'
  · exact absurd (by have := Λ.add_mem (hs' _ h) hkt; convert this using 1; ring) hb'
  · exact absurd (by have := Λ.add_mem (hs _ h) hkt; convert this using 1; ring) ha'
  · have := Λ.neg_mem h; convert this using 1; ring

theorem area_conj (Λ : AddSubgroup ℂ) : area (Λ.map (starRingEnd ℂ).toAddMonoidHom) = area Λ := by
  unfold area
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨_, ⟨w₁, h₁, rfl⟩, _, ⟨w₂, h₂, rfl⟩, rfl⟩
    refine ⟨w₁, h₁, w₂, h₂, ?_⟩
    rw [← abs_neg]
    congr 1
    simp
    ring
  · rintro ⟨w₁, h₁, w₂, h₂, rfl⟩
    refine ⟨_, ⟨w₁, h₁, rfl⟩, _, ⟨w₂, h₂, rfl⟩, ?_⟩
    rw [← abs_neg]
    congr 1
    simp
    ring

theorem mem_conj {Λ : AddSubgroup ℂ} {z : ℂ} :
    z ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ↔ (starRingEnd ℂ) z ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨_, h, by simp⟩

theorem thetaTranslate_conjugateLattice (Λ : AddSubgroup ℂ) (t : ℂ) (G : ℂ → ℂ) :
    U1 (Λ.map (starRingEnd ℂ).toAddMonoidHom) ((starRingEnd ℂ) t) (starRingEnd ℂ ∘ G ∘ starRingEnd ℂ) =
      starRingEnd ℂ ∘ U1 Λ t G ∘ starRingEnd ℂ := by
  funext z
  simp only [U1, area_conj, Function.comp, map_mul, map_add, ← Complex.exp_conj, map_sub, map_div₀,
    map_neg, Complex.conj_ofReal, Complex.conj_conj, map_ofNat]

theorem IsLat.conj {Λ : AddSubgroup ℂ} (h : IsLat Λ) : IsLat (Λ.map (starRingEnd ℂ).toAddMonoidHom) := by
  obtain ⟨w₁, w₂, hi, rfl⟩ := h
  refine ⟨starRingEnd ℂ w₁, starRingEnd ℂ w₂, ?_, ?_⟩
  · have := hi.map' Complex.conjLIE.toLinearEquiv.toLinearMap (LinearEquiv.ker _)
    have e : ![starRingEnd ℂ w₁, starRingEnd ℂ w₂] =
        Complex.conjLIE.toLinearEquiv.toLinearMap ∘ ![w₁, w₂] := by
      funext i
      fin_cases i <;> simp
    rw [e]
    exact this
  · rw [AddMonoidHom.map_closure, Set.image_pair]
    rfl

theorem conj_conj_lat (Λ : AddSubgroup ℂ) :
    (Λ.map (starRingEnd ℂ).toAddMonoidHom).map (starRingEnd ℂ).toAddMonoidHom = Λ := by
  ext z
  rw [mem_conj, mem_conj, Complex.conj_conj]

theorem sgStar_conj {Λ : AddSubgroup ℂ} (h : IsLat Λ) :
    sgStar (Λ.map (starRingEnd ℂ).toAddMonoidHom) = starRingEnd ℂ ∘ sgStar Λ ∘ starRingEnd ℂ := by
  obtain ⟨⟨hd, h1, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ h
  have huniq := (GlobalTheory.OddTheta.sgStar_laws _ h.conj).2.2.1 (starRingEnd ℂ ∘ sgStar Λ ∘ starRingEnd ℂ)
    (fun z => differentiableAt_conj_conj_iff.mpr (hd _)) (by
      rintro _ ⟨ω, hω, rfl⟩ z
      have e : (starRingEnd ℂ).toAddMonoidHom ω = starRingEnd ℂ ω := rfl
      rw [e, thetaTranslate_conjugateLattice, mem_conj]
      simp only [Function.comp, hU ω hω, map_mul, map_div₀, Complex.conj_conj, map_ofNat]
      split_ifs <;> simp)
  funext z
  rw [huniq z, deriv_conj_conj]
  simp [h1]

theorem evenTheta_conjugateLattice {Λ : AddSubgroup ℂ} (h : IsLat Λ) (t : ℂ) :
    GL3Theta.th0 (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ t) =
      starRingEnd ℂ ∘ GL3Theta.th0 Λ t ∘ starRingEnd ℂ := by
  funext z
  simp only [GL3Theta.th0]
  rw [sgStar_conj h, thetaTranslate_conjugateLattice]
  simp [GL3Theta.th0]

theorem iteratedDeriv_conj_conj (n : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv n (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) =
      starRingEnd ℂ ∘ iteratedDeriv n f ∘ starRingEnd ℂ := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]

theorem taylorCoeff_complexConj_conjugate (f : ℂ → ℂ) (n : ℕ) :
    coef1 (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) n = starRingEnd ℂ (coef1 f n) := by
  simp [coef1, iteratedDeriv_conj_conj]

theorem twoTorsionCMPoint_complexConj {D : D7} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.IsTwoTorsionPointUnkilled D Λ t) :
    GL3Theta.IsTwoTorsionPointUnkilled D (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ t) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> rw [mem_conj]
  · simpa [map_ofNat] using h1
  · simpa [map_ofNat, sub_eq_add_neg] using h3
  · simpa [map_ofNat, sub_eq_add_neg] using h2

theorem exists_ext (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ σ : ℂ →+* ℂ, ∀ x, x ∈ M → x ∈ TaylorLogMetric.Qbar → cj M ρ x = σ x := by
  have hc : Set.Countable ((M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ) : Set ℂ) :=
    (Algebraic.countable ℚ ℂ).mono fun x hx => mem_algebraicClosure_iff.1 hx.2
  haveI : Countable (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ) := hc.to_subtype
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq
    (K := (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ)) (M ⊓ TaylorLogMetric.Qbar : IntermediateField ℚ ℂ).val.toRingHom
    (ρ.comp (IntermediateField.inclusion inf_le_left)).toRingHom
  refine ⟨σ.toRingHom, fun x h1 h2 => ?_⟩
  rw [cj_of_mem _ _ h1]
  exact (hσ ⟨x, h1, h2⟩).symm

theorem isLat_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) : IsLat (lamOf D cc δ) :=
  (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).1

theorem coef_translate_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) {x : ℂ}
    (hx : InRationalLattice (lamOf D cc δ) x) (n : ℕ) :
    coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n ∈ TaylorLogMetric.Qbar := by
  obtain ⟨⟨-, hg2, hg3⟩, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.InducedType.induced_type D).1).2 cc δ h
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := TaylorLogMetric.Qbar)
    (coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n) (fun σ => by
      have hσ : ∀ z ∈ TaylorLogMetric.Qbar, cj ⊤ (topHom (σ : ℂ →+* ℂ)) z = z := fun z hz => by
        rw [cj_top]; exact σ.commutes ⟨z, hz⟩
      have hK : FixK D ⊤ (topHom (σ : ℂ →+* ℂ)) := fun a => ⟨IntermediateField.mem_top, hσ _ (by
        rw [mem_algebraicClosure_iff]
        exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (a : D.host.E)).algHom D.host.φ₀.toRatAlgHom)⟩
      have hL := lamConj_eq_self (isLat_lamOf h) (hσ _ hg2) (hσ _ hg3)
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      have hg := GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ h ⊤ _ hK IntermediateField.mem_top IntermediateField.mem_top x x (2 * m)
        (by omega) (by convert hmx using 1; push_cast; ring) (by
          unfold Adp1 StarPt
          rw [hL]
          by_cases hin : x / ((2 * (2 * m) : ℕ) : ℂ) ∈ lamOf D cc δ
          · exact Or.inl ⟨hin, hin⟩
          · obtain ⟨h1, h2⟩ := htor _ ⟨m * (2 * (2 * m)), by positivity, by
              convert hmx using 1; push_cast; field_simp⟩ hin
            exact Or.inr ⟨hin, hin, IntermediateField.mem_top, IntermediateField.mem_top, (hσ _ h1).symm,
              (hσ _ h2).symm⟩) (fun _ => IntermediateField.mem_top) n
      rw [hL, cj_top] at hg
      exact hg)
  rw [← hy]
  exact y.2

theorem taylorCoeff_evenTheta_cmCurve_algebraic {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) {t : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) (n : ℕ) : coef1 (GL3Theta.th0 (lamOf D cc δ) t) n ∈ TaylorLogMetric.Qbar := by
  have hx : InRationalLattice (lamOf D cc δ) t := ⟨2, by norm_num, by exact_mod_cast ht.1⟩
  rw [taylorCoeff_evenTheta_eq_normalised_translate]
  exact div_mem (coef_translate_mem h hx n) (coef_translate_mem h hx 0)

theorem weylMatrix_mul_apply (D : D7) : ∃ k : ℤ, w0 D * (1 - w0 D) = 2 * k := by
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by omega⟩
  have hm' : (D.host.d : ℂ) + 1 = 8 * (m : ℂ) := by exact_mod_cast hm
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = D.host.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  refine ⟨m, ?_⟩
  unfold w0
  push_cast
  linear_combination (1 / 4 : ℂ) * hm' + (1 / 4 : ℂ) * hs -
    (1 / 4 : ℂ) * ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq

theorem twoTorsionCMPoint_iff (D : D7) (Λ : AddSubgroup ℂ) (t : ℂ) :
    GL3Theta.IsTwoTorsionPointUnkilled D Λ t ↔ 2 * t ∈ Λ ∧ w0 D * t ∉ Λ ∧ (1 - w0 D) * t ∉ Λ := by
  have : 1 - w0 D = (1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 := by unfold w0; ring
  rw [this]
  rfl

theorem embeddingConj_evenTheta_coeff_of_fixes_field {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') (n : ℕ) :
    cj ⊤ ρ (coef1 (GL3Theta.th0 (lamOf D cc δ) t) n) = coef1 (GL3Theta.th0 (lamConj ⊤ ρ (lamOf D cc δ)) t') n := by
  obtain ⟨hex, -, -, hadd, hmul, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨cc', δ', h', -, hL⟩ :=
    GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
  rw [twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨u, hu⟩ := hex (t / 8) ⟨16, by norm_num, by convert ht.1 using 1; push_cast; ring⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have hg := GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top t (8 * u) 4
    (by norm_num) (by convert ht.1 using 1; push_cast; ring)
    (by unfold Adp1; convert hu using 1 <;> push_cast <;> ring) (fun _ => IntermediateField.mem_top)
  have h2 := hadd _ _ _ _ hu hu
  have h4 := hadd _ _ _ _ h2 h2
  have h8 : StarPt ⊤ ρ (lamOf D cc δ) t (8 * u) := by
    convert hadd _ _ _ _ h4 h4 using 1 <;> ring
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  have ha' : D.host.φ₀ ((((1 - a : 𝓞 D.host.K) : D.host.K) : D.host.E)) = 1 - w0 D := by
    rw [← ha]
    change D.host.φ₀ (algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K (1 - a))) = _
    rw [map_sub, map_sub, map_sub, map_one, map_one, map_one]
    rfl
  have e2 := (hord 2 _ _ h8).1 (by exact_mod_cast ht.1)
  have ea := (hord 1 _ _ (hmul a _ _ h8)).2
  have eb := (hord 1 _ _ (hmul (1 - a) _ _ h8)).2
  rw [ha] at ea
  rw [ha'] at eb
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at e2 ea eb
  obtain ⟨k, hk⟩ := weylMatrix_mul_apply D
  have hlat : IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := hL ▸ isLat_lamOf h'
  have hdiff : t' - 8 * u ∈ lamConj ⊤ ρ (lamOf D cc δ) :=
    two_torsion_unique hlat (w0 D) k hk ht'.1 ht'.2.1 ht'.2.2 e2 (fun hh => ht.2.1 (ea hh))
      (fun hh => ht.2.2 (eb hh)) (by
        rw [hL, ← ha]
        exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc' δ' h').2.2.2.2 a)
  have hth := evenTheta_add_lattice_mem hlat (8 * u) hdiff
  rw [add_sub_cancel] at hth
  rw [hth, taylorCoeff_evenTheta_eq_normalised_translate, taylorCoeff_evenTheta_eq_normalised_translate, cj_top_div, hg, hg]

theorem cj_rhoBar (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (x : ℂ) :
    cj M (rhoBar M ρ) x = starRingEnd ℂ (cj M ρ x) := rfl

theorem embeddingConj_evenTheta_coeff_top {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') (n : ℕ) :
    cj ⊤ ρ (coef1 (GL3Theta.th0 (lamOf D cc δ) t) n) = coef1 (GL3Theta.th0 (lamConj ⊤ ρ (lamOf D cc δ)) t') n := by
  obtain ⟨hK, hT, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ h ⊤ ρ
    ⟨fun _ _ => IntermediateField.mem_top, IntermediateField.mem_top, IntermediateField.mem_top⟩
  rcases hK with hK | hK
  · exact embeddingConj_evenTheta_coeff_of_fixes_field h ρ hK ht ht' n
  · have hL : lamConj ⊤ (rhoBar ⊤ ρ) (lamOf D cc δ) =
        (lamConj ⊤ ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    obtain ⟨cc', δ', h', -, hL'⟩ :=
      GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ _ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
    have hlat : IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := by
      rw [← conj_conj_lat (lamConj ⊤ ρ (lamOf D cc δ)), ← hL, hL']
      exact (isLat_lamOf h').conj
    have key := embeddingConj_evenTheta_coeff_of_fixes_field h _ hK (t' := starRingEnd ℂ t') ht (hL ▸ twoTorsionCMPoint_complexConj ht') n
    rw [hL, evenTheta_conjugateLattice hlat, taylorCoeff_complexConj_conjugate, cj_rhoBar] at key
    exact (starRingEnd ℂ).injective key

theorem cmTheta_taylorCoeff_algebraic_and_conjugate : ∀ D : D7, use1 D := by
  intro D cc δ h
  refine ⟨fun x hx n => coef_translate_mem h hx n, fun t ht n => taylorCoeff_evenTheta_cmCurve_algebraic h ht n, ?_⟩
  intro M ρ h2 h3 t t' ht ht' hM n
  obtain ⟨⟨-, hg2, hg3⟩, -⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.InducedType.induced_type D).1).2 cc δ h
  obtain ⟨σ, hσ⟩ := exists_ext M ρ
  have hL : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (topHom σ) (lamOf D cc δ) :=
    lamConj_congr (by rw [cj_top]; exact hσ _ h2 hg2) (by rw [cj_top]; exact hσ _ h3 hg3)
  rw [hL] at ht' ⊢
  rw [hσ _ (hM n) (taylorCoeff_evenTheta_cmCurve_algebraic h ht n), ← cj_top]
  exact embeddingConj_evenTheta_coeff_top h _ ht ht' n

end GlobalTheory.ThetaConj
