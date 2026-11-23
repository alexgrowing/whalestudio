import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSubInOfCob2InStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithmStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.KLift

section Alg
variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem map_formalGroupLawCoboundaryOne_eq (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) {τ : Type} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun i => by cases i <;> simp [hu, hv]))]
  congr 1
  funext i; cases i <;> rfl

theorem map_swap (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map φ (swap c) = swap (map φ c) := by
  unfold swap
  rw [mvPowerSeriesMap_evalTwoGroups φ c _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem powerSeriesEvalTwoGroups_sub {τ : Type} (a b : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : at2 (a - b) u v = at2 a u v - at2 b u v :=
  subst_sub (hasSubst_of_constantCoeff_zero (fun i => by cases i <;> simp [hu, hv])) a b

theorem swap_sub (a b : MvPowerSeries (Fin d ⊕ Fin d) R) : swap (a - b) = swap a - swap b :=
  powerSeriesEvalTwoGroups_sub a b _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)

theorem const_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    {τ : Type} (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) : constantCoeff (op μ u v i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (fun j => by cases j <;> simp [hu, hv]))
    (fun j => by cases j <;> simp [hu, hv]) (hμ i)

theorem formalGroupLawCoboundaryTwo_sub (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (a b : MvPowerSeries (Fin d ⊕ Fin d) R) : cob2 μ (a - b) = cob2 μ a - cob2 μ b := by
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  unfold cob2
  rw [powerSeriesEvalTwoGroups_sub a b _ _ h2 h3, powerSeriesEvalTwoGroups_sub a b _ _ (const_op μ hμ _ _ h1 h2) h3,
    powerSeriesEvalTwoGroups_sub a b _ _ h1 (const_op μ hμ _ _ h2 h3), powerSeriesEvalTwoGroups_sub a b _ _ h1 h2]
  ring

theorem map_formalGroupLawCoboundaryTwo (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    map φ (cob2 μ c) = cob2 (fun i => map φ (μ i)) (map φ c) := by
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have m1 : (fun i => map φ ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x1 :=
    funext fun _ => map_X _ _
  have m2 : (fun i => map φ ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x2 :=
    funext fun _ => map_X _ _
  have m3 : (fun i => map φ ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x3 :=
    funext fun _ => map_X _ _
  have mop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (fun i => map φ (op μ u v i)) =
        op (fun i => map φ (μ i)) (fun i => map φ (u i)) (fun i => map φ (v i)) :=
    fun u v hu hv => funext fun i => mvPowerSeriesMap_evalTwoGroups φ (μ i) u v hu hv
  unfold cob2
  rw [map_sub, map_add, map_sub, mvPowerSeriesMap_evalTwoGroups φ c _ _ h2 h3, mvPowerSeriesMap_evalTwoGroups φ c _ _ (const_op μ hμ _ _ h1 h2) h3,
    mvPowerSeriesMap_evalTwoGroups φ c _ _ h1 (const_op μ hμ _ _ h2 h3), mvPowerSeriesMap_evalTwoGroups φ c _ _ h1 h2, mop _ _ h1 h2, mop _ _ h2 h3,
    m1, m2, m3]

theorem constantCoeff_coboundaryOne_zero_of_constCoeff (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) (hf : constantCoeff f = 0) : constantCoeff (cob1 μ f) = 0 := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hμ) hμ hf,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) hf,
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
      (fun _ => constantCoeff_X _) hf, sub_zero, sub_zero]

end Alg

end GlobalTheory.QLog.KLift

namespace GlobalTheory.QLog.KLift

section Ideal
variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_sub {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) : In N (f - g) := by
  intro α
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a - b, N.sub_mem ha hb, by rw [map_sub, ea, eb, map_sub]⟩

theorem in_add {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) : In N (f + g) := by
  intro α
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add, ea, eb, map_add]⟩

theorem in_mono {N N' : Ideal B} (h : N ≤ N') {f : MvPowerSeries σ Q} (hf : In N f) : In N' f := by
  intro α
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨a, h ha, ea⟩

theorem in_map (K : MvPowerSeries σ B) : In (⊤ : Ideal B) (map (algebraMap B Q) K) :=
  fun α => ⟨coeff α K, trivial, coeff_map _ _ _⟩

theorem dIn_sub {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : DIn N f) (hg : DIn N g) :
    DIn N (f - g) := by
  intro α i
  obtain ⟨a, ha, ea⟩ := hf α i
  obtain ⟨b, hb, eb⟩ := hg α i
  exact ⟨a - b, N.sub_mem ha hb, by rw [map_sub, mul_sub, ea, eb, map_sub]⟩

theorem dIn_map (K : MvPowerSeries σ B) : DIn (⊤ : Ideal B) (map (algebraMap B Q) K) :=
  fun α i => ⟨(α i : B) * coeff α K, trivial, by rw [coeff_map, map_mul, map_natCast]⟩

end Ideal

end GlobalTheory.QLog.KLift

namespace GlobalTheory.QLog.KLift

section Frame
variable {p : ℕ} [hp : Fact p.Prime] {B O Q C : Type} [CommRing B] [CommRing Q] [CommRing O]
  [Algebra B Q] [CommRing C] [Algebra O C] {θ : B →+* O} (F : IsFrame p Q θ)
  (G : IsFrame p C (RingHom.id O)) {Θ : Q →+* C}
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))

include G hΘ in
theorem ker_of_alg (b : B) (h : Θ (algebraMap B Q b) = 0) : θ b = 0 := by
  rw [hΘ] at h
  exact (injective_iff_map_eq_zero (algebraMap O C)).1 G.inj _ h

include F G hΘ in
theorem kerQ (q : Q) (h : Θ q = 0) :
    ∃ k : ℕ, ∃ b ∈ RingHom.ker θ, (p : Q) ^ k * q = algebraMap B Q b := by
  obtain ⟨k, b, e⟩ := F.denom q
  refine ⟨k, b, RingHom.mem_ker.2 (ker_of_alg G hΘ b ?_), e⟩
  rw [← e, map_mul, h, mul_zero]

include G hΘ in
theorem zero_of (q : Q) (k : ℕ) (b : B) (e : (p : Q) ^ k * q = algebraMap B Q b) (hb : θ b = 0) :
    Θ q = 0 := by
  have := congrArg Θ e
  rw [map_mul, map_pow, map_natCast, hΘ, hb, map_zero] at this
  exact (G.unit_p.pow k).mul_right_eq_zero.1 this

include G hΘ in
theorem in_ker {σ : Type} (h : MvPowerSeries σ Q) (hi : In (⊤ : Ideal B) h) (h0 : map Θ h = 0) :
    In (RingHom.ker θ) h := by
  intro α
  obtain ⟨b, -, e⟩ := hi α
  refine ⟨b, RingHom.mem_ker.2 (ker_of_alg G hΘ b ?_), e⟩
  rw [← e, ← coeff_map, h0, map_zero]

include F G hΘ in
theorem gen {σ : Type} (α : σ →₀ ℕ) (hα : α ≠ 0) (c : C)
    (hc : ∀ j, ∃ o : O, (α j : C) * c = algebraMap O C o) :
    ∃ q : Q, Θ q = c ∧ ∀ j, ∃ b : B, (α j : Q) * q = algebraMap B Q b := by
  have hpp := hp.out
  obtain ⟨j₀, hj₀, hmin⟩ := α.support.exists_min_image (fun j => (α j).factorization p)
    (Finsupp.support_nonempty_iff.2 hα)
  have hne : α j₀ ≠ 0 := Finsupp.mem_support_iff.1 hj₀
  set k := (α j₀).factorization p with hk
  have hdvd : ∀ j, p ^ k ∣ α j := by
    intro j
    by_cases hj : α j = 0
    · rw [hj]; exact dvd_zero _
    · exact (hpp.pow_dvd_iff_le_factorization hj).2 (hmin j (Finsupp.mem_support_iff.2 hj))
  set m := α j₀ / p ^ k with hmdef
  have hm : α j₀ = p ^ k * m := (Nat.mul_div_cancel' (hdvd j₀)).symm
  have hcop : Nat.Coprime m p := (Nat.coprime_ordCompl hpp hne).symm
  obtain ⟨u, hu⟩ := G.unit_coprime m hcop
  obtain ⟨o, ho⟩ := hc j₀
  obtain ⟨b, hb⟩ := F.surj (o * ↑u⁻¹)
  obtain ⟨v, hv⟩ := F.unit_p.pow k
  refine ⟨↑v⁻¹ * algebraMap B Q b, ?_, fun j => ?_⟩
  · have e1 : (p : C) ^ k * c = algebraMap O C (o * ↑u⁻¹) := by
      have hmC : (m : C) = algebraMap O C ↑u := by rw [hu, map_natCast]
      have hui : algebraMap O C ↑u * algebraMap O C ↑u⁻¹ = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [map_mul, ← ho, hm, Nat.cast_mul, Nat.cast_pow, hmC]
      linear_combination (-((p : C) ^ k * c)) * hui
    have e2 : (p : C) ^ k * Θ (↑v⁻¹ * algebraMap B Q b) = algebraMap O C (o * ↑u⁻¹) := by
      rw [← hb, ← hΘ, ← map_natCast Θ p, ← map_pow, ← map_mul, ← hv, Units.mul_inv_cancel_left]
    exact (G.unit_p.pow k).mul_left_cancel (e2.trans e1.symm)
  · obtain ⟨n, hn⟩ := hdvd j
    refine ⟨(n : B) * b, ?_⟩
    have hvv : (↑v : Q) * ↑v⁻¹ = 1 := Units.mul_inv v
    rw [hn, Nat.cast_mul, Nat.cast_pow, map_mul, map_natCast, ← hv]
    linear_combination ((n : Q) * algebraMap B Q b) * hvv

include F G hΘ in
theorem lift_coeffs {d : ℕ} (g : MvPowerSeries (Fin d) C) (w : Fin d → B)
    (hgD : DIn (⊤ : Ideal O) g) (hg0 : constantCoeff g = 0)
    (hw : ∀ i, lin g i = algebraMap O C (θ (w i))) :
    ∃ f₀ : MvPowerSeries (Fin d) Q, constantCoeff f₀ = 0 ∧ DIn (⊤ : Ideal B) f₀ ∧ map Θ f₀ = g ∧
      ∀ i, lin f₀ i = algebraMap B Q (w i) := by
  have ex : ∀ α : Fin d →₀ ℕ, ∃ q : Q, Θ q = coeff α g ∧
      (∀ j, ∃ b : B, (α j : Q) * q = algebraMap B Q b) ∧ (α = 0 → q = 0) ∧
      ∀ i, α = Finsupp.single i 1 → q = algebraMap B Q (w i) := by
    intro α
    by_cases h0 : α = 0
    · subst h0
      refine ⟨0, ?_, fun j => ⟨0, by simp⟩, fun _ => rfl,
        fun i h => absurd h.symm (Finsupp.single_ne_zero.2 one_ne_zero)⟩
      rw [map_zero, coeff_zero_eq_constantCoeff_apply, hg0]
    by_cases h1 : ∃ i, α = Finsupp.single i 1
    · obtain ⟨i, rfl⟩ := h1
      refine ⟨algebraMap B Q (w i), ?_,
        fun j => ⟨(((Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : B) * w i, by rw [map_mul, map_natCast]⟩,
        fun h => absurd h h0, fun i' h => ?_⟩
      · rw [hΘ, ← hw]; rfl
      · rw [(Finsupp.single_left_inj one_ne_zero).1 h]
    · obtain ⟨q, hq, hqD⟩ := gen F G hΘ α h0 (coeff α g)
        (fun j => by obtain ⟨o, -, e⟩ := hgD α j; exact ⟨o, e⟩)
      exact ⟨q, hq, hqD, fun h => absurd h h0, fun i h => absurd ⟨i, h⟩ h1⟩
  choose q hqΘ hqD hq0 hq1 using ex
  let f₀ : MvPowerSeries (Fin d) Q := q
  have hc : ∀ α, coeff α f₀ = q α := fun _ => rfl
  refine ⟨f₀, ?_, fun α j => ?_, ?_, fun i => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, hc]; exact hq0 0 rfl
  · obtain ⟨b, e⟩ := hqD α j; exact ⟨b, trivial, by rw [hc]; exact e⟩
  · ext α; rw [coeff_map, hc]; exact hqΘ α
  · show coeff _ f₀ = _
    rw [hc]; exact hq1 _ i rfl

end Frame

end GlobalTheory.QLog.KLift

namespace GlobalTheory.QLog.KLift

theorem const_map {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (φ : R →+* S)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (map φ (μ i)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ i, map_zero]

theorem formalGroupLawCoboundaryTwo_zero {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) : cob2 μ 0 = 0 := by
  simpa using formalGroupLawCoboundaryTwo_sub μ hμ 0 0

theorem swap_zero {R : Type} [CommRing R] {d : ℕ} : swap (0 : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 := by
  simpa using swap_sub (0 : MvPowerSeries (Fin d ⊕ Fin d) R) 0

theorem lift_quasiLog : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (g : MvPowerSeries (Fin d) C) (w : Fin d → B), QL (fun i => map θ (μ i)) ⊤ g → (∀ i, lin g i = algebraMap O C (θ (w i))) → ∃ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f ∧ map Θ f = g ∧ ∀ i, lin f i = algebraMap B Q (w i) := by
  intro p _ B O Q _ _ _ _ θ F d μ hμ C _ _ G Θ hΘ g w hg hw
  have hμ' : IsLift (RingHom.id O) (fun i => map θ (μ i)) :=
    ⟨hμ.law.const, hμ.law.unit, hμ.law.comm, by simpa only [map_id, RingHom.id_apply] using hμ.law⟩
  have hgD : DIn (⊤ : Ideal O) g := GlobalTheory.T.divided_in_of_quasi_logarithm p O O C (RingHom.id O) G d _ hμ' ⊤ g hg
  obtain ⟨f₀, hf0c, hf0D, hf0Θ, hf0l⟩ := lift_coeffs F G hΘ g w hgD hg.1 hw
  have hμQ : ∀ i, constantCoeff (up Q μ i) = 0 := const_map _ μ hμ.const
  have hμC : ∀ i, constantCoeff (up C (fun i => map θ (μ i)) i) = 0 :=
    const_map _ _ (const_map θ μ hμ.const)
  have hΘμ : (fun i => map Θ (up Q μ i)) = up C (fun i => map θ (μ i)) := by
    have hc : Θ.comp (algebraMap B Q) = (algebraMap O C).comp θ := RingHom.ext hΘ
    funext i
    unfold up
    rw [← RingHom.comp_apply (map Θ), ← map_comp, ← RingHom.comp_apply (map (algebraMap O C)),
      ← map_comp, hc]
  set κ := cob1 (up Q μ) f₀ with hκ
  have hκΘ : map Θ κ = cob1 (up C (fun i => map θ (μ i))) g := by
    rw [hκ, map_formalGroupLawCoboundaryOne_eq Θ _ hμQ, hΘμ, hf0Θ]
  have hκD : DIn (⊤ : Ideal B) κ := by
    have hX : ∀ s : Fin d → Fin d ⊕ Fin d,
        (fun i => (X (s i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) =
          up Q (fun i => (X (s i) : MvPowerSeries (Fin d ⊕ Fin d) B)) :=
      fun s => funext fun i => (map_X _ _).symm
    have h1 := (dIn_subst_up p B O Q θ F (Fin d) (Fin d ⊕ Fin d) ⊤ f₀ μ hf0D hμ.const).1
    have h2 := (dIn_subst_up p B O Q θ F (Fin d) (Fin d ⊕ Fin d) ⊤ f₀
      (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) B)) hf0D
      (fun i => constantCoeff_X _)).1
    have h3 := (dIn_subst_up p B O Q θ F (Fin d) (Fin d ⊕ Fin d) ⊤ f₀
      (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B)) hf0D
      (fun i => constantCoeff_X _)).1
    rw [← hX Sum.inl] at h2
    rw [← hX Sum.inr] at h3
    exact dIn_sub (dIn_sub h1 h2) h3
  have dec : ∀ α, ∃ b : B, Θ (coeff α κ) = algebraMap O C (θ b) := by
    intro α
    obtain ⟨o, -, e⟩ := hg.2.2 α
    obtain ⟨b, rfl⟩ := F.surj o
    exact ⟨b, by rw [← coeff_map, hκΘ, e]⟩
  choose b hb using dec
  let K : MvPowerSeries (Fin d ⊕ Fin d) B := fun α => if α = 0 then 0 else b α
  have hK : ∀ α, coeff α K = if α = 0 then 0 else b α := fun _ => rfl
  have hκ0 : constantCoeff κ = 0 := constantCoeff_coboundaryOne_zero_of_constCoeff _ hμQ f₀ hf0c
  set κ₁ := κ - map (algebraMap B Q) K with hκ1
  have hκ1Θ : map Θ κ₁ = 0 := by
    ext α
    rw [coeff_map, hκ1, map_sub, coeff_map, map_sub, hΘ, hK]
    split_ifs with h
    · subst h
      rw [coeff_zero_eq_constantCoeff_apply, hκ0]
      simp
    · rw [hb α, sub_self, map_zero]
  obtain ⟨hcob2, hsym⟩ := GlobalTheory.T.formalGroupLawCoboundary_symmCocycle_mod p B O Q θ F d μ hμ ⊤ f₀ hf0D
  have hD1 : DIn (RingHom.ker θ) κ₁ := by
    intro α i
    obtain ⟨c, -, e⟩ := dIn_sub hκD (dIn_map K) α i
    refine ⟨c, RingHom.mem_ker.2 (ker_of_alg G hΘ c ?_), e⟩
    rw [← e, map_mul, map_natCast, ← coeff_map, hκ1Θ, map_zero, mul_zero]
  have hc1 : constantCoeff κ₁ = 0 := by
    rw [hκ1, map_sub, hκ0, ← coeff_zero_eq_constantCoeff_apply, coeff_map, hK, if_pos rfl,
      map_zero, sub_zero]
  have hJ : ∀ α, ∃ k : ℕ, ∃ c ∈ RingHom.ker θ, (p : Q) ^ k * coeff α κ₁ = algebraMap B Q c :=
    fun α => kerQ F G hΘ _ (by rw [← coeff_map, hκ1Θ, map_zero])
  have hupK2 : cob2 (up Q μ) (map (algebraMap B Q) K) = map (algebraMap B Q) (cob2 μ K) :=
    (map_formalGroupLawCoboundaryTwo _ μ hμ.const K).symm
  have hcob : In (RingHom.ker θ) (cob2 (up Q μ) κ₁) := by
    apply in_ker G hΘ
    · rw [hκ1, formalGroupLawCoboundaryTwo_sub _ hμQ, hupK2]
      exact in_sub (in_mono le_top hcob2) (in_map _)
    · rw [map_formalGroupLawCoboundaryTwo Θ _ hμQ, hΘμ, hκ1Θ, formalGroupLawCoboundaryTwo_zero _ hμC]
  have hsw : In (RingHom.ker θ) (swap κ₁ - κ₁) := by
    apply in_ker G hΘ
    · have : swap κ₁ - κ₁ = map (algebraMap B Q) (K - swap K) := by
        rw [hκ1, swap_sub, hsym, map_sub, ← map_swap]; ring
      rw [this]; exact in_map _
    · rw [map_sub, map_swap, hκ1Θ, swap_zero, sub_zero]
  obtain ⟨e, he0, hel, heJ, heN⟩ := GlobalTheory.T.swap_sub_in_of_cob2_in p B O Q θ F d μ hμ (RingHom.ker θ) (RingHom.ker θ)
    le_rfl κ₁ (Or.inr hD1) hc1 hJ hcob hsw
  have heΘ : map Θ e = 0 := by
    ext α
    obtain ⟨k, c, hc, e'⟩ := heJ α
    rw [coeff_map, zero_of G hΘ _ k c e' (RingHom.mem_ker.1 hc), map_zero]
  have hl : ∀ i, lin (f₀ - e) i = algebraMap B Q (w i) := fun i => by
    have h2 : lin e i = 0 := congrFun hel i
    have h1 := hf0l i
    simp only [lin] at h1 h2 ⊢
    rw [map_sub, h1, h2, sub_zero]
  have hsub : cob1 (up Q μ) (f₀ - e) = map (algebraMap B Q) K + (κ₁ - cob1 (up Q μ) e) := by
    have := formalCoboundary_add hμQ (f₀ - e) e
    rw [sub_add_cancel] at this
    rw [hκ1]
    linear_combination (-1 : MvPowerSeries (Fin d ⊕ Fin d) Q) * this
  refine ⟨f₀ - e, ⟨?_, fun i => ⟨w i, trivial, hl i⟩, ?_⟩, ?_, hl⟩
  · rw [map_sub, hf0c, he0, sub_zero]
  · rw [hsub]; exact in_add (in_map K) (in_mono le_top heN)
  · rw [map_sub, hf0Θ, heΘ, sub_zero]

end GlobalTheory.QLog.KLift
