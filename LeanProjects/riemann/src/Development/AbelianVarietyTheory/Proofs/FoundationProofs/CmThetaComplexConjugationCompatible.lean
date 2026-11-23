import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaConj

open MeasureTheory

noncomputable abbrev lamBar (Λ : AddSubgroup ℂ) : AddSubgroup ℂ :=
  Λ.map (starRingEnd ℂ).toAddMonoidHom

theorem mem_lamBar {Λ : AddSubgroup ℂ} {w : ℂ} : w ∈ lamBar Λ ↔ (starRingEnd ℂ) w ∈ Λ := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro h
    exact ⟨_, h, by simp⟩

theorem eisG_lamBar (Λ : AddSubgroup ℂ) (k : ℕ) :
    eisG (lamBar Λ) k = (starRingEnd ℂ) (eisG Λ k) := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ lamBar Λ ∧ w ≠ 0} :=
    { toFun := fun w => ⟨(starRingEnd ℂ) w, mem_lamBar.2 (by simpa using w.2.1), by simpa using w.2.2⟩
      invFun := fun w => ⟨(starRingEnd ℂ) w, mem_lamBar.1 w.2.1, by simpa using w.2.2⟩
      left_inv := fun w => by simp
      right_inv := fun w => by simp }
  unfold eisG
  rw [Complex.conj_tsum, ← e.tsum_eq]
  refine tsum_congr fun w => ?_
  simp [e]

theorem g2_lamBar_eq_conj (Λ : AddSubgroup ℂ) : g2 (lamBar Λ) = (starRingEnd ℂ) (g2 Λ) := by
  simp only [g2, eisG_lamBar, map_mul, map_ofNat]

theorem g3_lamBar_eq_conj (Λ : AddSubgroup ℂ) : g3 (lamBar Λ) = (starRingEnd ℂ) (g3 Λ) := by
  simp only [g3, eisG_lamBar, map_mul, map_ofNat]

theorem area_lamBar (Λ : AddSubgroup ℂ) : area (lamBar Λ) = area Λ := by
  unfold area
  congr 1
  have key : ∀ w₁ w₂ : ℂ, |((starRingEnd ℂ) ((starRingEnd ℂ) w₁) * (starRingEnd ℂ) w₂).im| =
      |((starRingEnd ℂ) w₁ * w₂).im| := fun w₁ w₂ => by
    rw [← map_mul, Complex.conj_im, abs_neg]
  ext a
  constructor
  · rintro ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    exact ⟨ha, _, mem_lamBar.1 h₁, _, mem_lamBar.1 h₂, (key _ _).symm⟩
  · rintro ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    exact ⟨ha, (starRingEnd ℂ) w₁, mem_lamBar.2 (by simpa using h₁), (starRingEnd ℂ) w₂,
      mem_lamBar.2 (by simpa using h₂), (key _ _).symm⟩

variable {D : D7} {N N' : ℕ}

@[simp] theorem vBar_vBar (z : VC D N N') : vBar D (vBar D z) = z := by
  funext τ i j; simp [vBar]

theorem vBar_add (z w : VC D N N') : vBar D (z + w) = vBar D z + vBar D w := by
  funext τ i j; simp [vBar]

theorem vBar_neg (z : VC D N N') : vBar D (-z) = -vBar D z := by
  funext τ i j; simp [vBar]

theorem vBar_zero : vBar D (0 : VC D N N') = 0 := by
  funext τ i j; simp [vBar]

theorem Hf_bar (T : Tor D) (z w : VC D N N') :
    Hf D (torBar D T) (vBar D z) (vBar D w) = (starRingEnd ℂ) (Hf D T z w) := by
  have : area (torBar D T).abelian₂ = area T.abelian₂ := area_lamBar _
  simp only [Hf, this, vBar, map_div₀, map_sum, map_mul, Complex.conj_ofReal]

theorem qH_bar (T : Tor D) (z : VC D N N') : qH D (torBar D T) (vBar D z) = qH D T z := by
  simp only [qH, Hf_bar, Complex.conj_re]

theorem al_bar (T : Tor D) (z : VC D N N') : al D (torBar D T) (vBar D z) = al D T z := by
  simp only [al, Hf_bar, Complex.conj_re]

theorem conj_al (T : Tor D) (z : VC D N N') : (starRingEnd ℂ) (al D T z) = al D T z := by
  simp [al]

theorem norm_al (T : Tor D) (z : VC D N N') : ‖al D T z‖ = 1 := by
  simp [al]

theorem vBar_mem_La {T : Tor D} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {x : VC D N N'} :
    vBar D x ∈ La D (torBar D T) L L' ↔ x ∈ La D T L L' := by
  constructor
  · intro h
    have : ∀ y ∈ La D (torBar D T) L L', vBar D y ∈ La D T L L' := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, A, hA, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨_, mem_lamBar.1 hw, A, hA, ?_⟩
        funext τ i j; simp [vBar, embV, torBar]
      | zero => rw [vBar_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [vBar_add]; exact add_mem hx hy
      | neg x _ hx => rw [vBar_neg]; exact neg_mem hx
    simpa using this _ h
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨w, hw, A, hA, rfl⟩ := hy
      refine AddSubgroup.subset_closure
        ⟨(starRingEnd ℂ) w, mem_lamBar.2 (by simpa using hw), A, hA, ?_⟩
      funext τ i j; simp [vBar, embV, torBar]
    | zero => rw [vBar_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [vBar_add]; exact add_mem hx hy
    | neg x _ hx => rw [vBar_neg]; exact neg_mem hx

theorem cBar_U (T : Tor D) (x : VC D N N') (G : VC D N N' → ℂ) :
    cBar D (U D T x G) = U D (torBar D T) (vBar D x) (cBar D G) := by
  funext z
  have h := Hf_bar T (vBar D z) x
  rw [vBar_vBar] at h
  simp only [cBar, U, vBar_add, vBar_vBar, h, Hf_bar, map_mul, ← Complex.exp_conj, map_sub, map_div₀,
    map_neg, Complex.conj_ofReal, map_ofNat]

theorem differentiable_cBar {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (cBar D G) := by
  intro z
  have := (hG (star z)).star_star
  rw [star_star] at this
  exact this

theorem cBar_mem_Th {T : Tor D} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {G : VC D N N' → ℂ} (hG : G ∈ Th D T L L') :
    cBar D G ∈ Th D (torBar D T) L L' := by
  refine ⟨differentiable_cBar hG.1, fun x hx z => ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = vBar D y := ⟨_, (vBar_vBar x).symm⟩
  rw [← cBar_U, al_bar]
  have := hG.2 y (vBar_mem_La.1 hx) (vBar D z)
  simp only [cBar]
  rw [← this, map_mul, conj_al]

theorem fnConj_rhoBar (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D N N' → ℂ) :
    fnConj D M (rhoBar M ρ) G = cBar D (fnConj D M ρ G) := by
  funext z
  simp only [fnConj, cBar]
  rw [Complex.conj_tsum]
  refine tsum_congr fun α => ?_
  rw [map_mul]
  congr 1
  simp [mono, Finsupp.prod, vBar]

noncomputable def dens (T : Tor D) (G : VC D N N' → ℂ) (z : VC D N N') : ℝ :=
  ‖G z‖ ^ 2 * Real.exp (-Real.pi * (Hf D T z z).re)

theorem Hf_add_add_re (T : Tor D) (z x : VC D N N') :
    (Hf D T (z + x) (z + x)).re = (Hf D T z z).re + 2 * (Hf D T z x).re + (Hf D T x x).re := by
  simp only [Hf, Complex.div_ofReal_re, Complex.re_sum, Finset.mul_sum, ← mul_div_assoc, ← add_div,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  simp
  ring

theorem dens_U (T : Tor D) (x : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    dens T (U D T x G) z = dens T G (z + x) := by
  simp only [dens, U, norm_mul, mul_pow, Complex.norm_exp, Hf_add_add_re]
  rw [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  simp
  ring

theorem dens_add {T : Tor D} {A : AddSubgroup (VC D N N')} {G : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T A) {a : VC D N N'} (ha : a ∈ A) (z : VC D N N') :
    dens T G (z + a) = dens T G z := by
  rw [← dens_U]
  simp only [dens]
  rw [← hG.2 a ha z, norm_mul, norm_al, one_mul]

theorem dens_bar (T : Tor D) (G : VC D N N' → ℂ) (z : VC D N N') :
    dens (torBar D T) (cBar D G) z = dens T G (vBar D z) := by
  have h := Hf_bar T (vBar D z) (vBar D z)
  rw [vBar_vBar] at h
  simp [dens, h, cBar]

theorem measurePreserving_vBar :
    MeasurePreserving (vBar D : VC D N N' → VC D N N') volume volume :=
  volume_preserving_pi fun _ => volume_preserving_pi fun _ => volume_preserving_pi fun _ =>
    Complex.conjLIE.measurePreserving

noncomputable def vBarEquiv (D : D7) (N N' : ℕ) : VC D N N' ≃ᵐ VC D N N' where
  toFun := vBar D
  invFun := vBar D
  left_inv := vBar_vBar
  right_inv := vBar_vBar
  measurable_toFun := measurePreserving_vBar.measurable
  measurable_invFun := measurePreserving_vBar.measurable

theorem discrete_of_qH_int {T : Tor D} (hT : 0 < area T.abelian₂) {A : AddSubgroup (VC D N N')}
    (hA : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m) : DiscreteTopology A := by
  have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hq : ∀ x : VC D N N', qH D T x =
      Real.sqrt D.host.d / 2 * ((∑ τ, ∑ i, ∑ j, Complex.normSq (x τ i j)) / area T.abelian₂) := fun x => by
    simp only [qH, Hf, Complex.div_ofReal_re, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]
  have hc : Continuous (qH D T : VC D N N' → ℝ) := by
    rw [funext hq]
    fun_prop
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have : ({0} : Set A) = (fun x : A => qH D T (x : VC D N N')) ⁻¹' Set.Iio 1 := by
    ext x
    constructor
    · rintro rfl
      simp [hq]
    · intro hx
      obtain ⟨m, hm⟩ := hA x x.2
      have hS : 0 ≤ ∑ τ, ∑ i, ∑ j, Complex.normSq ((x : VC D N N') τ i j) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Complex.normSq_nonneg _
      have h0 : (0 : ℝ) ≤ m := by rw [← hm, hq]; positivity
      have h1 : (m : ℝ) < 1 := by rw [← hm]; exact hx
      have h0' : 0 ≤ m := by exact_mod_cast h0
      have h1' : m < 1 := by exact_mod_cast h1
      obtain rfl : m = 0 := by omega
      rw [hq, Int.cast_zero, mul_eq_zero, div_eq_zero_iff, div_eq_zero_iff] at hm
      have hS0 : ∑ τ, ∑ i, ∑ j, Complex.normSq ((x : VC D N N') τ i j) = 0 := by
        rcases hm with (h | h) | h | h
        · exact absurd h hd.ne'
        · norm_num at h
        · exact h
        · exact absurd h hT.ne'
      refine Subtype.ext (funext fun τ => funext fun i => funext fun j => ?_)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _).1 hS0 τ (Finset.mem_univ _)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _).1 h2 i (Finset.mem_univ _)
      have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Complex.normSq_nonneg _).1 h3 j
        (Finset.mem_univ _)
      exact Complex.normSq_eq_zero.1 h4
  rw [this]
  exact isOpen_Iio.preimage (hc.comp continuous_subtype_val)

theorem average_bar {A B : AddSubgroup (VC D N N')} [Countable B]
    (hAB : ∀ x, vBar D x ∈ B ↔ x ∈ A) {f : VC D N N' → ℝ} (hf : ∀ a ∈ A, ∀ z, f (a + z) = f z)
    {P Q : Set (VC D N N')} (hP : IsAddFundamentalDomain A P volume)
    (hQ : IsAddFundamentalDomain B Q volume) :
    ⨍ z in Q, f (vBar D z) = ⨍ z in P, f z := by
  have i1 : (volume : Measure (Fin N → ℂ)).IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  have i2 : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddLeftInvariant :=
    Measure.pi.isAddLeftInvariant _
  have i3 : (volume : Measure (VC D N N')).IsAddLeftInvariant := Measure.pi.isAddLeftInvariant _
  let e : A → B := fun a => ⟨vBar D a, (hAB _).2 a.2⟩
  have he : Function.Bijective e := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun b => ⟨vBar D b, (hAB _).1 (by simp)⟩, fun a => ?_, fun b => ?_⟩
    · simp [e]
    · simp [e]
  have hP' : IsAddFundamentalDomain B (vBar D ⁻¹' P) volume := by
    refine hP.preimage_of_equiv measurePreserving_vBar.quasiMeasurePreserving he fun a z => ?_
    change vBar D (vBar D a + z) = (a : VC D N N') + vBar D z
    rw [vBar_add, vBar_vBar]
  have hemb : MeasurableEmbedding (vBar D : VC D N N' → VC D N N') :=
    (vBarEquiv D N N').measurableEmbedding
  have h1 : ∫ z in Q, f (vBar D z) = ∫ z in P, f z := by
    rw [hQ.setIntegral_eq hP' fun b z => ?_]
    · exact measurePreserving_vBar.setIntegral_preimage_emb hemb f P
    · change f (vBar D ((b : VC D N N') + z)) = _
      rw [vBar_add, hf _ ((hAB _).1 (by simp))]
  have h2 : volume Q = volume P := by
    rw [hQ.measure_eq hP']
    exact measurePreserving_vBar.measure_preimage_emb hemb P
  rw [setAverage_eq, setAverage_eq, h1, Measure.real, Measure.real, h2]

theorem normSq_bar {T : Tor D} (hT : 0 < area T.abelian₂)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : ∀ x ∈ La D T L L', ∃ m : ℤ, qH D T x = m) {G : VC D N N' → ℂ} (hG : G ∈ Th D T L L')
    (x : VC D N N') :
    normSq D (torBar D T) (La D (torBar D T) L L') (cBar D (U D T x G)) =
      normSq D T (La D T L L') (U D T x G) := by
  have d1 := discrete_of_qH_int hT hA
  have d2 : DiscreteTopology (La D (torBar D T) L L') := by
    refine discrete_of_qH_int (T := torBar D T) ((area_lamBar T.abelian₂).symm ▸ hT) fun y hy => ?_
    obtain ⟨y, rfl⟩ : ∃ y', y = vBar D y' := ⟨_, (vBar_vBar y).symm⟩
    rw [qH_bar]
    exact hA y (vBar_mem_La.1 hy)
  have c2 := countable_of_discrete_addSubgroup (La D (torBar D T) L L')
  obtain ⟨P, -, -, hP⟩ := exists_isAddFundamentalDomain_addSubgroup (La D T L L')
  obtain ⟨Q, -, -, hQ⟩ := exists_isAddFundamentalDomain_addSubgroup (La D (torBar D T) L L')
  have hP' := Classical.epsilon_spec
    (p := fun Fd => IsAddFundamentalDomain (La D T L L') Fd volume) ⟨P, hP volume⟩
  have hQ' := Classical.epsilon_spec
    (p := fun Fd => IsAddFundamentalDomain (La D (torBar D T) L L') Fd volume) ⟨Q, hQ volume⟩
  have := average_bar (fun _ => vBar_mem_La) (f := dens T (U D T x G)) (fun a ha z => by
    rw [dens_U, dens_U, add_comm a z, add_right_comm, dens_add hG ha]) hP' hQ'
  simp only [← dens_bar] at this
  exact this

theorem fixK_or (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hM : ∀ τ x, embT D τ x ∈ M) :
    FixK D M ρ ∨ FixK D M (rhoBar M ρ) := by
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity)
  have hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M := fun a => by
    rw [← (GlobalTheory.InducedType.induced_type D).1.1 τ a]; exact hM _ _
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixK D M ρ' := fun ρ' h a => by
    refine ⟨hm a, ?_⟩
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM a) = σ a := DFunLike.congr_fun this a
    unfold cj TaylorLogMetric.liftM
    rw [dif_pos (hm a)]
    exact h2
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact Or.inl (key ρ h)
  · refine Or.inr (key _ ?_)
    change (starRingEnd ℂ) (ρ (σM b)) = _
    rw [h, map_neg, hcj, neg_neg]

theorem exists_periodPair_lamConj {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 (lamOf D cc δ) ∈ M)
    (h3 : g3 (lamOf D cc δ) ∈ M) :
    ∃ P : PeriodPair, (∀ z, z ∈ lamConj M ρ (lamOf D cc δ) ↔ z ∈ P.lattice) ∧
      g2 (lamConj M ρ (lamOf D cc δ)) = ρ (liftM M (g2 (lamOf D cc δ))) ∧
      g3 (lamConj M ρ (lamOf D cc δ)) = ρ (liftM M (g3 (lamOf D cc δ))) := by
  obtain ⟨⟨w₁, w₂, hw, -⟩, -, hΔ, -⟩ :=
    GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc
  have hne : ρ (liftM M (g2 (lamOf D cc δ))) ^ 3 - 27 * ρ (liftM M (g3 (lamOf D cc δ))) ^ 2 ≠ 0 := by
    have : liftM M (g2 (lamOf D cc δ)) ^ 3 - 27 * liftM M (g3 (lamOf D cc δ)) ^ 2 = 1 := by
      apply Subtype.ext
      unfold TaylorLogMetric.liftM
      rw [dif_pos h2, dif_pos h3]
      exact hΔ
    have h := congrArg ρ this
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at h
    rw [h]
    exact one_ne_zero
  let P₀ : PeriodPair := ⟨w₁, w₂, hw⟩
  obtain ⟨P, hP2, hP3⟩ :=
    (GlobalTheory.LatticeInvariants.invariants_dictionary P₀ P₀.lattice.toAddSubgroup fun _ => Iff.rfl).2.2.2.2.2.2 _ _ hne
  obtain ⟨e2, e3, -, -, -, hu, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary P P.lattice.toAddSubgroup fun _ => Iff.rfl
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (liftM M (g2 (lamOf D cc δ))) ∧ g3 Λ' = ρ (liftM M (g3 (lamOf D cc δ))))
    ⟨_, e2.trans hP2, e3.trans hP3⟩
  refine ⟨P, fun z => ?_, hs⟩
  have : lamConj M ρ (lamOf D cc δ) = P.lattice.toAddSubgroup :=
    hu _ (hs.1.trans (e2.trans hP2).symm) (hs.2.trans (e3.trans hP3).symm)
  rw [this]
  rfl

theorem torConj_rhoBar {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hM : DataIn D (tor0 D cc δ) M) :
    torConj D (tor0 D cc δ) M (rhoBar M ρ) = torBar D (torConj D (tor0 D cc δ) M ρ) := by
  obtain ⟨P, hP, a2, a3⟩ := exists_periodPair_lamConj hc M (rhoBar M ρ) hM.2.1 hM.2.2
  obtain ⟨-, -, b2, b3⟩ := exists_periodPair_lamConj hc M ρ hM.2.1 hM.2.2
  have : lamBar (lamConj M ρ (lamOf D cc δ)) = lamConj M (rhoBar M ρ) (lamOf D cc δ) := by
    refine (GlobalTheory.LatticeInvariants.invariants_dictionary P _ hP).2.2.2.2.2.1 _ ?_ ?_
    · rw [g2_lamBar_eq_conj, a2, b2]; rfl
    · rw [g3_lamBar_eq_conj, a3, b3]; rfl
  unfold torConj torBar
  congr 1
  exact this.symm

noncomputable def sesq (z w : VC D N N') : ℂ := ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)

theorem Hf_eq_sesq (T : Tor D) (z w : VC D N N') : Hf D T z w = sesq z w / (area T.abelian₂ : ℂ) := rfl

theorem im_Hf (T : Tor D) (z w : VC D N N') : (Hf D T z w).im = (sesq z w).im / area T.abelian₂ := by
  rw [Hf_eq_sesq, Complex.div_ofReal_im]

theorem sesq_smul_left (c : ℂ) (z w : VC D N N') : sesq (c • z) w = c * sesq z w := by
  simp [sesq, Finset.mul_sum, mul_assoc]

theorem sesq_smul_right (c : ℂ) (z w : VC D N N') :
    sesq z (c • w) = sesq z w * (starRingEnd ℂ) c := by
  simp only [sesq, Finset.sum_mul, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem sesq_add_left (z z' w : VC D N N') : sesq (z + z') w = sesq z w + sesq z' w := by
  simp [sesq, add_mul, Finset.sum_add_distrib]

theorem sesq_add_right (z w w' : VC D N N') : sesq z (w + w') = sesq z w + sesq z w' := by
  simp [sesq, mul_add, Finset.sum_add_distrib]

theorem sesq_neg_left (z w : VC D N N') : sesq (-z) w = -sesq z w := by simp [sesq]

theorem sesq_neg_right (z w : VC D N N') : sesq z (-w) = -sesq z w := by simp [sesq]

theorem sesq_self_im (z : VC D N N') : (sesq z z).im = 0 := by
  simp [sesq, Complex.im_sum, Complex.mul_conj]

theorem sesq_embV (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hG : admG1 D)
    (x y : Matrix (Fin N') (Fin N) D.host.E) :
    sesq (embV D (tor0 D cc δ) x) (embV D (tor0 D cc δ) y) =
      D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) := by
  have he : ∀ (x : Matrix (Fin N') (Fin N) D.host.E) τ i j,
      embV D (tor0 D cc δ) x τ i j = embT D τ (x i j) := fun _ _ _ _ => rfl
  rw [hYY, ← hG.2]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [map_sum, map_mul, he]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [D.host.conjE_apply]

theorem thetaQuadForm_int_selfDual_cmTorus {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L') :
    ∀ x ∈ La D (tor0 D cc δ) L L', ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨⟨w₁, w₂, hw, hcl⟩, -, -, -, lam_mul⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hc
  have hP : ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ (⟨w₁, w₂, hw⟩ : PeriodPair).lattice := fun z => by
    rw [hcl, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp
  obtain ⟨-, hdual⟩ := GlobalTheory.PlaneLattice.area_pos_and_selfDual _ _ hP
  have hS := GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL'
  have hLam : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  have hsq : ∀ z ∈ La D (tor0 D cc δ) L L', ∀ x ∈ YYl D L L',
      sesq z (embV D (tor0 D cc δ) x) ∈ lamOf D cc δ := by
    intro z hz x hx
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨w, hw, x', hx', rfl⟩ := hz
      obtain ⟨a, ha⟩ := hS x' hx' x hx
      rw [sesq_smul_left, sesq_embV cc δ hG, ← ha, mul_comm]
      exact lam_mul a _ hw
    | zero => simp [sesq]
    | add a b _ _ ha hb => rw [sesq_add_left]; exact add_mem ha hb
    | neg a _ ha => rw [sesq_neg_left]; exact neg_mem ha
  have hint : ∀ x ∈ La D (tor0 D cc δ) L L', ∀ y ∈ La D (tor0 D cc δ) L L',
      ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m := by
    intro z hz u hu
    simp only [im_Hf, hLam]
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨w, hw, x, hx, rfl⟩ := hu
      rw [sesq_smul_right]
      exact (hdual _).1 (hsq z hz x hx) w hw
    | zero => exact ⟨0, by simp [sesq]⟩
    | add a b _ _ ha hb =>
      obtain ⟨m, hm⟩ := ha
      obtain ⟨n, hn⟩ := hb
      exact ⟨m + n, by rw [sesq_add_right, Complex.add_im, add_div, hm, hn, Int.cast_add]⟩
    | neg a _ ha =>
      obtain ⟨m, hm⟩ := ha
      exact ⟨-m, by rw [sesq_neg_right, Complex.neg_im, neg_div, hm, Int.cast_neg]⟩
  intro x hx
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hx' : w0 D • x ∈ La D (tor0 D cc δ) L L' := by
    induction hx using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨w, hw, x', hx', rfl⟩ := hz
      refine AddSubgroup.subset_closure ⟨w0 D * w, ?_, x', hx', (mul_smul _ _ _).symm⟩
      rw [← ha]
      exact lam_mul a _ hw
    | zero => rw [smul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | neg a _ ha => rw [smul_neg]; exact neg_mem ha
  obtain ⟨m, hm⟩ := hint _ hx' x hx
  refine ⟨m, ?_⟩
  rw [← hm, im_Hf, sesq_smul_left, qH, Hf_eq_sesq, Complex.div_ofReal_re, Complex.mul_im,
    sesq_self_im]
  simp [w0]
  ring

theorem qH_int_of_fixK {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hM : DataIn D (tor0 D cc δ) M) (hρ : FixK D M ρ)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : SD D L) (hL' : SD D L') :
    0 < area (torConj D (tor0 D cc δ) M ρ).abelian₂ ∧
      ∀ x ∈ La D (torConj D (tor0 D cc δ) M ρ) L L',
        ∃ m : ℤ, qH D (torConj D (tor0 D cc δ) M ρ) x = m := by
  obtain ⟨cc', δ', hc', -, hlam⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M ρ hρ hM.2.1 hM.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := (GlobalTheory.InducedType.induced_type D).2 M ρ hρ hM.1
  have hT : torConj D (tor0 D cc δ) M ρ = ⟨fun τ => embT D (π τ), lamOf D cc' δ'⟩ := by
    unfold torConj
    congr 1
    funext τ x
    exact hπ τ x
  rw [hT]
  obtain ⟨-, hδ, -, har, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'
  refine ⟨?_, fun x hx => ?_⟩
  · have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    have hn : (0 : ℝ) < Ideal.absNorm cc' := by
      exact_mod_cast Nat.pos_of_ne_zero fun h => hc'.1.1 (Ideal.absNorm_eq_zero_iff.1 h)
    have hδ' : 0 < ‖δ'‖ := norm_pos_iff.2 hδ
    change 0 < area (lamOf D cc' δ')
    rw [har]
    positivity
  · have hy : (fun τ => x (π.symm τ)) ∈ La D (tor0 D cc' δ') L L' := by
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, A, hA, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨w, hw, A, hA, ?_⟩
        funext τ i j; simp [embV, tor0]
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx
    obtain ⟨m, hm⟩ := thetaQuadForm_int_selfDual_cmTorus hc' hL hL' _ hy
    refine ⟨m, ?_⟩
    rw [← hm]
    simp only [qH, Hf, tor0]
    rw [← π.symm.sum_comp]

theorem useBar_holds : ∀ D : D7, useBar D := by
  intro D cc δ hc M ρ hM
  have hK := fixK_or M ρ hM.1
  have hT := torConj_rhoBar hc M ρ hM
  refine ⟨hK, hT, fun N N' L L' G => ⟨fnConj_rhoBar M ρ G, fun x => cBar_U _ x G, fun hG =>
    ⟨cBar_mem_Th hG, fun hL hL' x => ?_⟩⟩⟩
  rcases hK with h | h
  · obtain ⟨h1, h2⟩ := qH_int_of_fixK hc M ρ hM h hL hL'
    exact normSq_bar h1 h2 hG x
  · obtain ⟨h1, h2⟩ := qH_int_of_fixK hc M _ hM h hL hL'
    rw [hT] at h1 h2
    refine normSq_bar ((area_lamBar _).symm.trans_gt h1) (fun y hy => ?_) hG x
    rw [← qH_bar]
    exact h2 _ (vBar_mem_La.2 hy)

end GlobalTheory.ThetaConj
