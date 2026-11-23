import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamily
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction

noncomputable section

namespace SheetDecomposition

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem rigid_of_congr {Λ : Type} [AddCommGroup Λ] (B : Λ →+ Λ →+ ℝ) (pos : ∀ v, v ≠ 0 → 0 < B v v)
    (fin : ∀ C : ℝ, {v | B v v ≤ C}.Finite) (γ : Λ →+ Λ) (iso : ∀ x y, B (γ x) (γ y) = B x y) (M : ℕ) (hM : 3 ≤ M)
    (hγ : ∀ v, ∃ e, γ v = v + M • e) (v : Λ) : γ v = v := by
  by_contra hv
  have nn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases h : v = 0
    · simp [h]
    · exact (pos v h).le
  let W : Set Λ := {z | z ≠ 0 ∧ ∃ k : ℕ, 0 < k ∧ ∃ x, k • z = γ x - x}
  have h1 : γ v - v ∈ W := ⟨sub_ne_zero.2 hv, 1, one_pos, v, one_smul _ _⟩
  obtain ⟨z, ⟨⟨hz0, k, hk, x, hx⟩, hzC⟩, hmin⟩ := Set.exists_min_image
    (W ∩ {w | B w w ≤ B (γ v - v) (γ v - v)}) (fun w => B w w) ((fin _).inter_of_right _) ⟨_, h1, Set.mem_setOf_eq ▸ le_refl _⟩
  obtain ⟨e, he⟩ := hγ z
  have he' : M • e = γ z - z := by rw [he]; abel
  have hz := pos z hz0
  have hb : (M : ℝ) * (M * B e e) + B (γ z + z) (γ z + z) = 4 * B z z := by
    have : B (M • e) (M • e) = (M : ℝ) * (M * B e e) := by
      simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
    rw [← this, he']
    simp only [map_sub, map_add, AddMonoidHom.sub_apply, AddMonoidHom.add_apply, iso]
    ring
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlt : B e e < B z z := by
    have a1 := nn e
    have a2 := nn (γ z + z)
    have a3 : 9 * B e e ≤ (M : ℝ) * (M * B e e) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by nlinarith) a1
    linarith
  have e0 : e = 0 := by
    by_contra e0
    have := hmin e ⟨⟨e0, M, by omega, z, he'⟩, hlt.le.trans hzC⟩
    exact absurd hlt (not_lt.2 this)
  have hfix : γ z = z := by simpa [e0] using he
  have h0 : (k : ℝ) * B z z = 0 := by
    have : B (k • z) z = (k : ℝ) * B z z := by simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
    rw [← this, hx, map_sub, AddMonoidHom.sub_apply, ← iso x z, hfix, sub_self]
  have : (0 : ℝ) < k := by exact_mod_cast hk
  exact absurd h0 (mul_pos this hz).ne'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def reForm (R : RiemLat E g Λ) : Λ →+ Λ →+ ℝ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => (R.ip (R.P x) (R.P y)).re) fun y y' => by
    simp only [map_add, PeriodIso.ip_add_right', Complex.add_re]) fun x x' => by
    ext y
    simp only [map_add, PeriodIso.ip_add_left', Complex.add_re, AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]

theorem reForm_apply (R : RiemLat E g Λ) (x y : Λ) : reForm R x y = (R.ip (R.P x) (R.P y)).re := rfl

theorem reForm_pos (R : RiemLat E g Λ) (v : Λ) (hv : v ≠ 0) : 0 < reForm R v v := by
  refine R.pos _ fun h => hv (R.unimod.1 ?_)
  ext y
  have := R.im v y
  rw [h] at this
  simp only [zero_dotProduct, Complex.zero_im] at this
  simpa using this.symm

theorem periods_li (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) :
    LinearIndependent ℝ fun i => R.P (b i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  let Wz : Matrix ι ι ℤ := Matrix.of fun i j => R.form (b i) (b j)
  let Wr : Matrix ι ι ℝ := Wz.map (Int.castRingHom ℝ)
  have hWz : Wz.det ≠ 0 := HmCont.gram_det_ne_zero b R.form R.unimod.1
  have hWr : Wr.det ≠ 0 := by
    have : Wr.det = ((Wz.det : ℤ) : ℝ) := by
      have := (Int.castRingHom ℝ).map_det Wz
      simpa [Wr, RingHom.mapMatrix_apply] using this.symm
    rw [this]
    exact_mod_cast hWz
  have h0 : a ᵥ* Wr = 0 := by
    funext j
    have h := congrArg (fun z => (z ⬝ᵥ R.Hm *ᵥ star (R.P (b j))).im) ha
    simp only [sum_dotProduct, smul_dotProduct, Complex.im_sum, Complex.smul_im, R.im, zero_dotProduct,
      Complex.zero_im, smul_eq_mul] at h
    simpa [Wr, Wz, vecMul, dotProduct] using h
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hWr h0)

theorem periods_span (R : RiemLat E g Λ) : Submodule.span ℝ (Set.range R.P) = ⊤ := by
  have := R.free
  have := R.fin
  let b := Module.finBasisOfFinrankEq ℤ Λ R.rank
  have h := (periods_li R b).span_eq_top_of_card_eq_finrank' (by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm])
  refine top_le_iff.1 (h ▸ Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨_, rfl⟩

theorem reForm_eqv {R R' : RiemLat E g Λ} {γ : Λ ≃ₗ[𝓞 E] Λ} (hf : ∀ x y, R'.form (γ x) (γ y) = R.form x y)
    (h : R.EqvBy R' γ) (x y : Λ) : reForm R' (γ x) (γ y) = reForm R x y := by
  obtain ⟨φ, hφ⟩ := h
  rw [reForm_apply, reForm_apply, hφ, hφ, PeriodIso.isometry_of_periods R R' (periods_span R) γ φ hf hφ]

theorem reForm_cont {X : Type} [TopologicalSpace X] (R : X → RiemLat E g Λ) (hP : ∀ v, Continuous fun x => (R x).P v)
    (hH : Continuous fun x => (R x).Hm) (u v : Λ) : Continuous fun x => reForm (R x) u v :=
  Complex.continuous_re.comp ((hP v).dotProduct (hH.matrix_mulVec (hP u).star))

theorem short_finite {X : Type} [TopologicalSpace X] (R : X → RiemLat E g Λ) (hP : ∀ v, Continuous fun x => (R x).P v)
    (hH : Continuous fun x => (R x).Hm) (x₀ : X) (C : ℝ) :
    ∃ S : Set Λ, S.Finite ∧ ∀ᶠ x in 𝓝 x₀, ∀ v, reForm (R x) v v ≤ C → v ∈ S := by
  have := (R x₀).free
  have := (R x₀).fin
  let b := Module.finBasisOfFinrankEq ℤ Λ (R x₀).rank
  let T : X → (Fin (2 * g) → ℝ) → Fin g → ℂ := fun x a => ∑ i, a i • (R x).P (b i)
  let Q : X × (Fin (2 * g) → ℝ) → ℝ := fun p => ((R p.1).ip (T p.1 p.2) (T p.1 p.2)).re
  have hT : Continuous fun p : X × (Fin (2 * g) → ℝ) => T p.1 p.2 :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_snd).smul ((hP _).comp continuous_fst)
  have hQ : Continuous Q :=
    Complex.continuous_re.comp (hT.dotProduct ((hH.comp continuous_fst).matrix_mulVec hT.star))
  have hom : ∀ x (r : ℝ) a, Q (x, r • a) = r ^ 2 * Q (x, a) := fun x r a => by
    have : T x (r • a) = (r : ℂ) • T x a := by
      rw [← PeriodIso.real_smul_eq']
      simp only [T, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
    simp only [Q, this, PeriodIso.ip_smul_left', PeriodIso.ip_smul_right', Complex.star_def, Complex.conj_ofReal,
      Complex.re_ofReal_mul]
    ring
  have hK : IsCompact (Metric.sphere (0 : Fin (2 * g) → ℝ) 1) := isCompact_sphere _ _
  obtain ⟨c, hc, hc'⟩ := hK.exists_forall_le' (f := fun a => Q (x₀, a)) (a := 0)
    (hQ.comp (continuous_const.prodMk continuous_id)).continuousOn (fun a ha => (R x₀).pos _ fun h => by
      have h0 : a = 0 := funext (Fintype.linearIndependent_iff.1 (periods_li (R x₀) b) a h)
      simp [h0] at ha)
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ a ∈ Metric.sphere (0 : Fin (2 * g) → ℝ) 1, c / 2 < Q (x, a) := by
    apply hK.eventually_forall_of_forall_eventually
    intro a ha
    exact (isOpen_lt continuous_const hQ).mem_nhds (lt_of_lt_of_le (by linarith) (hc' a ha))
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * C / c + 1)
  refine ⟨b.equivFun ⁻¹' {f | ∀ i, f i ∈ Set.Icc (-(N : ℤ)) N},
    (Set.Finite.pi' fun _ => Set.finite_Icc _ _).preimage b.equivFun.injective.injOn, ?_⟩
  filter_upwards [hev] with x hx v hv i
  let a : Fin (2 * g) → ℝ := fun i => (b.equivFun v i : ℝ)
  have hTa : T x a = (R x).P v := by
    conv_rhs => rw [← b.sum_equivFun v]
    simp only [T, a, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  have hQa : Q (x, a) ≤ C := by
    simp only [Q, hTa]
    exact hv
  have hn : ‖a‖ ≤ N := by
    by_contra hlt
    push Not at hlt
    have hn : 0 < ‖a‖ := lt_of_le_of_lt (Nat.cast_nonneg N) hlt
    have h1 := hx (‖a‖⁻¹ • a) (by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
    have h2 : Q (x, a) = ‖a‖ ^ 2 * Q (x, ‖a‖⁻¹ • a) := by
      rw [← hom, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have h3 : ‖a‖ ^ 2 * (c / 2) ≤ C := by
      refine le_trans ?_ hQa
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1.le (sq_nonneg _)
    have h4 : ‖a‖ ^ 2 ≤ 2 * C / c := by
      rw [le_div_iff₀ hc]
      linarith
    nlinarith
  have h5 : |a i| ≤ N := (norm_le_pi_norm a i).trans hn
  have h6 : |b.equivFun v i| ≤ (N : ℤ) := by
    simp only [a] at h5
    exact_mod_cast h5
  exact abs_le.1 h6

theorem near_trivial {X : Type} [TopologicalSpace X] (R : X → RiemLat E g Λ) (hP : ∀ v, Continuous fun x => (R x).P v)
    (hH : Continuous fun x => (R x).Hm) (x₀ : X) (M : ℕ) (hM : 3 ≤ M) :
    ∀ᶠ p : X × X in 𝓝 (x₀, x₀), ∀ γ : Λ ≃ₗ[𝓞 E] Λ, (∀ v, ∃ e, γ v = v + M • e) →
      (∀ u v, reForm (R p.2) (γ u) (γ v) = reForm (R p.1) u v) → γ = 1 := by
  have := (R x₀).free
  have := (R x₀).fin
  let b := Module.finBasisOfFinrankEq ℤ Λ (R x₀).rank
  obtain ⟨C, hC⟩ := Finite.exists_le fun i => reForm (R x₀) (b i) (b i)
  obtain ⟨S, hS, hS'⟩ := short_finite R hP hH x₀ (C + 1)
  have h1 : ∀ᶠ x in 𝓝 x₀, ∀ i, reForm (R x) (b i) (b i) < C + 1 :=
    eventually_all.2 fun i => (isOpen_lt (reForm_cont R hP hH _ _) continuous_const).mem_nhds
      (lt_of_le_of_lt (hC i) (lt_add_one C))
  let G : Set (Λ ≃ₗ[𝓞 E] Λ) := (fun γ i => γ (b i)) ⁻¹' {f | ∀ i, f i ∈ S}
  have hG : G.Finite := (Set.Finite.pi' fun _ => hS).preimage fun γ _ γ' _ h => by
    ext v
    rw [← b.sum_equivFun v]
    simp only [map_sum, map_zsmul]
    exact Finset.sum_congr rfl fun i _ => by rw [show γ (b i) = γ' (b i) from congrFun h i]
  have h2 : ∀ᶠ p : X × X in 𝓝 (x₀, x₀), ∀ γ ∈ G, (∀ v, ∃ e, γ v = v + M • e) →
      (∀ u v, reForm (R p.2) (γ u) (γ v) = reForm (R p.1) u v) → γ = 1 := by
    refine (eventually_all_finite hG).2 fun γ _ => ?_
    by_cases h : ∀ u v, reForm (R x₀) (γ u) (γ v) = reForm (R x₀) u v
    · refine Eventually.of_forall fun p hγ _ => ?_
      ext v
      refine rigid_of_congr (reForm (R x₀)) (reForm_pos _) (fun C' => ?_) γ.toLinearMap.toAddMonoidHom h M hM hγ v
      obtain ⟨S', hS₁, hS₂⟩ := short_finite R hP hH x₀ C'
      exact hS₁.subset hS₂.self_of_nhds
    · push Not at h
      obtain ⟨u, v, huv⟩ := h
      have : ∀ᶠ p : X × X in 𝓝 (x₀, x₀), reForm (R p.2) (γ u) (γ v) ≠ reForm (R p.1) u v :=
        (isOpen_ne_fun ((reForm_cont R hP hH _ _).comp continuous_snd)
          ((reForm_cont R hP hH _ _).comp continuous_fst)).mem_nhds huv
      filter_upwards [this] with p hp _ h using absurd (h u v) hp
  have h3 := (continuous_fst.tendsto (x₀, x₀)).eventually h1
  have h4 := (continuous_snd.tendsto (x₀, x₀)).eventually hS'
  filter_upwards [h2, h3, h4] with p a2 a3 a4 γ hγ h
  exact a2 γ (fun i => a4 _ ((h _ _).trans_le (a3 i).le)) hγ h

end SheetDecomposition
