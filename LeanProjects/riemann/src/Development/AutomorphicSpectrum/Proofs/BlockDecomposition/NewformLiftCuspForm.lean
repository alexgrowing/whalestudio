import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Set Filter Topology CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups ModularForm Manifold ValuativeRel

namespace GlobalTheory.CompanionTheory.LiftCusp

open GroundTheory.Automorphic GroundTheory.Automorphic.GL2Classical GroundTheory.Automorphic.AutomorphicForm
open AdelicGLn GroundTheory.Global ModularForm

set_option linter.unusedSectionVars false

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem isZeroAtImInfty_slash₁ (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (δ : GL (Fin 2) ℚ) :
    IsZeroAtImInfty ((f : ℍ → ℂ) ∣[k] toReal δ) := by
  have hc : IsCusp (toReal δ • (OnePoint.infty : OnePoint ℝ)) (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    refine ⟨δ • OnePoint.infty, ?_⟩
    rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty]
    rfl
  exact f.zero_at_cusps' hc (toReal δ) rfl

theorem slash_periodic₁ {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) {δ : GL (Fin 2) ℝ} (T : ℝ)
    {s : SL(2, ℤ)} (hs : s ∈ Gamma1 N)
    (hreal : Matrix.SpecialLinearGroup.mapGL ℝ s * δ = δ * unipReal T) (z : ℍ) :
    (f ∣[k] δ) (T +ᵥ z) = (f ∣[k] δ) z := by
  have hper : (f ∣[k] δ) ∣[k] unipReal T = f ∣[k] δ := by
    rw [← SlashAction.slash_mul, ← hreal, SlashAction.slash_mul,
      hf _ (Subgroup.mem_map_of_mem _ hs)]
  have hpos : 0 < (unipReal T).det.val := by rw [det_unipReal]; exact one_pos
  have := congrFun hper z
  rw [slash_apply, σ_of_det_pos hpos, det_unipReal, abs_one, Complex.ofReal_one, _root_.one_zpow,
    mul_one, denom_unipReal, _root_.one_zpow, mul_one, unipReal_smul] at this
  exact this

theorem integral_archLift_eq_zero₁ (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    {δ : GL (Fin 2) ℚ} (hδ : 0 < (δ.det.val : ℚ)) {M : ℕ} (hM : 0 < M) {s : SL(2, ℤ)}
    (hs : s ∈ Gamma1 N)
    (hreal : Matrix.SpecialLinearGroup.mapGL ℝ s * toReal δ = toReal δ * unipReal (M : ℝ))
    {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    ∫ t in (0 : ℝ)..M, archLift k f (toReal δ * (unipReal t * h)) = 0 := by
  have hf : ∀ γ ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f := fun γ hγ =>
    SlashInvariantForm.slash_action_eqn f γ hγ
  set F := (f : ℍ → ℂ) ∣[k] toReal δ
  have hδR : 0 < (toReal δ).det.val := by rw [det_toReal]; exact_mod_cast hδ
  have hdne : ((toReal δ).det.val : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hδR.ne')
  set j := denom h ((UpperHalfPlane.I : ℍ) : ℂ)
  set z := h • UpperHalfPlane.I
  set C : ℂ := (((toReal δ).det.val : ℂ) ^ (k - 1))⁻¹ * (Real.sqrt (toReal δ).det.val : ℂ) ^ k *
    ((j / (‖j‖ : ℂ)) ^ (-k) * (Real.sqrt z.im : ℂ) ^ k)
  have key : ∀ t : ℝ, archLift k f (toReal δ * (unipReal t * h)) = C * F (t +ᵥ z) := by
    intro t
    have hy : 0 < (unipReal t * h).det.val := by
      rw [map_mul, Units.val_mul, det_unipReal, one_mul]
      exact hpos
    have h1 := archLift_mul_left (k := k) (f : ℍ → ℂ) hδR hy
    rw [archLift_unipReal_mul F hpos t] at h1
    rw [eq_inv_mul_iff_mul_eq₀ hdne |>.2 h1]
    simp only [C, j, z]
    ring
  have hzero : ∫ t in (0 : ℝ)..M, F (t +ᵥ z) = 0 := by
    refine integral_vadd_eq_zero (f.holo'.slash k (toReal δ)) (by exact_mod_cast hM)
      (fun z' => ?_) (isZeroAtImInfty_slash₁ f δ) z
    exact slash_periodic₁ hf (M : ℝ) hs hreal z'
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul, hzero, mul_zero]

theorem exists_period₁ (δ : GL (Fin 2) ℚ) : ∃ D : ℕ, 0 < D ∧ ∀ M : ℕ, D ∣ M → ∃ s ∈ Gamma1 N,
    Matrix.SpecialLinearGroup.mapGL ℝ s * toReal δ = toReal δ * unipReal (M : ℝ) := by
  set B : Matrix (Fin 2) (Fin 2) ℚ :=
    (δ : Matrix (Fin 2) (Fin 2) ℚ) * !![0, 1; 0, 0] * ((δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) with hB
  set D₀ : ℕ := ∏ p : Fin 2 × Fin 2, (B p.1 p.2).den with hD₀
  have hD₀pos : 0 < D₀ := Finset.prod_pos fun p _ => (B p.1 p.2).den_pos
  have hint : ∀ i j, ∃ c : ℤ, (c : ℚ) = D₀ * B i j := by
    intro i j
    obtain ⟨e, he⟩ : (B i j).den ∣ D₀ :=
      Finset.dvd_prod_of_mem (fun p : Fin 2 × Fin 2 => (B p.1 p.2).den) (Finset.mem_univ (i, j))
    refine ⟨e * (B i j).num, ?_⟩
    rw [he]
    push_cast
    rw [← Rat.mul_den_eq_num (B i j)]
    ring
  choose C hC using hint
  refine ⟨N * D₀, Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) hD₀pos, ?_⟩
  rintro _ ⟨m, rfl⟩
  set A : Matrix (Fin 2) (Fin 2) ℤ := 1 + ((N * m : ℕ) : ℤ) • Matrix.of C with hA
  set Mq : ℚ := ((N * D₀ * m : ℕ) : ℚ) with hMq
  have hcast : ∀ i j, ((A i j : ℤ) : ℚ) =
      ((δ * unipRat Mq * δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j := by
    have hu : ((unipRat Mq : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = 1 + Mq • !![0, 1; 0, 0] := by
      ext a b
      change unipMatrix (n := 2) (r := 1) (fun _ => Mq) a b = _
      rw [unipMatrix_apply]
      fin_cases a <;> fin_cases b <;> simp
    have hm : ((δ * unipRat Mq * δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = 1 + Mq • B := by
      rw [Units.val_mul, Units.val_mul, hu, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, hB, Matrix.mul_smul, Matrix.smul_mul]
    intro i j
    rw [hm, hA]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Int.cast_add,
      Int.cast_mul, hC, Int.cast_natCast]
    have : ((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) = (1 : Matrix (Fin 2) (Fin 2) ℚ) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [this, hMq]
    push_cast
    ring
  have hdet : A.det = 1 := by
    have e : (Int.castRingHom ℚ).mapMatrix A =
        ((δ * unipRat Mq * δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := by
      ext i j
      exact hcast i j
    have h1 : ((A.det : ℤ) : ℚ) = 1 := by
      have h2 : (Int.castRingHom ℚ) A.det = ((δ * unipRat Mq * δ⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
        rw [← e, RingHom.map_det]
      have h3 : (unipRat Mq).det.val = 1 := by
        have := det_unipReal (Mq : ℝ)
        rw [← toReal_unipRat, det_toReal] at this
        exact_mod_cast this
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
        h3, mul_one, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _)] at h2
      simpa using h2
    exact_mod_cast h1
  obtain ⟨s, hs⟩ : ∃ s : SL(2, ℤ), (s : Matrix (Fin 2) (Fin 2) ℤ) = A := ⟨⟨A, hdet⟩, rfl⟩
  refine ⟨s, ?_, ?_⟩
  · rw [Gamma1_mem, hs]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [hA, Matrix.add_apply]
  · have e1 : Matrix.SpecialLinearGroup.mapGL ℚ s = δ * unipRat Mq * δ⁻¹ :=
      Units.ext (Matrix.ext fun i j => by rw [← hcast i j, ← hs]; rfl)
    rw [← toReal_mapGL, e1, map_mul, map_mul, map_inv, toReal_unipRat, inv_mul_cancel_right]
    simp [hMq]

theorem exists_nat_mul_mem (e : 𝔸f) :
    ∃ D : ℕ, 0 < D ∧ (D : 𝔸f) * e ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact (K := ℚ)
    (isCompact_singleton (x := e))
  set z : ℤ := Rat.ringOfIntegersEquiv d
  have hz0 : z ≠ 0 := by
    intro h
    exact hd0 (Rat.ringOfIntegersEquiv.injective (by rw [map_zero]; exact h))
  have hdz : algebraMap (𝓞 ℚ) ℚ d = z := (Rat.ringOfIntegersEquiv_apply_coe d).symm
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, ?_⟩
  have h1 := hd e rfl
  rw [hdz, map_intCast] at h1
  rcases Int.natAbs_eq z with h | h
  · have hD1 : ((z.natAbs : ℕ) : ℤ) = z := by omega
    rw [show (z.natAbs : 𝔸f) = (z : 𝔸f) by rw [← Int.cast_natCast, hD1]]
    exact h1
  · have hD2 : ((z.natAbs : ℕ) : ℤ) = -z := by omega
    rw [show (z.natAbs : 𝔸f) = -(z : 𝔸f) by rw [← Int.cast_natCast, hD2, Int.cast_neg], neg_mul]
    exact neg_mem h1

theorem levelIdeal_mono {A B : ℕ} (h : A ∣ B) : levelIdeal B ⊆ levelIdeal A := by
  obtain ⟨c, rfl⟩ := h
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨(c : 𝔸f) * t, mul_mem (natCast_mem _ c) ht, by push_cast; ring⟩

variable (N) in
theorem exists_level_conj₁ (w : FiniteAdelicGL ℚ 2) : ∃ M : ℕ, 0 < M ∧ ∀ y ∈ levelIdeal M,
    w⁻¹ * unipFin y * w ∈ Gamma0Level N ∧
      ((w⁻¹ * unipFin y * w : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 - 1 ∈ levelIdeal N := by
  obtain ⟨M₀, hM₀, h₀⟩ := exists_level_conj N w
  obtain ⟨D, hD, hDe⟩ := exists_nat_mul_mem
    (((w⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 * (w : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1)
  refine ⟨M₀ * (N * D), Nat.mul_pos hM₀ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) hD),
    fun y hy => ⟨h₀ y (levelIdeal_mono (Dvd.intro _ rfl) hy), ?_⟩⟩
  obtain ⟨t, ht, rfl⟩ := hy
  rw [conj_unipFin_apply, Matrix.one_apply_eq, add_sub_cancel_left]
  exact ⟨(M₀ : 𝔸f) * t * _, mul_mem (mul_mem (natCast_mem _ M₀) ht) hDe, by push_cast; ring⟩

theorem valued_natCast_lt_one_of_mem {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (hn : (n : 𝓞 K) ∈ v.asIdeal) : Valued.v ((n : ℕ) : v.adicCompletion K) < 1 := by
  have h1 : v.valuation K (algebraMap (𝓞 K) K (n : 𝓞 K)) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem v _).2 hn
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 K) K (n : 𝓞 K))
  have e : algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (n : 𝓞 K)) = ((n : ℕ) : v.adicCompletion K) := by
    simp
  exact (e ▸ h2 : Valued.v ((n : ℕ) : v.adicCompletion K) = _).trans_lt h1

theorem valued_natCast_lt_one (v : Ad3.Pl) (h : Ad3.pOf v ∣ N) :
    Valued.v ((N : ℕ) : Ad3.Qv v) < 1 := by
  have hm : ((Ad3.pOf v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  refine valued_natCast_lt_one_of_mem v N ?_
  obtain ⟨c, hc⟩ := h
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hm

theorem valued_entry {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) (v : Ad3.Pl)
    (hv : Ad3.pOf v ∣ N) : Valued.v ((u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 v) = 1 := by
  have hi := (mem_integralFiniteGL_iff ℚ 2).1 hu.1
  have hVW : (u : Matrix (Fin 2) (Fin 2) 𝔸f) * ((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h11 := congrFun (congrFun hVW 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h11
  have hloc := congrArg (GodementSection.adeleAt v) h11
  simp only [map_add, map_mul, map_one, GodementSection.adeleAt_apply] at hloc
  have ha : Valued.v ((u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 v) ≤ 1 := hi.1 1 1 v
  have hb : Valued.v (((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 v) ≤ 1 := hi.2 1 1 v
  have hs : Valued.v (((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1 v) ≤ 1 := hi.2 0 1 v
  obtain ⟨t, ht, hct⟩ := hu.2
  have hc : Valued.v ((u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 v) < 1 := by
    have e : (u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 v = ((N : ℕ) : Ad3.Qv v) * t v := by
      have e2 : GodementSection.adeleAt v ((N : 𝔸f) * t) = ((N : ℕ) : Ad3.Qv v) * t v := by
        rw [map_mul, map_natCast]
        rfl
      rw [hct]
      exact e2
    rw [e, map_mul]
    exact mul_lt_one_of_lt_of_le (valued_natCast_lt_one v hv) (ht v)
  have hcs : Valued.v ((u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 0 v *
      ((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 0 1 v) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hc hs
  have hab : Valued.v ((u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 v *
      ((u⁻¹ : FiniteAdelicGL ℚ 2) : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 v) = 1 := by
    rw [eq_sub_of_add_eq' hloc]
    exact Valuation.map_one_sub_of_lt _ hcs
  rw [map_mul] at hab
  refine le_antisymm ha ?_
  calc (1 : _) = _ := hab.symm
    _ ≤ _ := mul_le_of_le_one_right' hb

theorem ord_eq_zero_of_valued (v : Ad3.Pl) (x : (Ad3.Qv v)ˣ) (h : Valued.v (x : Ad3.Qv v) = 1) :
    GroundTheory.LocalField.ord (x : Ad3.Qv v) = 0 := by
  have h1 : (x : Ad3.Qv v) ∈ 𝒪[Ad3.Qv v] :=
    (GroundTheory.Global.mem_valuationInteger_iff v _).2 ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 h.le)
  have h2 : ((x⁻¹ : (Ad3.Qv v)ˣ) : Ad3.Qv v) ∈ 𝒪[Ad3.Qv v] := by
    refine (GroundTheory.Global.mem_valuationInteger_iff v _).2 ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
  exact GroundTheory.LocalField.ord_unit (⟨⟨x, h1⟩, ⟨_, h2⟩, by ext; simp, by ext; simp⟩ : 𝒪[Ad3.Qv v]ˣ)

theorem exists_idele {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) :
    ∃ d : 𝔸fˣ, (∀ v, GroundTheory.LocalField.ord ((Ad3.R.lf v d : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0) ∧
      ∀ v, Ad3.pOf v ∣ N → ((Ad3.R.lf v d : (Ad3.Qv v)ˣ) : Ad3.Qv v) = GodementSection.glAt v u 1 1 := by
  classical
  set f : ∀ v : Ad3.Pl, Ad3.Qv v := fun v =>
    if Ad3.pOf v ∣ N then (u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 v else 1 with hf
  have hfv : ∀ v, Valued.v (f v) = 1 := by
    intro v
    simp only [hf]
    split_ifs with h
    · exact valued_entry hu v h
    · exact map_one _
  have hfne : ∀ v, f v ≠ 0 := fun v h0 => by
    have := hfv v
    rw [h0, map_zero] at this
    exact zero_ne_one this
  let x : 𝔸f := ⟨f, Filter.Eventually.of_forall fun v => (hfv v).le⟩
  let y : 𝔸f := ⟨fun v => (f v)⁻¹, Filter.Eventually.of_forall fun v => by
    change Valued.v (f v)⁻¹ ≤ 1
    rw [map_inv₀, hfv v, inv_one]⟩
  have hxy : x * y = 1 := by
    refine Subtype.ext (funext fun v => ?_)
    exact mul_inv_cancel₀ (hfne v)
  have hyx : y * x = 1 := by rw [mul_comm, hxy]
  refine ⟨⟨x, y, hxy, hyx⟩, fun v => ?_, fun v hv => ?_⟩
  · exact ord_eq_zero_of_valued v _ (hfv v)
  · change f v = _
    simp only [hf, if_pos hv]
    rfl

theorem omega_one {χ : DirichletCharacter ℂ N} {ω : HeckeCharacter ℚ} (hω : Ad3.R.Om N χ ω)
    {u : FiniteAdelicGL ℚ 2} (h1 : (u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 - 1 ∈ levelIdeal N) {d : 𝔸fˣ}
    (hord : ∀ v, GroundTheory.LocalField.ord ((Ad3.R.lf v d : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0)
    (hd : ∀ v, Ad3.pOf v ∣ N → ((Ad3.R.lf v d : (Ad3.Qv v)ˣ) : Ad3.Qv v) = GodementSection.glAt v u 1 1) :
    (ω.toIdele (IdeleGroup.ofFinite d) : ℂ) = 1 := by
  have := hω.val d 1 hord (fun v hv => ?_)
  · simpa using this
  · obtain ⟨t, ht, hteq⟩ := h1
    have hN0 : ((N : ℕ) : Ad3.Qv v) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have e : GodementSection.glAt v u 1 1 - (((1 : ℤ)) : Ad3.Qv v) = ((N : ℕ) : Ad3.Qv v) * t v := by
      have h2 := congrArg (GodementSection.adeleAt v) hteq
      rw [map_sub, map_one, map_mul, map_natCast] at h2
      rw [Int.cast_one]
      exact h2
    rw [hd v hv, e, inv_mul_cancel_left₀ hN0]
    exact (GroundTheory.Global.mem_valuationInteger_iff v _).2 (ht v)

theorem unipotent_eq_adelic (x : 𝔸[ℚ]) : Ad3.uni2 x = unipAdele x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change _ = unipMatrix (n := 2) (r := 1) (fun _ => x) a b
  rw [unipMatrix_apply]
  fin_cases a <;> fin_cases b <;> simp [Ad3.uni2]

theorem setIntegral_eq_level {φ : AdelicGL ℚ 2 → ℂ}
    (hl : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL ℚ 2), φ (diagonal ℚ 2 γ * g) = φ g)
    (h : GL (Fin 2) ℝ) {w : FiniteAdelicGL ℚ 2} {M : ℕ} [NeZero M]
    (hinv : ∀ y ∈ levelIdeal M, ∀ g', φ (g' * finEmb ℚ 2 (w⁻¹ * unipFin y * w)) = φ g') :
    ∫ x in fundamentalSet ℚ, φ (unipAdele x * (realEmb h * finEmb ℚ 2 w)) ∂adeleMeasure ℚ =
      levelConstant M • ∫ t in (0 : ℝ)..M, φ (realEmb (unipReal t * h) * finEmb ℚ 2 w) := by
  set G : ℝ → ℂ := fun t => φ (realEmb (unipReal t * h) * finEmb ℚ 2 w)
  have hfd : ∫ x in fundamentalSet ℚ, φ (unipAdele x * (realEmb h * finEmb ℚ 2 w)) ∂adeleMeasure ℚ =
      ∫ x in levelDomain M, φ (unipAdele x * (realEmb h * finEmb ℚ 2 w)) ∂adeleMeasure ℚ := by
    refine (isAddFundamentalDomain_fundamentalSet ℚ).setIntegral_eq
      (isAddFundamentalDomain_levelDomain M) fun ξ x => ?_
    obtain ⟨_, q, rfl⟩ := ξ
    change φ (unipAdele (algebraMap ℚ 𝔸[ℚ] q + x) * _) = _
    rw [unipAdele_add, unipAdele_algebraMap, mul_assoc, hl]
  rw [hfd]
  have heq : Set.EqOn (fun x : 𝔸[ℚ] => φ (unipAdele x * (realEmb h * finEmb ℚ 2 w)))
      (fun x => G (RationalIdeles.realEquiv x.1)) (levelDomain M) := by
    intro x hx
    have e : unipAdele x * (realEmb h * finEmb ℚ 2 w) =
        realEmb (unipReal (RationalIdeles.realEquiv x.1) * h) * finEmb ℚ 2 w *
          finEmb ℚ 2 (w⁻¹ * unipFin x.2 * w) := by
      rw [unipAdele_eq]
      apply (prodEquiv ℚ 2).injective
      simp only [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
      rw [Prod.mk.injEq]
      exact ⟨rfl, by group⟩
    simp only [G]
    rw [e, hinv _ hx.2]
  rw [setIntegral_congr_fun (measurableSet_levelDomain M) heq]
  set A : Set (InfiniteAdeleRing ℚ) := RationalIdeles.realEquiv ⁻¹' Set.Ico (0 : ℝ) M
  calc ∫ x in levelDomain M, G (RationalIdeles.realEquiv x.1) ∂adeleMeasure ℚ
      = ∫ x in (A ×ˢ levelIdeal M : Set (InfiniteAdeleRing ℚ × 𝔸f)), G (RationalIdeles.realEquiv x.1)
          ∂((infiniteAdeleMeasure ℚ).prod (finiteAdeleMeasure ℚ)) := rfl
    _ = (finiteAdeleMeasure ℚ (levelIdeal M)).toReal •
          ∫ x in A, G (RationalIdeles.realEquiv x) ∂infiniteAdeleMeasure ℚ := by
        have hf := integral_fun_fst (μ := (infiniteAdeleMeasure ℚ).restrict A)
          (ν := (finiteAdeleMeasure ℚ).restrict (levelIdeal M))
          (fun a : InfiniteAdeleRing ℚ => G (RationalIdeles.realEquiv a))
        rw [← Measure.prod_restrict]
        refine hf.trans ?_
        rw [measureReal_restrict_apply_univ, measureReal_def]
    _ = (finiteAdeleMeasure ℚ (levelIdeal M)).toReal •
          ∫ t in Set.Ico (0 : ℝ) M, G t ∂(infiniteAdeleMeasure ℚ).map realHomeomorph := by
        congr 1
        exact (realHomeomorph.measurableEmbedding.setIntegral_map (μ := infiniteAdeleMeasure ℚ)
          G (Set.Ico (0 : ℝ) M)).symm
    _ = levelConstant M • ∫ t in (0 : ℝ)..M, G t := by
        rw [map_infiniteAdeleMeasure, Measure.restrict_smul, integral_smul_nnreal_measure,
          intervalIntegral.integral_of_le (Nat.cast_nonneg M), integral_Ico_eq_integral_Ioo,
          ← integral_Ioc_eq_integral_Ioo, levelConstant, NNReal.smul_def, smul_smul]

theorem integral_zero (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (γ : GL (Fin 2) ℚ)
    {h : GL (Fin 2) ℝ} (hdet : 0 < ((toReal γ)⁻¹ * h).det.val) {M : ℕ} (hM : 0 < M)
    (hp₁ : ∃ s ∈ Gamma1 N, Matrix.SpecialLinearGroup.mapGL ℝ s * toReal γ⁻¹ = toReal γ⁻¹ * unipReal (M : ℝ))
    (hp₂ : ∃ s ∈ Gamma1 N, Matrix.SpecialLinearGroup.mapGL ℝ s * toReal (γ⁻¹ * epsilon) =
      toReal (γ⁻¹ * epsilon) * unipReal (M : ℝ)) :
    ∫ t in (0 : ℝ)..M, archLift k f ((toReal γ)⁻¹ * (unipReal t * h)) = 0 := by
  have hsplit : ((toReal γ)⁻¹ * h).det.val = ((γ.det.val : ℚ) : ℝ)⁻¹ * h.det.val := by
    rw [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val, det_toReal]
  rcases lt_or_gt_of_ne (Units.ne_zero γ.det) with hneg | hpos
  · have hh : h.det.val < 0 := by
      rw [hsplit] at hdet
      have : ((γ.det.val : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
      have : ((γ.det.val : ℚ) : ℝ)⁻¹ < 0 := inv_lt_zero.2 this
      nlinarith
    set δ := γ⁻¹ * epsilon with hδdef
    have hδ : 0 < (δ.det.val : ℚ) := by
      simp only [δ, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      have hε : (epsilon.det.val : ℚ) = -1 := by
        have := det_toReal_epsilon
        rw [det_toReal] at this
        exact_mod_cast this
      rw [hε]
      have : (γ.det.val : ℚ)⁻¹ < 0 := inv_lt_zero.2 hneg
      linarith
    set h' := toReal epsilon * h
    have hh' : 0 < (unipReal (-(M : ℝ)) * h').det.val := by
      simp only [h', map_mul, Units.val_mul, det_unipReal, det_toReal_epsilon, one_mul]
      linarith
    have hrew : ∀ t : ℝ, archLift k f ((toReal γ)⁻¹ * (unipReal t * h)) =
        archLift k f (toReal δ * (unipReal (-t) * h')) := by
      intro t
      congr 1
      simp only [δ, h', map_mul, map_inv]
      have e := toReal_epsilon_mul_unipReal_mul (-t)
      rw [neg_neg] at e
      rw [← e]
      group
    simp_rw [hrew]
    rw [intervalIntegral.integral_comp_neg (fun s => archLift k f (toReal δ * (unipReal s * h'))),
      neg_zero]
    have hshift := intervalIntegral.integral_comp_sub_right
      (fun s => archLift k f (toReal δ * (unipReal s * h'))) (M : ℝ) (a := 0) (b := M)
    simp only [zero_sub, sub_self] at hshift
    rw [← hshift]
    have hsub : ∀ s : ℝ, archLift k f (toReal δ * (unipReal (s - M) * h')) =
        archLift k f (toReal δ * (unipReal s * (unipReal (-(M : ℝ)) * h'))) := by
      intro s
      rw [sub_eq_add_neg, unipReal_add, mul_assoc]
    simp_rw [hsub]
    obtain ⟨s, hs, hreal⟩ := hp₂
    exact integral_archLift_eq_zero₁ f hδ hM hs hreal hh'
  · have hh : 0 < h.det.val := by
      rw [hsplit] at hdet
      have : (0 : ℝ) < ((γ.det.val : ℚ) : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hpos)
      exact pos_of_mul_pos_right hdet this.le
    have hδ : 0 < ((γ⁻¹).det.val : ℚ) := by
      rw [map_inv, Units.val_inv_eq_inv_val]
      exact inv_pos.2 hpos
    obtain ⟨s, hs, hreal⟩ := hp₁
    have := integral_archLift_eq_zero₁ f hδ hM hs hreal hh
    rwa [map_inv] at this

theorem constantTerm_lift_eq_zero {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)} {ω : HeckeCharacter ℚ}
    {φ : AdelicGL ℚ 2 → ℂ} (hω : Ad3.R.Om N χ ω) (hL : Ad3.R.Lift k N f ω φ)
    (h : GL (Fin 2) ℝ) (w : FiniteAdelicGL ℚ 2) :
    ∫ x in fundamentalSet ℚ, φ (unipAdele x * (realEmb h * finEmb ℚ 2 w)) ∂adeleMeasure ℚ = 0 := by
  obtain ⟨γ, u, hu, hw, hdet⟩ := exists_finiteDiagonal_mul_pos N w h
  obtain ⟨M₁, hM₁, hc⟩ := exists_level_conj₁ N w
  obtain ⟨D₁, hD₁, hp₁⟩ := exists_period₁ (N := N) γ⁻¹
  obtain ⟨D₂, hD₂, hp₂⟩ := exists_period₁ (N := N) (γ⁻¹ * epsilon)
  have hM : 0 < M₁ * D₁ * D₂ := Nat.mul_pos (Nat.mul_pos hM₁ hD₁) hD₂
  obtain ⟨M, hMdef⟩ : ∃ M, M = M₁ * D₁ * D₂ := ⟨_, rfl⟩
  rw [← hMdef] at hM
  have : NeZero M := ⟨hM.ne'⟩
  have hinv : ∀ y ∈ levelIdeal M, ∀ g', φ (g' * finEmb ℚ 2 (w⁻¹ * unipFin y * w)) = φ g' := by
    intro y hy g'
    obtain ⟨h1, h2⟩ := hc y (levelIdeal_mono ⟨D₁ * D₂, by rw [hMdef]; ring⟩ hy)
    obtain ⟨d, hord, hd⟩ := exists_idele h1
    rw [hL.level _ h1 d hord hd g', omega_one hω h2 hord hd, one_mul]
  rw [setIntegral_eq_level hL.left h hinv]
  refine smul_eq_zero_of_right _ ?_
  obtain ⟨d, hord, hd⟩ := exists_idele hu
  have hdetn : ∀ t : ℝ, ((toReal γ)⁻¹ * (unipReal t * h)).det.val = ((toReal γ)⁻¹ * h).det.val := by
    intro t
    simp only [map_mul, Units.val_mul, det_unipReal, one_mul]
  have hint : ∀ t : ℝ, φ (realEmb (unipReal t * h) * finEmb ℚ 2 w) =
      (ω.toIdele (IdeleGroup.ofFinite d) : ℂ) * archLift (k : ℤ) f ((toReal γ)⁻¹ * (unipReal t * h)) := by
    intro t
    have e1 : realEmb (unipReal t * h) * finEmb ℚ 2 (finiteDiagonal ℚ 2 γ * u) =
        realEmb (unipReal t * h) * finEmb ℚ 2 (finiteDiagonal ℚ 2 γ) * finEmb ℚ 2 u := by
      rw [map_mul (finEmb ℚ 2), mul_assoc]
    rw [hw, e1, hL.level u hu d hord hd]
    congr 1
    rw [← hL.real _ (by rw [hdetn]; exact hdet), ← hL.left γ⁻¹]
    congr 1
    apply (prodEquiv ℚ 2).injective
    simp only [map_mul, map_inv, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk,
      Prod.inv_mk, inv_one, mul_one, one_mul, inv_mul_cancel]
  simp_rw [hint]
  rw [intervalIntegral.integral_const_mul,
    integral_zero f γ hdet hM (hp₁ M ⟨M₁ * D₂, by rw [hMdef]; ring⟩)
      (hp₂ M ⟨M₁ * D₁, by rw [hMdef]; ring⟩), mul_zero]

theorem lift_cuspidal : Ad3.R.B0 → Ad3.R.ConstantTermVanishingAlt := by
  intro _ k N _ _ χ _ f a _ _ ω φ hω hL g
  have e : ∀ x : 𝔸[ℚ], φ (Ad3.uni2 x * g) =
      φ (unipAdele x * (realEmb (realPart g) * finEmb ℚ 2 (prodEquiv ℚ 2 g).2)) := fun x => by
    rw [unipotent_eq_adelic, realEmb_realPart_mul_finEmb]
  simp_rw [e]
  exact constantTerm_lift_eq_zero hω hL _ _

end GlobalTheory.CompanionTheory.LiftCusp

end
