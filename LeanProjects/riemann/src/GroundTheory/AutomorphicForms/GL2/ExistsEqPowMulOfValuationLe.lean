import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
import GroundTheory.AutomorphicForms.MeasuresGL
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal ValuativeRel Topology Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem det_ne_zero (g : GL (Fin n) F) : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 :=
  (Matrix.GeneralLinearGroup.det g).ne_zero

theorem ordDet_mul (g h : GL (Fin n) F) : ordDet (g * h) = ordDet g + ordDet h := by
  rw [ordDet, ordDet, ordDet, Units.val_mul, Matrix.det_mul,
    LocalField.ord_mul (det_ne_zero g) (det_ne_zero h)]

theorem detPow_mul (g h : GL (Fin n) F) (s : ℂ) :
    detPow (g * h) s = detPow g s * detPow h s := by
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, detPow_eq_qs_zpow, ordDet_mul,
    zpow_add₀ (qs_ne_zero s)]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem det_mem_integer {X : Matrix (Fin n) (Fin n) F} (hX : ∀ i j, X i j ∈ 𝒪[F]) :
    X.det ∈ 𝒪[F] := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => hX _ _) _

theorem ord_nonneg_of_mem_integer {x : F} (hx : x ∈ 𝒪[F]) (h0 : x ≠ 0) : 0 ≤ LocalField.ord x :=
  (LocalField.mem_valBall_iff_le_ord h0).1 (LocalField.mem_valBall_zero_iff.2 hx)

theorem ordDet_of_mem_integralGL {k : GL (Fin n) F} (hk : k ∈ integralGL F n) : ordDet k = 0 := by
  obtain ⟨h1, h2⟩ := (mem_integralGL_iff F n).1 hk
  have hd1 := ord_nonneg_of_mem_integer (det_mem_integer h1) (det_ne_zero k)
  have hd2 := ord_nonneg_of_mem_integer (det_mem_integer h2) (det_ne_zero k⁻¹)
  have hsum := ordDet_mul k k⁻¹
  rw [mul_inv_cancel] at hsum
  have h0 : ordDet (1 : GL (Fin n) F) = 0 := by
    simp [ordDet, LocalField.ord_one]
  rw [h0] at hsum
  unfold ordDet at hsum ⊢
  omega

theorem detPow_of_mem_integralGL {k : GL (Fin n) F} (hk : k ∈ integralGL F n) (s : ℂ) :
    detPow k s = 1 := by
  rw [detPow_eq_qs_zpow, ordDet_of_mem_integralGL hk, zpow_zero]

variable (F n) in

theorem isClopen_shell (k : ℤ) : IsClopen {g : GL (Fin n) F | ordDet g = k} := by
  have hcont : Continuous fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F).det :=
    Units.continuous_val.matrix_det
  have hset : {g : GL (Fin n) F | ordDet g = k} = (fun g : GL (Fin n) F =>
      (g : Matrix (Fin n) (Fin n) F).det) ⁻¹'
        ((LocalField.valBall F k : Set F) \ (LocalField.valBall F (k + 1) : Set F)) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_sdiff, SetLike.mem_coe,
      LocalField.mem_valBall_iff_le_ord (det_ne_zero g), ordDet]
    omega
  rw [hset]
  have c1 : IsClopen (LocalField.valBall F k : Set F) :=
    ⟨LocalField.isClosed_valBall k, LocalField.isOpen_valBall k⟩
  have c2 : IsClopen (LocalField.valBall F (k + 1) : Set F) :=
    ⟨LocalField.isClosed_valBall (k + 1), LocalField.isOpen_valBall (k + 1)⟩
  exact (c1.diff c2).preimage hcont

variable (F n) in

theorem isCompact_shell (A : ℕ) (k : ℤ) :
    IsCompact {g : GL (Fin n) F | (∀ i j, (uniformizer F : F) ^ A * g i j ∈ 𝒪[F]) ∧ ordDet g = k} := by
  classical
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hord : LocalField.ord (uniformizer F : F) = 1 :=
    LocalField.ord_uniformizer (irreducible_uniformizer F)
  set B : ℤ := (A : ℤ) - ((n : ℤ) * A + k) with hB
  let box : ℤ → Set (Matrix (Fin n) (Fin n) F) := fun t =>
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (LocalField.valBall F t : Set F)
  have hbox : ∀ t, IsCompact (box t) := fun t =>
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => LocalField.isCompact_valBall t
  have hT : IsCompact (Units.embedProduct (Matrix (Fin n) (Fin n) F) ⁻¹'
      (box (-(A : ℤ)) ×ˢ (MulOpposite.unop ⁻¹' box B))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hbox _).prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 (hbox B)))
  refine hT.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {g : GL (Fin n) F | ∀ i j, (uniformizer F : F) ^ A * g i j ∈ 𝒪[F]} := by
      have : {g : GL (Fin n) F | ∀ i j, (uniformizer F : F) ^ A * g i j ∈ 𝒪[F]} =
          ⋂ i, ⋂ j, (fun g : GL (Fin n) F => (uniformizer F : F) ^ A * g i j) ⁻¹'
            (𝒪[F] : Set F) := by
        ext g; simp
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      rw [← LocalField.coe_valBall_zero]
      exact (LocalField.isClosed_valBall 0).preimage
        (continuous_const.mul (continuous_entry F n i j))
    exact h1.inter (isClopen_shell F n k).isClosed
  · rintro g ⟨hA, hk⟩
    simp only [Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op]
    have hϖA : (uniformizer F : F) ^ (-(A : ℤ)) ∈ LocalField.valBall F (-(A : ℤ)) := by
      rw [LocalField.mem_valBall_iff_le_ord (zpow_ne_zero _ hϖ), LocalField.ord_zpow hϖ, hord]
      simp
    have hϖA' : (uniformizer F : F) ^ A ∈ LocalField.valBall F (A : ℤ) := by
      rw [LocalField.mem_valBall_iff_le_ord (pow_ne_zero _ hϖ), LocalField.ord_pow hϖ, hord]
      simp
    refine ⟨fun i _ j _ => ?_, fun i _ j _ => ?_⟩
    · have h := LocalField.mul_mem_valBall hϖA (LocalField.mem_valBall_zero_iff.2 (hA i j))
      rw [add_zero, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hϖ, neg_add_cancel, zpow_zero,
        one_mul] at h
      exact h
    ·
      let Hm : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, hA i j⟩
      set c : F := (uniformizer F : F) ^ A with hc
      have hc0 : c ≠ 0 := pow_ne_zero _ hϖ
      have hH : (𝒪[F]).subtype.mapMatrix Hm = c • (g : Matrix (Fin n) (Fin n) F) := by
        ext i j; simp [Hm, c]
      have hdetG : IsUnit (g : Matrix (Fin n) (Fin n) F).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      have hinv : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
          c • ((𝒪[F]).subtype.mapMatrix Hm)⁻¹ := by
        rw [hH, Matrix.coe_units_inv, show c • (g : Matrix (Fin n) (Fin n) F) =
          (Units.mk0 c hc0) • (g : Matrix (Fin n) (Fin n) F) from rfl, Matrix.inv_smul' (A := (g : Matrix (Fin n) (Fin n) F)) (Units.mk0 c hc0) hdetG,
          Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, smul_smul, mul_inv_cancel₀ hc0,
          one_smul]
      have hdetH : ((𝒪[F]).subtype.mapMatrix Hm).det = c ^ n * (g : Matrix (Fin n) (Fin n) F).det := by
        rw [hH, Matrix.det_smul, Fintype.card_fin]
      have hval : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
          c * ((c ^ n * (g : Matrix (Fin n) (Fin n) F).det)⁻¹ * ((Matrix.adjugate Hm i j : 𝒪[F]) : F)) := by
        rw [hinv, Matrix.inv_def, ← RingHom.map_adjugate, Ring.inverse_eq_inv', hdetH]
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
          Subring.coe_subtype]
      show _ ∈ LocalField.valBall F B
      rw [hval]
      have hd : (c ^ n * (g : Matrix (Fin n) (Fin n) F).det)⁻¹ ∈
          LocalField.valBall F (-((n : ℤ) * A + k)) := by
        have hne : c ^ n * (g : Matrix (Fin n) (Fin n) F).det ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ hc0) (det_ne_zero g)
        rw [LocalField.mem_valBall_iff_le_ord (inv_ne_zero hne), LocalField.ord_inv hne,
          LocalField.ord_mul (pow_ne_zero _ hc0) (det_ne_zero g), LocalField.ord_pow hc0,
          hc, LocalField.ord_pow hϖ, hord]
        have : LocalField.ord (g : Matrix (Fin n) (Fin n) F).det = k := hk
        rw [this]
        linarith
      have h := LocalField.mul_mem_valBall hϖA' (LocalField.mul_mem_valBall hd
        (LocalField.mem_valBall_zero_iff.2 (Matrix.adjugate Hm i j).2))
      have hB' : (A : ℤ) + (-((n : ℤ) * A + k) + 0) = B := by rw [hB]; ring
      rw [hB'] at h
      exact h

theorem exists_eq_pow_mul_of_valuation_le {y : F} {m : ℕ}
    (h : valuation F y ≤ valuation F (uniformizer F : F) ^ m) :
    ∃ a ∈ 𝒪[F], y = (uniformizer F : F) ^ m * a := by
  rw [← mem_valBall_iff_exists, LocalField.mem_valBall]
  have hpow : LocalField.normalizedValuation F ((uniformizer F : F) ^ m) =
      WithZero.exp (-(m : ℤ)) := by
    rw [map_pow, LocalField.normalizedValuation_uniformizer (irreducible_uniformizer F),
      ← WithZero.exp_nsmul]
    simp
  rw [← hpow, LocalField.normalizedValuation_le_iff, map_pow]
  exact h

theorem IsSchwartzBruhat.exists_congruence_invariant {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ m : ℕ, ∀ k ∈ congruenceSubgroup F n m, ∀ X : Matrix (Fin n) (Fin n) F,
      Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧ Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := by
  classical
  obtain ⟨r, A, hinv, hsupp⟩ := hΦ.exists_invariant
  have hk1 : ∀ k ∈ congruenceSubgroup F n (r + A), ∀ i j, ∃ a ∈ 𝒪[F],
      (k : Matrix (Fin n) (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j =
        (uniformizer F : F) ^ (r + A) * a := fun k hk i j =>
    exists_eq_pow_mul_of_valuation_le (((mem_congruenceSubgroup_iff F n).1 hk).2 i j)
  have key : ∀ k ∈ congruenceSubgroup F n (r + A), ∀ X : Matrix (Fin n) (Fin n) F,
      (∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F]) →
      Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧
        Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := by
    intro k hk X hX
    choose a ha hae using hk1 k hk
    constructor
    · have : (k : Matrix (Fin n) (Fin n) F) * X =
          X + ((k : Matrix (Fin n) (Fin n) F) - 1) * X := by
        rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
      rw [this, hinv X]
      intro i j
      refine ⟨∑ l, a i l * ((uniformizer F : F) ^ A * X l j),
        Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l) (hX l j), ?_⟩
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.sub_apply, hae i l, pow_add]
      ring
    · have : X * (k : Matrix (Fin n) (Fin n) F) =
          X + X * ((k : Matrix (Fin n) (Fin n) F) - 1) := by
        rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
      rw [this, hinv X]
      intro i j
      refine ⟨∑ l, ((uniformizer F : F) ^ A * X i l) * a l j,
        Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (ha l j), ?_⟩
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.sub_apply, hae l j, pow_add]
      ring
  refine ⟨r + A, fun k hk X => ?_⟩
  by_cases hX : ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F]
  · exact key k hk X hX
  have hΦX : Φ X = 0 := by
    by_contra h
    exact hX (hsupp X h)
  have hk' : k⁻¹ ∈ congruenceSubgroup F n (r + A) := inv_mem hk
  constructor
  · by_contra hne
    have hY := hsupp _ fun h => hne (by rw [h, hΦX])
    have := (key k⁻¹ hk' _ hY).1
    rw [Units.inv_mul_cancel_left] at this
    exact hne this.symm
  · by_contra hne
    have hY := hsupp _ fun h => hne (by rw [h, hΦX])
    have := (key k⁻¹ hk' _ hY).2
    rw [Units.mul_inv_cancel_right] at this
    exact hne this.symm

theorem IsSchwartzBruhat.comp_mul_left {Φ : Matrix (Fin n) (Fin n) F → ℂ} (hΦ : IsSchwartzBruhat Φ)
    (a : GL (Fin n) F) : IsSchwartzBruhat fun X => Φ ((a : Matrix (Fin n) (Fin n) F) * X) := by
  let e : Matrix (Fin n) (Fin n) F ≃ₜ Matrix (Fin n) (Fin n) F :=
    { toFun := fun X => (a : Matrix (Fin n) (Fin n) F) * X
      invFun := fun X => ((a⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X
      left_inv := fun X => Units.inv_mul_cancel_left a X
      right_inv := fun X => Units.mul_inv_cancel_left a X
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  exact ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩

theorem exists_qs_eq {x : ℂ} (hx : x ≠ 0) :
    ∃ s : ℂ, qs F s = x ∧ s.re = -Real.logb (LocalField.residueCard F) ‖x‖ := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  have hL : 0 < Real.log (LocalField.residueCard F) := Real.log_pos hq
  have hL' : (Real.log (LocalField.residueCard F) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  refine ⟨-(Complex.log x) / (Real.log (LocalField.residueCard F) : ℂ), ?_, ?_⟩
  · rw [qs, Complex.cpow_def_of_ne_zero (by exact_mod_cast LocalField.residueCard_ne_zero)]
    have hlog : Complex.log (LocalField.residueCard F : ℂ) =
        (Real.log (LocalField.residueCard F) : ℂ) := by
      rw [Complex.ofReal_log (by positivity), Complex.ofReal_natCast]
    rw [hlog, show (Real.log (LocalField.residueCard F) : ℂ) *
        -(-Complex.log x / (Real.log (LocalField.residueCard F) : ℂ)) = Complex.log x by
      field_simp]
    exact Complex.exp_log hx
  · rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re, Real.logb, neg_div]

theorem exists_re_of_norm_qs_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ‖qs F s‖ < ε := by
  have hq : (1 : ℝ) < LocalField.residueCard F := by exact_mod_cast LocalField.one_lt_residueCard
  refine ⟨-Real.logb (LocalField.residueCard F) ε, fun s hs => ?_⟩
  rw [norm_qs]
  calc (LocalField.residueCard F : ℝ) ^ (-s.re)
      < (LocalField.residueCard F : ℝ) ^ (Real.logb (LocalField.residueCard F) ε) :=
        (Real.rpow_lt_rpow_left_iff hq).2 (by linarith)
    _ = ε := Real.rpow_logb (by positivity) hq.ne' hε

end GodementJacquet

end GroundTheory.Automorphic
