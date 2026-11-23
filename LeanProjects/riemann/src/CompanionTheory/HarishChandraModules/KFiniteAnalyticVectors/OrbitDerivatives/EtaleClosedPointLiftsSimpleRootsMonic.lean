import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.HasDerivAtMatrixExpZero
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.HaarBumpFunctions.PoulsenSmoothVectorsDense
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound

open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.FinalFormK

open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul CompanionTheory.Zuck BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
open PI.UpqRep (InLieHpk)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem dense_sm' {n : ℕ} {G : Set (Mat n)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)} (hG : IsMatGroup G) (θ : Mat n →L[ℝ] Mat n)
    (hθ : ∀ x ∈ G, θ x = x⁻¹) (hσ : RepOn G σ) (hc : ∀ v, ContinuousOn (fun g => σ g v) G) :
    Dense {v | IsSm G σ v} := by
  let S : Submodule ℂ H :=
    { carrier := {x | IsSm G σ x}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := IsSm.zero
      smul_mem' := fun c _ hx => hx.smul c }
  change Dense (S : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
  intro z hz
  have hρ : ∀ u, Continuous fun x : MG G hG => σ x.mat u := fun u =>
    (hc u).comp_continuous MG.continuous_mat fun g => g.mem
  obtain ⟨V, hV, hclose⟩ := admitted.Gard.exists_nhds_close (fun x : MG G hG => σ x.mat) hρ
    (fun u => by show σ 1 u = u; rw [hσ.map_one]; rfl) (Submodule.span ℂ {z})
  obtain ⟨φ, hφ, hφV⟩ := exists_isBump hG θ hθ hV
  let Q : H →L[ℂ] H := Sᗮ.starProjection
  have hQ : Q (avg hG φ σ z) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).2 (S.le_orthogonal_orthogonal (isSm_avg hσ hc hφ z))
  have hQz : Q z = z := Submodule.starProjection_eq_self_iff.2 hz
  refine admitted.Gard.eq_zero_of_alt_alt (haar : Measure (MG G hG)) (fun x : MG G hG => Q ∘L σ x.mat)
    (fun u => Q.continuous.comp (hρ u)) (hφ.smooth.continuous.comp MG.continuous_mat)
    (HasCompactSupport.intro (isCompact_supp hφ.cpt) fun x hx => image_eq_zero_of_notMem_tsupport (f := φ) hx)
    (fun x => hφ.nonneg _) hφ.one z (fun x hx => ?_) ?_
  · have h1 := hclose x (hφV x hx) z (Submodule.mem_span_singleton_self z)
    refine le_trans ?_ h1
    conv_lhs => rw [← hQz]
    show ‖Q (σ x.mat (Q z)) - Q z‖ ≤ _
    rw [← map_sub, hQz]
    exact Sᗮ.norm_starProjection_apply_le _
  · rw [← hQ, avg, apply_integral Q hφ.smooth.continuous hφ.cpt (hρ z)]
    rfl

variable {k r : ℕ}

theorem hGG (k r : ℕ) : IsMatGroup (GG k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r

theorem URep.dense (U : URep k r) : Dense {v | IsSm (GG k r) U.R.σ v} :=
  dense_sm' (hGG k r) (theta k r) theta_eq U.repOn U.rep.2.2

theorem hLie : ∀ X, InLieHpk k r X → ∀ t, ex X t ∈ GG k r := fun _ hX t => ex_mem_of_lie hX t

theorem act_coe (X : Obj k r) {g : Mx k r} (hg : g ∈ GG k r) (x : M X) (c : X.1.ι) :
    ((act X g x c : X.2.R.smSub) : X.2.R.H) = ∑ d, X.1.ρ g c d • X.2.R.σ g (x d) := by
  simp only [Zuck.act, mAct, dOp, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, LinearMap.compLeft_apply, Function.comp_apply, Submodule.coe_sum, Submodule.coe_smul,
    URep.sig_coe _ hg]

theorem sn_eq (X : Obj k r) (W : List (Mx k r)) (x : M X) : sn X W x = ∑ c, ‖dsW X.2.R.σ W (x c : X.2.R.H)‖ := by
  simp only [sn, dsigW_eq']

theorem sum_sn (X : Obj k r) (Ws : List (List (Mx k r))) (x : M X) :
    (Ws.map fun W => sn X W x).sum = ∑ c, nu X.2.R.σ Ws (x c : X.2.R.H) := by
  induction Ws with
  | nil => simp [nu]
  | cons W Ws ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [sn_eq, nu, List.map_cons, List.sum_cons, Finset.sum_add_distrib]

theorem exists_common {ι : Type} [Fintype ι] {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] {σ : Mx k r → (H →L[ℂ] H)} {T : ι → H → E}
    (h : ∀ c, Bdd (GG k r) (InLieHpk k r) σ (T c)) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ W ∈ Ws, LieWd k r W) ∧
      ∀ c v, IsSm (GG k r) σ v → ‖T c v‖ ≤ C * nu σ Ws v := by
  obtain ⟨C, Ws, hW, hb⟩ := Bdd.sum (T := fun c v => ‖T c v‖) Finset.univ fun c _ => by
    obtain ⟨C, Ws, hW, hb⟩ := h c
    exact ⟨C, Ws, hW, fun v hv => by rw [norm_norm]; exact hb v hv⟩
  refine ⟨|C|, Ws, abs_nonneg _, hW, fun c v hv => ?_⟩
  refine le_trans ?_ ((hb v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (nu_nonneg Ws v)))
  exact (Finset.single_le_sum (f := fun c => ‖T c v‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ c)).trans
    (le_abs_self _)

theorem etaleClosed_point_lifts_simple_roots_monic : Lift := by
  classical
  intro k r X T f hX ⟨C, Ws, hW, hb⟩ hf
  let t : X.1.ι → X.2.R.H → T.R.H := fun c v =>
    if hv : IsSm (GG k r) X.2.R.σ v then f (Pi.single c ⟨v, hv⟩) else 0
  have ht : ∀ c (v : X.2.R.smSub), t c v = f (Pi.single c v) := fun c v => dif_pos v.2
  have htw : TwInt (GG k r) (InLieHpk k r) X.2.R.σ T.R.σ (fun g c d => X.1.ρ g d c) t :=
    { lin := fun c => ⟨fun v w hv hw => by
          rw [ht c ⟨v, hv⟩, ht c ⟨w, hw⟩, ← map_add, ← Pi.single_add]
          exact ht c (⟨v, hv⟩ + ⟨w, hw⟩), fun a v hv => by
          rw [ht c ⟨v, hv⟩, ← map_smul, ← Pi.single_smul]
          exact ht c (a • ⟨v, hv⟩)⟩
      bdd := fun c => ⟨C, Ws, hW, fun v hv => by
        rw [ht c ⟨v, hv⟩]
        refine (hb _).trans (le_of_eq ?_)
        rw [sum_sn, Finset.sum_eq_single c (fun d _ hd => ?_) (by simp), Pi.single_eq_same]
        rw [Pi.single_eq_of_ne hd]
        refine List.sum_eq_zero fun a ha => ?_
        obtain ⟨W, hW0, rfl⟩ := List.mem_map.1 ha
        have := dsW_smul X.2.repOn (IsSm.zero (G := GG k r) (σ := X.2.R.σ)) 0 fun Y hY => hLie Y (hW W hW0 Y hY)
        simpa using this⟩
      eqv := fun g hg c v hv => by
        rw [ht c ⟨v, hv⟩, ← hf g hg]
        have e : act X g (Pi.single c ⟨v, hv⟩) =
            ∑ d, X.1.ρ g d c • Pi.single d (⟨X.2.R.σ g v, hv.apply X.2.repOn hg⟩ : X.2.R.smSub) := by
          funext e
          refine Subtype.ext ?_
          rw [act_coe X hg, Finset.sum_eq_single c (fun d _ hd => by simp [Pi.single_eq_of_ne hd]) (by simp),
            Finset.sum_apply, Finset.sum_eq_single e (fun d _ hd => by simp [Pi.single_eq_of_ne' hd]) (by simp)]
          simp
        rw [e, _root_.map_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [map_smul, ← ht] }
  have hM : ∀ c d, SmOn (GG k r) fun g => X.1.ρ g d c := fun c d => hX.smooth d c
  have hM1 : ∀ c d, X.1.ρ 1 d c = if c = d then 1 else 0 := fun c d => by
    rw [hX.one, Matrix.one_apply]; exact if_congr eq_comm rfl rfl
  have hfx : ∀ x : M X, f x = ∑ c, t c (x c) := fun x => by
    conv_lhs => rw [← Finset.univ_sum_single x, _root_.map_sum]
    exact Finset.sum_congr rfl fun c _ => (ht c (x c)).symm
  have hsum : ∀ (x : M X) (W : List (Mx k r)), LieWd k r W → ∀ s : Finset X.1.ι,
      IsSm (GG k r) T.R.σ (∑ c ∈ s, t c (x c)) ∧
        dsW T.R.σ W (∑ c ∈ s, t c (x c)) = ∑ c ∈ s, dsW T.R.σ W (t c (x c)) := by
    intro x W hW0 s
    have hWG : LieW (GG k r) W := fun Y hY => hLie Y (hW0 Y hY)
    induction s using Finset.induction_on with
    | empty => exact ⟨by simpa using IsSm.zero, by
        simpa using dsW_smul T.repOn (IsSm.zero (G := GG k r) (σ := T.R.σ)) 0 hWG⟩
    | insert i s hi ih =>
      have hi' := htw.isSm X.2.repOn hLie hM i (x i).2
      rw [Finset.sum_insert hi, Finset.sum_insert hi, dsW_add T.repOn hi' ih.1 hWG, ih.2]
      exact ⟨hi'.add ih.1, rfl⟩
  have hsm : ∀ x : M X, f x ∈ T.R.smSub := fun x => by
    rw [hfx]; exact (hsum x [] (by simp [LieWd]) _).1
  refine ⟨LinearMap.pi fun _ => f.codRestrict _ hsm, ⟨fun W hW0 => ?_, fun g hg => ?_⟩, fun x => rfl⟩
  · obtain ⟨D, Ws', hD, hW', hb'⟩ := exists_common fun c =>
      htw.bdd_dsW X.2.repOn T.repOn X.2.rep.2.1 (URep.dense X.2) hLie hM hM1 hW0 c
    refine ⟨D, Ws', hW', fun x => ?_⟩
    rw [sum_sn, sn_eq, Finset.mul_sum]
    show ∑ _c : Unit, ‖dsW T.R.σ W (f x)‖ ≤ _
    rw [Fintype.sum_unique, hfx, (hsum x W hW0 _).2]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => hb' c _ (x c).2)
  · refine LinearMap.ext fun x => funext fun u => Subtype.ext ?_
    show f (act X g x) = _
    rw [LinearMap.comp_apply, act_coe (one T) hg, hf g hg]
    show _ = ∑ d : Unit, (1 : Matrix Unit Unit ℂ) u d • T.R.σ g (f x)
    simp

abbrev GM (k r : ℕ) : Type := MG (GG k r) (hGG k r)

theorem isHaarOn_map : PI.BesselPeriodGGP.IsHaarOn (k := k) (r := r) (GG k r)
    ((haar : Measure (GM k r)).map MG.toM) := by
  have hE := MG.measurableEmbedding_toM (hG := hGG k r)
  refine ⟨hE.sigmaFinite_map, fun h => ?_, ?_, fun s hs => ?_⟩
  · have := congrArg (fun m : Measure (MtM (2 * r + k + 1)) => m univ) h
    simp only [hE.map_apply, preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact (isOpen_univ.measure_pos haar univ_nonempty).ne' this
  · rw [hE.map_apply]
    convert measure_empty (μ := (haar : Measure (GM k r)))
    ext x
    exact ⟨fun h => h x.mem, False.elim⟩
  · have hm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
      refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
      show Measurable fun x : Formalism.QuantumDeterminants.Mt k r => ∑ l, s i l * x l j
      fun_prop
    rw [Measure.map_map hm hE.measurable]
    have : (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s ∘ MG.toM : GM k r → _) = MG.toM ∘ fun x => MG.mk (hGG k r) s hs * x :=
      rfl
    rw [this, ← Measure.map_map hE.measurable (measurable_const_mul _), map_mul_left_eq_self]

theorem integrable_gN [(haar : Measure (GM k r)).IsInvInvariant] :
    Integrable (fun g : GM k r => B.gN g.mat ^ (-(((2 * r + k + 1) ^ 2 + 1 : ℕ) : ℝ))) haar := by
  have hE := MG.measurableEmbedding_toM (hG := hGG k r)
  have hR : (haar : Measure (GM k r)).IsMulRightInvariant := by
    rw [← Measure.inv_eq_self (haar : Measure (GM k r))]; infer_instance
  have hH : B.IsHaarOn (B.GV k r) ((haar : Measure (GM k r)).map MG.toM) :=
    { conc := isHaarOn_map.2.2.1
      left := isHaarOn_map.2.2.2
      right := fun s hs => by
        have hm : Measurable (B.rmulF s : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) := by
          refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
          show Measurable fun x : Formalism.QuantumDeterminants.Mt k r => ∑ l, x i l * s l j
          fun_prop
        rw [Measure.map_map hm hE.measurable]
        have : (B.rmulF s ∘ MG.toM : GM k r → _) = MG.toM ∘ fun x => x * MG.mk (hGG k r) s hs :=
          rfl
        rw [this, ← Measure.map_map hE.measurable (measurable_mul_const _), map_mul_right_eq_self]
      finite_compact := fun K hK => by
        rw [hE.map_apply]
        exact (MG.isClosedEmbedding_mat.isCompact_preimage hK).measure_lt_top
      ne_zero := isHaarOn_map.2.1 }
  have h := Formalism.FourierDecayAlt.P.norm_power_integrable_sharp k r _ (((2 * r + k + 1) ^ 2 + 1 : ℕ) : ℝ) hH (by
    unfold B.AB
    push_cast
    nlinarith [sq_nonneg ((k : ℝ) - 1), (Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
  rw [hE.lintegral_map] at h
  have hc : Continuous fun g : GM k r => B.gN g.mat :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp (MG.continuous_mat.matrix_elem i j))
  refine ⟨(hc.measurable.pow_const _).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Real.rpow_nonneg (Real.sqrt_nonneg _) _)).2 h

theorem inv_of_ds {U : URep k r} (hU : U.DS) : (haar : Measure (GM k r)).IsInvInvariant := by
  obtain ⟨ε, μ, -, P, hP, -⟩ := hU
  exact isInvInvariant_haar hP.1 _

theorem schur_GM {U : URep k r} (hU : U.DS) : ∃ d : ℝ, 0 < d ∧ ∀ v w v' w' : U.R.H,
    ∫ g : GM k r, ⟪w, U.R.σ g.mat v⟫_ℂ * star ⟪w', U.R.σ g.mat v'⟫_ℂ ∂haar = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ) := by
  obtain ⟨ε, μ, h⟩ := hU
  obtain ⟨d, hd, hS⟩ := CompanionTheory.LimBd.SchurHpk.threeDimData_schurH k r ε μ U.R.H U.R.σ _ h.1 h.2 isHaarOn_map
  refine ⟨d, hd, fun v w v' w' => ?_⟩
  rw [← (hS v w v' w').2, (MG.measurableEmbedding_toM (hG := hGG k r)).integral_map]
  rfl

theorem inner_inv (U : URep k r) (g : GM k r) (v w : U.R.H) :
    ⟪w, U.R.σ (g⁻¹).mat v⟫_ℂ = star ⟪v, U.R.σ g.mat w⟫_ℂ := by
  have := inner_map_left (σ := homMG (hGG k r) U.repOn) (fun g => U.rep.2.1 _ g.mem) g w v
  rw [Complex.star_def, inner_conj_symm]
  exact this.symm

def cf (X : Obj k r) (c : X.1.ι) (w : X.2.R.H) (x : M X) (g : GM k r) : ℂ :=
  ⟪w, ((act X (g⁻¹).mat x c : X.2.R.smSub) : X.2.R.H)⟫_ℂ

theorem cf_eq (X : Obj k r) (c : X.1.ι) (w : X.2.R.H) (x : M X) (g : GM k r) :
    cf X c w x g = ∑ d, X.1.ρ (g⁻¹).mat c d * ⟪w, X.2.R.σ (g⁻¹).mat (x d)⟫_ℂ := by
  simp only [cf, act_coe X (g⁻¹).mem, inner_sum, inner_smul_right]

theorem continuous_sig (U : URep k r) (v : U.R.H) : Continuous fun g : GM k r => U.R.σ g.mat v :=
  (U.rep.2.2 v).comp_continuous MG.continuous_mat fun g => g.mem

theorem continuous_rho {F : FRep k r} (hF : F.OK) (c d : F.ι) : Continuous fun g : GM k r => F.ρ g.mat c d :=
  (SmOn.continuousOn (A := GG k r) (hF.smooth c d)).comp_continuous MG.continuous_mat fun g => g.mem

theorem continuous_cf {X : Obj k r} (hX : X.1.OK) (c : X.1.ι) (w : X.2.R.H) (x : M X) : Continuous (cf X c w x) := by
  have : cf X c w x = _ := funext (cf_eq X c w x)
  rw [this]
  exact continuous_finsetSum _ fun d _ => ((continuous_rho hX c d).comp continuous_inv).mul
    (continuous_const.inner ((continuous_sig X.2 _).comp continuous_inv))

theorem cf_bound {X : Obj k r} (hX : X.1.OK) {m : ℕ} (hD : Decay X.2 m) (hm : X.1.deg + (2 * r + k + 1) ^ 2 + 1 ≤ m)
    (c : X.1.ι) {w : X.2.R.H} (hw : w ∈ X.2.R.sm) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, LieWd k r W) ∧ ∀ (x : M X) (g : GM k r),
      ‖cf X c w x g‖ ≤ C * (Ws.map fun W => sn X W x).sum * B.gN g.mat ^ (-(((2 * r + k + 1) ^ 2 + 1 : ℕ) : ℝ)) := by
  obtain ⟨C, Ws, hW, hb⟩ := hD
  obtain ⟨C', hC'⟩ := hX.growth
  refine ⟨|C'| * (|C| * nu X.2.R.σ Ws w), Ws, hW, fun x g => ?_⟩
  have hi : B.gN g.mat⁻¹ = B.gN g.mat := PI.PolynomialProperness.GN.gN_inv g.mem
  have h1 : 1 ≤ B.gN g.mat := PI.PolynomialProperness.GN.gN_ge_one g.mem
  set N := B.gN g.mat with hN
  have hN0 : 0 < N := one_pos.trans_le h1
  have hNi : B.gN (g⁻¹).mat = N := hi
  rw [cf_eq, sum_sn, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
  have a1 := hC' _ (g⁻¹).mem c d
  have a2 := hb _ (x d).2 w hw _ (g⁻¹).mem
  simp only [dsigW_eq'] at a2
  change _ ≤ C * nu X.2.R.σ Ws (x d) * nu X.2.R.σ Ws w at a2
  rw [hNi] at a1 a2
  have n1 := nu_nonneg (σ := X.2.R.σ) Ws (x d : X.2.R.H)
  have n2 := nu_nonneg (σ := X.2.R.σ) Ws w
  rw [Real.rpow_neg hN0.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity), norm_mul]
  have a3 : N ^ X.1.deg * N ^ ((2 * r + k + 1) ^ 2 + 1) ≤ N ^ m := by
    rw [← pow_add]; exact pow_le_pow_right₀ h1 (by omega)
  have a4 : ‖X.1.ρ (g⁻¹).mat c d‖ ≤ |C'| * N ^ X.1.deg :=
    a1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have a5 : N ^ m * ‖⟪w, X.2.R.σ (g⁻¹).mat (x d)⟫_ℂ‖ ≤ |C| * nu X.2.R.σ Ws w * nu X.2.R.σ Ws (x d) :=
    a2.trans (by rw [mul_right_comm]; gcongr; exact le_abs_self _)
  set q := ‖⟪w, X.2.R.σ (g⁻¹).mat (x d)⟫_ℂ‖
  have hq : 0 ≤ q := norm_nonneg _
  calc ‖X.1.ρ (g⁻¹).mat c d‖ * q * N ^ ((2 * r + k + 1) ^ 2 + 1)
      ≤ |C'| * N ^ X.1.deg * q * N ^ ((2 * r + k + 1) ^ 2 + 1) := by gcongr
    _ = |C'| * ((N ^ X.1.deg * N ^ ((2 * r + k + 1) ^ 2 + 1)) * q) := by ring
    _ ≤ |C'| * (N ^ m * q) := by gcongr
    _ ≤ |C'| * (|C| * nu X.2.R.σ Ws w * nu X.2.R.σ Ws (x d)) := by gcongr
    _ = _ := by ring

theorem act_mul {X : Obj k r} (hX : X.1.OK) {g h : Mx k r} (hg : g ∈ GG k r) (hh : h ∈ GG k r) (x : M X) :
    act X (g * h) x = act X g (act X h x) := by
  funext c
  refine Subtype.ext ?_
  rw [act_coe X (X.2.repOn.mul_mem _ hg _ hh), act_coe X hg]
  simp only [act_coe X hh, hX.mul g hg h hh, Matrix.mul_apply, _root_.map_sum, map_smul, Finset.smul_sum, smul_smul,
    Finset.sum_smul, X.2.repOn.apply_mul hg hh]
  exact Finset.sum_comm

theorem exists_pr [(haar : Measure (GM k r)).IsInvInvariant] {X : Obj k r} (hX : X.1.OK) {m : ℕ} (hD : Decay X.2 m)
    (hm : X.1.deg + (2 * r + k + 1) ^ 2 + 1 ≤ m) (T : URep k r) (c : X.1.ι) {w : X.2.R.H} (hw : w ∈ X.2.R.sm)
    (y : T.R.H) : (∀ x, Integrable (cf X c w x) haar) ∧ ∃ p, IsHom X (one T) p ∧ ∀ x y',
      ⟪y', (p x () : T.R.H)⟫_ℂ = ∫ g : GM k r, cf X c w x g * ⟪y', T.R.σ g.mat y⟫_ℂ ∂haar := by
  obtain ⟨C, Ws, hW, hb⟩ := cf_bound hX hD hm c hw
  have hI0 : ∀ x, Integrable (cf X c w x) haar := fun x =>
    (integrable_gN.const_mul _).mono' (continuous_cf hX c w x).aestronglyMeasurable (Eventually.of_forall (hb x))
  have hn : ∀ x (g : GM k r), ‖cf X c w x g • T.R.σ g.mat y‖ = ‖cf X c w x g‖ * ‖y‖ := fun x g => by
    rw [norm_smul, T.rep.2.1 _ g.mem]
  have hI : ∀ x, Integrable (fun g : GM k r => cf X c w x g • T.R.σ g.mat y) haar := fun x =>
    ((hI0 x).norm.mul_const ‖y‖).mono' ((continuous_cf hX c w x).smul (continuous_sig T y)).aestronglyMeasurable
      (Eventually.of_forall fun g => (hn x g).le)
  let f : M X →ₗ[ℂ] T.R.H :=
    { toFun := fun x => ∫ g : GM k r, cf X c w x g • T.R.σ g.mat y ∂haar
      map_add' := fun x x' => by
        rw [← integral_add (hI x) (hI x')]
        simp only [cf, map_add, Pi.add_apply, Submodule.coe_add, inner_add_right, add_smul]
      map_smul' := fun a x => by
        rw [RingHom.id_apply, ← integral_smul]
        simp only [cf, map_smul, Pi.smul_apply, Submodule.coe_smul, inner_smul_right, smul_smul] }
  obtain ⟨p, hp, hpf⟩ := etaleClosed_point_lifts_simple_roots_monic k r X T f hX
    ⟨C * ((∫ g : GM k r, B.gN g.mat ^ (-(((2 * r + k + 1) ^ 2 + 1 : ℕ) : ℝ)) ∂haar) * ‖y‖), Ws, hW, fun x => by
      refine (norm_integral_le_of_norm_le (((integrable_gN.const_mul
        (C * (Ws.map fun W => sn X W x).sum))).mul_const ‖y‖) (Eventually.of_forall fun g => ?_)).trans (le_of_eq ?_)
      · rw [hn]; exact mul_le_mul_of_nonneg_right (hb x g) (norm_nonneg _)
      · rw [integral_mul_const, integral_const_mul]; ring⟩
    (fun h hh x => by
      show ∫ g : GM k r, cf X c w (act X h x) g • T.R.σ g.mat y ∂haar = T.R.σ h (∫ g : GM k r, _ ∂haar)
      rw [← (T.R.σ h).integral_comp_comm (hI x),
        ← integral_mul_left_eq_self (fun g : GM k r => cf X c w (act X h x) g • T.R.σ g.mat y) (MG.mk _ h hh)]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [map_smul, cf]
      rw [← act_mul hX (MG.mem _) hh, ← T.repOn.apply_mul hh g.mem]
      have : ((MG.mk (hGG k r) h hh * g)⁻¹).mat * h = (g⁻¹).mat := by
        show ((MG.mk (hGG k r) h hh * g)⁻¹ * MG.mk (hGG k r) h hh).mat = _
        rw [_root_.mul_inv_rev, inv_mul_cancel_right]
      rw [this]
      rfl)
  refine ⟨hI0, p, hp, fun x y' => ?_⟩
  rw [hpf]
  show ⟪y', ∫ g : GM k r, cf X c w x g • T.R.σ g.mat y ∂haar⟫_ℂ = _
  rw [← integral_inner (hI x)]
  simp only [inner_smul_right]

theorem integrable_mul_coef {φ : GM k r → ℂ} (hφ : Integrable φ haar) (T : URep k r) (y y' : T.R.H) :
    Integrable (fun g : GM k r => φ g * ⟪y', T.R.σ g.mat y⟫_ℂ) haar :=
  hφ.mul_bdd (c := ‖y'‖ * ‖y‖) (continuous_const.inner (continuous_sig T y)).aestronglyMeasurable
    (Eventually.of_forall fun g => by
      refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
      rw [T.rep.2.1 _ g.mem])

theorem kfin_sm {U : URep k r} (hU : U.DS) {v : U.R.H} (hv : U.R.KFin v) : v ∈ U.R.sm := by
  obtain ⟨ε, μ, h⟩ := hU
  exact admitted.k_finite_smooth k r ε μ U.R.H U.R.σ h.1 h.2 v hv

theorem occurrence_induction : OccStep := by
  classical
  intro k r X T m hX hσ hT hD hm ⟨y, hy, I, _, v, w, c, d, hK, hc⟩
  have := inv_of_ds hσ
  by_contra hne
  push Not at hne
  obtain ⟨e, he, hS⟩ := schur_GM hT
  let x : I → M X := fun i => Pi.single (d i) ⟨v i, kfin_sm hσ (hK i).1⟩
  have h0 : ∀ i, Integrable (cf X (c i) (w i) (x i)) haar ∧
      ∫ g : GM k r, cf X (c i) (w i) (x i) g * ⟪y, T.R.σ g.mat y⟫_ℂ ∂haar = 0 := fun i => by
    obtain ⟨hI, p, hp, hpx⟩ := exists_pr hX hD hm T (c i) (kfin_sm hσ (hK i).2) y
    refine ⟨hI _, ?_⟩
    rw [← hpx, hne p hp]
    simp
  have h1 : ∀ g : GM k r, ⟪y, T.R.σ g.mat y⟫_ℂ * star ⟪y, T.R.σ g.mat y⟫_ℂ =
      ∑ i, cf X (c i) (w i) (x i) g * ⟪y, T.R.σ g.mat y⟫_ℂ := fun g => by
    rw [← inner_inv, hc _ (g⁻¹).mem, mul_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cf_eq, Finset.sum_eq_single (d i) (fun j _ hj => by simp [x, Pi.single_eq_of_ne hj]) (by simp)]
    simp [x, mul_comm]
  have h2 := hS y y y y
  simp only [h1] at h2
  rw [integral_finsetSum _ fun i _ => integrable_mul_coef (h0 i).1 T y y] at h2
  simp only [(h0 _).2, Finset.sum_const_zero] at h2
  have := (div_eq_zero_iff.1 h2.symm).resolve_right (by exact_mod_cast he.ne')
  exact hy (inner_self_eq_zero.1 (mul_self_eq_zero.1 this))

theorem exists_kfin {U : URep k r} (hU : U.DS) : ∃ w : U.R.H, w ≠ 0 ∧ U.R.KFin w := by
  obtain ⟨ε, μ, -, P, hP, hDS⟩ := hU
  obtain ⟨S, hfin, hst, -, ⟨w, hwS, hw0, -⟩, -⟩ := hDS.2.2.2.2.2.1
  refine ⟨w, hw0, S, hfin, hwS, fun g hg x hx => ?_⟩
  have := hst _ (PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hP hg).1 x hx
  simp only [(PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hP hg).2] at this
  exact this

theorem injectivity_induction : InjStep := by
  classical
  intro k r X S T m hX hσ hT hD hm hC x hx
  have := inv_of_ds hσ
  obtain ⟨w, hw0, hwK⟩ := exists_kfin hσ
  have hws := kfin_sm hσ hwK
  obtain ⟨e, he, hS⟩ := schur_GM hσ
  have key : ∀ x : M X, (∀ s p, IsHom X (one (T s)) p → p x = 0) → ∀ c, ⟪w, (x c : X.2.R.H)⟫_ℂ = 0 := by
    intro x hx c
    have h0 : ∀ b, Integrable (fun g : GM k r => cf X b w x g * (⟪w, X.2.R.σ g.mat w⟫_ℂ * X.1.ρ g.mat c b)) haar ∧
        ∫ g : GM k r, cf X b w x g * (⟪w, X.2.R.σ g.mat w⟫_ℂ * X.1.ρ g.mat c b) ∂haar = 0 := fun b => by
      obtain ⟨I, _, s, y, y', hy⟩ := hC w w hwK hwK c b
      have hI := (exists_pr hX hD hm X.2 b hws w).1 x
      have e : (fun g : GM k r => cf X b w x g * (⟪w, X.2.R.σ g.mat w⟫_ℂ * X.1.ρ g.mat c b)) =
          fun g => ∑ i, cf X b w x g * ⟪y' i, (T (s i)).R.σ g.mat (y i)⟫_ℂ := funext fun g => by
        rw [hy _ g.mem, Finset.mul_sum]
      rw [e, integral_finsetSum _ fun i _ => integrable_mul_coef hI _ _ _]
      refine ⟨integrable_finsetSum _ fun i _ => integrable_mul_coef hI _ _ _, Finset.sum_eq_zero fun i _ => ?_⟩
      obtain ⟨-, p, hp, hpx⟩ := exists_pr hX hD hm (T (s i)) b hws (y i)
      rw [← hpx, hx _ p hp]
      simp
    have h1 : ∀ g : GM k r, ⟪w, X.2.R.σ g.mat w⟫_ℂ * star ⟪(x c : X.2.R.H), X.2.R.σ g.mat w⟫_ℂ =
        ∑ b, cf X b w x g * (⟪w, X.2.R.σ g.mat w⟫_ℂ * X.1.ρ g.mat c b) := fun g => by
      have h2 : X.1.ρ g.mat * X.1.ρ (g⁻¹).mat = 1 := by
        rw [← hX.mul _ g.mem _ (g⁻¹).mem, ← MG.mat_mul, mul_inv_cancel]; exact hX.one
      rw [← inner_inv]
      simp only [cf_eq, Finset.sum_mul]
      rw [Finset.sum_comm]
      have h3 : ∀ d, ∑ b, X.1.ρ (g⁻¹).mat b d * ⟪w, X.2.R.σ (g⁻¹).mat (x d)⟫_ℂ *
          (⟪w, X.2.R.σ g.mat w⟫_ℂ * X.1.ρ g.mat c b) = (1 : Matrix X.1.ι X.1.ι ℂ) c d *
            (⟪w, X.2.R.σ g.mat w⟫_ℂ * ⟪w, X.2.R.σ (g⁻¹).mat (x d)⟫_ℂ) := fun d => by
        rw [← h2, Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      simp only [h3, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h2 := hS w w w (x c)
    simp only [h1] at h2
    rw [integral_finsetSum _ fun b _ => (h0 b).1] at h2
    simp only [(h0 _).2, Finset.sum_const_zero] at h2
    have := (div_eq_zero_iff.1 h2.symm).resolve_right (by exact_mod_cast he.ne')
    exact (mul_eq_zero.1 this).resolve_left fun h => hw0 (inner_self_eq_zero.1 h)
  have h4 : ∀ g ∈ GG k r, ∀ d, ⟪w, X.2.R.σ g (x d)⟫_ℂ = 0 := by
    intro g hg d
    have h5 := key (act X g x) fun s p hp => by
      rw [← LinearMap.comp_apply, hp.equiv g hg, LinearMap.comp_apply, hx s p hp, map_zero]
    simp only [act_coe X hg, inner_sum, inner_smul_right] at h5
    have h2 : X.1.ρ g⁻¹ * X.1.ρ g = 1 := by
      rw [← hX.mul _ ((hGG k r).2.2.2 g hg).1 _ hg, mul_eq_one_comm.1 ((hGG k r).2.2.2 g hg).2]; exact hX.one
    have h6 : X.1.ρ g *ᵥ (fun d => ⟪w, X.2.R.σ g (x d)⟫_ℂ) = 0 := funext h5
    have h7 := congrArg (X.1.ρ g⁻¹ *ᵥ ·) h6
    simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h7
    exact congrFun h7 d
  funext d
  refine Subtype.ext ?_
  obtain ⟨ε, μ, hDS⟩ := hσ
  let V : Submodule ℂ X.2.R.H :=
    { carrier := {z | ∀ g ∈ GG k r, ⟪w, X.2.R.σ g z⟫_ℂ = 0}
      add_mem' := fun ha hb g hg => by rw [map_add, inner_add_right, ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by simp
      smul_mem' := fun a z hz g hg => by rw [map_smul, inner_smul_right, hz g hg, mul_zero] }
  have hcl : IsClosed (V : Set X.2.R.H) := by
    have : (V : Set X.2.R.H) = ⋂ g ∈ GG k r, {z | ⟪w, X.2.R.σ g z⟫_ℂ = 0} := by ext z; simp [V]
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (continuous_const.inner (X.2.R.σ g).continuous) continuous_const
  rcases CompanionTheory.LimBd.SchurHpk.isIrredOn_of_ds hDS.2 V hcl (fun a ha z hz g hg => by
    rw [← X.2.repOn.apply_mul hg ha]; exact hz _ (X.2.repOn.mul_mem _ hg _ ha)) with h | h
  · have : (x d : X.2.R.H) ∈ V := fun g hg => h4 g hg d
    rwa [h, Submodule.mem_bot] at this
  · have : w ∈ V := by rw [h]; trivial
    have h8 := this 1 X.2.repOn.one_mem
    rw [X.2.repOn.map_one] at h8
    exact absurd (inner_self_eq_zero.1 h8) hw0

end CompanionTheory.D.gk.FinalFormK
