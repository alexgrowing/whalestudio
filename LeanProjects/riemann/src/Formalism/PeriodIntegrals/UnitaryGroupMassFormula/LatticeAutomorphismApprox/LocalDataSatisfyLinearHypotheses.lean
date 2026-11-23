import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SecondCoordinateVectorMemSpan

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem inv_mem_of_val (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : ℕ)
    (hc : Valued.v ((c : v.adicCompletion I.F)) = 1) : ((c : KV I v))⁻¹ ∈ OV I v := by
  have h1 : Valued.v (((c : v.adicCompletion I.F))⁻¹) = 1 := by rw [map_inv₀, hc, inv_one]
  show ((c : v.adicCompletion I.F))⁻¹ ∈ v.adicCompletionIntegers I.F
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 h1.le

theorem lat_of_inAt (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) {g : ℕ} (hv : (g : 𝓞 I.F) ∈ v.asIdeal)
    (x : VA I) (hx : InAt I g 1 x) :
    PI.FinKW.vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨c, hc, hcx⟩ := hx
  obtain ⟨w, hw, hweq⟩ := vecV_mL I v 1 _ hcx
  have hval := Gl.val_nat I.F v c (Gl.not_mem_of_coprime v hc hv)
  apply PI.UnitaryGroupMassFormula.AdIndexEq.cancel_nat v hval
  have h1 : c • PI.FinKW.vecV I v x = w := by
    rw [← Nat.cast_smul_eq_nsmul (RV I v), ← psiV_natCast I v c, ← vecV_smul', hweq, Nat.cast_one, one_smul]
  rw [h1]
  exact hw

theorem cong_pair (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) {g c : ℕ} (hc : Valued.v ((c : v.adicCompletion I.F)) = 1)
    (X X0 Z w : Fin I.n → RV I v)
    (hZ : Z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (hw : w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (hD : (c : RV I v) • (X0 - X) = (g : RV I v) • w) (q : RV I v)
    (hq : hl I v X0 Z = (g : RV I v) * q) (hq1 : p1 q ∈ OV I v) (hq2 : p1 (sigV I v q) ∈ OV I v) :
    (∃ s ∈ OV I v, p1 (hl I v X Z) = (g : KV I v) * s) ∧
      (∃ s ∈ OV I v, p1 (hl I v Z X) = (g : KV I v) * s) := by
  have hc0 : (c : KV I v) ≠ 0 := by
    intro h0
    have h0' : ((c : v.adicCompletion I.F)) = 0 := h0
    rw [h0', map_zero] at hc
    exact zero_ne_one hc
  have hinv : ((c : KV I v))⁻¹ * (c : KV I v) = 1 := inv_mul_cancel₀ hc0
  have hci := inv_mem_of_val I v c hc
  have hsig : ∀ m : ℕ, sigV I v (m : RV I v) = m := fun m => map_natCast _ m
  have key : (c : RV I v) * hl I v X Z = (g : RV I v) * ((c : RV I v) * q - hl I v w Z) := by
    have h1 : hl I v X Z = hl I v X0 Z - hl I v (X0 - X) Z := by rw [hl_sub_left]; ring
    have h2 : hl I v ((c : RV I v) • (X0 - X)) Z = hl I v ((g : RV I v) • w) Z := by rw [hD]
    rw [hl_smul_left, hl_smul_left, hsig, hsig] at h2
    rw [h1, mul_sub, h2, hq]
    ring
  have key2 : (c : RV I v) * hl I v Z X = (g : RV I v) * ((c : RV I v) * sigV I v q - hl I v Z w) := by
    have h3 : sigV I v ((c : RV I v) * hl I v X Z) =
        sigV I v ((g : RV I v) * ((c : RV I v) * q - hl I v w Z)) := by rw [key]
    simp only [map_mul, map_sub, hsig] at h3
    rw [hl_swap I v X Z, hl_swap I v w Z]
    exact h3
  have hwZ := hl_int I v ε p1 hp w Z hw hZ
  have hZw := hl_int I v ε p1 hp Z w hZ hw
  constructor
  · refine ⟨((c : KV I v))⁻¹ * ((c : KV I v) * p1 q - p1 (hl I v w Z)),
      mul_mem hci (sub_mem (mul_mem (natCast_mem _ c) hq1) hwZ), ?_⟩
    have k1 := congrArg p1 key
    simp only [map_mul, map_sub, map_natCast] at k1
    linear_combination ((c : KV I v))⁻¹ * k1 - p1 (hl I v X Z) * hinv
  · refine ⟨((c : KV I v))⁻¹ * ((c : KV I v) * p1 (sigV I v q) - p1 (hl I v Z w)),
      mul_mem hci (sub_mem (mul_mem (natCast_mem _ c) hq2) hZw), ?_⟩
    have k1 := congrArg p1 key2
    simp only [map_mul, map_sub, map_natCast] at k1
    linear_combination ((c : KV I v))⁻¹ * k1 - p1 (hl I v Z X) * hinv

theorem local_data_satisfy_linear_hypotheses : BridgeA := by
  intro I g r k e f z Rf hH v hv _hsum p1 hp t ht1 htz
  obtain ⟨hg, _hs, _hn, hee, hff, hef, hz, _ht, hi, hiz⟩ := hH
  have hLat : ∀ x, InAt I g 1 x →
      PI.FinKW.vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x hx => lat_of_inAt I v hv x hx
  have hz0 : PI.FinKW.vecV I v Rf.z0 ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    PI.FinKW.LocTo.mem_local_lattice_iff I _ Rf.vectorsInLattice.2.1 v
  have m1 : ∀ X ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), vec1 p1 X ∈ Lam1 I v p1 :=
    fun X hX => Submodule.subset_span ⟨X, hX, rfl⟩
  have m2 : ∀ X ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), vec2 p1 X ∈ Lam2 I v p1 :=
    fun X hX => Submodule.subset_span ⟨X, hX, rfl⟩
  have hcong : ∀ (a : Fin I.n → I.E) (a0 : VA I), InAt I g g (a0 - incl I a) → ZMod' I g (hA I a0 Rf.z0) →
      (∃ s ∈ OV I v, p1 (hl I v (PI.FinKW.vecV I v (incl I a)) (PI.FinKW.vecV I v Rf.z0)) = (g : KV I v) * s) ∧
      (∃ s ∈ OV I v, p1 (hl I v (PI.FinKW.vecV I v Rf.z0) (PI.FinKW.vecV I v (incl I a))) = (g : KV I v) * s) := by
    intro a a0 hD hZ
    obtain ⟨c, hc, hcD⟩ := hD
    obtain ⟨w, hw, hweq⟩ := vecV_mL I v g _ hcD
    obtain ⟨q, hqI, hq⟩ := hZ
    have hval := Gl.val_nat I.F v c (Gl.not_mem_of_coprime v hc hv)
    have hD' : (c : RV I v) • (PI.FinKW.vecV I v a0 - PI.FinKW.vecV I v (incl I a)) = (g : RV I v) • w := by
      rw [← hweq, vecV_smul', psiV_natCast, Gl.vecV_sub]
    have hq' : hl I v (PI.FinKW.vecV I v a0) (PI.FinKW.vecV I v Rf.z0) =
        (g : RV I v) * PI.FinKW.psiV I v q := by
      rw [← psiV_hA, hq, map_mul, psiV_natCast]
    have hqq := adaptedProjection_psiV_mem_integers_of_mem_intAf I v _ p1 hp q hqI
    exact cong_pair I v _ p1 hp hval _ _ _ w hz0 hw hD' _ hq' hqq.1 hqq.2
  have hite : ∀ (P : Prop) [Decidable P], p1 (inclV I v (if P then 1 else 0)) = if P then 1 else 0 := by
    intro P _
    split_ifs <;> simp
  have hgK : (g : KV I v) ≠ 0 := by
    rw [← map_natCast (algebraMap I.F (KV I v)) g]
    exact (map_ne_zero _).2 (by exact_mod_cast (show g ≠ 0 by omega))
  unfold LinData LinHyp
  beta_reduce
  refine ⟨natCast_mem _ g, ?_, pr_int I v _ p1 hp, ?_, ?_, m1 _ (hLat _ hiz), m2 _ (hLat _ hiz), m1 _ hz0,
    m2 _ hz0, ?_, natCast_mem _ t, ?_, ?_, ?_, ?_⟩
  ·
    intro h
    let ginv : OV I v := ⟨(g : KV I v)⁻¹, h⟩
    have hunit : IsUnit (g : OV I v) := by
      refine isUnit_iff_exists_inv.2 ⟨ginv, Subtype.ext ?_⟩
      show ((g : OV I v) : KV I v) * (g : KV I v)⁻¹ = 1
      push_cast
      exact mul_inv_cancel₀ hgK
    exact (IsLocalRing.mem_maximalIdeal _).1 (natCast_mem_max I.F v g hv) hunit
  · intro i
    exact ⟨m1 _ (hLat _ (hi i).1), m1 _ (hLat _ (hi i).2), m2 _ (hLat _ (hi i).1), m2 _ (hLat _ (hi i).2)⟩
  · intro i j
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pr_rat, hee, map_zero, map_zero]
    · rw [pr_rat, hff, map_zero, map_zero]
    · rw [pr_rat, hef, hite]
    · rw [pr_rat, hformE_swap, hef]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
  · intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pr_rat, (hz i).1, map_zero, map_zero]
    · rw [pr_rat, (hz i).2, map_zero, map_zero]
    · rw [pr_rat, hformE_swap, (hz i).1, map_zero, map_zero, map_zero]
    · rw [pr_rat, hformE_swap, (hz i).2, map_zero, map_zero, map_zero]
  ·
    obtain ⟨q, hq⟩ := Nat.modEq_iff_dvd.1 ht1
    refine ⟨((-q : ℤ) : KV I v), intCast_mem _ _, ?_⟩
    have h2 := congrArg (Int.cast : ℤ → KV I v) hq
    push_cast at h2 ⊢
    linear_combination -h2
  · rw [pr_rat, htz]
    simp only [map_neg, map_natCast]
  · intro i
    obtain ⟨⟨s1, hs1, e1⟩, ⟨s2, hs2, e2⟩⟩ := hcong (e i) (Rf.e0 i) (Rf.basisApprox i).1 (Rf.formsAtZero.2 i).1
    obtain ⟨⟨s3, hs3, e3⟩, ⟨s4, hs4, e4⟩⟩ := hcong (f i) (Rf.f0 i) (Rf.basisApprox i).2 (Rf.formsAtZero.2 i).2
    exact ⟨⟨s1, hs1, by rw [pr_vec]; exact e1⟩, ⟨s3, hs3, by rw [pr_vec]; exact e3⟩,
      ⟨s2, hs2, by rw [pr_vec]; exact e2⟩, ⟨s4, hs4, by rw [pr_vec]; exact e4⟩⟩
  · obtain ⟨q, hqI, hq⟩ := Rf.formsAtZero.1
    refine ⟨p1 (PI.FinKW.psiV I v q), (adaptedProjection_psiV_mem_integers_of_mem_intAf I v _ p1 hp q hqI).1, ?_⟩
    rw [pr_vec, ← psiV_hA]
    have h2 := congrArg (fun y => p1 (PI.FinKW.psiV I v y)) hq
    simp only [map_add, map_one, map_mul, map_natCast] at h2
    exact h2

end PI.UnitaryGroupMassFormula.ScXuExists.BrA

end
