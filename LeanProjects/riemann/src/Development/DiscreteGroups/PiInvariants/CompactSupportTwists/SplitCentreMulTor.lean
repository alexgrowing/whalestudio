import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ContinuousPA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.SizeBounds.SizetHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CuspRapidDecayGL.CuspRapidDecaySiegelGL
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.Rs
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GlobalTheory.CuspBoundSiegel

namespace DiscreteGroups.T1.G.Dcy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem logSize_nonneg (g : GA E n) : 0 ≤ logSize g := add_nonneg (logSizeM_nonneg _) (logSizeM_nonneg _)

theorem redSize_nonneg (g : GA E n) : 0 ≤ redSize g := by
  unfold redSize
  exact le_ciInf fun _ => logSize_nonneg _

theorem redSize_le (g : GA E n) (γ : GL (Fin n) E) : redSize g ≤ logSize (ratGL E n γ * g) := by
  unfold redSize
  exact ciInf_le ⟨0, by rintro _ ⟨δ, rfl⟩; exact logSize_nonneg _⟩ γ

theorem logAbs_det_mul' (x y : GA E n) : logAbs (x * y).val.det = logAbs x.val.det + logAbs y.val.det := by
  rw [Units.val_mul, Matrix.det_mul]
  exact (D1.logAbsBasic E).2.1 _ _ (Matrix.isUnits_det_units x) (Matrix.isUnits_det_units y)

theorem logAbs_ratGL' (γ : GL (Fin n) E) : logAbs (ratGL E n γ).val.det = 0 := by
  have h : (ratGL E n γ).val.det = algebraMap E (Ad E) γ.val.det := by
    rw [RingHom.map_det]; rfl
  rw [h]
  exact (D1.logAbsBasic E).2.2 _ (Matrix.isUnits_det_units γ).ne_zero

theorem logAbs_prod_units {ι : Type*} (s : Finset ι) (f : ι → (Ad E)ˣ) :
    logAbs (∏ i ∈ s, (f i : Ad E)) = ∑ i ∈ s, logAbs (f i : Ad E) := by
  rw [← Units.coe_prod, logAbs_eq_log_ideleNorm, map_prod,
    Real.log_prod fun i _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _]
  exact Finset.sum_congr rfl fun i _ => (logAbs_eq_log_ideleNorm (f i)).symm

theorem tor_eq (x : Fin n → ℝ) :
    (An.tor E x : GA E n) = diagUnits n (fun i => posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _)) :=
  Units.ext (by rw [E1.tor_val, coe_diagUnits])

theorem logAbs_det_tor (x : Fin n → ℝ) :
    logAbs (An.tor E x : GA E n).val.det = Module.finrank ℚ E * ∑ i, x i := by
  rw [E1.tor_val, det_diagonal,
    logAbs_prod_units Finset.univ (fun i => (posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [E1.posIdele_val, E1.logAbs_pA]

theorem splitCentre_mul_tor (τ : ℝ) (y : Fin n → ℝ) :
    splitCentre E n τ * (An.tor E y : GA E n) = An.tor E (fun i => τ + y i) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) n (Real.exp_pos τ)
  rw [Real.log_exp] at h
  rw [← h, tor_eq, tor_eq, ← map_mul]
  congr 1
  funext i
  rw [Pi.mul_apply, ← GlobalTheory.CuspBoundSiegel.posIdele_mul]
  exact GlobalTheory.CuspBoundSiegel.posIdele_congr _ _ (Real.exp_add _ _).symm

theorem cp_decay (ψ : Sm E n) (hψ : IsCuspForm ψ) (hA : ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) (R M : ℝ) :
    ∃ C : ℝ, ∀ g : GA E n, |logAbs g.val.det| ≤ R → ‖ψ.1 g‖ ≤ C * Real.exp (-(M * redSize g)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨‖ψ.1 1‖ * Real.exp (|M| * redSize (1 : GA E 0)), fun g _ => ?_⟩
    have hg : g = 1 := Units.ext (Subsingleton.elim _ _)
    subst hg
    have hr := redSize_nonneg (1 : GA E 0)
    rw [mul_assoc, ← Real.exp_add]
    refine le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp ?_)
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self M)) hr]
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) n
  set d : ℕ := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  have had : n * d ≠ 0 := (Nat.mul_pos hn hd0).ne'
  set m : AdelicGLn.AdelicGL E n → ℝ :=
    fun b => (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) with hm
  have hmpos : ∀ b, 0 < m b := fun b => (IdeleGroup.ideleModule E _).2
  set s : AdelicGLn.AdelicGL E n → ℝ := fun b => m b ^ (((n * d : ℕ) : ℝ)⁻¹) with hs
  have hspos : ∀ b, 0 < s b := fun b => Real.rpow_pos_of_pos (hmpos b) _
  have hspow : ∀ b, s b ^ (n * d) = m b := fun b => Real.rpow_inv_natCast_pow (hmpos b).le had
  set f : AdelicGLn.AdelicGL E n → AdelicGLn.AdelicGL E n :=
    fun b => b * (diagUnits n (fun _ : Fin n => posIdele (K := E) (s b) (hspos b)))⁻¹ with hf
  have hmc : Continuous m :=
    continuous_subtype_val.comp ((IdeleGroup.continuous_ideleModule (K := E)).comp (AdelicGLn.continuous_det E n))
  have hsc : Continuous fun b => (⟨s b, hspos b⟩ : {r : ℝ // 0 < r}) :=
    Continuous.subtype_mk (hmc.rpow_const fun b => Or.inl (hmpos b).ne') _
  have hfc : Continuous f := continuous_id.mul ((continuous_diagUnits n).comp
    (continuous_pi fun _ => GlobalTheory.CuspBoundSiegel.continuous_posIdele_pos.comp hsc)).inv
  have hω'c : IsCompact (f '' ω) := hω.image hfc
  have hω'B : f '' ω ⊆ (adelicBorel (K := E) (n := n) : Set (AdelicGLn.AdelicGL E n)) := by
    rintro _ ⟨b, hb, rfl⟩
    exact mul_mem (hωB hb) (inv_mem (diagUnits_mem_adelicBorel n _))
  have hω'1 : ∀ b ∈ f '' ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1 := by
    rintro _ ⟨b, -, rfl⟩
    have e : IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det
        (diagUnits n (fun _ : Fin n => posIdele (K := E) (s b) (hspos b)))) =
        IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) :=
      Subtype.ext (by rw [GlobalTheory.CuspBoundSiegel.ideleModule_det_diagUnits_posIdele, hspow])
    simp only [hf, map_mul, map_inv, e, mul_inv_cancel]
    rfl
  have P := PositivityTheory.S2.CuspBdd.cuspRapidDecaySiegelGL E n ψ hψ (f '' ω) hω'c hω'B hω'1 t ht
  choose Cf hCf using P
  obtain ⟨CS, hCS0, hCS⟩ := PositivityTheory.Rg.BcB.E.E3.sizet_holds E n (f '' ω)
    (maxCompact (K := E) (n := n) : Set (AdelicGLn.AdelicGL E n)) hω'c isCompact_maxCompact
  obtain ⟨B₁, hB₁⟩ := (hω'c.image (continuous_abs.comp (continuous_logAbs_det (E := E) (n := n)))).bddAbove
  obtain ⟨B₂, hB₂⟩ := ((isCompact_maxCompact (K := E) (n := n)).image
    (continuous_abs.comp (continuous_logAbs_det (E := E) (n := n)))).bddAbove
  set P0 : ℝ := max M 0 with hP0
  set N : ℝ := P0 * CS with hN
  have hN0 : 0 ≤ N := mul_nonneg (le_max_right _ _) hCS0
  set T : ℝ := (R + B₁ + B₂) / ((n : ℝ) * d) with hT
  set C₀ : ℝ := ∑ j, (|Cf (Pi.single j N)| + |Cf (Pi.single j (-N))|) with hC₀
  have hC₀0 : 0 ≤ C₀ := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨C₀ * Real.exp (P0 * CS * (1 + T)), fun g hg => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩ := hsieg g
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  set ρ := (∏ i, r i) ^ ((n : ℝ)⁻¹) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hprod _
  have hρa : ρ ^ n = ∏ i, r i := Real.rpow_inv_natCast_pow hprod.le hn.ne'
  set r' : Fin n → ℝ := fun i => r i / ρ with hr'
  have hr'pos : ∀ i, 0 < r' i := fun i => div_pos (hr i) hρpos
  have hD : diagUnits n (fun i => posIdele (K := E) (r i) (hr i)) =
      diagUnits n (fun _ : Fin n => posIdele (K := E) ρ hρpos) *
        diagUnits n (fun i => posIdele (K := E) (r' i) (hr'pos i)) := by
    rw [← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, ← GlobalTheory.CuspBoundSiegel.posIdele_mul]
    exact GlobalTheory.CuspBoundSiegel.posIdele_congr _ _ (by simp only [hr']; field_simp)
  set D' := diagUnits n (fun i => posIdele (K := E) (r' i) (hr'pos i)) with hD'
  have key : ratGL E n γ * g = splitCentre E n (Real.log (s b) + Real.log ρ) * (f b * D' * k) := by
    change AdelicGLn.diagonal E n γ * g = _
    rw [e, hD, GlobalTheory.CuspBoundSiegel.diagUnits_posIdele n hρpos, splitCentre_add]
    simp only [hf, GlobalTheory.CuspBoundSiegel.diagUnits_posIdele n (hspos b)]
    symm
    calc splitCentre E n (Real.log (s b)) * splitCentre E n (Real.log ρ) *
          (b * (splitCentre E n (Real.log (s b)))⁻¹ * D' * k)
        = splitCentre E n (Real.log (s b)) * (splitCentre E n (Real.log ρ) *
            (b * (splitCentre E n (Real.log (s b)))⁻¹)) * D' * k := by group
      _ = splitCentre E n (Real.log (s b)) * ((b * (splitCentre E n (Real.log (s b)))⁻¹) *
            splitCentre E n (Real.log ρ)) * D' * k := by rw [splitCentre_comm (Real.log ρ)]
      _ = (splitCentre E n (Real.log (s b)) * b) * (splitCentre E n (Real.log (s b)))⁻¹ *
            splitCentre E n (Real.log ρ) * D' * k := by group
      _ = (b * splitCentre E n (Real.log (s b))) * (splitCentre E n (Real.log (s b)))⁻¹ *
            splitCentre E n (Real.log ρ) * D' * k := by rw [splitCentre_comm (Real.log (s b)) b]
      _ = b * (splitCentre E n (Real.log ρ) * D') * k := by group
  have hrat' : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * r' j ≤ r' i := fun i j hij => by
    simp only [hr']
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hrat i j hij) hρpos.le
  have hprod1 : ∏ i, r' i = 1 := by
    simp only [hr']
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa, div_self hprod.ne']
  set τ : ℝ := Real.log (s b) + Real.log ρ with hτdef
  set y : Fin n → ℝ := fun i => Real.log (r' i) with hy
  have hDy : (D' : GA E n) = An.tor E y := by
    rw [tor_eq, hD']
    congr 1
    funext i
    exact GlobalTheory.CuspBoundSiegel.posIdele_congr _ _ (Real.exp_log (hr'pos i)).symm
  have hkey2 : ratGL E n γ * g = f b * An.tor E (fun i => τ + y i) * k := by
    rw [key, ← splitCentre_mul_tor, ← hDy, mul_assoc (f b), ← mul_assoc, ← mul_assoc,
      splitCentre_comm τ (f b)]
    group
  have hsumy : ∑ i, y i = 0 := by
    simp only [hy]
    rw [← Real.log_prod fun i _ => (hr'pos i).ne', hprod1, Real.log_one]
  have hψeq : ψ.1 g = ψ.1 (f b * D' * k) := by
    rw [← hψ.1.left γ g, key, hA]
  have hfb : f b ∈ f '' ω := ⟨b, hb, rfl⟩

  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |y i|) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hyn : ‖y‖ ≤ |y j| :=
    (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => by rw [Real.norm_eq_abs]; exact hj i (Finset.mem_univ _)
  have hsingle : ∀ c : ℝ, ∏ i, r' i ^ (Pi.single j c : Fin n → ℝ) i = Real.exp (y j * c) := fun c => by
    rw [Finset.prod_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, Real.rpow_zero]) (by simp),
      Pi.single_eq_same, Real.exp_mul, Real.exp_log (hr'pos j)]
  have hterm : ∀ c : ℝ, |Cf (Pi.single j c)| ≤ C₀ → ‖ψ.1 g‖ ≤ C₀ * Real.exp (y j * c) := fun c hc => by
    rw [hψeq]
    calc ‖ψ.1 (f b * D' * k)‖ ≤ Cf (Pi.single j c) * ∏ i, r' i ^ (Pi.single j c : Fin n → ℝ) i :=
          hCf (Pi.single j c) (f b) hfb r' hr'pos hrat' hprod1 k hk
      _ = Cf (Pi.single j c) * Real.exp (y j * c) := by rw [hsingle]
      _ ≤ C₀ * Real.exp (y j * c) :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans hc) (Real.exp_pos _).le
  have hle1 : |Cf (Pi.single j N)| ≤ C₀ :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun j => |Cf (Pi.single j N)| + |Cf (Pi.single j (-N))|)
        (fun _ _ => by positivity) (Finset.mem_univ j))
  have hle2 : |Cf (Pi.single j (-N))| ≤ C₀ :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun j => |Cf (Pi.single j N)| + |Cf (Pi.single j (-N))|)
        (fun _ _ => by positivity) (Finset.mem_univ j))
  have hψb : ‖ψ.1 g‖ ≤ C₀ * Real.exp (-(N * ‖y‖)) := by
    have hmono : ∀ u : ℝ, u ≤ -(N * ‖y‖) → C₀ * Real.exp u ≤ C₀ * Real.exp (-(N * ‖y‖)) := fun u hu =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hu) hC₀0
    rcases le_or_gt 0 (y j) with h0 | h0
    · refine (hterm (-N) hle2).trans (hmono _ ?_)
      rw [abs_of_nonneg h0] at hyn
      nlinarith
    · refine (hterm N hle1).trans (hmono _ ?_)
      rw [abs_of_neg h0] at hyn
      nlinarith

  have hlog : logAbs g.val.det = logAbs (f b : GA E n).val.det + d * (n * τ) + logAbs (k : GA E n).val.det := by
    have h1 := congrArg (fun x : GA E n => logAbs x.val.det) hkey2
    simp only [logAbs_det_mul', logAbs_ratGL', zero_add, logAbs_det_tor, Finset.sum_add_distrib, hsumy,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_zero] at h1
    rw [h1]
  have hb1 : |logAbs (f b : GA E n).val.det| ≤ B₁ := hB₁ ⟨f b, hfb, rfl⟩
  have hk2 : |logAbs (k : GA E n).val.det| ≤ B₂ := hB₂ ⟨k, hk, rfl⟩
  have hnd : 0 < (n : ℝ) * d := by positivity
  have hτ : |τ| ≤ T := by
    rw [hT, le_div_iff₀ hnd]
    have h2 : |(d : ℝ) * (n * τ)| ≤ R + B₁ + B₂ := by
      rw [show (d : ℝ) * (n * τ) = logAbs g.val.det - logAbs (f b : GA E n).val.det - logAbs (k : GA E n).val.det by
        rw [hlog]; ring]
      refine (abs_sub _ _).trans ?_
      refine add_le_add ((abs_sub _ _).trans (add_le_add hg hb1)) hk2
    rw [show (d : ℝ) * (n * τ) = ((n : ℝ) * d) * τ by ring, abs_mul, abs_of_pos hnd] at h2
    linarith

  have hxn : ‖(fun i => τ + y i : Fin n → ℝ)‖ ≤ |τ| + ‖y‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have hyi : |y i| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
    linarith [abs_add_le τ (y i)]
  have hsize : redSize g ≤ CS * (1 + (T + ‖y‖)) := by
    calc redSize g ≤ logSize (ratGL E n γ * g) := redSize_le g γ
      _ = logSize (f b * An.tor E (fun i => τ + y i) * k) := by rw [hkey2]
      _ ≤ CS * (1 + ‖(fun i => τ + y i : Fin n → ℝ)‖) := hCS _ hfb _ hk _
      _ ≤ CS * (1 + (T + ‖y‖)) := mul_le_mul_of_nonneg_left (by linarith) hCS0
  have hrs0 := redSize_nonneg g
  have hexp : -(N * ‖y‖) ≤ P0 * CS * (1 + T) + -(M * redSize g) := by
    have h1 : M * redSize g ≤ P0 * redSize g := mul_le_mul_of_nonneg_right (le_max_left _ _) hrs0
    have h2 : P0 * redSize g ≤ P0 * (CS * (1 + (T + ‖y‖))) := mul_le_mul_of_nonneg_left hsize (le_max_right _ _)
    have h3 : P0 * (CS * (1 + (T + ‖y‖))) = P0 * CS * (1 + T) + N * ‖y‖ := by rw [hN]; ring
    linarith
  calc ‖ψ.1 g‖ ≤ C₀ * Real.exp (-(N * ‖y‖)) := hψb
    _ ≤ C₀ * Real.exp (P0 * CS * (1 + T) + -(M * redSize g)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) hC₀0
    _ = C₀ * Real.exp (P0 * CS * (1 + T)) * Real.exp (-(M * redSize g)) := by rw [Real.exp_add]; ring

theorem cp_decay_wt (ψ : Sm E n) (hψ : IsCuspForm ψ) (hA : ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) (R : ℝ)
    (M : ℕ) : ∃ C : ℝ, ∀ x : H E n 0, |ldet x| ≤ R → ‖ψ.1 x.1‖ * wt x ^ M ≤ C := by
  obtain ⟨C, hC⟩ := cp_decay ψ hψ hA R 1
  set a : ℝ := 1 + redSize (1 : GA E 0) with ha
  have ha0 : 0 ≤ a := by have := redSize_nonneg (1 : GA E 0); linarith
  refine ⟨max C 0 * (M.factorial * Real.exp a), fun x hx => ?_⟩
  have hx2 : x.2 = 1 := Units.ext (Subsingleton.elim _ _)
  have hw : wt x = a + redSize x.1 := by rw [wt, hx2, ha]; ring
  have hrs := redSize_nonneg x.1
  have hψx : ‖ψ.1 x.1‖ ≤ max C 0 * Real.exp (-redSize x.1) := by
    have := hC x.1 hx
    rw [one_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hpow : wt x ^ M ≤ M.factorial * Real.exp (a + redSize x.1) := by
    rw [hw]
    have := Real.pow_div_factorial_le_exp _ (add_nonneg ha0 hrs) M
    rw [div_le_iff₀ (by exact_mod_cast M.factorial_pos)] at this
    linarith
  calc ‖ψ.1 x.1‖ * wt x ^ M ≤ (max C 0 * Real.exp (-redSize x.1)) * (M.factorial * Real.exp (a + redSize x.1)) :=
        mul_le_mul hψx hpow (pow_nonneg (by rw [hw]; linarith) _)
          (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)
    _ = max C 0 * (M.factorial * Real.exp a) := by
        rw [Real.exp_add]
        have : Real.exp (-redSize x.1) * Real.exp (redSize x.1) = 1 := by rw [← Real.exp_add]; simp
        calc max C 0 * Real.exp (-redSize x.1) * (↑M.factorial * (Real.exp a * Real.exp (redSize x.1)))
            = max C 0 * (↑M.factorial * Real.exp a) * (Real.exp (-redSize x.1) * Real.exp (redSize x.1)) := by ring
          _ = _ := by rw [this, mul_one]

end DiscreteGroups.T1.G.Dcy

end
