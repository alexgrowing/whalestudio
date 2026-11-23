import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CuspPairA

set_option linter.all false

noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.BcB PositivityTheory.Rg.Rs.JInitBnd
open scoped Pointwise

namespace DiscreteGroups.T1.G.CP

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cp_core (hRD : GlobalTheory.Published.CuspRapidDecaySiegelGL) (ψ φ : Sm E n) (hψ : IsCuspForm ψ)
    (hZ : ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) (hφ : IsAutForm φ)
    {Ω : Set (GA E n)} (hΩ : IsCompact Ω) (R : ℝ) :
    ∃ C : ℝ, ∀ x : GA E n, |logAbs x.val.det| ≤ R → ∀ z ∈ Ω, ‖ψ.1 x‖ * ‖φ.1 (x * z)‖ ≤ C := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨‖ψ.1 1‖ * ‖φ.1 1‖, fun x _ z _ => ?_⟩
    have h1 : x = 1 := Units.ext (Subsingleton.elim _ _)
    rw [h1, one_mul, show z = 1 from Units.ext (Subsingleton.elim _ _)]
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) n
  have hd0 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have had : n * Module.finrank ℚ E ≠ 0 := (Nat.mul_pos hn hd0).ne'
  set m : AdelicGLn.AdelicGL E n → ℝ :=
    fun b => (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) with hm
  have hmpos : ∀ b, 0 < m b := fun b => (IdeleGroup.ideleModule E _).2
  set s : AdelicGLn.AdelicGL E n → ℝ := fun b => m b ^ (((n * Module.finrank ℚ E : ℕ) : ℝ)⁻¹) with hs
  have hspos : ∀ b, 0 < s b := fun b => Real.rpow_pos_of_pos (hmpos b) _
  have hspow : ∀ b, s b ^ (n * Module.finrank ℚ E) = m b := fun b => Real.rpow_inv_natCast_pow (hmpos b).le had
  set f : AdelicGLn.AdelicGL E n → AdelicGLn.AdelicGL E n :=
    fun b => b * (diagUnits n (fun _ : Fin n => posIdele (K := E) (s b) (hspos b)))⁻¹ with hf
  have hmc : Continuous m :=
    continuous_subtype_val.comp (continuous_ideleModule.comp (AdelicGLn.continuous_det E n))
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
  obtain ⟨N0, hN0⟩ := uniform_exp φ hφ
  have hQc : IsCompact ((maxCompact (K := E) (n := n) : Set (GA E n)) * Ω) :=
    (isCompact_maxCompact (K := E) (n := n)).mul hΩ
  obtain ⟨C2, hC20, hC2⟩ := uniform_growth0 φ hφ.level N0 hN0 (hω.mul hQc)
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le
    (hQc.image (GlobalTheory.ConstTermGrowth.continuous_mapInf (E := E) (a := n)).inv)
  have hlast : n - 1 < n := by omega
  set M : ℝ := 2 * (N0 : ℝ) with hM
  set lam : Fin n → ℝ := fun i =>
    (if i = (⟨n - 1, hlast⟩ : Fin n) then M else 0) - (if i = (⟨0, hn⟩ : Fin n) then M else 0) with hlam
  obtain ⟨C1, hC1⟩ := hRD E n ψ hψ (f '' ω) hω'c hω'B hω'1 t ht lam
  obtain ⟨Bω, hBω⟩ := hω.exists_bound_of_continuousOn
    (DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).continuousOn
  set t₀ : ℝ := |Real.log t| with ht₀
  set S : ℝ := (R + Bω) / Module.finrank ℚ E with hSdef
  refine ⟨C1 * (C2 * (B * B * 3) ^ N0 * Real.exp (N0 * (S + 4 * n * t₀))), fun x hx z hz => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨r, hr, hrat, rfl⟩, k, hk, e⟩ := hsieg x
  set ℓ : Fin n → ℝ := fun i => Real.log (r i) with hℓ
  have hsr : ∀ q, -t₀ ≤ PositivityTheory.Rg.Rs.An.sr ℓ q := fun q => by
    unfold PositivityTheory.Rg.Rs.An.sr
    split_ifs with h
    · have h1 := hrat ⟨q - 1, by omega⟩ ⟨q, h.2⟩ (by show q = q - 1 + 1; omega)
      have h2 := Real.log_le_log (mul_pos ht (hr _)) h1
      rw [Real.log_mul ht.ne' (hr _).ne'] at h2
      have h3 := neg_abs_le (Real.log t)
      simp only [hℓ]
      linarith
    · simp only [ht₀, neg_nonpos]; exact abs_nonneg _
  have e2 : ratGL E n γ * x = b * diagUnits n (fun i => posIdele (K := E) (r i) (hr i)) * k := e
  have hsum : |∑ i, ℓ i| ≤ S := by
    have e1 : logAbs (ratGL E n γ * x).val.det = logAbs x.val.det := by rw [lAbs_mul, lAbs_rat, zero_add]
    rw [e2, lAbs_mul, lAbs_mul, lAbs_diag, lAbs_maxCompact hk, add_zero] at e1
    have hbb := hBω b hb
    rw [Real.norm_eq_abs] at hbb
    have hdpos : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast hd0
    have e3 : (Module.finrank ℚ E : ℝ) * ∑ i, ℓ i = logAbs x.val.det - logAbs b.val.det := by
      simp only [hℓ]; linarith
    rw [hSdef, le_div_iff₀ hdpos, show |∑ i, ℓ i| * (Module.finrank ℚ E : ℝ) =
      |(Module.finrank ℚ E : ℝ) * ∑ i, ℓ i| by rw [abs_mul, abs_of_pos hdpos, mul_comm], e3]
    exact (abs_sub_le_abs_add_abs _ _).trans (add_le_add hx hbb)
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
  have key : ratGL E n γ * x = splitCentre E n (Real.log (s b) + Real.log ρ) * (f b * D' * k) := by
    change AdelicGLn.diagonal E n γ * x = _
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
  have hr'rat : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * r' j ≤ r' i := fun i j hij => by
    simp only [hr']
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hrat i j hij) hρpos.le
  have hr'prod : ∏ i, r' i = 1 := by
    simp only [hr']
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hρa, div_self hprod.ne']
  have hpsi0 : ‖ψ.1 x‖ ≤ C1 * ∏ i, r' i ^ lam i := by
    calc ‖ψ.1 x‖ = ‖ψ.1 (ratGL E n γ * x)‖ := by rw [hψ.1.left]
      _ = ‖ψ.1 (f b * D' * k)‖ := by rw [key, hZ]
      _ ≤ _ := hC1 (f b) ⟨b, hb, rfl⟩ r' hr'pos hr'rat hr'prod k hk
  set L := ∑ q ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ q with hLdef
  have hL : L = ℓ ⟨0, hn⟩ - ℓ ⟨n - 1, hlast⟩ := sum_sr ℓ hn
  have hlog : ∀ i, Real.log (r' i) = ℓ i - Real.log ρ := fun i => Real.log_div (hr i).ne' hρpos.ne'
  have hprodlam : ∏ i, r' i ^ lam i = Real.exp (-(M * L)) := by
    rw [show ∏ i, r' i ^ lam i = ∏ i, Real.exp (Real.log (r' i) * lam i) from
      Finset.prod_congr rfl fun i _ => Real.rpow_def_of_pos (hr'pos i) _, ← Real.exp_sum]
    congr 1
    simp only [hlog, hlam, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [hL]; ring
  have hpsi : ‖ψ.1 x‖ ≤ C1 * Real.exp (-(M * L)) := by rw [← hprodlam]; exact hpsi0
  have htor : diagUnits n (fun i => posIdele (K := E) (r i) (hr i)) = PositivityTheory.Rg.Rs.An.tor E ℓ := by
    unfold PositivityTheory.Rg.Rs.An.tor
    congr 1
    funext i
    exact GlobalTheory.CuspBoundSiegel.posIdele_congr _ _ (Real.exp_log (hr i)).symm
  have hq : k * z ∈ (maxCompact (K := E) (n := n) : Set (GA E n)) * Ω := Set.mul_mem_mul hk hz
  have e4 : φ.1 (x * z) = φ.1 ((b * (k * z)) * infGL E n ((mI (k * z))⁻¹ * dg ℓ * mI (k * z))) := by
    rw [← hφ.left γ (x * z), ← mul_assoc (ratGL E n γ) x z, e2, htor, mul_assoc _ k z,
      key0 b _ (k * z) (pFin_tor ℓ), mI, mI, pInf_tor]
  have hz' : GlobalTheory.CuspRep.height ((mI (k * z))⁻¹ * dg (E := E) ℓ * mI (k * z)) ≤
      B * B * GlobalTheory.CuspRep.height (dg (E := E) ℓ) := by
    have h1 := hB (mI (k * z))⁻¹ ⟨k * z, hq, rfl⟩ (dg ℓ * mI (k * z))
    have h2 := hB (mI (k * z))⁻¹ ⟨k * z, hq, rfl⟩ (dg ℓ)⁻¹
    rw [← _root_.mul_inv_rev, height_inv', height_inv'] at h2
    rw [mul_assoc]
    calc _ ≤ B * GlobalTheory.CuspRep.height (dg (E := E) ℓ * mI (k * z)) := h1
      _ ≤ B * (B * GlobalTheory.CuspRep.height (dg (E := E) ℓ)) := mul_le_mul_of_nonneg_left h2 hB0
      _ = _ := by ring
  have hA0 : 0 ≤ S + 2 * (L + 2 * (n : ℝ) * t₀) := by
    have h1 := bound_nonneg ℓ t₀ hsr
    have h2 := (abs_nonneg _).trans hsum
    linarith
  have hcoord : ∀ i, |ℓ i| ≤ S + 2 * (L + 2 * (n : ℝ) * t₀) := fun i => coord_bound ℓ hn t₀ S hsr hsum i
  have hD3 := height_dg (E := E) ℓ _ hcoord hA0
  have hphi : ‖φ.1 (x * z)‖ ≤ C2 * (B * B * (3 * Real.exp (S + 2 * (L + 2 * (n : ℝ) * t₀)))) ^ N0 := by
    rw [e4]
    have hy1 := one_le_height ((mI (k * z))⁻¹ * dg (E := E) ℓ * mI (k * z))
    calc _ ≤ C2 * GlobalTheory.CuspRep.height ((mI (k * z))⁻¹ * dg (E := E) ℓ * mI (k * z)) ^ N0 :=
          hC2 _ (Set.mul_mem_mul hb hq) _
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
          (hz'.trans (mul_le_mul_of_nonneg_left hD3 (mul_nonneg hB0 hB0))) _) hC20
  have hC1' : 0 ≤ C1 := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h (Real.exp_pos (-(M * L)))
    linarith [norm_nonneg (ψ.1 x)]
  have hexp : Real.exp (-(M * L)) * Real.exp (N0 * (S + 2 * (L + 2 * (n : ℝ) * t₀))) =
      Real.exp (N0 * (S + 4 * n * t₀)) := by
    rw [← Real.exp_add]; congr 1; rw [hM]; ring
  calc ‖ψ.1 x‖ * ‖φ.1 (x * z)‖
      ≤ (C1 * Real.exp (-(M * L))) * (C2 * (B * B * (3 * Real.exp (S + 2 * (L + 2 * (n : ℝ) * t₀)))) ^ N0) :=
        mul_le_mul hpsi hphi (norm_nonneg _) (mul_nonneg hC1' (Real.exp_pos _).le)
    _ = C1 * (C2 * (B * B * 3) ^ N0 *
          (Real.exp (-(M * L)) * Real.exp (N0 * (S + 2 * (L + 2 * (n : ℝ) * t₀))))) := by
        rw [Real.exp_nat_mul, show B * B * (3 * Real.exp (S + 2 * (L + 2 * (n : ℝ) * t₀))) =
          B * B * 3 * Real.exp (S + 2 * (L + 2 * (n : ℝ) * t₀)) by ring, mul_pow]
        ring
    _ = _ := by rw [hexp]

end DiscreteGroups.T1.G.CP

end
