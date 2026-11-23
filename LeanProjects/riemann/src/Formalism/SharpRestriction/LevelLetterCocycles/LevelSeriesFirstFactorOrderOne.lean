import Formalism.SharpRestriction.LevelLetterCocycles.LevelOneUniformizerCoeffVanish
import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevM

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {W : LocWach PD LL O v n}

theorem prim_pow_p {ζ : LL} (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    ∃ j : ℕ, IsPrimitiveRoot (ζ ^ PD.p) (PD.p ^ j) := by
  obtain ⟨j, hj⟩ := hζ
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have : ζ = 1 := by simpa using hj
    exact ⟨0, by simp [this]⟩
  · refine ⟨j - 1, ?_⟩
    have h := hj.pow_of_dvd PD.hp.ne_zero (dvd_pow_self PD.p (by omega))
    have e : PD.p ^ j / PD.p = PD.p ^ (j - 1) := by
      have := Nat.pow_div (show 1 ≤ j by omega) PD.hp.pos
      rwa [pow_one] at this
    rwa [e] at h

theorem cc_lev_φpow (hlevφ : ∀ (i : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
      W.lev i ζ (W.φA f) = PowerSeries.rescale (PD.p : LL) (W.lev (i - 1) (ζ ^ PD.p) f))
    (s : ℕ) : ∀ (a : ZMod n) (ζ : LL), (∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) → ∀ f : LetA O n,
    PowerSeries.constantCoeff (W.lev a ζ ((W.φA ^ s) f)) =
      PowerSeries.constantCoeff (W.lev (a - (s : ZMod n)) (ζ ^ (PD.p ^ s)) f) := by
  induction s with
  | zero => intro a ζ _ f; simp
  | succ s ih =>
    intro a ζ hζ f
    rw [pow_succ', AlgHom.mul_apply, hlevφ a ζ hζ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ih (a - 1) (ζ ^ PD.p) (prim_pow_p hζ) f, ← pow_mul, ← pow_succ']
    congr 2
    push_cast; ring

variable {levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B)}

theorem cc_lev_ps (Ti : Formalism.MainNotions.UnusedSlot80.LevE.Comparison₂ W levB) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (a : ZMod n)
    (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (s : ℕ) (hs : 1 ≤ s) :
    PowerSeries.constantCoeff (W.lev a ζ (ps W s)) = (PD.p : LL) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  unfold ps
  rw [cc_lev_φpow Ti.hlevφ s a ζ ⟨1, by simpa using hζ⟩]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [pow_succ', pow_mul, hζ.pow_eq_one, one_pow]
  unfold qA
  rw [map_add, map_add]
  have h0 := Formalism.MainNotions.UnusedSlot80.LevE.level_one_uniformizer_coeff_vanish hR (a - ((s' + 1 : ℕ) : ZMod n)) 1 0 (by omega)
  rw [pow_one, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
  rw [h0, zero_add]
  unfold lA
  rw [map_natCast, map_natCast]

variable [IsDomain O]

theorem level_series_first_factor_order_one (Ti : Formalism.MainNotions.UnusedSlot80.LevE.Comparison₂ W levB) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev a ζ (ps W 0) = PowerSeries.X * u ∧ PowerSeries.constantCoeff u ≠ 0 := by
  obtain ⟨w, hw, w', hww, -⟩ := Formalism.MainNotions.UnusedSlot80.LevC.q_unit W hR hp0
  obtain ⟨u₀, hu₀, hu₀c⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.lev_q_simple W a ζ hζ
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  refine ⟨W.lev a ζ w' * u₀, ?_, ?_⟩
  · rw [hp0w, map_mul, hu₀]; ring
  · rw [map_mul]
    refine mul_ne_zero ?_ hu₀c
    intro h0
    have := congrArg (fun g => PowerSeries.constantCoeff (W.lev a ζ g)) hww
    simp only [map_mul, map_one, h0, mul_zero] at this
    exact zero_ne_one this

theorem lev_prod_ps (Ti : Formalism.MainNotions.UnusedSlot80.LevE.Comparison₂ W levB) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hp0 : ((PD.p : ℕ) : O) ≠ 0) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (E : ℕ → ℕ) :
    ∀ N : ℕ, ∃ u : PowerSeries LL, W.lev a ζ (∏ s ∈ Finset.range N, ps W s ^ E s) =
      PowerSeries.X ^ (if N = 0 then 0 else E 0) * u ∧ PowerSeries.constantCoeff u ≠ 0 := by
  have hpL : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  intro N
  induction N with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨u, hu, huc⟩ := ih
    rw [Finset.prod_range_succ, map_mul, hu, map_pow]
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      obtain ⟨u₁, hu₁, hu₁c⟩ := level_series_first_factor_order_one Ti hR hp0 a ζ hζ
      refine ⟨u * u₁ ^ E 0, ?_, ?_⟩
      · rw [hu₁]; simp only [if_true, pow_zero, one_mul, Nat.succ_ne_zero, if_false, mul_pow]; ring
      · rw [map_mul, map_pow]; exact mul_ne_zero huc (pow_ne_zero _ hu₁c)
    · refine ⟨u * W.lev a ζ (ps W N) ^ E N, ?_, ?_⟩
      · rw [if_neg (by omega), if_neg (by omega)]; ring
      · rw [map_mul, map_pow, cc_lev_ps Ti hR a ζ hζ N hpos]
        exact mul_ne_zero huc (pow_ne_zero _ hpL)

section Ser

variable {V : Type} [AddCommGroup V] [Module LL V]

omit [IsDomain O] in
theorem smulS_vanish_neg {f : ℤ → V} (hf : LB 0 f) (g : PowerSeries LL) (r : ℤ) (hr : r < 0) :
    smulS g f r = 0 := by
  rw [smulS_eq_sum hf g r 0 (by omega)]; simp

omit [IsDomain O] in
theorem LB_delta (v : V) : LB 0 (fun k : ℤ => if k = 0 then v else 0) := fun k hk => by simp [show k ≠ 0 by omega]

omit [IsDomain O] in
theorem smulS_delta (g : PowerSeries LL) (v : V) (r : ℤ) :
    smulS g (fun k : ℤ => if k = 0 then v else 0) r = (if 0 ≤ r then PowerSeries.coeff r.toNat g else 0) • v := by
  rcases lt_or_ge r 0 with h | h
  · rw [if_neg (by omega), zero_smul]
    exact smulS_vanish_neg (LB_delta v) g r h
  · rw [if_pos h, smulS_eq_sum (LB_delta v) g r (r.toNat + 1) (by omega), Finset.sum_eq_single r.toNat]
    · rw [if_pos (show r - ((r.toNat : ℕ) : ℤ) = 0 by omega)]
    · intro j _ hj; rw [if_neg (show r - (j : ℤ) ≠ 0 by omega), smul_zero]
    · intro hj; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) hj

omit [IsDomain O] in
theorem Dg_of_mul {Fil : ℤ → Submodule LL V} (hF : Antitone Fil) {m : ℤ} {F : ℤ → V} (hLB : LB m F)
    (D : ℕ) (u : PowerSeries LL) (hu : PowerSeries.constantCoeff u ≠ 0) (s : ℤ)
    (h : Dg Fil (s + D) (smulS (PowerSeries.X ^ D * u) F)) : Dg Fil s F := by
  have h1 := Dg_smulS hF (LB_smulS hLB _) h u⁻¹
  rw [← smulS_mul hLB, show u⁻¹ * (PowerSeries.X ^ D * u) = PowerSeries.X ^ D by
    rw [mul_comm, mul_assoc, PowerSeries.mul_inv_cancel _ hu, mul_one], smulS_X_pow hLB] at h1
  intro r
  have := h1 (r + D)
  simp only [add_sub_cancel_right] at this
  rwa [show s + (D : ℤ) - (r + D) = s - r by ring] at this

omit [IsDomain O] in
theorem LB_sum {ι : Type} (s : Finset ι) {m : ℤ} (F : ι → ℤ → V) (h : ∀ j, LB m (F j)) :
    LB m (fun k => ∑ j ∈ s, F j k) := fun k hk => Finset.sum_eq_zero fun j _ => h j k hk

omit [IsDomain O] in
theorem smulS_sum {ι : Type} (s : Finset ι) {m : ℤ} (F : ι → ℤ → V) (h : ∀ j, LB m (F j))
    (g : PowerSeries LL) : smulS g (fun k => ∑ j ∈ s, F j k) = fun k => ∑ j ∈ s, smulS g (F j) k := by
  induction s using Finset.induction_on with
  | empty => funext k; simp [smulS]
  | insert a s ha ih =>
    have e1 : (fun k => ∑ j ∈ insert a s, F j k) = F a + fun k => ∑ j ∈ s, F j k := by
      funext k; rw [Finset.sum_insert ha]; rfl
    rw [e1, smulS_add (h a) (LB_sum s F h), ih]
    funext k
    rw [Finset.sum_insert ha]
    rfl

omit [IsDomain O] in
theorem smulS_sum_delta {d : ℕ} (g : PowerSeries LL) (G : Fin d → PowerSeries LL) (vv : Fin d → V) (r : ℤ) :
    smulS g (fun k => ∑ j, smulS (G j) (fun k : ℤ => if k = 0 then vv j else 0) k) r =
      ∑ j, (if 0 ≤ r then PowerSeries.coeff r.toNat (g * G j) else 0) • vv j := by
  rw [smulS_sum Finset.univ _ (fun j => LB_smulS (LB_delta (vv j)) (G j)) g]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smulS_mul (LB_delta (vv j)), smulS_delta]

theorem dg_core {Fil : ℤ → Submodule LL V} (hF : Antitone Fil) {d I : ℕ} (G : Fin d → PowerSeries LL)
    (vv : Fin d → V) (cc : Fin I → Fin d → LL) (Nser : Fin I → PowerSeries LL) (α : Fin I → ℤ) (D0 : ℕ)
    (uD : PowerSeries LL) (huD : PowerSeries.constantCoeff uD ≠ 0) (lam0 : LL) (hlam0 : lam0 ≠ 0) (s : ℤ)
    (hid : ∀ j, PowerSeries.C lam0 * (PowerSeries.X ^ D0 * uD) * G j =
      ∑ i, PowerSeries.C (cc i j) * Nser i)
    (E : Fin I → ℕ) (hE : ∀ i, (E i : ℤ) = s + D0 + α i)
    (hdvd : ∀ i, (PowerSeries.X : PowerSeries LL) ^ E i ∣ Nser i)
    (hfil : ∀ i, ∑ j, cc i j • vv j ∈ Fil (-α i)) :
    Dg Fil s (fun k => ∑ j, smulS (G j) (fun k : ℤ => if k = 0 then vv j else 0) k) := by
  have hLB : LB 0 (fun k => ∑ j, smulS (G j) (fun k : ℤ => if k = 0 then vv j else 0) k) :=
    LB_sum _ _ (fun j => LB_smulS (LB_delta (vv j)) (G j))
  refine Dg_of_mul hF hLB D0 uD huD s ?_
  intro r
  rw [smulS_sum_delta]
  have key : lam0 • ∑ j, (if 0 ≤ r then PowerSeries.coeff r.toNat (PowerSeries.X ^ D0 * uD * G j) else 0) • vv j =
      ∑ i, (if 0 ≤ r then PowerSeries.coeff r.toNat (Nser i) else 0) • ∑ j, cc i j • vv j := by
    by_cases h0 : 0 ≤ r
    · simp only [if_pos h0, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrArg (PowerSeries.coeff r.toNat) (hid j)
      rw [mul_assoc, PowerSeries.coeff_C_mul, map_sum] at this
      simp only [PowerSeries.coeff_C_mul] at this
      rw [← Finset.sum_smul, this]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp [if_neg h0]
  have hmem : lam0 • ∑ j, (if 0 ≤ r then PowerSeries.coeff r.toNat (PowerSeries.X ^ D0 * uD * G j) else 0) • vv j ∈
      Fil (s + D0 - r) := by
    rw [key]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h0 : 0 ≤ r
    · rw [if_pos h0]
      by_cases hr : r < E i
      · rw [PowerSeries.X_pow_dvd_iff.1 (hdvd i) r.toNat (by omega), zero_smul]; exact (Fil _).zero_mem
      · exact (Fil _).smul_mem _ (hF (show s + D0 - r ≤ -α i by have := hE i; omega) (hfil i))
    · rw [if_neg h0, zero_smul]; exact (Fil _).zero_mem
  have := (Fil (s + D0 - r)).smul_mem lam0⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hlam0, one_smul] at this

end Ser

theorem first_factor_power_isUnit_etale [NeZero n] (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (H : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (ps W 0 ^ H)) := by
  rw [map_pow]; exact (Formalism.MainNotions.UnusedSlot80.LevC.ps_unitE W hR 0).pow H

theorem qφ_mem [NeZero n] (C : Formalism.MainNotions.UnusedSlot80.LevC.Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) (e : ℕ) (y : W.DD T)
    (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T c' y) :
    W.q ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 •
      W.φD T (abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y) ∈ W.N T := by
  have hyP : ((W.φD T) ^ e) y ∈ Pp W T c' e := Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e hy
  obtain ⟨z', hz'N, hz'l, hz'e⟩ := Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' e T hT _ hyP
  rw [one_smul] at hz'e
  set z : W.DD T := abelian₂ W A (c' + (e : ZMod n)) e • ((W.φD T) ^ e) y with hzdef
  have hzN : z ∈ W.N T := by rw [hz'e]; exact hz'N.1
  have hzl : (letE (c' + (e : ZMod n)) : LetA O n) • z = z := by rw [hz'e]; exact hz'l
  have h5T := C.h5 T _ _ hT.1 (Formalism.MainNotions.UnusedSlot80.PhiPowers.jumpsLet_of_win W A hA T hT)
  have hQ : W.Q = W.q := by simp [LocWach.Q, C.hs]
  set i : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with hidef
  have hi1 : i - 1 = c' + (e : ZMod n) := by rw [hidef]; push_cast; ring
  have hzNl : z ∈ W.Nl T (i - 1) := by
    rw [hi1]; exact ⟨z, hzN, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hzl⟩
  have hM := h5T.1 i z hzNl
  rw [hQ] at hM
  have hMH : Formalism.MainNotions.UnusedSlot80.PhiPowers.Mw A.G₀ A.S A.η (A.ty i) ≤ A.Hs i (e + 1) 0 := by
    have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' (e + 1) (e + 1) (by omega) le_rfl
    rwa [Nat.sub_self] at this
  obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hMH
  rw [hdd, pow_add, mul_comm, mul_smul]
  exact (W.N T).smul_mem _ hM

theorem lev0Mpr_of [NeZero n] (C : Formalism.MainNotions.UnusedSlot80.LevC.Ctx W) (Ti : Formalism.MainNotions.UnusedSlot80.LevE.Comparison₂ W levB)
    (hmem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      levB T i ζ x k ∈ DcrisL PD T.ρ (W.emb i))
    (hMC : Formalism.MainNotions.N.Pv.LocalLengthBound.MemCrit W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) : Formalism.MainNotions.UnusedSlot80.LevC.LevelZeroModPRefined A c' e T b sol := by
  intro x k f hxP hrep hfr0 hSk
  obtain ⟨κ, hS⟩ := hSk
  set a : ZMod n := c' + (e : ZMod n) with hadef
  set a' : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with ha'def
  have ha' : a' = a + 1 := by rw [ha'def, hadef]; push_cast; ring
  set H : ℕ := A.Hs a' (e + 1) 0 with hHdef
  set U : LetA O n := Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e with hUdef
  set Λ' : LetA O n := abelian₂ W A a' (e + 1) with hΛ'def
  have hlam : Λ' = ps W 0 ^ H * U := Formalism.MainNotions.UnusedSlot80.LevC.lam_succ W A c' e
  have hUΔ : U ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W C.hR.1 A _ e)
  choose w hwΔ hfw using hfr0
  set aa' : Fin d → LetA O n := fun m => letE a' * (W.π₀ * U) * w m with haa'
  have haa'Δ : ∀ m, aa' m ∈ W.AΔ := fun m => W.AΔ.mul_mem (W.AΔ.mul_mem
    (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a') (W.AΔ.mul_mem C.hR.1 hUΔ)) (hwΔ m)
  obtain ⟨κ₀, Hh, hHh⟩ := Formalism.MainNotions.UnusedSlot80.LevC.horTr_exists W C.hO2 C.hH C.hCA T hT.1 c' b sol hb (A.M PD.p)
  have hHΔ : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T c' (Hh j) := fun j =>
    Formalism.MainNotions.UnusedSlot80.LevE.hor_mem T c' b hb.1 sol C.hR.1 (A.M PD.p) κ₀ j (hHh j)
  obtain ⟨Pu, hPu⟩ := first_factor_power_isUnit_etale C.hR H
  set Pinv : W.EE := ((Pu⁻¹ : W.EEˣ) : W.EE) with hPinv
  have hPP : Pinv * algebraMap (LetA O n) W.EE (ps W 0 ^ H) = 1 := by rw [hPinv, ← hPu]; exact Units.inv_mul Pu
  set Y : W.DD T := ∑ j, aa' j • ((W.φD T) ^ (e + 1)) (Hh j) with hY
  set z : W.DD T := Pinv • Y with hz

  have hΛz : Λ' • z = U • Y := by
    rw [hz, ← algebraMap_smul W.EE Λ', smul_smul, hlam, map_mul, mul_comm (algebraMap _ _ (ps W 0 ^ H)),
      mul_assoc, mul_comm (algebraMap _ _ (ps W 0 ^ H)), hPP, mul_one, algebraMap_smul]
  have hzP : InFP W T c' (e + 1) 1 (Λ' • z) := by
    rw [hΛz, hY, Finset.smul_sum]
    refine ⟨_, AddSubgroup.sum_mem _ fun j _ => ?_, (one_smul _ _).symm⟩
    rw [smul_smul]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' (e + 1) (W.AΔ.mul_mem hUΔ (haa'Δ j)) (hHΔ j)

  have hzrep : RepVV W T c' (e + 1) (A.M PD.p) Λ' b sol (lA W ^ 0 • z) (fun m => lE W κ₀ * f m) := by
    rw [Formalism.MainNotions.UnusedSlot80.LevC.repVV_iff]
    refine ⟨κ₀, Hh, hHh, 0, fun m => lA W ^ κ₀ * (U * aa' m), fun m =>
      ⟨W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.LevC.lA_mem W κ₀) (W.AΔ.mul_mem hUΔ (haa'Δ m)), ?_⟩, ?_⟩
    · rw [hlam, Formalism.MainNotions.UnusedSlot80.LevC.lE_eq, map_mul, map_mul, map_mul, ← hfw m]
      ring
    · have e0 : lA W ^ 0 • (lA W ^ κ₀ • Λ' • (lA W ^ 0 • z) -
          ∑ m, (lA W ^ κ₀ * (U * aa' m)) • ((W.φD T) ^ (e + 1)) (Hh m)) = 0 := by
        rw [pow_zero, one_smul, one_smul, hΛz, hY, Finset.smul_sum, Finset.smul_sum]
        simp only [smul_smul]
        exact sub_self _
      rw [e0]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' (e + 1) _

  suffices hzN : InFNc W T a' 1 z from
    Formalism.MainNotions.UnusedSlot80.LevC.mem_of_sec_eq C A hA c' hc' T hT b sol hb (e + 1) x z k 0 κ₀ f hxP hzP hzN hrep hzrep

  have hYΔ : ∀ δ ∈ W.DelF, W.γD T δ Y = Y := by
    intro δ hδ
    rw [hY, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', haa'Δ j δ hδ, Formalism.MainNotions.UnusedSlot80.PhiPowers.φD_pow_Δ W T (hHΔ j).1.2 (e + 1) δ hδ]
  have hPz : ps W 0 ^ H • z = Y := by
    rw [hz, ← algebraMap_smul W.EE (ps W 0 ^ H), smul_smul, mul_comm, hPP, one_smul]
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := by
    intro δ hδ
    refine Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T (g := ps W 0 ^ H) ⟨Pu, hPu⟩ ?_
    rw [← (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W C.hR.1 0) H) δ hδ, ← Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', hPz, hYΔ δ hδ,
      (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W C.hR.1 0) H) δ hδ, hPz]
  have hYl : (letE a' : LetA O n) • Y = Y := by
    rw [hY, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, haa', ← mul_assoc, ← mul_assoc, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self]
  have hzl : (letE a' : LetA O n) • z = z := by rw [hz, smul_comm, hYl]

  obtain ⟨w0, hw0, w0', hww0, -⟩ := Formalism.MainNotions.UnusedSlot80.LevC.q_unit W C.hR C.hp0
  have hZN : ∀ j, W.q ^ H • W.φD T (abelian₂ W A a e • ((W.φD T) ^ e) (Hh j)) ∈ W.N T := fun j =>
    qφ_mem C A hA c' hc' T hT e (Hh j) (hHΔ j)
  have hQ : W.Q = W.q := by simp [LocWach.Q, C.hs]
  have hdec : W.Q ^ (H + H) • z = ∑ j, (w0 ^ H * (letE a' * W.π₀ * w j)) •
      (W.q ^ H • W.φD T (abelian₂ W A a e • ((W.φD T) ^ e) (Hh j))) := by
    have e1 : W.Q ^ (H + H) • z = (W.q ^ H * w0 ^ H) • Y := by
      rw [hQ, hz, ← algebraMap_smul W.EE (W.q ^ (H + H)), smul_smul, ← algebraMap_smul W.EE (W.q ^ H * w0 ^ H)]
      congr 1
      rw [pow_add, hw0, mul_pow]
      simp only [map_mul]
      linear_combination (algebraMap (LetA O n) W.EE (w0 ^ H) * algebraMap (LetA O n) W.EE (ps W 0 ^ H) *
        algebraMap (LetA O n) W.EE (w0 ^ H)) * hPP
    rw [e1, hY, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [φD_smulA, ← Formalism.MainNotions.UnusedSlot80.PhiPowers.pow_apply_succ, smul_smul, smul_smul, smul_smul, haa']
    unfold Formalism.MainNotions.UnusedSlot80.LevC.LamUp at hUdef
    rw [hUdef]
    congr 1
    ring
  have hK : W.Q ^ (H + H) • z ∈ W.N T := by
    rw [hdec]; exact (W.N T).sum_mem fun j _ => (W.N T).smul_mem _ (hZN j)

  obtain ⟨I, g, c₀, α, hg, hF⟩ := hS
  choose u hu hgu using fun i => (hg i).1
  set den : Fin I → LetA O n := fun i => ∏ s ∈ Finset.range (e + 1), ps W s ^ (-(α i s)).toNat with hden
  set num : Fin I → LetA O n := fun i => ∏ s ∈ Finset.range (e + 1), ps W s ^ (α i s).toNat with hnum
  set DEN : LetA O n := ∏ i, den i with hDEN
  set DENx : Fin I → LetA O n := fun i => ∏ i' ∈ Finset.univ.erase i, den i' with hDENx
  have hDENi : ∀ i, DEN = den i * DENx i := fun i => (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  set Nn : Fin I → LetA O n := fun i => letE a' * num i * u i * DENx i with hNn
  have hLetA : ∀ m, DEN * lA W ^ κ * aa' m = ps W 0 ^ H * ∑ i, Nn i * algebraMap O (LetA O n) (c₀ i m) := by
    intro m
    apply W.EE_inj
    have h1 := hF m
    simp only at h1
    have hfw' : algebraMap (LetA O n) W.EE (aa' m) = algebraMap (LetA O n) W.EE (ps W 0 ^ H) * f m :=
      (hfw m).symm
    have h2 : algebraMap (LetA O n) W.EE (DEN * lA W ^ κ * aa' m) =
        algebraMap (LetA O n) W.EE (DEN * ps W 0 ^ H) * (lE W κ * f m) := by
      rw [map_mul (algebraMap (LetA O n) W.EE) (DEN * lA W ^ κ) (aa' m), hfw', Formalism.MainNotions.UnusedSlot80.LevC.lE_eq,
        map_mul, map_mul]
      ring
    rw [h2, h1, map_mul (algebraMap (LetA O n) W.EE) (ps W 0 ^ H), map_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hgi := hgu i
    rw [hDENi i, IsScalarTower.algebraMap_apply O (LetA O n) W.EE (c₀ i m)]
    calc algebraMap (LetA O n) W.EE (den i * DENx i * ps W 0 ^ H) *
          (g i * algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) (c₀ i m)))
        = algebraMap (LetA O n) W.EE (ps W 0 ^ H) * algebraMap (LetA O n) W.EE (DENx i) *
          (algebraMap (LetA O n) W.EE (den i) * g i) *
            algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) (c₀ i m)) := by
          simp only [map_mul]; ring
      _ = _ := by
        rw [hgi]
        simp only [hNn, map_mul]
        ring

  have hpL : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  have hLetA' : ∀ j, DEN * lA W ^ κ * ((w0 ^ H * (letE a' * W.π₀ * w j)) * (W.q ^ H * W.φA (abelian₂ W A a e))) =
      W.q ^ (H + H) * ∑ i, Nn i * algebraMap O (LetA O n) (c₀ i j) := by
    intro j
    have h := hLetA j
    simp only [haa'] at h
    have hU' : W.φA (abelian₂ W A a e) = U := by rw [hUdef]; rfl
    rw [hU', pow_add, hw0, mul_pow]
    linear_combination (w0 ^ H * w0 ^ H * ps W 0 ^ H) * h
  have hexp : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → ∀ j' : ℤ,
      W.levN T a' ζ ⟨W.Q ^ (H + H) • z, hK⟩ j' ∈ Formalism.MainNotions.WachCoordinates.FilLev W T a' 0 (((H + H : ℕ) : ℤ) - j') := by
    intro ζ hζ j'
    set Fil' : ℤ → Submodule LL (T.V ⊗[Qp] B) := fun u =>
      (Formalism.MainNotions.WachCoordinates.FilLev W T a' 0 u).comap (ιV PD (LL := LL) (V := T.V)) with hFil'
    have hFa : Antitone Fil' := fun u u' h => Submodule.comap_mono (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T a' 0 h)
    rw [Ti.hEq]
    show levB T a' ζ ⟨W.Q ^ (H + H) • z, hK⟩ j' ∈ Fil' (((H + H : ℕ) : ℤ) - j')

    set cj : Fin d → LetA O n := fun j => w0 ^ H * (letE a' * W.π₀ * w j) with hcj
    have hsub : (⟨W.Q ^ (H + H) • z, hK⟩ : ↥(W.N T)) =
        ∑ j, cj j • (⟨_, hZN j⟩ : ↥(W.N T)) := Subtype.ext (by
          rw [Submodule.coe_sum]
          simp only [Submodule.coe_smul]
          exact hdec)
    have hdecB : levB T a' ζ ⟨W.Q ^ (H + H) • z, hK⟩ j' =
        ∑ j, smulS (W.lev a' ζ (cj j)) (levB T a' ζ ⟨_, hZN j⟩) j' := by
      rw [hsub, map_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [Formalism.MainNotions.UnusedSlot80.LevE.levB_smul W levB Ti.hEq Ti.hsupp]
    rw [hdecB]
    set N₀ : ℤ := (((PD.p - 1) * A.M PD.p : ℕ) : ℤ) + H with hN₀
    by_cases hlo : j' < N₀
    ·
      set vv : Fin d → T.V ⊗[Qp] B := fun j => ((PD.p : LL) ^ κ₀) •
        ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ (e + 1)) (cmpD W T (b j)) with hvv
      set g₁ : PowerSeries LL := W.lev a' ζ (W.q ^ H * W.φA (abelian₂ W A a e)) with hg₁
      have hagree : ∀ j, smulS (W.lev a' ζ (cj j)) (levB T a' ζ ⟨_, hZN j⟩) j' =
          smulS (W.lev a' ζ (cj j * (W.q ^ H * W.φA (abelian₂ W A a e)))) (fun k : ℤ => if k = 0 then vv j else 0) j' := by
        intro j
        obtain ⟨mj, hmj⟩ := Ti.hsupp T a' ζ ⟨_, hZN j⟩
        have hEF := Formalism.MainNotions.UnusedSlot80.LevE.expFrame0_of Ti C.hs C.hR C.hp0 C.h5 C.hH C.hCA A hA c' hc' T hT b sol hb
          e ζ hζ (A.M PD.p) κ₀ j (Hh j) (hHh j) H (hZN j)
        have h1 := Formalism.MainNotions.UnusedSlot80.LevE.smulS_congr_lt (LB_mono (fun k hk => hmj k hk) (min_le_left mj 0))
          (LB_mono (LB_smulS (LB_delta (vv j)) g₁) (min_le_right mj 0)) (W.lev a' ζ (cj j)) N₀ hEF j' hlo
        rw [h1, ← smulS_mul (LB_delta (vv j)), ← map_mul]
      rw [Finset.sum_congr rfl fun j _ => hagree j]

      obtain ⟨uD, huD, huDc⟩ : ∃ uD : PowerSeries LL, W.lev a' ζ DEN =
          PowerSeries.X ^ (∑ i, (-(α i 0)).toNat) * uD ∧ PowerSeries.constantCoeff uD ≠ 0 := by
        choose ui hui huic using fun i => lev_prod_ps Ti C.hR C.hp0 a' ζ hζ (fun s => (-(α i s)).toNat) (e + 1)
        refine ⟨∏ i, ui i, ?_, ?_⟩
        · rw [hDEN, map_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun i _ => by rw [hui i]; simp
        · rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => huic i
      have hl : W.lev a' ζ (lA W) = PowerSeries.C (PD.p : LL) := by
        unfold lA; rw [map_natCast, map_natCast]
      have hid : ∀ j, PowerSeries.C ((PD.p : LL) ^ κ) * (PowerSeries.X ^ (∑ i, (-(α i 0)).toNat) * uD) *
          W.lev a' ζ (cj j * (W.q ^ H * W.φA (abelian₂ W A a e))) =
          ∑ i, PowerSeries.C (algebraMap O LL (c₀ i j)) * W.lev a' ζ (W.q ^ (H + H) * Nn i) := by
        intro j
        rw [← huD]
        have h := congrArg (W.lev a' ζ) (hLetA' j)
        simp only [map_mul, map_pow, map_sum, hl] at h
        have h' : ∑ i, PowerSeries.C (algebraMap O LL (c₀ i j)) * W.lev a' ζ (W.q ^ (H + H) * Nn i) =
            W.lev a' ζ (W.q ^ (H + H)) * ∑ i, W.lev a' ζ (Nn i * algebraMap O (LetA O n) (c₀ i j)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul (W.lev a' ζ) (W.q ^ (H + H)) (Nn i), map_mul (W.lev a' ζ) (Nn i),
            AlgHom.commutes, PowerSeries.algebraMap_apply]
          ring
        rw [h']
        simp only [hcj, map_mul, map_pow, map_sum]
        linear_combination h
      have hdg := dg_core hFa (fun j => W.lev a' ζ (cj j * (W.q ^ H * W.φA (abelian₂ W A a e)))) vv
        (fun i j => algebraMap O LL (c₀ i j)) (fun i => W.lev a' ζ (W.q ^ (H + H) * Nn i)) (fun i => α i 0)
        (∑ i, (-(α i 0)).toNat) uD huDc ((PD.p : LL) ^ κ) (pow_ne_zero _ hpL) (((H + H : ℕ) : ℤ)) hid
        (fun i => 2 * H + (α i 0).toNat + ∑ i' ∈ Finset.univ.erase i, (-(α i' 0)).toNat)
        (fun i => by
          have h1 : (∑ x, (((-(α x 0)).toNat : ℕ) : ℤ)) = (((-(α i 0)).toNat : ℕ) : ℤ) +
              ∑ x ∈ Finset.univ.erase i, (((-(α x 0)).toNat : ℕ) : ℤ) :=
            (Finset.add_sum_erase Finset.univ (fun x => (((-(α x 0)).toNat : ℕ) : ℤ)) (Finset.mem_univ i)).symm
          have h2 := Int.toNat_sub_toNat_neg (α i 0)
          push_cast
          rw [h1]
          omega)
        (fun i => by
          obtain ⟨u₀, hu₀, -⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.lev_q_simple W a' ζ hζ
          obtain ⟨un, hun, -⟩ := lev_prod_ps Ti C.hR C.hp0 a' ζ hζ (fun s => (α i s).toNat) (e + 1)
          have hq : (PowerSeries.X : PowerSeries LL) ^ (H + H) ∣ W.lev a' ζ (W.q ^ (H + H)) := by
            rw [map_pow, hu₀, mul_pow]; exact Dvd.intro _ rfl
          have hnu : (PowerSeries.X : PowerSeries LL) ^ (α i 0).toNat ∣ W.lev a' ζ (num i) := by
            rw [hnum]; simp only at hun ⊢; rw [hun]
            simp only [Nat.add_one_ne_zero, if_false]; exact Dvd.intro _ rfl
          have hde : (PowerSeries.X : PowerSeries LL) ^ (∑ i' ∈ Finset.univ.erase i, (-(α i' 0)).toNat) ∣
              W.lev a' ζ (DENx i) := by
            rw [hDENx]
            simp only
            rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
            refine Finset.prod_dvd_prod_of_dvd _ _ fun i' _ => ?_
            obtain ⟨ud, hud, -⟩ := lev_prod_ps Ti C.hR C.hp0 a' ζ hζ (fun s => (-(α i' s)).toNat) (e + 1)
            rw [hden]; simp only at hud ⊢; rw [hud]
            simp only [Nat.add_one_ne_zero, if_false]; exact Dvd.intro _ rfl
          have h3 := mul_dvd_mul hq (mul_dvd_mul hnu hde)
          rw [← pow_add, ← pow_add] at h3
          rw [show 2 * H + (α i 0).toNat + ∑ i' ∈ Finset.univ.erase i, (-(α i' 0)).toNat =
            H + H + ((α i 0).toNat + ∑ i' ∈ Finset.univ.erase i, (-(α i' 0)).toNat) by ring]
          refine h3.trans (Dvd.intro (W.lev a' ζ (letE a') * W.lev a' ζ (u i)) ?_)
          rw [hNn]
          simp only [map_mul]
          ring)
        (fun i => by
          have hcond := (hg i).2 0 (by omega)
          show ιV PD (LL := LL) (V := T.V) (∑ j, algebraMap O LL (c₀ i j) • vv j) ∈
            Formalism.MainNotions.WachCoordinates.FilLev W T a' 0 (-(α i 0))
          have e1 : ∑ j, algebraMap O LL (c₀ i j) • vv j = ((PD.p : LL) ^ κ₀) • dvO W T (e + 1) b (c₀ i) := by
            unfold dvO dv
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hvv]; simp only; rw [smul_comm]
          rw [e1, map_smul]
          exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hcond))
      exact hdg j'
    ·
      rw [← hdecB]
      have hD := hmem T a' ζ ⟨_, hK⟩ j'
      obtain ⟨τ, hτ, hover⟩ := Formalism.MainNotions.UnusedSlot80.LevC.tau_over W C.hbij a'
      set Mw' : ℕ := Formalism.MainNotions.UnusedSlot80.PhiPowers.Mw A.G₀ A.S A.η (A.ty a') with hMw'
      have hJ : ∀ u, IsJumpV PD T.ρ τ u → -(Mw' : ℤ) ≤ u := fun u hu =>
        (Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty a') (hA.2.2.2.2.1 a') (hT.2 a' τ hτ u hu)).1
      have hlow := Formalism.MainNotions.UnusedSlot80.LevC.fil_low W T a' τ hover C.hbij.2 Mw' hJ hD
      have hMH : Mw' ≤ H := by
        have := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' (e + 1) (e + 1) (by omega) le_rfl
        rwa [Nat.sub_self] at this
      have hHh : H ≤ A.h := Formalism.MainNotions.UnusedSlot80.ArcC.hs_le_h A hA a' (e + 1) 0
      have hlt := Formalism.MainNotions.UnusedSlot80.ArcC.two_h_lt A C.h5p
      have hle : ((H + H : ℕ) : ℤ) - j' ≤ -(Mw' : ℤ) := by
        have : (N₀ : ℤ) ≤ j' := by omega
        rw [hN₀] at this
        push_cast at this ⊢
        nlinarith
      have hF := Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hlow
      show ιV PD (LL := LL) (V := T.V) (levB T a' ζ ⟨_, hK⟩ j') ∈ Formalism.MainNotions.WachCoordinates.FilLev W T a' 0 _
      refine Submodule.mem_map_of_mem (Submodule.mem_map.2 ⟨levB T a' ζ ⟨_, hK⟩ j', ⟨hF, ?_⟩, by simp⟩)
      simpa using hD
  have hz' : z ∈ W.N T := hMC T hT.1 a' z (H + H) hK hzl hexp
  exact ⟨z, ⟨hz', hzΔ⟩, hzl, (one_smul _ _).symm⟩

end Formalism.MainNotions.UnusedSlot80.LevM

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem lev0MprL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h : AdmArcA D HW F Cm)
    (hMC : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
      haveI := neZero_finrank_max_unramified K
      Formalism.MainNotions.N.Pv.LocalLengthBound.MemCrit ((HW l).W K 1 LL hG)) : LevelZeroModPRefinedLocal D HW := by
  intro l _ K LL hG hCA h5l A hA c' hc' T hT d b sol hb e
  have := neZero_finrank_max_unramified K
  have C := ctx_of D HW F Cm h l K LL hG hCA h5l
  have h4 := h.2.1
  exact LevM.lev0Mpr_of C (levETie_of D HW F Cm h4 l K LL hG) ((Cm l).C K 1 LL hG).tie.levB_mem
    (hMC l K LL hG hCA h5l) A hA c' hc' T hT b sol hb e

end Formalism.MainNotions.UnusedSlot80
