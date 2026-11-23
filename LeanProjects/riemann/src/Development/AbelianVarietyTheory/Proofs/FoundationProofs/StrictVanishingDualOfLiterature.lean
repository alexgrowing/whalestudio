import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductUnramifiedClassesVanishesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductCoboundaryModStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScalingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductDualTwistIsTwoCocycleUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDualCocycleCoboundaryOfVanishOnFixingStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightCommutatorInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLiftStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairAlternatingNeOnCycloKernelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficientsStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherRest
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqComap

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.StrictKill

section Basic

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rb6.norm_le_one_of_mem c hx

theorem place_eq {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)} (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hv' : ((p : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' :=
  _root_.GlobalTheory.IdealComapPreimage.main hp hv hv'

theorem cg_self (n : ℕ) (a : Qbar l) : Cg n a a := by
  unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _

theorem cv_of_eq (n : ℕ) {a b : Fin 2 → Qbar l} (h : a = b) : Cv n a b := by
  subst h; intro i; exact cg_self n _

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem sub_one_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) (i j : Fin 2) :
    (M - 1) i j ∈ c.O := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  split_ifs
  · exact sub_mem (hM i j) (one_mem _)
  · exact sub_mem (hM i j) (zero_mem _)

theorem det_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) : M.det ∈ c.O := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

end Basic

section Twist

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem colRep_apply (W : R2 Ω l) (s : G ℚ Ω) (v : Fin 2 → Qbar l) : Loc.colRep W s v = mat W s *ᵥ v := by
  simp [Loc.colRep, mat, Matrix.toLin'_apply]

theorem mat_dual1 (W : R2 Ω l) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l)) • mat W s := by
  simp only [mat, dual1, tw_val, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, eps]

theorem dt_inv (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) : (dt W s)⁻¹ = dt W s := by
  have h := DFunLike.congr_fun h2 s
  simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h
  exact inv_eq_of_mul_eq_one_right h

theorem val_dt (W : R2 Ω l) (s : G ℚ Ω) : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem eps_eq (s : G ℚ Ω) :
    eps l s = algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rfl

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  rw [eps_eq]; exact c.O.algebraMap_mem _

theorem dual_representation_integral_entries (c : Coef l) (W : R2 Ω l) (hW : ∀ s i j, mat W s i j ∈ c.O) (h2 : dt W ^ 2 = 1) :
    ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  intro s i j
  rw [mat_dual1, dt_inv W h2, Matrix.smul_apply, smul_eq_mul, val_dt]
  exact mul_mem (mul_mem (eps_mem c s) (det_mem c (hW s))) (hW s i j)

theorem cont_dual1 (W : R2 Ω l) (hW : Continuous W) (h2 : dt W ^ 2 = 1) : Continuous (dual1 W) := by
  have he : Continuous (fun s : G ℚ Ω => eps l s) := by
    have hz : Continuous (fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) :=
      Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (continuous_subtype_val.comp hz)
  have hdv : Continuous (fun s => ((dt W s : (Qbar l)ˣ) : Qbar l)) := by
    simp only [val_dt]
    exact (Units.continuous_val.comp hW).matrix_det
  have hm : Continuous (fun s => mat (dual1 W) s) := by
    have : (fun s => mat (dual1 W) s) = fun s => (eps l s * ((dt W s : (Qbar l)ˣ) : Qbar l)) • mat W s := by
      funext s; rw [mat_dual1, dt_inv W h2]
    rw [this]; exact (he.mul hdv).smul (Units.continuous_val.comp hW)
  refine Units.continuous_iff.2 ⟨hm, ?_⟩
  have : (fun s => (((dual1 W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))) =
      fun s => mat (dual1 W) s⁻¹ := by
    funext s; simp [mat, map_inv]
  rw [this]; exact hm.comp continuous_inv

variable [IsAlgClosure ℚ Ω]

theorem cycZ_one {A : ValuationSubring Ω} {v : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) : cycZ ℚ Ω l σ = 1 :=
  Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
    rw [cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp)

theorem unr_dual1 (S : Finset Pl) (W : R2 Ω l) (hS : ContainsAbove S l)
    (hunr : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) :
    ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
  intro w hw B hB s hs
  have h1 : W s = 1 := hunr w hw B hB hs
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (hS w h)
  have h2 : cycZ ℚ Ω l s = 1 := cycZ_one hl hB hs
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [dual1, tw_val]
  simp [h1, h2, dt, cycBar]

end Twist

section Main

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem isIntegralCocycleOneModPow_of_integral_cocycle (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) {a : G ℚ Ω → Fin 2 → Qbar l}
    (ha : a ∈ Z1 (Loc.colRep W)) (hint : ∀ s i, a s i ∈ c.O) : Coc1 c n W H a := by
  refine ⟨ha.1.continuousOn, hint, fun s _ t _ => cv_of_eq n ?_⟩
  rw [ha.2 s t, colRep_apply]

theorem unr_smul (W : R2 Ω l) (a : Qbar l) {y : G ℚ Ω → Fin 2 → Qbar l} (h : Unr W y) :
    Unr W (fun s => a • y s) := by
  intro w hw
  obtain ⟨B, hB, x, hx⟩ := h w hw
  exact ⟨B, hB, a • x, fun s hs => by show a • y s = _; rw [hx s hs, Matrix.mulVec_smul, smul_sub]⟩

theorem trivial_cyclotomic_le_det_one (W : R2 Ω l) : N0g W ≤ H0g W := by
  intro g hg
  rw [N0g, Subgroup.mem_inf] at hg
  rw [H0g, Subgroup.mem_inf]
  refine ⟨hg.1, ?_⟩
  have h1 : W g = 1 := hg.2
  rw [MonoidHom.mem_ker]
  simp [dt, h1]

theorem commutator_det_one_le (W : R2 Ω l) : ⁅H0g W, H0g W⁆ ≤ H0g W := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem main : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A := by
  intro hLit l _ Ω _ _ _ e S A W hN hES z hz hzU hzT
  by_contra hzB
  obtain ⟨c, y, S', hWc, hy, hyc, hyU, hyG, hT⟩ := hES

  obtain ⟨c1, k1, hcc1, hy1int, hy1loc, -, -⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c y hN.cont hWc hN.unr hy hyU A
  have hWc1 : ∀ s i j, mat W s i j ∈ c1.O := fun s i j => hcc1 (hWc s i j)
  obtain ⟨c2, k2, hc12, hz2int, hz2loc, hz2triv, -⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S (dual1 W) c1 z
    (cont_dual1 W hN.cont hN.det2) (dual_representation_integral_entries c1 W hWc1 hN.det2) (unr_dual1 S W hN.above hN.unr) hz hzU A
  have hWc2 : ∀ s i j, mat W s i j ∈ c2.O := fun s i j => hc12 (hWc1 s i j)
  set a1 : Qbar l := ((l : ℕ) : Qbar l) ^ k1 with ha1def
  set a2 : Qbar l := ((l : ℕ) : Qbar l) ^ k2 with ha2def
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := by
    intro h0
    have := norm_l_lt_one (l := l)
    have h1 : ‖((l : ℕ) : Qbar l)‖ = 0 := by rw [h0, norm_zero]
    have h2 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := (map_natCast _ _).symm
    rw [h2, norm_algebraMap', Padic.norm_p] at h1
    have : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
    linarith
  have ha1 : a1 ≠ 0 := pow_ne_zero _ hl0
  have ha2 : a2 ≠ 0 := pow_ne_zero _ hl0
  set y' : G ℚ Ω → Fin 2 → Qbar l := fun s => a1 • y s with hy'def
  set z' : G ℚ Ω → Fin 2 → Qbar l := fun s => a2 • z s with hz'def
  have hy' : y' ∈ Z1 (Loc.colRep W) := (Z1 (Loc.colRep W)).smul_mem a1 hy
  have hz' : z' ∈ Z1 (Loc.colRep (dual1 W)) := (Z1 (Loc.colRep (dual1 W))).smul_mem a2 hz
  have hy'int : ∀ s i, y' s i ∈ c2.O := fun s i => hc12 (hy1int s i)
  have hz'int : ∀ s i, z' s i ∈ c2.O := fun s i => hz2int s i
  have hy'U : Unr W y' := unr_smul W a1 hyU
  have hz'U : Unr (dual1 W) z' := unr_smul (dual1 W) a2 hzU
  have ha1O : a1 ∈ c2.O := pow_mem (natCast_mem _ _) _
  have hT' : ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
      KillsMu (normV w) ψ → Function.Surjective ψ → Tame c2 W y' n w ψ :=
    fun n hn w hw hd ψ hK hs => GlobalTheory.T.eulerSystemTameClass_scale_enlarge_coefficients l Ω W c c2 y n w ψ a1 (le_trans hcc1 hc12) ha1O (hT n hn w hw hd ψ hK hs)
  obtain ⟨xA, hxA, hxAe⟩ := hz2triv hzT

  have hloc : ∀ n : ℕ, ∀ v ∈ S, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      Cob2 c2 n (Dec (F := ℚ) B) (cup W y' z') := by
    intro n v _
    by_cases hlv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨v0, hAv0, hlv0⟩ := hN.atL
      have hv : v = v0 := place_eq (Fact.out : l.Prime) hlv hlv0
      subst hv
      refine ⟨A, hAv0, ?_⟩
      exact GlobalTheory.T.cup_product_coboundary_mod l Ω c2 n W (Dec (F := ℚ) A) y' z' hN.cont hWc2 hN.det2
        (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy' hy'int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz' hz'int)
        (Or.inr ⟨xA, hxA, fun s hs => cv_of_eq n (hxAe s hs)⟩)
    · obtain ⟨B, hB, -⟩ := hyU v hlv
      obtain ⟨x1, hx1, hx1e⟩ := hy1loc v hlv B hB
      obtain ⟨x2, hx2, hx2e⟩ := hz2loc v hlv B hB
      exact ⟨B, hB, GlobalTheory.T.cupProduct_unramifiedClasses_vanishes hLit l Ω c2 n W v B y' z' hN.cont hWc2 hN.det2 hB hlv
        (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy' hy'int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz' hz'int)
        ⟨x1, fun i => hc12 (hx1 i), fun s hs => cv_of_eq n (hx1e s hs)⟩
        ⟨x2, hx2, fun s hs => cv_of_eq n (hx2e s hs)⟩⟩

  have hyN : ∃ g ∈ N0g W, y' g ≠ 0 := by
    by_contra h
    push_neg at h
    apply hyG
    refine GlobalTheory.T.greenbergOrdinary_of_vanishing_on_cycloKernel l Ω e S A W hN y hy fun g hg => ?_
    have := h g hg
    exact (smul_eq_zero.mp this).resolve_left ha1
  have hzN : ∃ g ∈ N0g W, z' g ≠ 0 := by
    by_contra h
    push_neg at h
    apply hzB
    refine GlobalTheory.T.tateDual_cocycle_coboundary_of_vanish_on_fixing l Ω e S A W hN z hz fun g hg => ?_
    have := h g hg
    exact (smul_eq_zero.mp this).resolve_left ha2
  obtain ⟨g, hg, h, hh, hne⟩ := GlobalTheory.T.cocycle_pair_alternating_ne_on_cycloKernel l Ω e S A W hN y' hy' z' hz' hyN hzN
  obtain ⟨φ, hφ, hde⟩ := GlobalTheory.T.exists_commutator_det_nonzero l Ω e S A W hN
  have hφH : φ ∈ H0g W := commutator_det_one_le W hφ
  have hgW : W g = 1 := (Subgroup.mem_inf.mp hg).2
  have hhW : W h = 1 := (Subgroup.mem_inf.mp hh).2
  have hcomm : g * h * g⁻¹ * h⁻¹ ∈ ⁅H0g W, H0g W⁆ := by
    have := Subgroup.commutator_mem_commutator (trivial_cyclotomic_le_det_one W hg) (trivial_cyclotomic_le_det_one W hh)
    rwa [commutatorElement_def] at this
  have hφ1 : φ * (g * h * g⁻¹ * h⁻¹) ∈ ⁅H0g W, H0g W⁆ := mul_mem hφ hcomm
  have hmat : mat W (φ * (g * h * g⁻¹ * h⁻¹)) = mat W φ := by
    simp [mat, map_mul, map_inv, hgW, hhW]
  set de : Qbar l := (mat W φ - 1).det with hdedef
  set de' : Qbar l := om (y' h) (z' g) - om (y' g) (z' h) with hde'def
  have hde' : de' ≠ 0 := sub_ne_zero.mpr hne
  have hdeO : ‖de‖ ≤ 1 := norm_le_one_of_mem c2 (det_mem c2 (sub_one_mem c2 (hWc2 φ)))

  have key : ∀ n : ℕ, 1 ≤ n → ‖de ^ 2 * de'‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n hn
    obtain ⟨u, hu, huint, huS, hucup⟩ := GlobalTheory.T.local_cochains_glue_global hLit l Ω c2 n S (cup W y' z') hN.l_odd hN.above
      (GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified l Ω c2 n S W y' z' hN.cont hWc2 hN.det2 hN.above hN.unr hy' hz' hy'int hz'int hy'U hz'U)
      (hloc n)
    have hr := GlobalTheory.T.cohomology_unramified_lift hLit l Ω e S A W hN c2 y' z' u S' n hn hWc2 hy' hz' hy'int hz'int hy'U hz2loc
      ⟨xA, hxA, hxAe⟩ (hT' n hn) hu huint huS hucup
    have hc := GlobalTheory.T.height_commutator_invariance l Ω n c2 W y' z' u hWc2 hy' hz' hucup φ hφH g hg h hh
    have h0 := hr φ hφ
    have h1 := hr _ hφ1
    rw [hmat] at h1
    unfold Cg at h0 h1 hc
    rw [sub_zero] at h0 h1
    set L := ‖((l : ℕ) : Qbar l) ^ n‖
    set t1 := ht W y' z' u (φ * (g * h * g⁻¹ * h⁻¹))
    set t0 := ht W y' z' u φ
    have e1 : de ^ 2 * de' = de * (de * de' - (t1 - t0)) + de * t1 - de * t0 := by ring
    have b1 : ‖de * (de * de' - (t1 - t0))‖ ≤ L := by
      rw [norm_mul, norm_sub_rev]
      calc ‖de‖ * ‖t1 - t0 - de * de'‖ ≤ 1 * L := by
            gcongr
        _ = L := one_mul L
    rw [e1]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact h0))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le b1 h1)
  have hx0 : de ^ 2 * de' ≠ 0 := mul_ne_zero (pow_ne_zero 2 hde) hde'
  have hpos : 0 < ‖de ^ 2 * de'‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (norm_l_lt_one (l := l))
  have hk := key (n + 1) (by omega)
  rw [norm_pow] at hk
  have hmono : ‖((l : ℕ) : Qbar l)‖ ^ (n + 1) ≤ ‖((l : ℕ) : Qbar l)‖ ^ n :=
    pow_le_pow_of_le_one (norm_nonneg _) (norm_l_lt_one (l := l)).le (by omega)
  linarith

end Main

end GlobalTheory.Ord2.StrictKill
