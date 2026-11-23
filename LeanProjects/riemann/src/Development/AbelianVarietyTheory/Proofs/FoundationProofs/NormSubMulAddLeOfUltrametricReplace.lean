import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalConditionsIndependentOfPlaceOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsPlaceOverRat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RatUnramToIntUnram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameOfShCoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobOfShapiroSystem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameClassLimitOfNormCompatibleShapiroSystemStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameShapiroSystemLimitUnramifiedAwayFromLStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

noncomputable section

namespace GlobalTheory.KZ

open GlobalTheory.KZGlobAsm in

theorem glob_of_shapiro_system_noLayer (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (W : R2 Ω l) (c : Coef l) (A : ValuationSubring Ω) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l)
    (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (hWc : Continuous W) (hθc : Continuous θ) (hWO : ∀ s i j, mat W s i j ∈ c.O) (hWθ : ∀ s, mat W s = (θ s : Qbar l) • ρ s)
    (hρO : ∀ s i j, ρ s i j ∈ c.O) (hχO : ∀ r x, χ r x ∈ c.O)
    (hχc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hcong : ∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (hY : ∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) (hYc : ∀ r x i, Continuous fun s => Y r s x i)
    (hYO : ∀ r s x i, Y r s x i ∈ c.O)
    (hYp : ∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) :
    ∃ y : G ℚ Ω → Fin 2 → Qbar l, y ∈ Z1 (Loc.colRep W) ∧ (∀ s i, y s i ∈ c.O) ∧ Unr W y ∧
      (∀ r s i, ‖y s i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
      SpLink A e χ (fun r s x => Y r s x 1) y := by
  set η : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l := fun r x => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x with hη
  have hηO : ∀ r x, η r x ∈ c.O := fun r x => c.O.mul_mem (inv_pow_val_mem l c e r x) (hχO r x)
  have hηn : ∀ r x, ‖η r x‖ ≤ 1 := fun r x => norm_le_one_of_mem c (hηO r x)
  have hYn : ∀ r s x i, ‖Y r s x i‖ ≤ 1 := fun r s x i => norm_le_one_of_mem c (hYO r s x i)
  have hηc := eta_compat l c e χ hχO hχc
  set a : ℕ → G ℚ Ω → Fin 2 → Qbar l := fun r => spec (η r) (Y r) with ha
  have haE : ∀ r s i, a r s i = ∑ x, η r x * Y r s x i := by
    intro r s i; simp only [ha, spec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have haO : ∀ r s i, a r s i ∈ c.O := by
    intro r s i; rw [haE]; exact c.O.sum_mem fun x _ => c.O.mul_mem (hηO r x) (hYO r s x i)
  have haN : ∀ r s i, ‖a r s i‖ ≤ 1 := fun r s i => norm_le_one_of_mem c (haO r s i)
  have hstep : ∀ r s i, ‖a (r + 1) s i - a r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
    spec_cauchy l Y η hYn hηn hYp hηc
  have hlim : ∀ s i, ∃ b ∈ c.O, ∀ r, ‖b - a r s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
    fun s i => GlobalTheory.coef_limit l c (fun r => a r s i) (fun r => haO r s i) (fun r => hstep r s i)
  choose y hyO hyA using hlim
  have happ : ∀ r s t i, ‖a r (s * t) i - (a r s + mat W s *ᵥ a r t) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
    intro r s t i
    have h := spec_approx_cocycle l r ρ (cycMod ℚ Ω l r)⁻¹ (Y r) (η r) (fun s => (θ s : Qbar l)) (hY r)
      (fun s i j => norm_le_one_of_mem c (hρO s i j)) (hYn r) (hηn r)
      (fun s x => by simpa only [MonoidHom.inv_apply, inv_inv] using hcong r s x) s t i
    rw [hWθ s, Matrix.smul_mulVec]
    exact h
  have hcoc : ∀ s t, y (s * t) = y s + mat W s *ᵥ y t :=
    GlobalTheory.T.isCocycle_of_padic_limit_of_approx_cocycles l (mat W) a y (fun s i j => norm_le_one_of_mem c (hWO s i j)) haN happ
      (fun r s i => hyA s i r)
  have hac : ∀ r i, Continuous fun s => a r s i := by
    intro r i
    simp only [haE]
    exact continuous_finset_sum _ fun x _ => continuous_const.mul (hYc r x i)
  have hyc : Continuous y := by
    refine continuous_pi fun i => ?_
    refine TendstoUniformly.continuous (F := fun r s => a r s i) (p := Filter.atTop) ?_
      (Filter.Eventually.of_forall fun r => hac r i).frequently
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hq1 : ‖((l : ℕ) : Qbar l)‖ < 1 := GlobalTheory.norm_natCast_prime_qbar l
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq1
    filter_upwards [(ht.eventually (gt_mem_nhds hε))] with r hr s
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (by simpa [norm_pow] using hyA s i r) hr
  have hZ1 : y ∈ Z1 (Loc.colRep W) := by
    refine ⟨hyc, fun g h => ?_⟩
    rw [hcoc g h]
    rfl
  refine ⟨y, hZ1, hyO, ?_, fun r s i => hyA s i r, GlobalTheory.T.kummerScalarLayerLink_of_shapiroSpecialization_approx l Ω A e χ Y y (fun r s _ _ => hyA s 1 r)⟩
  exact GlobalTheory.T.unramified_away_from_l_of_twisted_shapiro_limit l Ω W c θ ρ Y η y hWc hθc hWO hWθ hρO hYc hYO hY hYp hηO (fun r s x => hcong r s x) hZ1
    (fun r s i => hyA s i r)

theorem iwSys2_of_shCoc (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (A : ValuationSubring Ω) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l))
    (ν : G ℚ Ω → (Qbar l)ˣ) (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
    (hWθ : ∀ s, mat W s = (θ s : Qbar l) • ρ s)
    (hY : ∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) (hO : ∀ r s x i, Y r s x i ∈ c.O)
    (hN : ∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)
      (Y (r + 1)) s)
    (hρ : ∀ s ∈ Dec (F := ℚ) A, ρ s 1 0 = 0 ∧ ρ s 1 1 = (ν s : Qbar l)) :
    IwSys2 c A ν (fun r s x => Y r s x 1) := by
  have hρmul : ∀ s t, ρ (s * t) = ρ s * ρ t := by
    intro s t
    have h := mat_mul' W s t
    rw [hWθ, hWθ, hWθ, map_mul, Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h
    exact smul_right_injective _ (mul_ne_zero (θ s).ne_zero (θ t).ne_zero) h
  refine ⟨fun s hs t ht => ?_, fun r => ⟨fun s x => hO r s x 1, fun s hs t _ x => ?_⟩, fun r s x => ?_⟩
  · apply Units.ext
    rw [Units.val_mul, ← (hρ _ (mul_mem hs ht)).2, ← (hρ s hs).2, ← (hρ t ht).2, hρmul, Matrix.mul_apply,
      Fin.sum_univ_two, (hρ s hs).1, zero_mul, zero_add]
  · have h := congrFun (hY r s t x) 1
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, (hρ s hs).1, (hρ s hs).2, zero_mul,
      zero_add, MonoidHom.inv_apply] at h
    exact h
  · have h := congrFun (congrFun (hN r s) x) 1
    simp only [push, Finset.sum_apply] at h
    exact h

end GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem norm_sub_mul_add_le_of_ultrametric_replace {l : ℕ} [Fact l.Prime] {a b c' d P : Qbar l} {ε : ℝ} (h1 : ‖a - (P * b + d)‖ ≤ ε)
    (h2 : ‖c' - b‖ ≤ ε) (hP : ‖P‖ ≤ 1) : ‖a - (P * c' + d)‖ ≤ ε := by
  have e : a - (P * c' + d) = (a - (P * b + d)) + P * (b - c') := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rw [norm_mul, norm_sub_rev b c']
  exact (mul_le_of_le_one_left (norm_nonneg _) hP).trans h2

theorem middle_glue2 : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (A : ValuationSubring Ω) (e : ℕ) (S : Finset Pl) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ)
    (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ν : G ℚ Ω → (Qbar l)ˣ)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  Continuous W → Continuous θ → (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) →
  (∀ s i j, ρ s i j ∈ c.O) → (∀ r x, χ r x ∈ c.O) →
  (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) →
  (∀ r, ShCoc ρ (cycMod ℚ Ω l r)⁻¹ (Y r)) → (∀ r x i, Continuous fun s => Y r s x i) → (∀ r s x i, Y r s x i ∈ c.O) →
  (∀ r s, Y r s = push (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) (Y (r + 1)) s) →
  (∀ s ∈ Dec (F := ℚ) A, ρ s 1 0 = 0 ∧ ρ s 1 1 = (ν s : Qbar l)) →
  (∀ w : Pl, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) →
  (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∀ s ∈ Ine (F := ℚ) B, θ s = 1) →
  (∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
    KillsMu (normV w) ψ → Function.Surjective ψ →
    ∃ (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (P u : Qbar l)
      (b : ℕ → Fin 2 → Qbar l),
      (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) ∧ (∀ r x i, Continuous fun s => Yw r s x i) ∧
      (∀ r s x i, Yw r s x i ∈ c.O) ∧
      (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) ∧
      P ∈ c.O ∧ ‖u‖ = 1 ∧ (∀ r i, b r i ∈ c.O) ∧
      (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i -
          (P • spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
      (∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n P (u * (mat W σ - 1).det))) →
  ∃ (m : ℕ) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl),
    (∀ r s i, ‖y s i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (Y r) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
    Sys W c (fun s => (((l : ℕ) : Qbar l) ^ m) • y s) S' ∧ IwSys2 c A ν (fun r s x => ((l : ℕ) : Qbar l) ^ m * Y r s x 1) ∧
    SpLink A e χ (fun r s x => ((l : ℕ) : Qbar l) ^ m * Y r s x 1) (fun s => (((l : ℕ) : Qbar l) ^ m) • y s) := by
  intro l _ Ω _ _ _ W c A e S χ θ ρ ν Y hW hθc hWO hWθ hρO hχO hχcomp hχtw hY hYc hYO hYpush hDec hunrS hθI htame
  have hLO : ((l : ℕ) : Qbar l) ∈ c.O := natCast_mem c.O l
  have hL1 : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := GlobalTheory.Ord2.FirstDer.norm_le_one_of_mem c hLO
  obtain ⟨y0, hZ1, hy0O, hUnr0, hap0, hSp⟩ :=
    glob_of_shapiro_system_noLayer l Ω W c A e χ θ ρ Y hW hθc hWO hWθ hρO hχO hχcomp hχtw hY hYc hYO hYpush
  have hIw := iwSys2_of_shCoc l Ω W c A θ ρ ν Y hWθ hY hYO hYpush hDec
  let Bq : Pl → ValuationSubring Ω := fun q => Classical.choose (GlobalTheory.exists_isPlaceOver_rat Ω q)
  have hBq : ∀ q, IsPlaceOver (Bq q) q := fun q => Classical.choose_spec (GlobalTheory.exists_isPlaceOver_rat Ω q)
  let mq : Pl → ℕ := fun q => Classical.choose (GlobalTheory.rat_unram_to_int_unram l Ω W c (Bq q) hW hWO)
  have hmq : ∀ q, ∀ (Z : G ℚ Ω → Fin 2 → Qbar l) (v : Fin 2 → Qbar l), (∀ s i, Z s i ∈ c.O) →
      (∀ s ∈ Ine (F := ℚ) (Bq q), Z s = mat W s *ᵥ v - v) → ∃ t : Fin 2 → Qbar l, (∀ i, t i ∈ c.O) ∧
        ∀ s ∈ Ine (F := ℚ) (Bq q), (((l : ℕ) : Qbar l) ^ mq q) • Z s = mat W s *ᵥ t - t :=
    fun q => Classical.choose_spec (GlobalTheory.rat_unram_to_int_unram l Ω W c (Bq q) hW hWO)
  have hpowO : ∀ k, ((l : ℕ) : Qbar l) ^ k ∈ c.O := fun k => pow_mem hLO k
  refine ⟨S.sup mq, y0, S, fun r s i => hap0 r s i, ⟨hWO, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (Z1 (Loc.colRep W)).smul_mem _ hZ1
  · intro s i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_mem (hpowO _) (hy0O s i)
  · intro q hq
    obtain ⟨B, hB, x, hx⟩ := hUnr0 q hq
    refine ⟨B, hB, ((l : ℕ) : Qbar l) ^ S.sup mq • x, fun s hs => ?_⟩
    show ((l : ℕ) : Qbar l) ^ S.sup mq • y0 s = _
    rw [hx s hs, Matrix.mulVec_smul, smul_sub]
  · intro n hn w hwS hdiv ψ hkill hsurj
    obtain ⟨Yw, P, u, b, hYw, hYwc, hYwO, hYwpush, hP, hu, hb, happ, hfrob⟩ := htame n hn w hwS hdiv ψ hkill hsurj
    have hP1 : ‖P‖ ≤ 1 := GlobalTheory.Ord2.FirstDer.norm_le_one_of_mem c hP
    have happ' : ∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i - (P • y0 s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
      intro r s i
      have h1 := happ r s i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      exact norm_sub_mul_add_le_of_ultrametric_replace h1 (hap0 r s i) hP1
    obtain ⟨Yt, b', hYt, hYtc, hYtO, hb'O, hsum, hYtap⟩ :=
      GlobalTheory.T.tameClass_limit_of_normCompatible_shapiroSystem l Ω W c e n χ θ ρ ψ Yw y0 P b hWO hWθ hρO hχO hχcomp hχtw hYw hYwc hYwO hYwpush hP hb hy0O happ'
    refine GlobalTheory.KZ.tame_of_shCoc l Ω c W _ n w ψ (fun s x => ((l : ℕ) : Qbar l) ^ S.sup mq • Yt s x) P u
      (((l : ℕ) : Qbar l) ^ S.sup mq • b') ?_ ?_ ?_ hP hu ?_ ?_ hfrob ?_
    · intro s t x
      show ((l : ℕ) : Qbar l) ^ S.sup mq • Yt (s * t) x = ((l : ℕ) : Qbar l) ^ S.sup mq • Yt s x +
        mat W s *ᵥ (((l : ℕ) : Qbar l) ^ S.sup mq • Yt t (x * ψ s))
      rw [hYt s t x, smul_add, Matrix.mulVec_smul]
    · intro x i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact continuous_const.mul (hYtc x i)
    · intro s x i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (hpowO _) (hYtO s x i)
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (hpowO _) (hb'O i)
    · intro s
      rw [← Finset.smul_sum, hsum s, smul_add, smul_comm (((l : ℕ) : Qbar l) ^ S.sup mq) P (y0 s),
        Matrix.mulVec_smul, smul_sub]
    · intro q hqw hql
      refine ⟨Bq q, hBq q, ?_⟩
      have hψθ : ∀ s ∈ Ine (F := ℚ) (Bq q), ψ s = 1 ∧ θ s = 1 := fun s hs =>
        ⟨GlobalTheory.Ord2.FirstDer.killsMu_ine hqw hkill (hBq q) hs, hθI q hql (Bq q) (hBq q) s hs⟩
      obtain ⟨v, hv⟩ := GlobalTheory.T.tameShapiroSystem_limit_unramified_away_from_l l Ω W c n e χ θ ρ ψ Yw Yt q (Bq q) hql (hBq q) hψθ hW hWO hWθ hρO hχO
        hYw hYwc hYwO hYwpush hYtap
      by_cases hqS : q ∈ S
      · have hle : mq q ≤ S.sup mq := Finset.le_sup hqS
        have hex : ∀ a, ∃ t : Fin 2 → Qbar l, (∀ i, t i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) (Bq q),
            (((l : ℕ) : Qbar l) ^ mq q) • Yt s a = mat W s *ᵥ t - t :=
          fun a => hmq q (fun s => Yt s a) (v a) (fun s i => hYtO s a i) (fun s hs => hv s hs a)
        choose t ht1 ht2 using hex
        refine ⟨fun a => ((l : ℕ) : Qbar l) ^ (S.sup mq - mq q) • t a, fun a i => ?_, fun s hs a => ?_⟩
        · simp only [Pi.smul_apply, smul_eq_mul]
          exact mul_mem (hpowO _) (ht1 a i)
        · have hpow : ((l : ℕ) : Qbar l) ^ S.sup mq =
              ((l : ℕ) : Qbar l) ^ (S.sup mq - mq q) * ((l : ℕ) : Qbar l) ^ mq q := by
            rw [← pow_add, Nat.sub_add_cancel hle]
          show ((l : ℕ) : Qbar l) ^ S.sup mq • Yt s a = _
          rw [hpow, mul_smul, ht2 a s hs, Matrix.mulVec_smul, smul_sub]
      · refine ⟨fun _ => 0, fun _ _ => zero_mem _, fun s hs a => ?_⟩
        have hW1 : W s = 1 := hunrS q hqS (Bq q) (hBq q) hs
        have hm1 : mat W s = 1 := by simp [mat, hW1]
        show ((l : ℕ) : Qbar l) ^ S.sup mq • Yt s a = _
        rw [hv s hs a, hm1]
        simp
  · refine ⟨hIw.1, fun r => ⟨fun s x => ?_, fun s hs t ht x => ?_⟩, fun r s x => ?_⟩
    · exact mul_mem (hpowO _) ((hIw.2.1 r).1 s x)
    · have h := (hIw.2.1 r).2 s hs t ht x
      simp only at h ⊢
      rw [h]
      ring
    · have h := hIw.2.2 r s x
      simp only at h ⊢
      rw [h, Finset.mul_sum]
  · intro n
    obtain ⟨r0, hr0⟩ := hSp n
    refine ⟨r0, fun r hr s hs hcyc => ?_⟩
    have h := hr0 r hr s hs hcyc
    unfold Cg sp at h ⊢
    simp only [Pi.smul_apply, smul_eq_mul] at h ⊢
    have hk : ‖((l : ℕ) : Qbar l) ^ S.sup mq‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hL1
    refine le_trans ?_ h
    rw [← Finset.sum_congr rfl fun x _ => (mul_left_comm _ (((l : ℕ) : Qbar l) ^ S.sup mq) _).symm,
      ← Finset.mul_sum, ← mul_sub, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hk

end GlobalTheory.KZ
