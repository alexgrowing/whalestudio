import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.NormCongruenceUnits.Hypotheses4N
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.ExLLeOfCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

namespace UpperTheory.Esk.PropMVAux

variable {l : ℕ} [Fact l.Prime]

theorem add_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_one_of {x : Qbar l} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - 1‖ ≠ ‖(1 : Qbar l)‖ := by rw [norm_one]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, norm_one, max_eq_right h.le] at h2

def oneU (l : ℕ) [Fact l.Prime] : Subgroup (Qbar l)ˣ where
  carrier := {x | ‖(x : Qbar l) - 1‖ < 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have e : ((a * b : (Qbar l)ˣ) : Qbar l) - 1 = a * (b - 1) + (a - 1) := by rw [Units.val_mul]; ring
    show ‖_‖ < 1
    rw [e]
    refine add_lt ?_ ha
    rw [norm_mul, norm_one_of ha, one_mul]
    exact hb
  inv_mem' {a} ha := by
    have e : (a : Qbar l) * (((a⁻¹ : (Qbar l)ˣ) : Qbar l) - 1) = -(a - 1) := by
      rw [mul_sub, Units.mul_inv]; ring
    have h := congrArg norm e
    rw [norm_mul, norm_one_of ha, one_mul, norm_neg] at h
    show ‖_‖ < 1
    rw [h]
    exact ha

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem cyc_mem (s : G F Ω) : cycBar F Ω l s ^ (l - 1) ∈ oneU l := by
  have e : ((cycBar F Ω l s ^ (l - 1) : (Qbar l)ˣ) : Qbar l) - 1 =
      algebraMap ℚ_[l] (Qbar l) ((((cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1 : ℤ_[l])) : ℚ_[l]) := by
    rw [Units.val_pow_eq_pow_val]
    change (algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l s : ℤ_[l]) : ℚ_[l])) ^ _ - 1 = _
    simp
  show ‖_‖ < 1
  rw [e, norm_algebraMap']
  change ‖(cycZ F Ω l s : ℤ_[l]) ^ (l - 1) - 1‖ < 1
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_pow,
    map_one, ZMod.pow_card_sub_one_eq_one, sub_self]
  exact ((cycZ F Ω l s).isUnit.map _).ne_zero

theorem cont_cyc : Continuous (cycBar F Ω l) :=
  have h : Continuous fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l]) :=
    (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom h).comp (continuous_cycZ F Ω l)

theorem cyc_frob [IsAlgClosure F Ω] {A : ValuationSubring Ω} {v : Pl F} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (h : IsPlaceOver A v) {σ : G F Ω} (hσ : IsFrob A (normV v) σ) :
    ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV v : Qbar l) := by
  change algebraMap ℚ_[l] (Qbar l) ((cycZ F Ω l σ : ℤ_[l]) : ℚ_[l]) = _
  rw [cycZ_of_isFrob hl h hσ]
  simp

theorem fin_l : {w : Pl F | ((l : ℕ) : 𝓞 F) ∈ w.asIdeal}.Finite := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

theorem cond_ex (ω : HChar F) {m : ℕ} (hm : 0 < m) (h : ω.OrderDvd m) :
    ∃ c : Pl F → ℕ, (∀ w, IsCondAt w ω (c w)) ∧ (∀ w, c w = 0 ↔ ω.UnrAt w) ∧ {w | c w ≠ 0}.Finite := by
  classical
  have ho := isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => congrArg (fun ξ : HChar F => ξ.1 x) h
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  have hex : ∀ w, ∃ n, ω.LevelLe w n := fun w => ⟨M, fun x hu hx => key w x hu fun _ => hx⟩
  have h0 : ∀ w, Nat.find (hex w) = 0 ↔ ω.UnrAt w := fun w => by rw [Nat.find_eq_zero, HChar.unrAt_iff]
  refine ⟨fun w => Nat.find (hex w), fun w => ⟨Nat.find_spec (hex w), fun n hn => Nat.find_min' (hex w) hn⟩, h0,
    hS.subset fun w hw => ?_⟩
  by_contra hS
  exact hw ((h0 w).2 fun x hx => key w x hx fun h => absurd h hS)

theorem loc_zpow {ω : HChar F} {w : Pl F} (hu : ω.UnrAt w) (x : (w.adicCompletion F)ˣ) :
    ∃ n : ℤ, ω.loc w x = ω.val w ^ n := by
  have hx0 : Valued.v (x : w.adicCompletion F) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v (x : w.adicCompletion F) = WithZero.exp n := ⟨_, (WithZero.exp_log hx0).symm⟩
  have hun : IsUnitAt w (x * atFin w (unif w) ^ n) := by
    have h2 := unif_spec w
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, hn, ← WithZero.exp_add]
    simp
  have h3 := hu _ hun
  rw [map_mul, map_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h3
  exact ⟨_, h3⟩

theorem closed_oneU : IsClosed (oneU l : Set (Qbar l)ˣ) := by
  have : IsClosed {x : Qbar l | ‖x - 1‖ < 1} := by
    simpa only [Metric.ball, dist_eq_norm] using IsUltrametricDist.isClosed_ball (1 : Qbar l) 1
  exact this.preimage Units.continuous_val

theorem dec_cong {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) {ι : Qbar l ≃+* ℂ} {ω : HChar F}
    {ξ : G F Ω →* (Qbar l)ˣ} (hc : Continuous ξ) (hL : IsLAdicOf art ι ω 0 ξ) {w : Pl F} (hu : ω.UnrAt w)
    (hv : ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1) {A : ValuationSubring Ω} (hA : IsPlaceOver A w) {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A) : Cong (ξ σ) 1 := by
  have hm : toAb F Ω σ ∈ (art.comp (localIdele F w)).range.topologicalClosure := by
    rw [ha.dec w A hA]
    exact ⟨σ, hσ, rfl⟩
  have hle : (art.comp (localIdele F w)).range ≤ (oneU l).comap (liftAb ξ hc) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := toAb_surjective (art (localIdele F w x))
    obtain ⟨n, hn⟩ := loc_zpow hu x
    have hv' : Units.map ι.symm.toRingHom.toMonoidHom (ω.val w) ∈ oneU l := hv
    have e : ξ τ = Units.map ι.symm.toRingHom.toMonoidHom (ω.val w) ^ n := by
      rw [← map_zpow, ← hn]
      exact Units.ext (hL.loc_away (Or.inr rfl) x τ hτ.symm)
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, ← hτ, liftAb_toAb, e]
    exact zpow_mem hv' _
  have h := Subgroup.topologicalClosure_minimal _ hle (closed_oneU.preimage (continuous_liftAb ξ hc)) hm
  rw [Subgroup.mem_comap, liftAb_toAb] at h
  exact h

theorem tr_det (ι : Qbar l ≃+* ℂ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (a b : ℂ)
    (h : M.charpoly.map ι.toRingHom = Polynomial.X ^ 2 - C a * Polynomial.X + C b) : M.trace = ι.symm a ∧ M.det = ι.symm b := by
  rw [Matrix.charpoly_fin_two] at h
  have h2 := congrArg (coeff · 1) h
  have h3 := congrArg (coeff · 0) h
  simp [coeff_X_pow, coeff_C] at h2 h3
  rw [← h2, ← h3]
  simp

theorem det_res [IsAlgClosure F Ω] (ξ : G F Ω →* (Qbar l)ˣ) (hξ : Continuous ξ) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (hr : Continuous r) (k : ℕ) (hk : l - 1 ∣ k) (hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w, w ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ‖(r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ σ⁻¹)‖ < 1 ∧
      (r σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ξ σ⁻¹ * (cycBar F Ω l σ : Qbar l) ^ k) :
    Matrix.GeneralLinearGroup.det.comp r = cycBar F Ω l ^ (-(k : ℤ)) * ξ ∧ ResSum r ![1, ξ] := by
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have c1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp (hr.comp continuous_inv)
  have c2 : Continuous fun g : G F Ω => (ξ g⁻¹ : Qbar l) := Units.continuous_val.comp (hξ.comp continuous_inv)
  have c3 : Continuous fun g : G F Ω => (cycBar F Ω l g : Qbar l) := Units.continuous_val.comp cont_cyc
  have hdet : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ξ g⁻¹ * (cycBar F Ω l g : Qbar l) ^ k := fun g => by
    refine congrFun (Continuous.ext_on hD c1.matrix_det (c2.mul (c3.pow k)) ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    exact (h v hv A hA σ hσ).2
  have htr : ∀ g : G F Ω, ‖(r g⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ g⁻¹)‖ < 1 := fun g => by
    have h0 : IsClosed {x : Qbar l | ‖x‖ < 1} := by
      simpa only [Metric.ball, dist_zero_right] using IsUltrametricDist.isClosed_ball (0 : Qbar l) 1
    have h1 := h0.preimage (c1.matrix_trace.sub (continuous_const.add c2 : Continuous fun g : G F Ω => 1 + (ξ g⁻¹ : Qbar l)))
    refine h1.closure_subset_iff.2 ?_ (hD g)
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    exact (h v hv A hA σ hσ).1
  refine ⟨MonoidHom.ext fun g => Units.ext ?_, fun g i => ?_⟩
  · have h1 := hdet g⁻¹
    rw [inv_inv] at h1
    change (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det = ((cycBar F Ω l g ^ (-(k : ℤ)) * ξ g : (Qbar l)ˣ) : Qbar l)
    rw [h1]
    simp [mul_comm]
  · have h1 := hdet g⁻¹
    have h2 := htr g⁻¹
    rw [inv_inv] at h1 h2
    have h3 : ‖(r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det - ξ g‖ < 1 := by
      obtain ⟨t, rfl⟩ := hk
      have h4 : ‖((cycBar F Ω l g⁻¹ ^ ((l - 1) * t) : (Qbar l)ˣ) : Qbar l) - 1‖ < 1 := by
        rw [pow_mul]; exact pow_mem (cyc_mem g⁻¹) t
      rw [h1, ← mul_sub_one, norm_mul, hn, one_mul, ← Units.val_pow_eq_pow_val]
      exact h4
    have e : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly - ∏ j, (Polynomial.X - C ((![1, ξ] j g : (Qbar l)ˣ) : Qbar l)) =
        C (-((r g : Matrix (Fin 2) (Fin 2) (Qbar l)).trace - (1 + ξ g))) * Polynomial.X + C ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)).det - ξ g) := by
      rw [Matrix.charpoly_fin_two, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.one_apply, Units.val_one, map_neg, map_sub, map_add, map_one]
      ring
    rw [← coeff_sub, e]
    rcases i with _ | _ | i
    · rwa [coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero, zero_add, coeff_C_zero]
    · rwa [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero, norm_neg]
    · rw [coeff_add, coeff_mul_X, coeff_C_succ, coeff_C_succ, add_zero, norm_zero]
      exact zero_lt_one

theorem norm_eq_one {x y : Qbar l} (hy : ‖y‖ = 1) (h : ‖x - y‖ < 1) : ‖x‖ = 1 := by
  have h1 : ‖x - y‖ ≠ ‖y‖ := by rw [hy]; exact h.ne
  have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1
  rwa [sub_add_cancel, hy, max_eq_right h.le] at h2

theorem nu_lt {ι : Qbar l ≃+* ℂ} {x : ℂ} : Wc.nu ι x < 1 ↔ ‖ι.symm x‖ < 1 := by
  rw [Wc.nu_apply, ← NNReal.coe_lt_one, coe_nnnorm]

theorem nu_eq {ι : Qbar l ≃+* ℂ} {x : ℂ} : Wc.nu ι x = 1 ↔ ‖ι.symm x‖ = 1 := by
  rw [Wc.nu_apply, ← NNReal.coe_eq_one, coe_nnnorm]

open Classical in
theorem prod_away {ι : Qbar l ≃+* ℂ} (D : Wc.LDat F ι) (S : Set (InfinitePlace F)) (t : ℕ) (w : Pl F)
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) = 1 :=
  Finset.prod_eq_one fun v _ => by
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hw (h ▸ D.mem v)

open Classical in
theorem prod_at {ι : Qbar l ≃+* ℂ} (D : Wc.LDat F ι) (S : Set (InfinitePlace F)) (t : ℕ) (w : Pl F) (v₀ : InfinitePlace F)
    (hv : D.pl v₀ = w) : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) = if v₀ ∈ S then (l : ℂ) ^ t else 1 := by
  rw [Finset.prod_eq_single v₀ (fun v _ hne => if_neg fun h => hne (D.inj (h.1.trans hv.symm)))
    (fun h => absurd (Finset.mem_univ _) h)]
  by_cases h : v₀ ∈ S <;> simp [hv, h]

end UpperTheory.Esk.PropMVAux
